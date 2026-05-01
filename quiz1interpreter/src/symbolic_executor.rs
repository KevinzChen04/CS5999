use patronus::expr::{Context, Expr, ExprRef, ForEachChild, SerializableIrNode, Type, TypeCheck, simplify_single_expression, simple_transform_expr};
use patronus::smt::{CheckSatResponse, SolverContext};
use patronus::system::TransitionSystem;
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StepResult {
    Ok,
    BadStateReached,
}

#[derive(Debug, Clone, Default)]
pub struct ExecutionStats {
    /// Total number of ITE nodes encountered during symbolic execution.
    /// This is the requested "branching path" count regardless of feasibility/forking.
    pub ite_encountered: usize,
    /// Number of calls to `check_condition_sat` (proxy for SMT calls).
    pub smt_calls: usize,
    /// Number of states in the transition system.
    pub state_variables: usize,
    /// Number of transition statements (`state.next` present).
    pub transition_statements: usize,
    /// Total number of unique ITE nodes in the transition system (static, pre-execution).
    pub static_ite_count: usize,
    /// Cumulative number of paths generated before merge over all steps.
    pub total_paths_generated: usize,
    /// Number of active paths after the most recent merge.
    pub active_paths: usize,
}

#[derive(Clone)]
pub struct ExecutionPath {
    pub state_translation: HashMap<ExprRef, ExprRef>,
    /// State values before the most recent transition, used to evaluate system
    /// constraints together with the current inputs (constraints relate
    /// pre-transition state to the inputs that drive the transition).
    pub pre_transition_state: HashMap<ExprRef, ExprRef>,
    pub path_conditions: Vec<ExprRef>,
    /// Pre-computed substituted+simplified forms of `path_conditions`, ready to
    /// assert directly to the solver without any further processing.
    pub asserted_path_conditions: Vec<ExprRef>,
    pub input_translation: HashMap<ExprRef, ExprRef>,
    pub post_transition_state: HashMap<ExprRef, ExprRef>,
    /// Pre-computed substituted+simplified system constraints for this path's
    /// state/input context, ready to assert directly to the solver.
    pub asserted_constraints: Vec<ExprRef>,
}

impl ExecutionPath {
    pub fn new() -> Self {
        ExecutionPath {
            state_translation: HashMap::new(),
            pre_transition_state: HashMap::new(),
            path_conditions: Vec::new(),
            asserted_path_conditions: Vec::new(),
            input_translation: HashMap::new(),
            post_transition_state: HashMap::new(),
            asserted_constraints: Vec::new(),
        }
    }

    pub fn serialize_to_str(&self, ctx: &Context) -> String {
        let mut result = String::new();
        result.push_str("ExecutionPath {\n");

        result.push_str("  variable_definitions:\n");
        for (key, value) in &self.state_translation {
            result.push_str(&format!("\t{} -> {}\n", key.serialize_to_str(ctx), value.serialize_to_str(ctx)));
        }

        result.push_str("  path_conditions:\n");
        for cond in &self.path_conditions {
            result.push_str(&format!("\t{}\n", cond.serialize_to_str(ctx)));
        }

        result.push_str("  input_translation:\n");
        for (key, value) in &self.input_translation {
            result.push_str(&format!("\t{} -> {}\n", key.serialize_to_str(ctx), value.serialize_to_str(ctx)));
        }

        result.push_str("}");
        result
    }
}

pub struct SymbolicExecutor {
    ts: TransitionSystem,
    current_step: usize,
    paths: Vec<ExecutionPath>,
    state_types: HashMap<ExprRef, Type>,
    input_types: HashMap<ExprRef, Type>,
    all_symbols: HashSet<ExprRef>,
    /// Symbols added since the last time they were declared to the solver.
    /// Drained at the start of `check_condition_sat` (before any push) so
    /// that declarations live at solver level 0 and survive push/pop cycles.
    pending_declarations: Vec<ExprRef>,
    constraints: Vec<ExprRef>,
    bad_state: Option<(ExprRef, ExecutionPath)>,
    stats: ExecutionStats,
}

impl SymbolicExecutor {
    pub fn new(ts: &TransitionSystem) -> Self {
        SymbolicExecutor {
            ts: ts.clone(),
            current_step: 0,
            paths: Vec::new(),
            state_types: HashMap::new(),
            input_types: HashMap::new(),
            all_symbols: HashSet::new(),
            pending_declarations: Vec::new(),
            constraints: Vec::new(),
            bad_state: None,
            stats: ExecutionStats::default(),
        }
    }

    fn count_static_ites(ctx: &Context, ts: &TransitionSystem) -> usize {
        let mut visited: HashSet<ExprRef> = HashSet::new();
        let mut worklist: Vec<ExprRef> = Vec::new();
        for state in &ts.states {
            if let Some(next) = state.next { worklist.push(next); }
            if let Some(init) = state.init { worklist.push(init); }
        }
        for &bad in &ts.bad_states { worklist.push(bad); }
        for &c in &ts.constraints { worklist.push(c); }

        let mut count = 0usize;
        while let Some(expr) = worklist.pop() {
            if !visited.insert(expr) { continue; }
            match &ctx[expr] {
                Expr::BVIte { .. } | Expr::ArrayIte { .. } => count += 1,
                _ => {}
            }
            ctx[expr].for_each_child(|c| worklist.push(*c));
        }
        count
    }

    pub fn init(&mut self, ctx: &mut Context) {
        self.stats = ExecutionStats::default();
        self.stats.state_variables = self.ts.states.len();
        self.stats.transition_statements = self.ts.states.iter().filter(|s| s.next.is_some()).count();
        self.stats.static_ite_count = Self::count_static_ites(ctx, &self.ts);

        for state in &self.ts.states {
            let tpe = state.symbol.get_type(ctx);
            self.state_types.insert(state.symbol, tpe);
        }
        for input in &self.ts.inputs {
            let tpe = input.get_type(ctx);
            self.input_types.insert(*input, tpe);
        }

        let mut initial_path = ExecutionPath::new();

        for state in &self.ts.states {
            if let Some(init_expr) = state.init {
                // States with init values start as their init value directly.
                initial_path.state_translation.insert(state.symbol, init_expr);
            } else {
                // States without init values start as a fresh t0 symbol.
                let name = ctx.get_symbol_name(state.symbol).unwrap_or("state");
                let t0_name = format!("{}_t0", name);
                let tpe = self.state_types[&state.symbol];
                let t0_sym = match tpe {
                    Type::BV(width) => ctx.bv_symbol(&t0_name, width),
                    Type::Array(arr_type) => {
                        ctx.array_symbol(&t0_name, arr_type.index_width, arr_type.data_width)
                    }
                };
                initial_path.state_translation.insert(state.symbol, t0_sym);
                if self.all_symbols.insert(t0_sym) {
                    self.pending_declarations.push(t0_sym);
                }
            }
        }

        self.constraints = self.ts.constraints.clone();

        self.paths.push(initial_path);
        self.current_step = 0;
        self.stats.active_paths = self.paths.len();
    }

    fn substitute_expr(
        &self,
        ctx: &mut Context,
        expr: ExprRef,
        path: &ExecutionPath,
    ) -> ExprRef {
        let translations = &path.input_translation;
        let definitions = &path.state_translation;
        
        simple_transform_expr(ctx, expr, |_ctx, e, _children| {
            if translations.contains_key(&e) {
                Some(translations[&e])
            } else if definitions.contains_key(&e) {
                Some(definitions[&e])
            } else {
                None 
            }
        })
    }

    /// Pre-compute substituted+simplified system constraints for a given state/input context.
    /// The substitution uses `state_map` (typically pre_transition_state) and `input_map`.
    fn precompute_constraints(
        &self,
        ctx: &mut Context,
        state_map: &HashMap<ExprRef, ExprRef>,
        input_map: &HashMap<ExprRef, ExprRef>,
    ) -> Vec<ExprRef> {
        // Build a temporary path carrying only the maps needed for substitution.
        let sub_path = ExecutionPath {
            state_translation: state_map.clone(),
            pre_transition_state: HashMap::new(),
            path_conditions: Vec::new(),
            asserted_path_conditions: Vec::new(),
            input_translation: input_map.clone(),
            post_transition_state: HashMap::new(),
            asserted_constraints: Vec::new(),
        };
        let constraints = self.constraints.clone();
        let mut result = Vec::with_capacity(constraints.len());
        for &c in &constraints {
            let sub = self.substitute_expr(ctx, c, &sub_path);
            let simplified = simplify_single_expression(ctx, sub);
            result.push(simplified);
        }
        result
    }

    fn get_ite_components(&self, ctx: &Context, expr: ExprRef) -> Option<(ExprRef, ExprRef, ExprRef)> {
        match &ctx[expr] {
            Expr::BVIte { cond, tru, fals } => Some((*cond, *tru, *fals)),
            Expr::ArrayIte { cond, tru, fals } => Some((*cond, *tru, *fals)),
            _ => None,
        }
    }

    /// Check whether `condition` is satisfiable under the current path context.
    ///
    /// Symbols are declared at solver level 0 (before any push) via `pending_declarations`
    /// so that they survive push/pop cycles and are never re-declared needlessly.
    /// Path conditions and system constraints are asserted from pre-computed fields on
    /// the path, avoiding repeated substitution and simplification work.
    fn check_condition_sat<S: SolverContext>(
        &mut self,
        ctx: &mut Context,
        solver: &mut S,
        path: &ExecutionPath,
        condition: ExprRef,
    ) -> Option<bool> {
        self.stats.smt_calls += 1;

        // Declare any symbols that have been added since the last call.
        // This happens at the base solver level (before push) so the declarations
        // are permanent and survive all subsequent push/pop pairs.
        for sym in self.pending_declarations.drain(..) {
            let _ = solver.declare_const(ctx, sym);
        }

        if solver.push().is_err() {
            return None;
        }

        // Assert pre-computed path conditions — no substitution or simplification needed.
        for &pc in &path.asserted_path_conditions {
            let _ = solver.assert(ctx, pc);
        }

        // Assert pre-computed system constraints — no substitution or simplification needed.
        for &c in &path.asserted_constraints {
            let _ = solver.assert(ctx, c);
        }

        let substituted_cond = self.substitute_expr(ctx, condition, path);
        let simplified_cond = simplify_single_expression(ctx, substituted_cond);
        let _ = solver.assert(ctx, simplified_cond);

        let result = match solver.check_sat() {
            Ok(CheckSatResponse::Sat) => Some(true),
            Ok(CheckSatResponse::Unsat) => Some(false),
            _ => None,
        };

        let _ = solver.pop();
        result
    }

    fn explore_paths<S: SolverContext>(
        &mut self,
        ctx: &mut Context,
        solver: &mut S,
        path_stack: &mut Vec<ExecutionPath>,
        state_symbol: ExprRef,
        next_expr: ExprRef,
    ) {
        let mut i = 0;
        while i < path_stack.len() {

            let substituted = self.substitute_expr(ctx, next_expr, &path_stack[i]);
            // Simplify only AFTER resolve_ite so that ITE structure is preserved
            // during feasibility pruning. Pre-simplification converts 1-bit ITEs
            // like ite(A, 0, B) into and(not(A), B), hiding the outer condition
            // from resolve_ite and causing spurious path forks.
            let new_state = self.resolve_ite(ctx, solver, i, path_stack, substituted);
            let simplified = simplify_single_expression(ctx, new_state);
            path_stack[i].post_transition_state.insert(state_symbol, simplified);

            i += 1;
        }
    }

    /// Resolves all ITEs by assuming the condition is true and adding the false condition 
    /// To a growing path stack. Only added as follows:
    ///
    /// - If only one branch is feasible, follow that branch (no extra path condition).
    /// - If both branches are feasible, fork: the current path takes the true branch
    ///   (with `cond` added to its path conditions) and a cloned path is returned for
    ///   later re-evaluation by `explore_paths` (with `¬cond` in its conditions).
    /// - If neither branch is feasible, the path is infeasible (panic).
    fn resolve_ite<S: SolverContext>(
        &mut self,
        ctx: &mut Context,
        solver: &mut S,
        i: usize,
        path_stack: &mut Vec<ExecutionPath>,
        expr: ExprRef,
    ) -> ExprRef {
        if let Some((cond, tru, fals)) = self.get_ite_components(ctx, expr) {
            self.stats.ite_encountered += 1;
            let cond_sat = self.check_condition_sat(ctx, solver, &path_stack[i], cond);
            let neg_cond = ctx.not(cond);
            let neg_sat = self.check_condition_sat(ctx, solver, &path_stack[i], neg_cond);

            match (cond_sat, neg_sat) {
                (Some(true), Some(false)) => {
                    self.resolve_ite(ctx, solver, i, path_stack, tru)
                }
                (Some(false), Some(true)) => {
                    self.resolve_ite(ctx, solver, i, path_stack, fals)
                }
                (Some(true), Some(true)) => {
                    // Fork: path i takes the true branch, a clone takes the false branch.
                    // Pre-compute the simplified assertion form at insertion time so that
                    // check_condition_sat never needs to re-substitute or re-simplify.
                    let simplified_cond = simplify_single_expression(ctx, cond);
                    let simplified_neg = simplify_single_expression(ctx, neg_cond);

                    let mut forked_path = path_stack[i].clone();
                    path_stack[i].path_conditions.push(cond);
                    path_stack[i].asserted_path_conditions.push(simplified_cond);
                    forked_path.path_conditions.push(neg_cond);
                    forked_path.asserted_path_conditions.push(simplified_neg);
                    path_stack.push(forked_path);
                    self.resolve_ite(ctx, solver, i, path_stack, tru)
                }
                (Some(false), Some(false)) => {
                    panic!("Infeasible path: both branches of ITE are UNSAT");
                }
                _ => {
                    panic!("SMT solver returned an unexpected result while resolving ITE");
                }
            }
        } else {
            let mut children = Vec::new();
            ctx[expr].for_each_child(|c| children.push(*c));

            if children.is_empty() {
                return expr;
            }

            let mut resolved_children = Vec::new();
            let mut any_changed = false;
            for &child in &children {
                let resolved = self.resolve_ite(ctx, solver, i, path_stack, child);
                if resolved != child {
                    any_changed = true;
                }
                resolved_children.push(resolved);
            }

            if !any_changed {
                return expr;
            }

            let child_map: HashMap<ExprRef, ExprRef> = children
                .iter()
                .zip(resolved_children.iter())
                .map(|(&old, &new)| (old, new))
                .collect();

            simple_transform_expr(ctx, expr, |_ctx, e, _| {
                child_map.get(&e).copied()
            })
        }
    }

    pub fn step<S: SolverContext>(&mut self, ctx: &mut Context, solver: &mut S) -> StepResult {
        if self.bad_state.is_some() {
            return StepResult::BadStateReached;
        }

        self.current_step += 1;
        let next_step = self.current_step;
        
        let mut new_paths = Vec::new();
        let states: Vec<_> = self.ts.states.clone();

        let input_timestamp = next_step - 1;
        let mut timestamped_inputs = HashMap::new();
        for input in &self.ts.inputs {
            let original_name = ctx.get_symbol_name(*input).unwrap_or("input");
            let timestamped_name = format!("{}_t{}", original_name, input_timestamp);
            let tpe = self.input_types[input];
            let timestamped_sym = match tpe {
                Type::BV(width) => ctx.bv_symbol(&timestamped_name, width),
                Type::Array(arr_type) => {
                    ctx.array_symbol(&timestamped_name, arr_type.index_width, arr_type.data_width)
                }
            };
            timestamped_inputs.insert(*input, timestamped_sym);
            if self.all_symbols.insert(timestamped_sym) {
                self.pending_declarations.push(timestamped_sym);
            }
        }

        let previous_paths = self.paths.clone();
        for path in &previous_paths {
            let mut base_path = ExecutionPath::new();
            base_path.path_conditions = path.path_conditions.clone();
            base_path.asserted_path_conditions = path.asserted_path_conditions.clone();
            base_path.input_translation = timestamped_inputs.clone();
            base_path.state_translation = path.state_translation.clone();
            // Snapshot pre-transition state so constraints can be evaluated
            // against the state values that were current when inputs were applied.
            base_path.pre_transition_state = path.state_translation.clone();

            // Pre-compute system constraints substituted with this path's context.
            // All forks produced by explore_paths share the same pre_transition_state
            // and input_translation, so they all inherit this pre-computed result.
            base_path.asserted_constraints = self.precompute_constraints(
                ctx,
                &base_path.pre_transition_state,
                &base_path.input_translation,
            );

            let mut path_stack = vec![base_path];

            for state in &states {
                if let Some(next_expr) = state.next {
                    self.explore_paths(ctx, solver, &mut path_stack, state.symbol, next_expr);
                }
            }

            for p in path_stack.iter_mut() {
                for (key, value) in p.post_transition_state.iter() {
                    p.state_translation.insert(*key, *value);
                }
            }

            new_paths.extend(path_stack);
        }
        self.stats.total_paths_generated += new_paths.len();


        // Merge paths that reached the same post-transition state.
        // Use a HashMap keyed on a sorted representation of state_translation for O(n) lookup
        // instead of the previous O(n²) nested scan.
        let mut state_key_to_idx: HashMap<Vec<(ExprRef, ExprRef)>, usize> = HashMap::new();
        let mut merged_paths: Vec<ExecutionPath> = Vec::new();

        for path in new_paths {
            let mut key: Vec<(ExprRef, ExprRef)> = path.state_translation
                .iter()
                .map(|(&k, &v)| (k, v))
                .collect();
            key.sort_unstable();

            if let Some(&idx) = state_key_to_idx.get(&key) {
                let existing = &mut merged_paths[idx];

                let cond_existing = if existing.path_conditions.is_empty() {
                    ctx.get_true()
                } else {
                    existing.path_conditions.iter().copied()
                        .reduce(|a, b| ctx.and(a, b))
                        .unwrap()
                };

                let cond_new = if path.path_conditions.is_empty() {
                    ctx.get_true()
                } else {
                    path.path_conditions.iter().copied()
                        .reduce(|a, b| ctx.and(a, b))
                        .unwrap()
                };

                let merged_cond = ctx.or(cond_existing, cond_new);
                let simplified_merged = simplify_single_expression(ctx, merged_cond);
                existing.path_conditions = vec![merged_cond];
                existing.asserted_path_conditions = vec![simplified_merged];
            } else {
                state_key_to_idx.insert(key, merged_paths.len());
                merged_paths.push(path);
            }
        }

        self.paths = merged_paths;
        self.stats.active_paths = self.paths.len();

        // Bad states are checked at time N with state@N and inputs@N.
        // The path's input_translation holds inputs@(N-1) (the transition inputs),
        // so we create fresh inputs timestamped at next_step for the bad state check.
        let mut bad_check_inputs = HashMap::new();
        for input in &self.ts.inputs {
            let original_name = ctx.get_symbol_name(*input).unwrap_or("input");
            let timestamped_name = format!("{}_t{}", original_name, next_step);
            let tpe = self.input_types[input];
            let timestamped_sym = match tpe {
                Type::BV(width) => ctx.bv_symbol(&timestamped_name, width),
                Type::Array(arr_type) => {
                    ctx.array_symbol(&timestamped_name, arr_type.index_width, arr_type.data_width)
                }
            };
            bad_check_inputs.insert(*input, timestamped_sym);
            if self.all_symbols.insert(timestamped_sym) {
                self.pending_declarations.push(timestamped_sym);
            }
        }

        // Check whether any bad state is satisfiable on any path after this step.
        let bad_states = self.ts.bad_states.clone();
        let mut found_bad: Option<(ExprRef, ExecutionPath)> = None;

        let paths_for_bad_check = self.paths.clone();
        'outer: for &bad_expr in &bad_states {
            for path in &paths_for_bad_check {
                // Build a check path: state@N with fresh inputs@N.
                // pre_transition_state = state@N so constraints are evaluated at time N.
                let bad_asserted_constraints = self.precompute_constraints(
                    ctx,
                    &path.state_translation,
                    &bad_check_inputs,
                );
                let bad_check_path = ExecutionPath {
                    state_translation: path.state_translation.clone(),
                    pre_transition_state: path.state_translation.clone(),
                    path_conditions: path.path_conditions.clone(),
                    asserted_path_conditions: path.asserted_path_conditions.clone(),
                    input_translation: bad_check_inputs.clone(),
                    post_transition_state: HashMap::new(),
                    asserted_constraints: bad_asserted_constraints,
                };
                if self.check_condition_sat(ctx, solver, &bad_check_path, bad_expr) == Some(true) {
                    found_bad = Some((bad_expr, bad_check_path));
                    break 'outer;
                }
            }
        }

        if let Some(bad) = found_bad {
            self.bad_state = Some(bad);
            return StepResult::BadStateReached;
        }

        StepResult::Ok
    }

    pub fn stats(&self) -> &ExecutionStats {
        &self.stats
    }


    fn print_bad_state(&self, ctx: &mut Context) {
        if let Some((bad_expr, ref bad_path)) = self.bad_state {
            println!("  === BAD STATE reached at step {} ===", self.current_step);
            println!("  Bad state expression: {}", bad_expr.serialize_to_str(ctx));
            let substituted = self.substitute_expr(ctx, bad_expr, bad_path);
            let simplified = simplify_single_expression(ctx, substituted);
            println!("  Evaluated: {}", simplified.serialize_to_str(ctx));
            println!("  Path condition:");
            for &cond in &bad_path.path_conditions {
                let sub = self.substitute_expr(ctx, cond, bad_path);
                let simp = simplify_single_expression(ctx, sub);
                println!("    {}", simp.serialize_to_str(ctx));
            }
        }
    }

    pub fn print_step(&self, ctx: &mut Context) {
        println!("Step {}:", self.current_step);

        if self.bad_state.is_some() {
            self.print_bad_state(ctx);
            println!();
            return;
        }

        println!("  All symbols:");
        for sym in &self.all_symbols {
            let name = ctx.get_symbol_name(*sym).unwrap_or("unknown");
            println!("    {}", name);
        }
        println!();

        for (path_idx, path) in self.paths.iter().enumerate() {
            println!("  Path_condition {}:", path_idx + 1); 

            println!("    Variables:");
            for state in &self.ts.states {
                if let Some(&value) = path.state_translation.get(&state.symbol) {
                    let sym_name = ctx.get_symbol_name(state.symbol).unwrap_or("unknown").to_string();
                    let simplified = simplify_single_expression(ctx, value);
                    println!("      {} = {}", sym_name, simplified.serialize_to_str(ctx));
                }
            }
            
            for input in &self.ts.inputs {
                let original_name = ctx.get_symbol_name(*input).unwrap_or("input").to_string();
                if let Some(&value) = path.input_translation.get(input) {
                    let sym_name = ctx.get_symbol_name(value).unwrap_or("unknown");
                    println!("      {} = {}", original_name, sym_name);
                }
            }
            
            println!("    Path Constraints:");
            let mut constraint_idx = 0;
            for &constraint in &path.path_conditions {
                let substituted = self.substitute_expr(ctx, constraint, &path);
                let simplified = simplify_single_expression(ctx, substituted);
                println!("      Constraint {}: {}", constraint_idx, simplified.serialize_to_str(ctx));
                constraint_idx += 1;
            }
            
            println!("    System Constraints:");
            let mut sys_constraint_idx = 0;
            let constraints = self.constraints.clone();
            for &constraint in &constraints {
                let substituted = self.substitute_expr(ctx, constraint, &path);
                let simplified = simplify_single_expression(ctx, substituted);
                println!("      Constraint {}: {}", sys_constraint_idx, simplified.serialize_to_str(ctx));
                sys_constraint_idx += 1;
            }
            
            
            println!();
        }
    }
}
