use patronus::expr::{Context, Expr, ExprRef, ForEachChild, SerializableIrNode, Type, TypeCheck, simplify_single_expression, simple_transform_expr};
use patronus::smt::{CheckSatResponse, SolverContext};
use patronus::system::TransitionSystem;
use std::collections::{HashMap, HashSet};

/// Represents a single execution path with its constraints
#[derive(Clone)]
pub struct ExecutionPath {
    pub state_translation: HashMap<ExprRef, ExprRef>,
    pub path_conditions: Vec<ExprRef>,
    pub input_translation: HashMap<ExprRef, ExprRef>,
}

impl ExecutionPath {
    pub fn new() -> Self {
        ExecutionPath {
            state_translation: HashMap::new(),
            path_conditions: Vec::new(),
            input_translation: HashMap::new(),
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

/// Symbolic executor for transition systems
pub struct SymbolicExecutor {
    ts: TransitionSystem,
    current_step: usize,
    paths: Vec<ExecutionPath>,
    state_types: HashMap<ExprRef, Type>,
    input_types: HashMap<ExprRef, Type>,
    all_symbols: HashSet<ExprRef>,
    constraints: Vec<ExprRef>,
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
            constraints: Vec::new(),
        }
    }

    pub fn init(&mut self, ctx: &mut Context) {
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
            // All states start as state_t0 symbols, regardless of init values.
            // On the first step, states with init values will be set to their
            // init value instead of stepping.
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
            self.all_symbols.insert(t0_sym);
        }

        self.constraints = self.ts.constraints.clone();

        self.paths.push(initial_path);
        self.current_step = 0;
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

    fn get_ite_components(&self, ctx: &Context, expr: ExprRef) -> Option<(ExprRef, ExprRef, ExprRef)> {
        match &ctx[expr] {
            Expr::BVIte { cond, tru, fals } => Some((*cond, *tru, *fals)),
            Expr::ArrayIte { cond, tru, fals } => Some((*cond, *tru, *fals)),
            _ => None,
        }
    }

    fn check_condition_sat<S: SolverContext>(
        &self,
        ctx: &mut Context,
        solver: &mut S,
        path: &ExecutionPath,
        condition: ExprRef,
    ) -> Option<bool> {
        if solver.push().is_err() {
            return None;
        }

        for sym in &self.all_symbols {
            let _ = solver.declare_const(ctx, *sym);
        }
        
        for &pc in &path.path_conditions {
            let substituted = self.substitute_expr(ctx, pc, path);
            let simplified = simplify_single_expression(ctx, substituted);
            let _ = solver.assert(ctx, simplified);
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


    fn prune_infeasible_paths<S: SolverContext>(
        &self,
        ctx: &mut Context,
        solver: &mut S,
        path_stack: Vec<ExecutionPath>,
    ) -> Vec<ExecutionPath> {

        let mut feasible_paths = Vec::new();

        for path in path_stack {

            if solver.push().is_err() {
                // If push fails, conservatively keep the path
                feasible_paths.push(path);
                continue;
            }

            for sym in &self.all_symbols {
                let _ = solver.declare_const(ctx, *sym);
            }

            let constraints = self.constraints.clone();
            for &constraint in &constraints {
                let substituted = self.substitute_expr(ctx, constraint, &path);
                let simplified = simplify_single_expression(ctx, substituted);
                let _ = solver.assert(ctx, simplified);
            }

            for &pc in &path.path_conditions {
                let substituted = self.substitute_expr(ctx, pc, &path);
                let simplified = simplify_single_expression(ctx, substituted);
                let _ = solver.assert(ctx, simplified);
            }

            let result = solver.check_sat();
            let is_sat = match &result {
                Ok(CheckSatResponse::Sat) => true,
                Ok(CheckSatResponse::Unsat) => false,
                _ => panic!("got unexpected SAT response (not SAT or UNSAT)"),
            };
            let _ = solver.pop();

            if is_sat {
                feasible_paths.push(path);
            }
        }

        feasible_paths
    }


    fn explore_paths<S: SolverContext>(
        &self,
        ctx: &mut Context,
        solver: &mut S,
        path_stack: &mut Vec<ExecutionPath>,
        state_symbol: ExprRef,
        next_expr: ExprRef,
    ) {
        let mut i = 0;
        while i < path_stack.len() {

            let substituted = self.substitute_expr(ctx, next_expr, &path_stack[i]);
            let simplified = simplify_single_expression(ctx, substituted);
            let new_state = self.resolve_ite(ctx, solver, i, path_stack, simplified);
            path_stack[i].state_translation.insert(state_symbol, new_state);

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
        &self,
        ctx: &mut Context,
        solver: &mut S,
        i: usize,
        path_stack: &mut Vec<ExecutionPath>,
        expr: ExprRef,
    ) -> ExprRef {
        if let Some((cond, tru, fals)) = self.get_ite_components(ctx, expr) {
            // Check feasibility of both branches under the current path conditions
            let cond_sat = self.check_condition_sat(ctx, solver, &path_stack[i], cond);
            let neg_cond = ctx.not(cond);
            let neg_sat = self.check_condition_sat(ctx, solver, &path_stack[i], neg_cond);

            match (cond_sat, neg_sat) {
                (Some(true), Some(false)) => {
                    // Only the true branch is feasible
                    self.resolve_ite(ctx, solver, i, path_stack, tru)
                }
                (Some(false), Some(true)) => {
                    // Only the false branch is feasible
                    self.resolve_ite(ctx, solver, i, path_stack, fals)
                }
                (Some(true), Some(true)) => {
                    // Both branches are feasible — fork the path
                    let mut forked_path = path_stack[i].clone();
                    path_stack[i].path_conditions.push(cond);
                    forked_path.path_conditions.push(neg_cond);
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
            // Not an ITE — collect children, resolve each, and rebuild if any changed
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

            // Build a mapping from original children to resolved children
            let child_map: HashMap<ExprRef, ExprRef> = children
                .iter()
                .zip(resolved_children.iter())
                .map(|(&old, &new)| (old, new))
                .collect();

            // Rebuild the expression with resolved children
            simple_transform_expr(ctx, expr, |_ctx, e, _| {
                child_map.get(&e).copied()
            })
        }
    }


    /// On the first step (step 0 -> 1), states with init values are set to
    /// their init value instead of evaluating the next-state function.
    /// States without init values step normally even on the first step.
    pub fn step<S: SolverContext>(&mut self, ctx: &mut Context, solver: &mut S) {
        self.current_step += 1;
        let next_step = self.current_step;
        let is_first_step = next_step == 1;
        
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
            self.all_symbols.insert(timestamped_sym);
        }

        for path in &self.paths {
            let mut base_path = ExecutionPath::new();
            base_path.path_conditions = path.path_conditions.clone();
            base_path.input_translation = timestamped_inputs.clone();
            base_path.state_translation = path.state_translation.clone();

            let mut path_stack = vec![base_path];

            if is_first_step {
                for state in &states {
                    if let Some(init_expr) = state.init {
                        for p in path_stack.iter_mut() {
                            p.state_translation.insert(state.symbol, init_expr);
                        }
                    } else if let Some(next_expr) = state.next {
                        self.explore_paths(ctx, solver, &mut path_stack, state.symbol, next_expr);
                    }
                }
            } else {
                for state in &states {
                    if let Some(next_expr) = state.next {
                        self.explore_paths(ctx, solver, &mut path_stack, state.symbol, next_expr);
                    }
                }
            }

            let feasible_paths = self.prune_infeasible_paths(ctx, solver, path_stack);

            new_paths.extend(feasible_paths);
        }

        self.paths = new_paths;
    }


    pub fn print_step(&self, ctx: &mut Context) {
        println!("Step {}:", self.current_step);

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
