use baa::BitVecOps;
use patronus::expr::{Context, Expr, ExprRef, ForEachChild, SerializableIrNode, Type, TypeCheck, simplify_single_expression, simple_transform_expr};
use patronus::smt::{CheckSatResponse, SolverContext};
use patronus::system::TransitionSystem;
use std::collections::{HashMap, HashSet};

/// Represents a single execution path with its constraints
#[derive(Clone)]
pub struct ExecutionPath {
    /// Variable definitions: maps timestamped symbols to their values
    /// e.g., input_t1 -> 16'x0000, counter -> 16'x0001
    pub variable_definitions: HashMap<ExprRef, ExprRef>,
    /// Path conditions (constraints that don't define variables)
    pub path_conditions: Vec<ExprRef>,
    /// Translation map from original symbols to their current values
    pub input_translation: HashMap<ExprRef, ExprRef>,
}

impl ExecutionPath {
    pub fn new() -> Self {
        ExecutionPath {
            variable_definitions: HashMap::new(),
            path_conditions: Vec::new(),
            input_translation: HashMap::new(),
        }
    }
}

/// Symbolic executor for transition systems
pub struct SymbolicExecutor {
    /// Deep copy of the transition system
    ts: TransitionSystem,
    /// Current step
    current_step: usize,
    /// All execution paths (breadth-first across steps)
    paths: Vec<ExecutionPath>,
    /// Mapping from original state symbols to their types (width for bv)
    state_types: HashMap<ExprRef, Type>,
    /// Mapping from original input symbols to their types
    input_types: HashMap<ExprRef, Type>,
}

impl SymbolicExecutor {
    /// Create a new symbolic executor from a transition system
    /// Makes a deep copy of the transition system
    pub fn new(ts: &TransitionSystem) -> Self {
        SymbolicExecutor {
            ts: ts.clone(), // Deep copy
            current_step: 0,
            paths: Vec::new(),
            state_types: HashMap::new(),
            input_types: HashMap::new(),
        }
    }

    /// Initialize the symbolic executor
    pub fn init(&mut self, ctx: &mut Context) {
        // Collect state and input types
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
                // If it has an initial value, put it directly in variable_definitions
                initial_path.variable_definitions.insert(state.symbol, init_expr);
            } else {
                // No initial value - store the symbol itself in variable_definitions
                initial_path.variable_definitions.insert(state.symbol, state.symbol);
            }
        }

        self.paths.push(initial_path);
        self.current_step = 0;
    }

    /// Substitute all symbols in an expression using the translation map and variable definitions
    fn substitute_expr(
        &self,
        ctx: &mut Context,
        expr: ExprRef,
        path: &ExecutionPath,
    ) -> ExprRef {
        let translations = &path.input_translation;
        let definitions = &path.variable_definitions;
        
        simple_transform_expr(ctx, expr, |_ctx, e, _children| {
            // Check if this is a symbol we need to translate (inputs)
            if translations.contains_key(&e) {
                Some(translations[&e])
            } else if definitions.contains_key(&e) {
                // Check if this is a state variable in definitions
                Some(definitions[&e])
            } else {
                None // No translation
            }
        })
    }

    /// Check if an expression is an ITE and return its components
    fn get_ite_components(&self, ctx: &Context, expr: ExprRef) -> Option<(ExprRef, ExprRef, ExprRef)> {
        match &ctx[expr] {
            Expr::BVIte { cond, tru, fals } => Some((*cond, *tru, *fals)),
            Expr::ArrayIte { cond, tru, fals } => Some((*cond, *tru, *fals)),
            _ => None,
        }
    }

    /// Check if an expression is always true or always false using SMT solver
    /// Returns: Some(true) if always true, Some(false) if always false, None if neithers
    fn check_always_true_or_false<S: SolverContext>(
        &self,
        ctx: &mut Context,
        solver: &mut S,
        expr: ExprRef,
    ) -> Option<bool> {
        if solver.push().is_err() {
            return None;
        }

        // Collect and declare all symbols
        let mut all_symbols = HashSet::new();
        self.collect_symbols(ctx, expr, &mut all_symbols);

        for sym in &all_symbols {
            let _ = solver.declare_const(ctx, *sym);
        }

        // Check if expression is always false (UNSAT)
        let _ = solver.assert(ctx, expr);
        let is_always_false = match solver.check_sat() {
            Ok(CheckSatResponse::Unsat) => true,
            _ => false,
        };
        let _ = solver.pop();

        if is_always_false {
            return Some(false);
        }

        // Check if expression is always true (negation is UNSAT)
        if solver.push().is_err() {
            return None;
        }

        for sym in &all_symbols {
            let _ = solver.declare_const(ctx, *sym);
        }

        let neg_expr = ctx.not(expr);
        let _ = solver.assert(ctx, neg_expr);
        let is_always_true = match solver.check_sat() {
            Ok(CheckSatResponse::Unsat) => true,
            _ => false,
        };
        let _ = solver.pop();

        if is_always_true {
            Some(true)
        } else {
            None
        }
    }

    /// Check if a condition is satisfiable given current path conditions
    /// Returns: Some(true) if SAT, Some(false) if UNSAT, None if neither
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

        // Collect and declare all symbols
        let mut all_symbols = HashSet::new();
        for (&sym, &value) in &path.variable_definitions {
            let eq = ctx.equal(sym, value);
            self.collect_symbols(ctx, eq, &mut all_symbols);
        }
        for &pc in &path.path_conditions {
            self.collect_symbols(ctx, pc, &mut all_symbols);
        }
        self.collect_symbols(ctx, condition, &mut all_symbols);

        for sym in &all_symbols {
            let _ = solver.declare_const(ctx, *sym);
        }

        // Assert existing constraints
        for (&sym, &value) in &path.variable_definitions {
            let eq = ctx.equal(sym, value);
            let _ = solver.assert(ctx, eq);
        }
        for &pc in &path.path_conditions {
            let _ = solver.assert(ctx, pc);
        }

        // Assert the condition we're checking
        let _ = solver.assert(ctx, condition);

        let result = match solver.check_sat() {
            Ok(CheckSatResponse::Sat) => Some(true),
            Ok(CheckSatResponse::Unsat) => Some(false),
            _ => None,
        };

        let _ = solver.pop();
        result
    }

    /// Process a single ITE expression with SAT-based pruning
    /// Returns branches to explore: each branch is (value, optional condition to add)
    fn process_ite_with_sat<S: SolverContext>(
        &self,
        ctx: &mut Context,
        solver: &mut S,
        path: &ExecutionPath,
        cond: ExprRef,
        tru: ExprRef,
        fals: ExprRef,
    ) -> Vec<(ExprRef, Option<ExprRef>)> {
        let mut branches = Vec::new();

        // Check if path ∧ cond is SAT (2 SMT calls total)
        let cond_sat = self.check_condition_sat(ctx, solver, path, cond);
        
        // Check if path ∧ ¬cond is SAT
        let neg_cond = ctx.not(cond);
        let neg_sat = self.check_condition_sat(ctx, solver, path, neg_cond);

        match (cond_sat, neg_sat) {
            (Some(true), Some(true)) => {
                // Both branches are feasible - cond can be true or false
                // Must explore both paths WITH conditions added
                branches.push((tru, Some(cond)));
                branches.push((fals, Some(neg_cond)));
            }
            (Some(true), Some(false)) => {
                // path ∧ cond = SAT, path ∧ ¬cond = UNSAT
                // This means cond must be TRUE given path (¬cond is FALSE)
                // Therefore cond is redundant - take true branch WITHOUT adding condition
                branches.push((tru, None));
            }
            (Some(false), Some(true)) => {
                // path ∧ cond = UNSAT, path ∧ ¬cond = SAT
                // This means cond must be FALSE given path (¬cond is TRUE)
                // Therefore ¬cond is redundant - take false branch WITHOUT adding condition
                branches.push((fals, None));
            }
            (Some(false), Some(false)) => {
                // Both UNSAT - path is infeasible (impossible case)
                // Return empty to signal infeasibility
            }
            _ => {
                // Unknown - conservatively explore both
                branches.push((tru, Some(cond)));
                branches.push((fals, Some(neg_cond)));
            }
        }

        branches
    }

    /// Execute one step of symbolic execution using DFS
    /// Processes all current paths and creates new paths for the next timestep
    pub fn step<S: SolverContext>(&mut self, ctx: &mut Context, solver: &mut S) {
        self.current_step += 1;
        let next_step = self.current_step;
        
        let mut new_paths = Vec::new();
        let states: Vec<_> = self.ts.states.clone();

        for path in &self.paths {
            let mut base_path = ExecutionPath::new();
            base_path.path_conditions = path.path_conditions.clone();

            // Create new timestamped input variables and update translations
            let input_timestamp = next_step - 1;
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
                base_path.input_translation.insert(*input, timestamped_sym);
            }

            // Add transition system constraints
            // for &constraint in &self.ts.constraints {
            //     // Create a temporary path that combines old state values with new input translations
            //     let mut combined_path = ExecutionPath::new();
            //     combined_path.variable_definitions = path.variable_definitions.clone();
            //     combined_path.input_translation = base_path.input_translation.clone();
                
            //     let substituted = self.substitute_expr(ctx, constraint, &combined_path);
            //     let simplified = simplify_single_expression(ctx, substituted); 

            //     // Only add non-tautology constraints
            //     if !self.is_tautology(ctx, solver, simplified) {
            //         base_path.path_conditions.push(simplified);
            //     }
            // }

            // DFS exploration of state transitions
            // Stack contains: (current_path, state_index)
            let mut stack: Vec<(ExecutionPath, usize)> = vec![(base_path.clone(), 0)];

            let mut combined_path_for_next = ExecutionPath::new();
            combined_path_for_next.variable_definitions = path.variable_definitions.clone();
            combined_path_for_next.input_translation = base_path.input_translation.clone();

            while let Some((current_path, state_idx)) = stack.pop() {
                if state_idx >= states.len() {
                    // All states processed
                    new_paths.push(current_path);
                    continue;
                }

                let state = &states[state_idx];
                let next_expr = if let Some(next) = state.next {
                    // Substitute using the combined path 
                    self.substitute_expr(ctx, next, &combined_path_for_next)
                } else {
                    // No next expression - state stays the same
                    path.variable_definitions[&state.symbol]
                };

                // Process the expression, handling nested ITEs with DFS
                self.process_state_transition_dfs(
                    ctx,
                    solver,
                    &mut stack,
                    current_path,
                    state_idx,
                    state.symbol,
                    next_expr,
                );
            }
        }

        self.paths = new_paths;
    }

    /// Process a state transition expression using DFS, handling nested ITEs
    fn process_state_transition_dfs<S: SolverContext>(
        &self,
        ctx: &mut Context,
        solver: &mut S,
        stack: &mut Vec<(ExecutionPath, usize)>,
        path: ExecutionPath,
        state_idx: usize,
        state_symbol: ExprRef,
        expr: ExprRef,
    ) {
        // Inner stack for processing nested ITEs within this state's expression
        let mut expr_stack: Vec<(ExecutionPath, ExprRef)> = vec![(path, expr)];

        while let Some((mut current_path, current_expr)) = expr_stack.pop() {
            if let Some((cond, tru, fals)) = self.get_ite_components(ctx, current_expr) {
                // This is an ITE - check SAT and determine branches
                let branches = self.process_ite_with_sat(ctx, solver, &current_path, cond, tru, fals);

                for (value, opt_condition) in branches {
                    let mut branch_path = current_path.clone();
                    
                    if let Some(condition) = opt_condition {
                        branch_path.path_conditions.push(condition);
                    }

                    expr_stack.push((branch_path, value));
                }
            } else {
                // this is a final value for this state
                current_path.variable_definitions.insert(state_symbol, current_expr);
                stack.push((current_path, state_idx + 1));
            }
        }
    }

    /// Collect all symbols used in an expression
    fn collect_symbols(&self, ctx: &Context, expr: ExprRef, symbols: &mut HashSet<ExprRef>) {
        // Check if this is a symbol
        if ctx[expr].is_symbol() {
            symbols.insert(expr);
        }
        
        // Recursively collect from children
        ctx[expr].for_each_child(|child| {
            self.collect_symbols(ctx, *child, symbols);
        });
    }

    /// Get the current step number
    pub fn current_step(&self) -> usize {
        self.current_step
    }

    /// Get all current paths
    pub fn paths(&self) -> &[ExecutionPath] {
        &self.paths
    }

    /// Get the transition system
    pub fn transition_system(&self) -> &TransitionSystem {
        &self.ts
    }

    /// Check if an expression is a tautology (always true) using SMT solver
    fn is_tautology<S: SolverContext>(
        &self,
        ctx: &mut Context,
        solver: &mut S,
        expr: ExprRef,
    ) -> bool {
        self.check_always_true_or_false(ctx, solver, expr) == Some(true)
    }

    /// Print the current state of symbolic execution
    pub fn print_step(&self, ctx: &mut Context) {
        println!("Step {}:", self.current_step);
        
        if self.current_step == 0 {
            if let Some(path) = self.paths.first() {
                println!("  Variables:");
                for state in &self.ts.states {
                    let original_name = ctx.get_symbol_name(state.symbol).unwrap_or("state").to_string();
                    if let Some(&value) = path.variable_definitions.get(&state.symbol) {
                        let value_str = value.serialize_to_str(ctx);
                        println!("    {} = {}", original_name, value_str);
                    }
                }
            }
        } else {
            // After step - print all paths with variables and constraints
            for (path_idx, path) in self.paths.iter().enumerate() {
                println!("  Path_condition {}:", path_idx + 1); 

                println!("    Variables:");
                for state in &self.ts.states {
                    if let Some(&value) = path.variable_definitions.get(&state.symbol) {
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
                
                println!();
            }
        }
    }
}
