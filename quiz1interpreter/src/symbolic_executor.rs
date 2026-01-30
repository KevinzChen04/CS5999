use patronus::expr::{Context, Expr, ExprRef, SerializableIrNode, Type, TypeCheck, simplify_single_expression, simple_transform_expr};
use patronus::smt::{CheckSatResponse, SolverContext};
use patronus::system::TransitionSystem;
use std::collections::{HashMap, HashSet};

/// Represents a single execution path with its constraints
#[derive(Clone)]
pub struct ExecutionPath {
    /// Variable definitions: maps state variables to their values
    /// e.g., counter -> 16'x0001
    pub variable_definitions: HashMap<ExprRef, ExprRef>,
    /// Path conditions
    pub path_conditions: Vec<ExprRef>,
    /// Transition system constraints (inherited from the system)
    pub constraints: Vec<ExprRef>,
    /// Translation map inputs to their input state
    /// e.g., input -> input_t1
    pub input_translation: HashMap<ExprRef, ExprRef>,
}

impl ExecutionPath {
    pub fn new() -> Self {
        ExecutionPath {
            variable_definitions: HashMap::new(),
            path_conditions: Vec::new(),
            constraints: Vec::new(),
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
    /// All symbols used across all paths 
    all_symbols: HashSet<ExprRef>,
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
            all_symbols: HashSet::new(),
        }
    }

    /// Initialize the symbolic executor
    pub fn init(&mut self, ctx: &mut Context) {
        // Collect state and input types
        for state in &self.ts.states {
            let tpe = state.symbol.get_type(ctx);
            self.state_types.insert(state.symbol, tpe);
            self.all_symbols.insert(state.symbol);
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

        // Add transition system constraints to initial path
        // These will be inherited by all divergent paths
        for &constraint in &self.ts.constraints {
            let simplified = simplify_single_expression(ctx, constraint);
            initial_path.constraints.push(simplified);
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
                None 
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

        for sym in &self.all_symbols {
            let _ = solver.declare_const(ctx, *sym);
        }

        // Assert existing constraints
        for (&sym, &value) in &path.variable_definitions {
            let eq = ctx.equal(sym, value);
            let _ = solver.assert(ctx, eq);
        }
        for &constraint in &path.constraints {
            let _ = solver.assert(ctx, constraint);
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

        // Check if path ∧ cond is SAT
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
                // cond is redundant - take true branch without adding condition
                branches.push((tru, None));
            }
            (Some(false), Some(true)) => {
                // not cond is redundant - take false branch without adding condition
                branches.push((fals, None));
            }
            (Some(false), Some(false)) => {
                // Both UNSAT - path is infeasible
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

        // Create new timestamped input symbols once per step and add to global symbol set
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
            base_path.constraints = path.constraints.clone();

            // Use the pre-created timestamped inputs
            base_path.input_translation = timestamped_inputs.clone();

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

    /// Print the current state of symbolic execution
    pub fn print_step(&self, ctx: &mut Context) {
        println!("Step {}:", self.current_step);

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
