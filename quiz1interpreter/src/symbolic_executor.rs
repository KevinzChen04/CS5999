use baa::BitVecOps;
use patronus::expr::{Context, Expr, ExprRef, SerializableIrNode, Type, TypeCheck, simplify_single_expression};
use patronus::smt::{CheckSatResponse, SolverContext};
use patronus::system::TransitionSystem;
use std::collections::{HashMap, HashSet};

/// Represents a single execution path with its constraints
#[derive(Clone)]
pub struct ExecutionPath {
    /// Variable definitions: maps timestamped symbols to their values
    /// e.g., counter_t1 -> 16'x0000, _resetCount_t1 -> add(...)
    pub variable_definitions: HashMap<ExprRef, ExprRef>,
    /// Path conditions (constraints that don't define variables)
    pub path_conditions: Vec<ExprRef>,
    /// Translation map from original symbols to their current values
    pub translations: HashMap<ExprRef, ExprRef>,
}

impl ExecutionPath {
    pub fn new() -> Self {
        ExecutionPath {
            variable_definitions: HashMap::new(),
            path_conditions: Vec::new(),
            translations: HashMap::new(),
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
    /// Sets up initial state variables with their init values or as symbolic variables (no timestamps)
    /// Sets up inputs as name_t0
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

        // Create initial execution path
        let mut initial_path = ExecutionPath::new();

        // Initialize state variables directly in variable_definitions (no timestamps)
        for state in &self.ts.states {
            if let Some(init_expr) = state.init {
                // If it has an initial value, put it directly in variable_definitions
                initial_path.variable_definitions.insert(state.symbol, init_expr);
            } else {
                // No initial value - store the symbol itself in variable_definitions
                initial_path.variable_definitions.insert(state.symbol, state.symbol);
            }
        }

        // No inputs at step 0 - they will be created when we call step() for the first time

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
        use patronus::expr::simple_transform_expr;
        
        let translations = &path.translations;
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

    /// Substitute variable definitions into an expression recursively until fixed point
    /// Avoids infinite loops by limiting recursion depth
    fn substitute_definitions(
        ctx: &mut Context,
        expr: ExprRef,
        definitions: &HashMap<ExprRef, ExprRef>,
    ) -> ExprRef {
        Self::substitute_definitions_depth(ctx, expr, definitions, &mut HashSet::new())
    }

    /// Helper for substitute_definitions that tracks visited symbols to avoid cycles
    fn substitute_definitions_depth(
        ctx: &mut Context,
        expr: ExprRef,
        definitions: &HashMap<ExprRef, ExprRef>,
        visiting: &mut HashSet<ExprRef>,
    ) -> ExprRef {
        use patronus::expr::simple_transform_expr;
        
        simple_transform_expr(ctx, expr, |ctx, e, _children| {
            // Check if this is a defined variable we need to substitute
            if definitions.contains_key(&e) {
                // Avoid infinite recursion - if we're already visiting this symbol, don't substitute
                if visiting.contains(&e) {
                    return None;
                }
                
                // Mark this symbol as being visited
                visiting.insert(e);
                let value = definitions[&e];
                
                // If the value is the symbol itself, don't substitute
                if value == e {
                    visiting.remove(&e);
                    return None;
                }
                
                // Recursively substitute in the value
                let result = Self::substitute_definitions_depth(ctx, value, definitions, visiting);
                visiting.remove(&e);
                
                Some(result)
            } else {
                None // No substitution
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
    /// Returns: Some(true) if SAT, Some(false) if UNSAT, None if unknown
    fn check_condition_sat<S: SolverContext>(
        &self,
        ctx: &mut Context,
        solver: &mut S,
        path: &ExecutionPath,
        condition: ExprRef,
    ) -> Option<bool> {
        // First check if it's a tautology or contradiction
        if let Some(val) = Self::try_eval_bool(ctx, condition) {
            return Some(val);
        }

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

        // Check if condition is always true (tautology)
        if Self::try_eval_bool(ctx, cond) == Some(true) {
            // Always true - only take true branch, no condition to add
            branches.push((tru, None));
            return branches;
        }

        // Check if condition is always false
        if Self::try_eval_bool(ctx, cond) == Some(false) {
            // Always false - only take false branch, no condition to add
            branches.push((fals, None));
            return branches;
        }

        // Check if condition is SAT
        let cond_sat = self.check_condition_sat(ctx, solver, path, cond);
        
        // Check if negation is SAT
        let neg_cond = ctx.not(cond);
        let neg_sat = self.check_condition_sat(ctx, solver, path, neg_cond);

        match (cond_sat, neg_sat) {
            (Some(true), Some(true)) => {
                // Both branches are feasible - need to explore both
                branches.push((tru, Some(cond)));
                branches.push((fals, Some(neg_cond)));
            }
            (Some(true), Some(false)) => {
                // Only true branch is feasible
                branches.push((tru, Some(cond)));
            }
            (Some(false), Some(true)) => {
                // Only false branch is feasible
                branches.push((fals, Some(neg_cond)));
            }
            (Some(false), Some(false)) => {
                // This shouldn't happen - path is infeasible
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
            // Create base path - state variables will keep their original symbols
            let mut base_path = ExecutionPath::new();
            
            // Copy existing path conditions (but not variable definitions - we'll create new ones)
            base_path.path_conditions = path.path_conditions.clone();

            // Create new timestamped input variables and update translations
            // First input is at step 1, so we use step - 1 for the timestamp (input_t0 at step 1)
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
                base_path.translations.insert(*input, timestamped_sym);
            }

            // Add transition system constraints
            for &constraint in &self.ts.constraints {
                // Create a temporary path that combines old state values with new input translations
                let mut combined_path = ExecutionPath::new();
                combined_path.variable_definitions = path.variable_definitions.clone();
                combined_path.translations = base_path.translations.clone();
                
                let substituted = self.substitute_expr(ctx, constraint, &combined_path);
                // Simplify the constraint before adding it
                let simplified = simplify_single_expression(ctx, substituted);
                // Only add non-tautology constraints
                if !Self::is_tautology(ctx, simplified) {
                    base_path.path_conditions.push(simplified);
                }
            }

            // DFS exploration of state transitions
            // Stack contains: (current_path, state_index)
            let mut stack: Vec<(ExecutionPath, usize)> = vec![(base_path.clone(), 0)];

            // Create a combined path for substituting next expressions
            // It has old state values but new input translations
            let mut combined_path_for_next = ExecutionPath::new();
            combined_path_for_next.variable_definitions = path.variable_definitions.clone();
            combined_path_for_next.translations = base_path.translations.clone();

            while let Some((current_path, state_idx)) = stack.pop() {
                if state_idx >= states.len() {
                    // All states processed - this is a complete path
                    new_paths.push(current_path);
                    continue;
                }

                let state = &states[state_idx];
                let next_expr = if let Some(next) = state.next {
                    // Substitute using the combined path (old state values + new input translations)
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
                    
                    // Add condition to path if not a tautology
                    if let Some(condition) = opt_condition {
                        branch_path.path_conditions.push(condition);
                    }

                    // Continue processing this value (might have nested ITEs)
                    expr_stack.push((branch_path, value));
                }
            } else {
                // Not an ITE - this is a final value for this state
                // State variables use their original symbol (no timestamp)
                current_path.variable_definitions.insert(state_symbol, current_expr);
                
                // Push to main stack to continue with next state
                stack.push((current_path, state_idx + 1));
            }
        }
    }

    /// Collect all symbols used in an expression
    fn collect_symbols(&self, ctx: &Context, expr: ExprRef, symbols: &mut HashSet<ExprRef>) {
        use patronus::expr::ForEachChild;
        
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

    /// Try to evaluate an expression to a boolean constant
    /// Returns Some(true) if always true, Some(false) if always false, None if can't determine
    fn try_eval_bool(ctx: &Context, expr: ExprRef) -> Option<bool> {
        match &ctx[expr] {
            Expr::BVLiteral(v) => {
                if v.width() == 1 {
                    Some(v.is_true())
                } else {
                    None
                }
            }
            Expr::BVNot(inner, width) if *width == 1 => {
                Self::try_eval_bool(ctx, *inner).map(|b| !b)
            }
            Expr::BVAnd(a, b, width) if *width == 1 => {
                match (Self::try_eval_bool(ctx, *a), Self::try_eval_bool(ctx, *b)) {
                    (Some(a_val), Some(b_val)) => Some(a_val && b_val),
                    (Some(false), _) | (_, Some(false)) => Some(false),
                    _ => None,
                }
            }
            Expr::BVOr(a, b, width) if *width == 1 => {
                match (Self::try_eval_bool(ctx, *a), Self::try_eval_bool(ctx, *b)) {
                    (Some(a_val), Some(b_val)) => Some(a_val || b_val),
                    (Some(true), _) | (_, Some(true)) => Some(true),
                    _ => None,
                }
            }
            Expr::BVImplies(a, b) => {
                // implies(a, b) = !a || b
                match (Self::try_eval_bool(ctx, *a), Self::try_eval_bool(ctx, *b)) {
                    (Some(false), _) => Some(true),  // false implies anything = true
                    (_, Some(true)) => Some(true),   // anything implies true = true
                    (Some(true), Some(false)) => Some(false),
                    _ => None,
                }
            }
            Expr::BVEqual(a, b) => {
                // Check if both are the same expression
                if a == b {
                    return Some(true);
                }
                // Check if both are literals
                if let (Expr::BVLiteral(va), Expr::BVLiteral(vb)) = (&ctx[*a], &ctx[*b]) {
                    Some(va.get(ctx) == vb.get(ctx))
                } else {
                    None
                }
            }
            Expr::BVGreaterEqual(a, b) => {
                if let (Expr::BVLiteral(va), Expr::BVLiteral(vb)) = (&ctx[*a], &ctx[*b]) {
                    Some(va.get(ctx).is_greater_or_equal(&vb.get(ctx)))
                } else {
                    None
                }
            }
            Expr::BVGreater(a, b) => {
                if let (Expr::BVLiteral(va), Expr::BVLiteral(vb)) = (&ctx[*a], &ctx[*b]) {
                    Some(va.get(ctx).is_greater(&vb.get(ctx)))
                } else {
                    None
                }
            }
            Expr::BVIte { cond, tru, fals } => {
                match Self::try_eval_bool(ctx, *cond) {
                    Some(true) => Self::try_eval_bool(ctx, *tru),
                    Some(false) => Self::try_eval_bool(ctx, *fals),
                    None => None,
                }
            }
            _ => None,
        }
    }

    /// Check if an expression is a tautology (always true)
    fn is_tautology(ctx: &Context, expr: ExprRef) -> bool {
        Self::try_eval_bool(ctx, expr) == Some(true)
    }

    /// Print the current state of symbolic execution
    pub fn print_step(&self, ctx: &mut Context) {
        println!("Step {}:", self.current_step);
        
        if self.current_step == 0 {
            // Initial step - print only state variable definitions (no inputs yet)
            if let Some(path) = self.paths.first() {
                println!("  Variables:");
                // Print state variables from variable_definitions
                for state in &self.ts.states {
                    let original_name = ctx.get_symbol_name(state.symbol).unwrap_or("state").to_string();
                    if let Some(&value) = path.variable_definitions.get(&state.symbol) {
                        let value_str = value.serialize_to_str(ctx);
                        println!("    {} = {}", original_name, value_str);
                    }
                }
                // Don't print inputs at step 0 - they don't exist yet
            }
        } else {
            // After step - print all paths with variables and constraints
            for (path_idx, path) in self.paths.iter().enumerate() {
                println!("  Path_condition {}:", path_idx + 1);
                
                // Print variable definitions (substituted and simplified)
                println!("    Variables:");
                
                // Print state variables
                for state in &self.ts.states {
                    if let Some(&value) = path.variable_definitions.get(&state.symbol) {
                        let sym_name = ctx.get_symbol_name(state.symbol).unwrap_or("unknown").to_string();
                        // For state variables, just simplify without recursive substitution
                        // (to avoid expanding self-references like counter in add(counter, 1))
                        let simplified = simplify_single_expression(ctx, value);
                        println!("      {} = {}", sym_name, simplified.serialize_to_str(ctx));
                    }
                }
                
                // Print input variables (timestamped)
                for input in &self.ts.inputs {
                    let original_name = ctx.get_symbol_name(*input).unwrap_or("input").to_string();
                    if let Some(&value) = path.translations.get(input) {
                        let sym_name = ctx.get_symbol_name(value).unwrap_or("unknown");
                        println!("      {} = {}", original_name, sym_name);
                    }
                }
                
                // Substitute variable definitions into constraints, simplify, and filter tautologies
                println!("    Constraints:");
                let mut constraint_idx = 0;
                for &constraint in &path.path_conditions {
                    // Substitute all variable definitions into the constraint
                    let substituted = Self::substitute_definitions(ctx, constraint, &path.variable_definitions);
                    // Simplify the result
                    let simplified = simplify_single_expression(ctx, substituted);
                    
                    // Skip tautologies (always true constraints)
                    if !Self::is_tautology(ctx, simplified) {
                        println!("      Constraint {}: {}", constraint_idx, simplified.serialize_to_str(ctx));
                        constraint_idx += 1;
                    }
                }
                
                println!();
            }
        }
    }
}
