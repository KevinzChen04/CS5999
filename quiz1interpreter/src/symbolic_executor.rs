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
    /// Only untranslatable values are input symbols and uninitialized state symbols
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
    /// Sets up initial state variables as name_t0, unless they have an initial value
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

        // Initialize state variables in the translation map
        for state in &self.ts.states {
            let original_name = ctx.get_symbol_name(state.symbol).unwrap_or("state");
            
            if let Some(init_expr) = state.init {
                // If it has an initial value, translate directly to that value
                initial_path.translations.insert(state.symbol, init_expr);
            } else {
                // No initial value, create symbolic variable name_t0
                // This is an untranslatable symbol
                let timestamped_name = format!("{}_t0", original_name);
                let tpe = self.state_types[&state.symbol];
                let timestamped_sym = match tpe {
                    Type::BV(width) => ctx.bv_symbol(&timestamped_name, width),
                    Type::Array(arr_type) => {
                        ctx.array_symbol(&timestamped_name, arr_type.index_width, arr_type.data_width)
                    }
                };
                initial_path.translations.insert(state.symbol, timestamped_sym);
            }
        }

        // Initialize input variables in the translation map
        // Inputs are always untranslatable symbols
        for input in &self.ts.inputs {
            let original_name = ctx.get_symbol_name(*input).unwrap_or("input");
            let timestamped_name = format!("{}_t0", original_name);
            let tpe = self.input_types[input];
            let timestamped_sym = match tpe {
                Type::BV(width) => ctx.bv_symbol(&timestamped_name, width),
                Type::Array(arr_type) => {
                    ctx.array_symbol(&timestamped_name, arr_type.index_width, arr_type.data_width)
                }
            };
            initial_path.translations.insert(*input, timestamped_sym);
        }

        self.paths.push(initial_path);
        self.current_step = 0;
    }

    /// Substitute all symbols in an expression using the translation map
    fn substitute_expr(
        &self,
        ctx: &mut Context,
        expr: ExprRef,
        path: &ExecutionPath,
    ) -> ExprRef {
        use patronus::expr::simple_transform_expr;
        
        let translations = &path.translations;
        
        simple_transform_expr(ctx, expr, |_ctx, e, _children| {
            // Check if this is a symbol we need to translate
            if translations.contains_key(&e) {
                Some(translations[&e])
            } else {
                None // No translation
            }
        })
    }

    /// Substitute variable definitions into an expression recursively until fixed point
    fn substitute_definitions(
        ctx: &mut Context,
        expr: ExprRef,
        definitions: &HashMap<ExprRef, ExprRef>,
    ) -> ExprRef {
        use patronus::expr::simple_transform_expr;
        
        let mut current = expr;
        let mut prev = expr;
        
        // Keep substituting until no more changes (fixed point)
        loop {
            current = simple_transform_expr(ctx, current, |_ctx, e, _children| {
                // Check if this is a defined variable we need to substitute
                if definitions.contains_key(&e) {
                    Some(definitions[&e])
                } else {
                    None // No substitution
                }
            });
            
            if current == prev {
                break;
            }
            prev = current;
        }
        
        current
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
            // Create base path with new timestamped variables
            let mut base_path = path.clone();

            // Create new timestamped state variables and update translations
            for state in &states {
                let original_name = ctx.get_symbol_name(state.symbol).unwrap_or("state");
                let timestamped_name = format!("{}_t{}", original_name, next_step);
                let tpe = self.state_types[&state.symbol];
                let timestamped_sym = match tpe {
                    Type::BV(width) => ctx.bv_symbol(&timestamped_name, width),
                    Type::Array(arr_type) => {
                        ctx.array_symbol(&timestamped_name, arr_type.index_width, arr_type.data_width)
                    }
                };
                base_path.translations.insert(state.symbol, timestamped_sym);
            }

            // Create new timestamped input variables and update translations
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
                base_path.translations.insert(*input, timestamped_sym);
            }

            // Add transition system constraints
            for &constraint in &self.ts.constraints {
                let substituted = self.substitute_expr(ctx, constraint, &base_path);
                base_path.path_conditions.push(substituted);
            }

            // DFS exploration of state transitions
            // Stack contains: (current_path, state_index)
            let mut stack: Vec<(ExecutionPath, usize)> = vec![(base_path, 0)];

            while let Some((current_path, state_idx)) = stack.pop() {
                if state_idx >= states.len() {
                    // All states processed - this is a complete path
                    new_paths.push(current_path);
                    continue;
                }

                let state = &states[state_idx];
                let next_expr = if let Some(next) = state.next {
                    // Substitute using the ORIGINAL path's translations (before we updated them)
                    // We need to use the values from the previous step
                    self.substitute_expr(ctx, next, path)
                } else {
                    // No next expression - state stays the same
                    path.translations[&state.symbol]
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
                let new_state_sym = current_path.translations[&state_symbol];
                current_path.variable_definitions.insert(new_state_sym, current_expr);
                
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
            // Initial step - print variable definitions for initial values
            if let Some(path) = self.paths.first() {
                println!("  Variables:");
                for state in &self.ts.states {
                    let original_name = ctx.get_symbol_name(state.symbol).unwrap_or("state").to_string();
                    if let Some(&value) = path.translations.get(&state.symbol) {
                        let value_str = value.serialize_to_str(ctx);
                        // Only print if it's a concrete value (not a symbol referring to itself)
                        if ctx[value].is_symbol() {
                            let sym_name = ctx.get_symbol_name(value).unwrap_or("unknown");
                            println!("    {} = {}", original_name, sym_name);
                        } else {
                            println!("    {} = {}", original_name, value_str);
                        }
                    }
                }
                for input in &self.ts.inputs {
                    let original_name = ctx.get_symbol_name(*input).unwrap_or("input").to_string();
                    if let Some(&value) = path.translations.get(input) {
                        let sym_name = ctx.get_symbol_name(value).unwrap_or("unknown");
                        println!("    {} = {}", original_name, sym_name);
                    }
                }
            }
        } else {
            // After step - print all paths with variables and constraints
            for (path_idx, path) in self.paths.iter().enumerate() {
                println!("  Path_condition {}:", path_idx + 1);
                
                // Print variable definitions (substituted and simplified)
                println!("    Variables:");
                for (&sym, &value) in &path.variable_definitions {
                    let sym_name = ctx.get_symbol_name(sym).unwrap_or("unknown").to_string();
                    // Substitute other variable definitions into this value
                    let substituted = Self::substitute_definitions(ctx, value, &path.variable_definitions);
                    // Simplify the result
                    let simplified = simplify_single_expression(ctx, substituted);
                    println!("      {} = {}", sym_name, simplified.serialize_to_str(ctx));
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
