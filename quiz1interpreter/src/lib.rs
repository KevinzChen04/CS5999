use patronus;

pub mod symbolic_executor;
pub use symbolic_executor::{ExecutionPath, SymbolicExecutor};

/// Loads a BTOR2 file and returns the context and transition system
///
/// # Arguments
/// * `path` - Path to the BTOR2 file
///
/// # Returns
/// * `Result<(Context, TransitionSystem), Box<dyn std::error::Error>>` - The parsed context and transition system, or an error
pub fn load_btor2_file(
    path: &str,
) -> Result<(patronus::expr::Context, patronus::system::TransitionSystem), Box<dyn std::error::Error>>
{
    let (ctx, ts) = patronus::btor2::parse_file(path).ok_or("Failed to parse BTOR2 file")?;
    Ok((ctx, ts))
}

#[cfg(test)]
mod tests {
    use super::*;
    use patronus::smt::{Solver, Z3};

    #[test]
    fn test_symbolic_executor_init() {
        let (mut ctx, ts) = load_btor2_file("Quiz1.btor").expect("Failed to load BTOR2 file");
        let mut executor = SymbolicExecutor::new(&ts);
        executor.init(&mut ctx);
        
        // Should have exactly one path after init
        assert_eq!(executor.paths().len(), 1);
        assert_eq!(executor.current_step(), 0);
    }
    
    #[test]
    fn test_symbolic_executor_step() {
        let (mut ctx, ts) = load_btor2_file("Quiz1.btor").expect("Failed to load BTOR2 file");
        let mut solver = Z3.start(None::<std::fs::File>).expect("Failed to start solver");
        
        let mut executor = SymbolicExecutor::new(&ts);
        executor.init(&mut ctx);
        executor.step(&mut ctx, &mut solver);
        
        // After one step, should have some paths
        assert!(executor.paths().len() > 0);
        assert_eq!(executor.current_step(), 1);
    }
}
