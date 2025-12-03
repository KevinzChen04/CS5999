use clap::Parser;
use patronus::expr::SerializableIrNode;
use patronus::smt::{Solver, Z3};
use quiz1interpreter::SymbolicExecutor;

#[derive(Parser)]
#[command(name = "quiz1interpreter")]
#[command(about = "A BTOR2 file interpreter with symbolic execution")]
struct Cli {
    /// Path to the BTOR2 file
    input_path: String,
    /// Path for the output VCD file
    #[arg(short, long)]
    output_path: String,
    /// Number of symbolic execution steps to perform
    #[arg(short, long, default_value = "2")]
    steps: usize,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();

    let (mut ctx, ts) = quiz1interpreter::load_btor2_file(&cli.input_path)?;
    let mut solver = Z3.start(Some(std::fs::File::create("replay.smt").unwrap()))?;

    println!("Transition System: {}", ts.serialize_to_str(&ctx));
    println!("\n=== Symbolic Execution ===\n");

    // Create and initialize the symbolic executor
    let mut executor = SymbolicExecutor::new(&ts);
    executor.init(&mut ctx);

    // Print initial state (Step 0)
    executor.print_step(&mut ctx);

    // Perform symbolic execution steps
    for _ in 0..cli.steps {
        println!();
        executor.step(&mut ctx, &mut solver);
        executor.print_step(&mut ctx);
    }

    Ok(())
}
