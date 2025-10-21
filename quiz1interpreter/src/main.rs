use clap::Parser;
use quiz1interpreter;
// use std::borrow::Cow;

#[derive(Parser)]
#[command(name = "quiz1interpreter")]
#[command(about = "A BTOR2 file interpreter")]
struct Cli {
    /// Path to the BTOR2 file
    input_path: String,
    /// Path for the output VCD file
    #[arg(short, long)]
    output_path: String,
}

fn main() {
    let cli = Cli::parse();
    
    match quiz1interpreter::load_btor2_file(&cli.input_path) {
        Ok((ctx, ts)) => {
            println!("Transition System: {:?}", ts);

            let _interpreter = patronus::sim::Interpreter::new_with_wavedump(&ctx, &ts, &cli.output_path);
            println!("Interpreter created successfully");
        }
        Err(e) => {
            eprintln!("Failed to parse file '{}': {}", cli.input_path, e);
            std::process::exit(1);
        }

        
    }
}