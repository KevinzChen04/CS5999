//! Timing binary that compares BMC and symbolic execution runtime and
//! estimates solver-only time by replaying captured SMT commands.
//!
//! # Usage
//!
//!   cargo run --bin time_it -- simple_spi.btor --steps 20
//!   cargo run --bin time_it -- ./simple_spi.btor --steps 50 --smt-log replay.smt2

use clap::Parser;
use patronus::mc::{ModelCheckResult, bmc};
use patronus::smt::{Solver, Z3};
use quiz1interpreter::{ExecutionStats, StepResult, SymbolicExecutor, load_btor2_file};
use std::fs::File;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::time::{Duration, Instant};

#[derive(Parser)]
#[command(name = "time_it")]
#[command(about = "Time BMC, symbolic execution, and solver replay")]
struct Cli {
    /// BTOR2 file path or fixture name
    input: String,

    /// Maximum number of steps to run
    #[arg(short, long, default_value = "20")]
    steps: usize,

    /// Path where SMT replay commands are written
    #[arg(long, default_value = "time_it_replay.smt2")]
    smt_log: String,

    /// Print detailed symbolic execution/debug stats
    #[arg(long, default_value_t = false)]
    debug: bool,
}

fn resolve_path(input: &str) -> PathBuf {
    let p = Path::new(input);
    if p.components().count() > 1 || p.is_absolute() {
        p.to_path_buf()
    } else {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("fixtures")
            .join(input)
    }
}

fn run_bmc_timed(path: &str, k_max: usize) -> Result<(Duration, ModelCheckResult), Box<dyn std::error::Error>> {
    let (mut ctx, sys) = load_btor2_file(path)?;
    let mut solver = Z3.start(None::<File>)?;
    let start = Instant::now();
    let result = bmc(&mut ctx, &mut solver, &sys, true, false, k_max as u64)?;
    Ok((start.elapsed(), result))
}

fn run_symbolic_timed_with_replay(
    path: &str,
    k_max: usize,
    replay_path: &Path,
) -> Result<(Duration, StepResult, usize, ExecutionStats), Box<dyn std::error::Error>> {
    let (mut ctx, ts) = load_btor2_file(path)?;
    let mut final_result = StepResult::Ok;
    let mut steps_executed = 0usize;
    let start = Instant::now();

    let stats = {
        let replay_file = File::create(replay_path)?;
        let mut solver = Z3.start(Some(replay_file))?;
        let mut executor = SymbolicExecutor::new(&ts);
        executor.init(&mut ctx);

        for _ in 0..k_max {
            steps_executed += 1;
            final_result = executor.step(&mut ctx, &mut solver);
            if final_result == StepResult::BadStateReached {
                break;
            }
        }
        executor.stats().clone()
    }; // drop solver here so replay file is flushed/closed

    Ok((start.elapsed(), final_result, steps_executed, stats))
}

fn replay_solver_script_timed(replay_path: &Path) -> Result<(Duration, usize), Box<dyn std::error::Error>> {
    let script = std::fs::read_to_string(replay_path)?;
    // Approximate command count for reporting only.
    let command_count = script
        .lines()
        .map(str::trim)
        .filter(|line| line.starts_with('('))
        .count();

    let start = Instant::now();
    let output = Command::new("z3")
        .arg(replay_path)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .output()?;
    let elapsed = start.elapsed();
    if !output.status.success() {
        let err = String::from_utf8_lossy(&output.stderr).to_string();
        return Err(format!("solver replay failed: {}", err).into());
    }

    Ok((elapsed, command_count))
}

fn describe_bmc_result(result: &ModelCheckResult) -> String {
    match result {
        ModelCheckResult::Success => "SAFE".to_string(),
        ModelCheckResult::Unknown => "UNKNOWN".to_string(),
        ModelCheckResult::Fail(witness) => {
            let step = witness.inputs.len().saturating_sub(1);
            format!("UNSAFE at step {}", step)
        }
    }
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let cli = Cli::parse();
    let input_path = resolve_path(&cli.input);
    let input_path_str = input_path.to_string_lossy().into_owned();
    let replay_path = PathBuf::from(&cli.smt_log);

    let (bmc_time, bmc_result) = run_bmc_timed(&input_path_str, cli.steps)?;
    let (sym_time, sym_result, steps_executed, sym_stats) =
        run_symbolic_timed_with_replay(&input_path_str, cli.steps, &replay_path)?;
    let (solver_replay_time, command_count) = replay_solver_script_timed(&replay_path)?;

    println!("File              : {}", input_path_str);
    println!("Step bound        : {}", cli.steps);
    println!("SMT log           : {}", replay_path.display());
    println!();
    println!("BMC verdict       : {}", describe_bmc_result(&bmc_result));
    println!("BMC runtime       : {:?}", bmc_time);
    println!();
    println!("Symbolic verdict  : {:?}", sym_result);
    println!("Symbolic steps    : {}", steps_executed);
    println!("Symbolic runtime  : {:?}", sym_time);
    println!();
    println!("Replay commands   : {}", command_count);
    println!("Solver-only replay: {:?}", solver_replay_time);

    if sym_time.as_nanos() > 0 {
        let pct = (solver_replay_time.as_secs_f64() / sym_time.as_secs_f64()) * 100.0;
        println!("Solver share (approx): {:.2}%", pct);
    }

    if cli.debug {
        println!();
        println!("--- Debug stats ---");
        println!("ITE encountered   : {}", sym_stats.ite_encountered);
        println!("SMT calls         : {}", sym_stats.smt_calls);
        println!("State variables   : {}", sym_stats.state_variables);
        println!("Transition stmts  : {}", sym_stats.transition_statements);
        println!("Total paths gen   : {}", sym_stats.total_paths_generated);
        println!("Active paths(final): {}", sym_stats.active_paths);
    }

    Ok(())
}
