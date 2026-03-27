//! Debug binary that runs BMC and the SymbolicExecutor on a single BTOR2 file
//! and prints a verbose, step-by-step comparison so you can see exactly why
//! one tool finds (or misses) a bad state.
//!
//! # Usage
//!
//!   cargo run --bin debug_case -- Quiz1.btor
//!   cargo run --bin debug_case -- Quiz2.sat.btor --steps 20
//!   cargo run --bin debug_case -- /absolute/path/to/my.btor --steps 10
//!
//! If the argument does not contain a path separator it is treated as a fixture
//! name and resolved relative to `tests/fixtures/` inside this crate.

use clap::Parser;
use patronus::mc::{ModelCheckResult, bmc};
use patronus::smt::{Solver, Z3};
use quiz1interpreter::{StepResult, SymbolicExecutor, load_btor2_file};
use std::path::{Path, PathBuf};

// ── CLI ───────────────────────────────────────────────────────────────────────

#[derive(Parser)]
#[command(name = "debug_case")]
#[command(about = "Compare BMC vs SymbolicExecutor on a single BTOR2 file")]
struct Cli {
    /// BTOR2 file: a bare name like 'Quiz2.sat.btor' is looked up in
    /// tests/fixtures/; a path containing '/' is used as-is.
    input: String,

    /// Maximum number of steps to run (BMC bound = steps, symbolic = steps+1)
    #[arg(short, long, default_value = "20")]
    steps: usize,
}

// ── Path helpers ──────────────────────────────────────────────────────────────

fn resolve_path(input: &str) -> PathBuf {
    let p = Path::new(input);
    if p.components().count() > 1 || p.is_absolute() {
        // looks like an actual path
        p.to_path_buf()
    } else {
        // bare filename → look in tests/fixtures/
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("tests")
            .join("fixtures")
            .join(input)
    }
}

// ── BMC run ───────────────────────────────────────────────────────────────────

fn run_bmc_verbose(path: &str, k_max: usize) {
    println!("┌─ BMC (patronus) ───────────────────────────────────────────┐");

    let (mut ctx, sys) = match load_btor2_file(path) {
        Ok(v) => v,
        Err(e) => {
            println!("  ERROR loading file: {e}");
            println!("└────────────────────────────────────────────────────────────┘\n");
            return;
        }
    };

    let mut smt_ctx = Z3
        .start(None::<std::fs::File>)
        .expect("failed to start Z3");

    println!("  Running BMC up to k = {k_max} …");

    match bmc(&mut ctx, &mut smt_ctx, &sys, true, false, k_max as u64) {
        Ok(ModelCheckResult::Fail(witness)) => {
            let failing_step = witness.inputs.len().saturating_sub(1);
            println!("  Result  : UNSAFE");
            println!("  Bad step: k = {failing_step}");
            println!("  Witness : {} input frame(s)", witness.inputs.len());
        }
        Ok(ModelCheckResult::Success) => {
            println!("  Result  : SAFE (no bad state within k = {k_max})");
        }
        Ok(ModelCheckResult::Unknown) => {
            println!("  Result  : UNKNOWN (solver gave up)");
        }
        Err(e) => {
            println!("  ERROR   : {e:?}");
        }
    }

    println!("└────────────────────────────────────────────────────────────┘\n");
}

// ── Symbolic executor run ─────────────────────────────────────────────────────

fn run_symbolic_verbose(path: &str, k_max: usize) {
    println!("┌─ SymbolicExecutor ─────────────────────────────────────────┐");

    let (mut ctx, ts) = match load_btor2_file(path) {
        Ok(v) => v,
        Err(e) => {
            println!("  ERROR loading file: {e}");
            println!("└────────────────────────────────────────────────────────────┘\n");
            return;
        }
    };

    let mut solver = Z3
        .start(None::<std::fs::File>)
        .expect("failed to start Z3");

    let mut executor = SymbolicExecutor::new(&ts);
    executor.init(&mut ctx);

    println!("  Running symbolic execution up to step {k_max} …\n");

    // Print initial state
    print!("  ");
    executor.print_step(&mut ctx);

    let mut found_bad = false;
    for _step in 1..=k_max {
        let result = executor.step(&mut ctx, &mut solver);
        print!("  ");
        executor.print_step(&mut ctx);
        if result == StepResult::BadStateReached {
            found_bad = true;
            break;
        }
    }

    if !found_bad {
        println!("  Result: SAFE (no bad state within {} steps)", k_max);
    }

    println!("└────────────────────────────────────────────────────────────┘\n");
}

// ── Summary comparison ────────────────────────────────────────────────────────

fn run_summary(path: &str, k_max: usize) {
    // BMC verdict
    let bmc_verdict = {
        let (mut ctx, sys) = load_btor2_file(path)
            .unwrap_or_else(|e| panic!("failed to load '{}': {}", path, e));
        let mut smt_ctx = Z3.start(None::<std::fs::File>).expect("Z3 start");
        match bmc(&mut ctx, &mut smt_ctx, &sys, true, false, k_max as u64) {
            Ok(ModelCheckResult::Fail(w)) => {
                Some(w.inputs.len().saturating_sub(1))
            }
            _ => None,
        }
    };

    // Symbolic verdict
    let sym_verdict = {
        let (mut ctx, ts) = load_btor2_file(path)
            .unwrap_or_else(|e| panic!("failed to load '{}': {}", path, e));
        let mut solver = Z3.start(None::<std::fs::File>).expect("Z3 start");
        let mut executor = SymbolicExecutor::new(&ts);
        executor.init(&mut ctx);
        let mut found = None;
        for step in 1..=(k_max + 1) {
            if executor.step(&mut ctx, &mut solver) == StepResult::BadStateReached {
                found = Some(step);
                break;
            }
        }
        found
    };

    println!("┌─ Summary ──────────────────────────────────────────────────┐");
    match (bmc_verdict, sym_verdict) {
        (None, None) => {
            println!("  Both tools: SAFE within {k_max} steps  ✓");
        }
        (Some(bmc_step), Some(sym_step)) => {
            println!("  BMC       : UNSAFE at step {bmc_step}");
            println!("  Symbolic  : UNSAFE at step {sym_step}");
            let max_allowed = if bmc_step == 0 { 1 } else { bmc_step };
            if sym_step <= max_allowed {
                println!("  Agreement : ✓  (steps are consistent)");
            } else {
                println!(
                    "  Agreement : ✗  (symbolic reported step {sym_step} but BMC expected ≤ {max_allowed})"
                );
            }
        }
        (None, Some(sym_step)) => {
            println!("  BMC       : SAFE");
            println!("  Symbolic  : UNSAFE at step {sym_step}");
            println!("  Agreement : ✗  SPURIOUS violation in symbolic executor (possible unsoundness)");
        }
        (Some(bmc_step), None) => {
            println!("  BMC       : UNSAFE at step {bmc_step}");
            println!("  Symbolic  : SAFE (missed violation within {} steps)", k_max + 1);
            println!("  Agreement : ✗  Symbolic executor MISSED a real violation (possible incompleteness)");
        }
    }
    println!("└────────────────────────────────────────────────────────────┘");
}

// ── Entry point ───────────────────────────────────────────────────────────────

fn main() {
    let cli = Cli::parse();

    let path = resolve_path(&cli.input);
    let path_str = path.to_string_lossy().into_owned();

    println!("\n═══════════════════════════════════════════════════════════════");
    println!("  File : {}", path_str);
    println!("  Bound: {} steps", cli.steps);
    println!("═══════════════════════════════════════════════════════════════\n");

    run_bmc_verbose(&path_str, cli.steps);
    run_symbolic_verbose(&path_str, cli.steps);
    run_summary(&path_str, cli.steps);
    println!();
}
