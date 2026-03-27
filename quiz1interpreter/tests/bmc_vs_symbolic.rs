//! Integration tests that compare the output of the patronus BMC against
//! the SymbolicExecutor implemented in this crate.
//!
//! Both tools are run on every BTOR2 file in `tests/fixtures/`.  Their
//! verdicts on bad-state reachability must agree, and—when both find a
//! violation—the step numbers must be consistent:
//!
//! * The patronus BMC checks bad states at every step k = 0, 1, …, k_max
//!   (k = 0 is the initial state).
//! * The SymbolicExecutor calls `init()` to set up the initial state without
//!   checking bad states, then checks them on each subsequent `step()` call.
//!   Consequently the first opportunity to detect a bad state is at step 1,
//!   which corresponds to BMC's k = 1.
//!
//! For all BTOR2 files used here the initial state (k = 0) is always safe
//! due to the reset constraint, so both tools produce identical step numbers
//! when they agree on a violation.
//!
//! BTOR2 fixture naming convention
//! --------------------------------
//! * `*.sat.btor`   – the bad state IS reachable (expected Unsafe)
//! * `*.unsat.btor` – the bad state is NOT reachable within the bound (expected Safe)
//! * Other names    – reachability is verified by comparing both tools

use patronus::mc::{ModelCheckResult, bmc};
use patronus::smt::{Solver, Z3};
use quiz1interpreter::{StepResult, SymbolicExecutor, load_btor2_file};
use std::path::Path;

// ── Types ─────────────────────────────────────────────────────────────────────

/// The verdict produced by a model-checking run.
#[derive(Debug, PartialEq, Eq)]
enum McVerdict {
    /// No bad state found within the given bound.
    Safe,
    /// Bad state found; the inner value is the step at which it was detected.
    /// For the BMC this is 0-indexed (0 = initial state, 1 = after first
    /// transition, …).  For the symbolic executor it is 1-indexed because the
    /// initial state is never checked; the two indices agree for k ≥ 1.
    Unsafe(usize),
}

/// Whether a fixture is expected to be satisfiable (bad state reachable) or not.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Expected {
    Safe,
    Unsafe,
}

// ── Path helper ───────────────────────────────────────────────────────────────

/// Resolve a BTOR2 fixture filename relative to `tests/fixtures/` inside
/// the crate root.  Using `CARGO_MANIFEST_DIR` gives an absolute path that
/// is independent of the current working directory at test time.
fn fixture(filename: &str) -> String {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("fixtures")
        .join(filename)
        .to_string_lossy()
        .into_owned()
}

// ── BMC driver ────────────────────────────────────────────────────────────────

/// Run the patronus BMC on `path` for up to `k_max` steps using Z3.
///
/// Expression simplification is intentionally skipped so that both tools
/// operate on the exact same transition system.
fn run_bmc(path: &str, k_max: u64) -> McVerdict {
    let (mut ctx, sys) = load_btor2_file(path)
        .unwrap_or_else(|e| panic!("BMC: failed to load '{}': {}", path, e));

    let mut smt_ctx = Z3
        .start(None::<std::fs::File>)
        .expect("BMC: failed to start Z3");

    let result = bmc(&mut ctx, &mut smt_ctx, &sys, true, false, k_max)
        .expect("BMC: solver error");

    match result {
        ModelCheckResult::Fail(witness) => {
            // `witness.inputs` has one entry per step k = 0 …= failing_k,
            // so the failing step equals `witness.inputs.len() - 1`.
            McVerdict::Unsafe(witness.inputs.len().saturating_sub(1))
        }
        ModelCheckResult::Success => McVerdict::Safe,
        ModelCheckResult::Unknown => {
            panic!("BMC returned Unknown for '{}' — consider increasing k_max", path)
        }
    }
}

// ── Symbolic executor driver ──────────────────────────────────────────────────

/// Run the SymbolicExecutor on `path` for up to `k_max` steps using Z3.
///
/// The executor does **not** check bad states at k = 0 (initial state).
/// Bad states are first checked after the first `step()` call (k = 1).
fn run_symbolic(path: &str, k_max: usize) -> McVerdict {
    let (mut ctx, ts) = load_btor2_file(path)
        .unwrap_or_else(|e| panic!("Symbolic: failed to load '{}': {}", path, e));

    let mut solver = Z3
        .start(None::<std::fs::File>)
        .expect("Symbolic: failed to start Z3");

    let mut executor = SymbolicExecutor::new(&ts);
    executor.init(&mut ctx);

    for step in 1..=k_max {
        if executor.step(&mut ctx, &mut solver) == StepResult::BadStateReached {
            return McVerdict::Unsafe(step);
        }
    }

    McVerdict::Safe
}

// ── Core comparison helper ────────────────────────────────────────────────────

/// Run both tools on the fixture `btor_file` and assert their verdicts agree.
///
/// If `expected` is provided the test also asserts that both tools produce
/// the expected verdict, catching regressions in known-SAT / known-UNSAT cases.
///
/// Agreement rules
/// ---------------
/// * **Both Safe** – OK.
/// * **Both Unsafe** – Step numbers must match exactly for k ≥ 1.  The only
///   exception is if BMC found the violation at k = 0 (initial state, which
///   the symbolic executor cannot detect on its own); in that case the
///   symbolic executor is allowed to report it one step later.
/// * **BMC Safe, Symbolic Unsafe** – Test fails: spurious violation in the
///   symbolic executor (unsoundness).
/// * **BMC Unsafe, Symbolic Safe** – Test fails: the symbolic executor missed
///   a real violation within the bound (incompleteness).
fn compare(btor_file: &str, k_max: usize, expected: Option<Expected>) {
    let path = fixture(btor_file);

    let bmc_verdict = run_bmc(&path, k_max as u64);
    // The symbolic executor runs one extra step so it can detect violations
    // that BMC would catch at k = 0 (symbolic's first check is at step 1).
    let sym_verdict = run_symbolic(&path, k_max + 1);

    println!(
        "[{btor_file}]  BMC: {bmc_verdict:?}  |  Symbolic: {sym_verdict:?}"
    );

    // Check expected verdict against BMC (ground truth).
    if let Some(exp) = expected {
        match exp {
            Expected::Safe => assert_eq!(
                bmc_verdict,
                McVerdict::Safe,
                "[{btor_file}] Expected Safe but BMC found {bmc_verdict:?}"
            ),
            Expected::Unsafe => assert!(
                matches!(bmc_verdict, McVerdict::Unsafe(_)),
                "[{btor_file}] Expected Unsafe but BMC returned Safe within {k_max} steps"
            ),
        }
    }

    // Check that both tools agree.
    match (&bmc_verdict, &sym_verdict) {
        (McVerdict::Safe, McVerdict::Safe) => {}

        (McVerdict::Unsafe(bmc_step), McVerdict::Unsafe(sym_step)) => {
            let max_allowed = if *bmc_step == 0 { 1_usize } else { *bmc_step };
            assert!(
                *sym_step <= max_allowed,
                "[{btor_file}] BMC found bad state at step {bmc_step} but symbolic \
                 executor found it at step {sym_step} (expected ≤ {max_allowed})"
            );
        }

        (McVerdict::Safe, McVerdict::Unsafe(sym_step)) => panic!(
            "[{btor_file}] Symbolic executor reported a spurious bad state at step \
             {sym_step} that BMC did not confirm (possible unsoundness)"
        ),

        (McVerdict::Unsafe(bmc_step), McVerdict::Safe) => panic!(
            "[{btor_file}] BMC found a bad state at step {bmc_step} that the \
             symbolic executor missed within {} steps (possible incompleteness)",
            k_max + 1
        ),
    }
}

// ── Test cases ────────────────────────────────────────────────────────────────

/// Quiz 1: 16-bit counter that increments by 1 each cycle; bad state fires
/// when `!reset && counter > 10`.  The reset constraint forces `reset = 1`
/// during the initial cycle, so the earliest violation is at step 12.
#[test]
fn test_quiz1_bmc_vs_symbolic() {
    compare("Quiz1.btor", 20, Some(Expected::Unsafe));
}

/// Quiz 1 (fail-early variant): identical to Quiz1 but the threshold is 1
/// instead of 10, so the violation occurs much earlier (around step 3–4).
#[test]
fn test_quiz1_fail_early_bmc_vs_symbolic() {
    compare("Quiz1FailEarly.btor", 20, Some(Expected::Unsafe));
}

/// Quiz 1 (unsat variant): same circuit as Quiz1 but with an additional
/// `assume` that constrains `counter ≤ 9` whenever `!reset`, making the
/// `counter > 10` bad state unreachable.  Both tools must return Safe.
#[test]
fn test_quiz1_unsat_bmc_vs_symbolic() {
    compare("Quiz1.unsat.btor", 10, Some(Expected::Safe));
}

/// Quiz 2: a countdown counter starting near 4; bad state fires when the
/// counter reaches or exceeds 4 while not in reset.
#[test]
fn test_quiz2_sat_bmc_vs_symbolic() {
    compare("Quiz2.sat.btor", 20, Some(Expected::Unsafe));
}

/// Quiz 4 (sat variant): counter with a start signal and two bad-state
/// assertions; both should be reachable within the bound.
#[test]
fn test_quiz4_sat_bmc_vs_symbolic() {
    compare("Quiz4.sat.btor", 20, Some(Expected::Unsafe));
}

/// Quiz 4 (unsat variant): same circuit as Quiz4.sat but includes a `past()`
/// temporal register (`out` / `_cycles`) that makes both bad-state assertions
/// unreachable.  Both tools must return Safe.
#[test]
fn test_quiz4_unsat_bmc_vs_symbolic() {
    compare("Quiz4.unsat.btor", 10, Some(Expected::Safe));
}
