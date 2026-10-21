//! Solver subprocess handling. Lives in its own test binary because it sets
//! process-wide solver environment variables.

use bil::smt::{run_smt_prover, Prover, Verdict};
use std::fs;
use std::os::unix::fs::PermissionsExt;
use std::sync::mpsc;
use std::time::{Duration, Instant};

/// A solver that never reads stdin must still be killed by the wall-clock timeout,
/// even when the script is larger than the OS pipe buffer.
#[test]
fn solver_that_ignores_stdin_is_killed_by_timeout() {
    let dir = std::env::temp_dir().join(format!("bil-solver-proc-{}", std::process::id()));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let solver = dir.join("deaf-solver");
    fs::write(&solver, "#!/bin/sh\nexec sleep 30\n").unwrap();
    fs::set_permissions(&solver, fs::Permissions::from_mode(0o755)).unwrap();

    std::env::set_var("BIL_Z3_PATH", &solver);
    std::env::set_var("BIL_SOLVER_TIMEOUT_MS", "1000");

    // About 1 MiB of SMT-LIB, far beyond a 64 KiB pipe buffer.
    let mut script = String::new();
    for i in 0..40_000 {
        script.push_str(&format!("(declare-const v{} Int)\n", i));
    }
    script.push_str("(check-sat)\n");

    let (tx, rx) = mpsc::channel();
    let start = Instant::now();
    std::thread::spawn(move || {
        let _ = tx.send(run_smt_prover(Prover::Z3, &script));
    });
    let result = rx
        .recv_timeout(Duration::from_secs(15))
        .expect("solver call hung: timeout never fired while writing stdin");

    assert_eq!(result.verdict, Verdict::Unknown, "{}", result.detail);
    assert!(result.detail.contains("timeout"), "{}", result.detail);
    assert!(start.elapsed() < Duration::from_secs(10));
}
