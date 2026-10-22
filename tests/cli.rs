//! End-to-end tests of the `bil` binary: exit codes and the verdicts printed to users.
//!
//! These run the real executable, so they also cover `src/cli.rs` and `src/main.rs`,
//! which the library-facade tests never reach.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const BIL: &str = env!("CARGO_BIN_EXE_bil");

/// A false contract whose only counterexamples are x = ±37, which bounded sampling misses.
/// Only the SMT solver can refute it.
const SMT_ONLY_REFUTABLE: &str = r#"
fn sq(x: Int) -> Int
  requires x * x == 1369
  ensures  result == 0
=
  if true -> 0 - x fi
"#;

fn scratch_dir(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("bil-cli-{}-{}", std::process::id(), test));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn write_source(dir: &Path, src: &str) -> PathBuf {
    let path = dir.join("input.bil");
    fs::write(&path, src).unwrap();
    path
}

/// Writes an executable shell script that stands in for every SMT solver.
fn fake_solver(dir: &Path, body: &str) -> PathBuf {
    use std::os::unix::fs::PermissionsExt;
    let path = dir.join("fake-solver");
    fs::write(&path, format!("#!/bin/sh\ncat >/dev/null\n{}\n", body)).unwrap();
    fs::set_permissions(&path, fs::Permissions::from_mode(0o755)).unwrap();
    path
}

fn bil(args: &[&str]) -> Output {
    Command::new(BIL).args(args).output().expect("spawn bil")
}

fn bil_with_solver(solver: &Path, args: &[&str]) -> Output {
    Command::new(BIL)
        .args(args)
        .env("BIL_Z3_PATH", solver)
        .env("BIL_CVC5_PATH", solver)
        .env("BIL_VAMPIRE_PATH", solver)
        .env("BIL_SOLVER_TIMEOUT_MS", "2000")
        .output()
        .expect("spawn bil")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

#[test]
fn usage_errors_exit_nonzero() {
    assert_eq!(bil(&[]).status.code(), Some(1));
    assert_eq!(bil(&["frobnicate", "x.bil"]).status.code(), Some(1));
    assert_eq!(
        bil(&["verify", "/nonexistent/input.bil"]).status.code(),
        Some(1)
    );
}

/// Examples whose obligations are all proved exit 0. Examples with bounded-only
/// obligations exit 1 by default and 0 with `--allow-bounded`.
#[test]
fn verify_exit_code_on_every_example() {
    let bounded_only = ["gcd_refinement.bil", "smart_grid.bil"];
    for entry in fs::read_dir("examples").unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "bil") {
            continue;
        }
        let file = path.to_str().unwrap();
        let name = path.file_name().unwrap().to_str().unwrap();
        let strict = bil(&["verify", file]);
        let expected = if bounded_only.contains(&name) { 1 } else { 0 };
        assert_eq!(
            strict.status.code(),
            Some(expected),
            "{}:\n{}",
            name,
            stdout(&strict)
        );
        if expected == 1 {
            assert!(String::from_utf8_lossy(&strict.stderr).contains("--allow-bounded"));
        }
        let lenient = bil(&["verify", file, "--allow-bounded"]);
        assert_eq!(
            lenient.status.code(),
            Some(0),
            "{}:\n{}",
            name,
            stdout(&lenient)
        );
    }
}

#[test]
fn verify_exits_nonzero_on_bounded_counterexample() {
    let dir = scratch_dir("bounded-ce");
    let src = write_source(
        &dir,
        "fn f(x: Int) -> Int requires true ensures result == x + 1 = if true -> x fi\n",
    );
    let out = bil(&["verify", src.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(1), "{}", stdout(&out));
    assert!(stdout(&out).contains("[REFUTED]"));
}

#[test]
fn verify_exits_nonzero_on_false_lemma_and_never_proves_it() {
    let dir = scratch_dir("false-lemma");
    let src = write_source(
        &dir,
        "proof bogus() requires true ensures false { true }\n\
         fn f(x: Int) -> Int requires true ensures result == x + 1 = if true -> x fi\n",
    );
    let out = bil(&["verify", src.to_str().unwrap()]);
    let text = stdout(&out);
    assert_eq!(out.status.code(), Some(1), "{}", text);
    for line in text.lines().filter(|l| l.contains("`bogus`")) {
        assert!(
            !line.contains("PROVED"),
            "false lemma reported proved: {}",
            line
        );
    }
}

#[test]
fn verify_exits_nonzero_when_only_smt_finds_the_counterexample() {
    if bil::smt::find_solver_binary("z3").is_none() {
        eprintln!("skipping: z3 not installed");
        return;
    }
    let dir = scratch_dir("smt-only-ce");
    let src = write_source(&dir, SMT_ONLY_REFUTABLE);
    let out = bil(&["verify", src.to_str().unwrap()]);
    let text = stdout(&out);
    assert_eq!(out.status.code(), Some(1), "{}", text);
    assert!(
        text.lines()
            .any(|l| l.contains("Postcondition") && l.contains("[REFUTED]")),
        "{}",
        text
    );
    // The solver's model is shown as concrete values, not just "sat".
    assert!(
        text.contains("x = 37") || text.contains("x = -37"),
        "{}",
        text
    );
    assert!(!text.contains("SMT model: sat"), "{}", text);
}

#[test]
fn verify_json_exits_nonzero_on_refuted_obligation() {
    let dir = scratch_dir("json-refuted");
    let src = write_source(
        &dir,
        "fn f(x: Int) -> Int requires true ensures result == x + 1 = if true -> x fi\n",
    );
    let out = bil(&["verify", src.to_str().unwrap(), "--format", "json"]);
    assert_eq!(out.status.code(), Some(1));
    let parsed: serde_json::Value = serde_json::from_slice(&out.stdout).expect("valid JSON");
    assert!(parsed.as_array().is_some_and(|a| !a.is_empty()));
}

/// A broken solver must never turn into PROVED. Each case is solver output that
/// a naive parser could misread as `unsat`.
#[test]
fn broken_solver_output_is_never_reported_as_proved() {
    let cases = [
        (
            "smtlib-error-then-unsat",
            "echo '(error \"boom\")'\necho unsat",
        ),
        ("crash-no-output", "exit 139"),
        (
            "garbage",
            "echo 'segmentation fault (core dumped) unsatisfiable?'",
        ),
        ("timeout", "sleep 5\necho unsat"),
    ];
    for (name, body) in cases {
        let dir = scratch_dir(name);
        let solver = fake_solver(&dir, body);
        let src = write_source(&dir, SMT_ONLY_REFUTABLE);
        let out = bil_with_solver(&solver, &["verify", src.to_str().unwrap()]);
        let text = stdout(&out);
        for line in text.lines().filter(|l| l.contains("Postcondition")) {
            assert!(
                !line.contains("PROVED"),
                "case `{}`: broken solver produced a proof:\n{}",
                name,
                text
            );
        }
    }
}

/// A broken solver plus sampling that misses the counterexample leaves only
/// bounded evidence for a false contract, which must not exit 0 by default.
#[test]
fn verify_exits_nonzero_when_solver_fails_and_sampling_misses() {
    let dir = scratch_dir("bounded-only-exit");
    let solver = fake_solver(&dir, "echo '(error \"boom\")'");
    let src = write_source(&dir, SMT_ONLY_REFUTABLE);
    let out = bil_with_solver(&solver, &["verify", src.to_str().unwrap()]);
    assert_ne!(out.status.code(), Some(0), "{}", stdout(&out));
}

#[test]
fn model_check_exit_codes_follow_violations() {
    let dir = scratch_dir("mc-exit");
    let bad = write_source(
        &dir,
        "system Bad { state n: Int = 0  invariant Small: n < 3  terminal n == 5  \
         transition n < 5 -> n := n + 1 }\n",
    );
    let out = bil(&["model-check", bad.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(1));
    assert!(stdout(&out).contains("[VIOLATION]"));

    let json = bil(&["model-check", bad.to_str().unwrap(), "--json"]);
    assert_eq!(json.status.code(), Some(1));

    let good = dir.join("good.bil");
    fs::write(
        &good,
        "system Lin { state n: Int = 0  terminal n == 10  transition n < 10 -> n := n + 1 }\n",
    )
    .unwrap();
    let out = bil(&["model-check", good.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(0), "{}", stdout(&out));
    assert!(stdout(&out).contains("[VERIFIED]"));
}

#[test]
fn model_check_truncation_is_not_reported_as_verified() {
    let dir = scratch_dir("mc-truncated");
    let src = write_source(
        &dir,
        "system Lin { state n: Int = 0  terminal n == 100  transition n < 100 -> n := n + 1 }\n",
    );
    let out = bil(&["model-check", src.to_str().unwrap(), "--max-states", "10"]);
    let text = stdout(&out);
    assert!(!text.contains("[VERIFIED]"), "{}", text);
    assert!(text.contains("INCOMPLETE"), "{}", text);
}

// Bad flag values and unknown flags must fail loudly. Silently ignoring them would
// run a different analysis than the one requested.

#[test]
fn model_check_rejects_unparseable_bmc_depth() {
    let dir = scratch_dir("bad-bmc");
    let src = write_source(
        &dir,
        "system Lin { state n: Int = 0  terminal n == 10  transition n < 10 -> n := n + 1 }\n",
    );
    let out = bil(&["model-check", src.to_str().unwrap(), "--bmc", "abc"]);
    assert_ne!(out.status.code(), Some(0), "{}", stdout(&out));
}

#[test]
fn model_check_rejects_unparseable_max_states() {
    let dir = scratch_dir("bad-max-states");
    let src = write_source(
        &dir,
        "system Lin { state n: Int = 0  terminal n == 10  transition n < 10 -> n := n + 1 }\n",
    );
    let out = bil(&["model-check", src.to_str().unwrap(), "--max-states", "1O0"]);
    assert_ne!(out.status.code(), Some(0), "{}", stdout(&out));
}

#[test]
fn unknown_flags_are_rejected() {
    let src = "examples/gcd_refinement.bil";
    for args in [
        ["verify", src, "--jsno"],
        ["model-check", src, "--bmcc"],
        ["vm", src, "--dump-bytcode"],
    ] {
        let out = bil(&args);
        assert_ne!(out.status.code(), Some(0), "{:?} was accepted", args);
    }
}

#[test]
fn invalid_flag_values_and_missing_values_are_rejected() {
    let src = "examples/gcd_refinement.bil";
    let cases: &[&[&str]] = &[
        &["run", src, "--seed"],
        &["run", src, "--seed", "x"],
        &["vm", src, "--seed", "-1"],
        &["verify", src, "--format", "xml"],
        &["solve", src, "--prover", "z4"],
        &["solve", src, "--subsumes", "OnlyOne"],
        &["dump-ir", src, "--level", "mir"],
        &["build", src, "-o"],
    ];
    for args in cases {
        let out = bil(args);
        assert_eq!(out.status.code(), Some(1), "{:?} was accepted", args);
        let err = String::from_utf8_lossy(&out.stderr);
        assert!(
            err.contains("error:"),
            "{:?} gave no error message: {}",
            args,
            err
        );
    }
}

#[test]
fn valid_flags_are_still_accepted() {
    let dir = scratch_dir("valid-flags");
    let sys = write_source(
        &dir,
        "system Lin { state n: Int = 0  terminal n == 10  transition n < 10 -> n := n + 1 }\n",
    );
    let sys = sys.to_str().unwrap();
    let ex = "examples/gcd_refinement.bil";
    let cases: &[&[&str]] = &[
        &["model-check", sys, "--max-states", "1000", "--seed", "7"],
        &["model-check", sys, "--format", "json"],
        &["model-check", sys, "--format", "text"],
        &["run", ex, "--seed", "7", "--trace"],
        &["vm", ex, "--seed", "7", "--dump-bytecode"],
        &["dump-ir", ex, "--level", "lir"],
        &["check", ex],
    ];
    for args in cases {
        let out = bil(args);
        assert_eq!(
            out.status.code(),
            Some(0),
            "{:?} failed: {}",
            args,
            String::from_utf8_lossy(&out.stderr)
        );
    }
}

#[test]
fn oversized_source_file_is_rejected_before_reading_it_all() {
    let dir = scratch_dir("oversized");
    let path = dir.join("huge.bil");
    // 16 MiB of comment plus one byte: just over the cap.
    let mut src = String::from("// ");
    src.push_str(&"a".repeat(16 * 1024 * 1024 - 2));
    fs::write(&path, src).unwrap();
    let out = bil(&["check", path.to_str().unwrap()]);
    assert_eq!(out.status.code(), Some(1));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("exceeds maximum size"), "{err}");
}

#[test]
fn endless_input_stream_is_rejected_instead_of_exhausting_memory() {
    let out = Command::new(BIL)
        .args(["check", "/dev/zero"])
        .output()
        .expect("spawn bil");
    assert_eq!(out.status.code(), Some(1));
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(err.contains("exceeds maximum size"), "{err}");
}

#[test]
fn source_at_the_size_cap_is_still_accepted() {
    let dir = scratch_dir("at-cap");
    let path = dir.join("big.bil");
    let mut src = String::from("let x = 1\n// ");
    src.push_str(&"a".repeat(16 * 1024 * 1024 - src.len()));
    assert_eq!(src.len(), 16 * 1024 * 1024);
    fs::write(&path, src).unwrap();
    let out = bil(&["check", path.to_str().unwrap()]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "{}",
        String::from_utf8_lossy(&out.stderr)
    );
}
