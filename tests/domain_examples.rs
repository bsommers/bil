//! The domain models in `examples/domains/` stay green end to end, and every seeded bug in
//! `examples/domains/seeded_bugs/` is still caught with the counterexample the white paper cites.

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const BIL: &str = env!("CARGO_BIN_EXE_bil");

fn bil(args: &[&str]) -> Output {
    Command::new(BIL).args(args).output().expect("spawn bil")
}

fn text(out: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

fn bil_files(dir: &str) -> Vec<PathBuf> {
    let mut files: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "bil"))
        .collect();
    files.sort();
    files
}

fn z3_available() -> bool {
    if bil::smt::find_solver_binary("z3").is_none() {
        eprintln!("skipping: z3 not installed");
        return false;
    }
    true
}

#[test]
fn every_domain_model_verifies_model_checks_and_runs() {
    if !z3_available() {
        return;
    }
    let files = bil_files("examples/domains");
    assert!(files.len() >= 14, "expected the domain models, found {files:?}");
    // Each model runs in its own thread: the solver calls dominate and are independent.
    std::thread::scope(|scope| {
        for path in &files {
            scope.spawn(move || check_domain_model(path.to_str().unwrap()));
        }
    });
}

fn check_domain_model(p: &str) {
    // `verify` exits 1 on any refuted or only-bounded obligation, so 0 means every
    // obligation was proved.
    for cmd in ["check", "verify", "model-check", "run", "vm"] {
        let out = bil(&[cmd, p]);
        let t = text(&out);
        assert_eq!(out.status.code(), Some(0), "bil {cmd} {p} failed:\n{t}");
        if cmd == "verify" {
            assert!(
                !t.contains("BOUNDED") && !t.contains("REFUTED"),
                "{p}: every obligation should be proved by SMT:\n{t}"
            );
        }
    }
}

/// (file, command, expected exit code, text the output must contain)
const SEEDED: &[(&str, &str, i32, &str)] = &[
    (
        "bms_fault_always_opens.bil",
        "model-check",
        1,
        "Safety Invariant 'FaultOpensPack' violated",
    ),
    (
        "cyber_noncompliant_grant.bil",
        "run",
        1,
        "OntoLogic Axiom 'SeparationOfDuties' violated",
    ),
    (
        "infusion_alarm_always_cleared.bil",
        "model-check",
        1,
        "LTL FAILED] temporal `AlarmsAreAcknowledged`",
    ),
    (
        "mqtt_unordered_transport.bil",
        "model-check",
        1,
        "Safety Invariant 'ExactlyOnceSafety' violated at state { delivered=2",
    ),
    (
        "reactor_slow_sis.bil",
        "model-check",
        1,
        "Safety Invariant 'BelowDesignTemperature' violated",
    ),
    (
        "reactor_trip_shared_input.bil",
        "verify",
        1,
        "[REFUTED] fn `high_temp_trip`",
    ),
    (
        "robotics_stop_always_clears.bil",
        "model-check",
        1,
        "LTL FAILED] temporal `StopIsNotPermanent`",
    ),
    (
        "spe_late_cutoff.bil",
        "model-check",
        1,
        "Safety Invariant 'Deadline_CutOnDetect' violated",
    ),
    (
        "spe_overtemp_only_in_soak.bil",
        "model-check",
        1,
        "Safety Invariant 'OverTempIsTransient' violated",
    ),
    (
        "spe_slow_thermal_loop.bil",
        "model-check",
        1,
        "Safety Invariant 'NeverMeltAmorphousSi' violated",
    ),
    (
        "tls_early_finished.bil",
        "model-check",
        1,
        "Safety Invariant 'NoDataToUnverifiedPeer' violated",
    ),
];

#[test]
fn every_seeded_bug_is_caught() {
    if !z3_available() {
        return;
    }
    let dir = Path::new("examples/domains/seeded_bugs");
    let listed: Vec<PathBuf> = SEEDED.iter().map(|(f, ..)| dir.join(f)).collect();
    assert_eq!(
        bil_files(dir.to_str().unwrap()),
        listed,
        "every seeded bug needs an expectation here"
    );
    for (file, cmd, code, needle) in SEEDED {
        let p = dir.join(file);
        let out = bil(&[cmd, p.to_str().unwrap()]);
        let t = text(&out);
        assert_eq!(out.status.code(), Some(*code), "bil {cmd} {file}:\n{t}");
        assert!(t.contains(needle), "bil {cmd} {file}: missing {needle:?}:\n{t}");
    }
}
