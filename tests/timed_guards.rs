//! `clock` / `deadline` members of a `system`: syntax, lowering and the boundary semantics
//! of `within` (see docs/superpowers/specs/2026-10-24-timed-guards-design.md).

use std::process::{Command, Output};

const BIL: &str = env!("CARGO_BIN_EXE_bil");

fn text(out: &Output) -> String {
    format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    )
}

/// Writes `src` to a per-test temp file and runs `bil <cmd> <file> [extra..]`.
fn run(cmd: &str, name: &str, src: &str) -> (Option<i32>, String) {
    run_with(cmd, &[], name, src)
}

fn run_with(cmd: &str, extra: &[&str], name: &str, src: &str) -> (Option<i32>, String) {
    let dir = std::env::temp_dir().join("bil_timed_guards");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}.bil"));
    std::fs::write(&path, src).unwrap();
    let out = Command::new(BIL)
        .arg(cmd)
        .arg(path.to_str().unwrap())
        .args(extra)
        .output()
        .expect("spawn bil");
    (out.status.code(), text(&out))
}

/// A controller that, after `detected` is raised, takes `delay` scans to turn the heater off.
fn system(clock_deadline: &str, delay: i64) -> String {
    format!(
        "system Epi {{
  state detected: Bool = false
  state heater_off: Bool = false
  state wait: Int = 0
  {clock_deadline}
  terminal heater_off
  transition
     !detected                       -> detected := true
  [] detected && wait < {delay}      -> wait := wait + 1
  [] detected && wait >= {delay}     -> heater_off := true
}}
"
    )
}

const OK: &str = "clock scan period 1ms\n  deadline Cut: detected => heater_off within 3ms";

#[test]
fn parses_clock_and_deadline() {
    let (code, t) = run("check", "parses", &system(OK, 1));
    assert_eq!(code, Some(0), "{t}");
}

#[test]
fn rejects_unknown_unit() {
    let src = system("clock scan period 1ms\n  deadline Cut: detected => heater_off within 3mss", 1);
    let (code, t) = run("check", "bad_unit", &src);
    assert_ne!(code, Some(0), "{t}");
    assert!(t.contains("unit"), "{t}");
}

#[test]
fn rejects_zero_duration() {
    let src = system("clock scan period 0ms\n  deadline Cut: detected => heater_off within 3ms", 1);
    let (code, t) = run("check", "zero", &src);
    assert_ne!(code, Some(0), "{t}");
    assert!(t.contains("positive"), "{t}");
}

// `system(.., delay)` reacts after `delay` waiting scans plus one cut-off scan, so the
// response holds after `delay + 1` scans counted from the one that observes the latch.

fn deadline(period: &str, within: &str) -> String {
    format!("clock scan period {period}\n  deadline Cut: detected => heater_off within {within}")
}

#[test]
fn deadline_met_exactly_at_bound_passes() {
    let (code, t) = run("model-check", "met", &system(&deadline("1ms", "3ms"), 2));
    assert_eq!(code, Some(0), "{t}");
}

#[test]
fn deadline_missed_by_one_scan_fails() {
    let (code, t) = run("model-check", "missed", &system(&deadline("1ms", "3ms"), 3));
    assert_eq!(code, Some(1), "{t}");
    assert!(t.contains("Deadline_Cut"), "{t}");
}

#[test]
fn non_multiple_rounds_up() {
    // 5 ms on a 2 ms scan is 3 scans, not 2 and not 2.5.
    let d = deadline("2ms", "5ms");
    let (code, t) = run("model-check", "round_ok", &system(&d, 2));
    assert_eq!(code, Some(0), "{t}");
    let (code, t) = run("model-check", "round_late", &system(&d, 3));
    assert_eq!(code, Some(1), "{t}");
    assert!(t.contains("Deadline_Cut"), "{t}");
}

#[test]
fn symbolic_bmc_agrees() {
    let ok = system(&deadline("1ms", "3ms"), 2);
    let (code, t) = run_with("model-check", &["--bmc", "8"], "bmc_ok", &ok);
    assert_eq!(code, Some(0), "{t}");
    // BMC skips a system it cannot encode and prints nothing, so insist on a verdict.
    assert!(t.contains("BMC PROVED SAFE"), "{t}");
    let late = system(&deadline("1ms", "3ms"), 3);
    let (code, t) = run_with("model-check", &["--bmc", "8"], "bmc_late", &late);
    assert_eq!(code, Some(1), "{t}");
    assert!(t.contains("BMC VIOLATION"), "{t}");
}

#[test]
fn latch_cleared_before_response_fails() {
    let src = format!(
        "system Epi {{
  state detected: Bool = false
  state heater_off: Bool = false
  {}
  transition
     !detected && !heater_off -> detected := true
  [] detected                 -> detected := false
}}
",
        deadline("1ms", "3ms")
    );
    let (code, t) = run("model-check", "latch_cleared", &src);
    assert_eq!(code, Some(1), "{t}");
    assert!(t.contains("Latch_Cut"), "{t}");
}

/// Latch set in phase 0 (tight bound `a`), the controller moves to phase 1 (loose bound
/// 20 ms) and then cuts off on the third scan after the latch was seen.
fn phase_change(a: &str) -> String {
    format!(
        "system Epi {{
  state detected: Bool = false
  state heater_off: Bool = false
  state phase: Int = 0
  state wait: Int = 0
  clock scan period 1ms
  deadline Tight: detected => heater_off within {a} in phase == 0
  deadline Loose: detected => heater_off within 20ms in phase == 1
  terminal heater_off
  transition
     !detected                          -> detected := true
  [] detected && phase == 0             -> phase := 1
  [] detected && phase == 1 && wait < 1 -> wait := wait + 1
  [] detected && phase == 1 && wait >= 1 -> heater_off := true
}}
"
    )
}

#[test]
fn phase_change_keeps_original_bound() {
    let (code, t) = run("model-check", "phase_late", &phase_change("2ms"));
    assert_eq!(code, Some(1), "{t}");
    assert!(t.contains("Deadline_Tight"), "{t}");
}

#[test]
fn phase_change_within_original_bound_passes() {
    let (code, t) = run("model-check", "phase_ok", &phase_change("3ms"));
    assert_eq!(code, Some(0), "{t}");
}

#[test]
fn deadline_shorter_than_period_rejected() {
    let (code, t) = run("check", "short", &system(&deadline("2ms", "1ms"), 1));
    assert_ne!(code, Some(0), "{t}");
    assert!(t.contains("shorter"), "{t}");
}

#[test]
fn deadline_without_clock_rejected() {
    let src = system("deadline Cut: detected => heater_off within 3ms", 1);
    let (code, t) = run("check", "no_clock", &src);
    assert_ne!(code, Some(0), "{t}");
    assert!(t.contains("clock"), "{t}");
}

#[test]
fn systems_without_a_clock_are_unchanged() {
    let (code, t) = run("model-check", "plain", &system("", 3));
    assert_eq!(code, Some(0), "{t}");
}
