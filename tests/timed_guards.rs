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

/// Writes `src` to a per-test temp file and runs `bil <cmd> <file>`.
fn run(cmd: &str, name: &str, src: &str) -> (Option<i32>, String) {
    let dir = std::env::temp_dir().join("bil_timed_guards");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(format!("{name}.bil"));
    std::fs::write(&path, src).unwrap();
    let out = Command::new(BIL)
        .args([cmd, path.to_str().unwrap()])
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
