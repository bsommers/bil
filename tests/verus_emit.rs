//! `bil emit-verus` output must compile and verify under Verus
//! (see docs/superpowers/specs/2026-10-25-system-to-verus-refinement-design.md).
//! Skips when no Verus binary is found: `$VERUS`, then `verus` on `PATH`.

use std::path::{Path, PathBuf};
use std::process::Command;

const BIL: &str = env!("CARGO_BIN_EXE_bil");

/// Domain examples whose emission is known not to verify yet, each with the reason.
/// This list only shrinks.
const ALLOWLIST: &[(&str, &str)] = &[];

fn verus_bin() -> Option<PathBuf> {
    let candidate = std::env::var_os("VERUS")
        .map(PathBuf::from)
        .unwrap_or_else(|| PathBuf::from("verus"));
    let ok = Command::new(&candidate)
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false);
    ok.then_some(candidate)
}

/// Emits `bil_file` and runs Verus on it. `Ok(n)` is the verified count with 0 errors.
fn emit_and_verify(verus: &Path, bil_file: &Path) -> Result<u32, String> {
    let emitted = Command::new(BIL)
        .arg("emit-verus")
        .arg(bil_file)
        .output()
        .expect("spawn bil");
    if !emitted.status.success() {
        return Err(format!(
            "emit-verus failed: {}",
            String::from_utf8_lossy(&emitted.stderr)
        ));
    }
    let dir = std::env::temp_dir().join("bil_verus_emit");
    std::fs::create_dir_all(&dir).unwrap();
    let stem = bil_file.file_stem().unwrap().to_string_lossy();
    let rs = dir.join(format!("{stem}.rs"));
    std::fs::write(&rs, &emitted.stdout).unwrap();

    let out = Command::new(verus)
        .arg(&rs)
        .arg("--crate-type=lib")
        .output()
        .expect("spawn verus");
    let text = format!(
        "{}{}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    let summary = text
        .lines()
        .find_map(|l| l.strip_prefix("verification results:: "));
    match summary {
        Some(s) if s.ends_with("0 errors") => {
            Ok(s.split_whitespace().next().unwrap().parse().unwrap())
        }
        _ => Err(text.lines().take(12).collect::<Vec<_>>().join("\n")),
    }
}

fn domain_examples() -> Vec<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/domains");
    let mut v: Vec<PathBuf> = std::fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|x| x == "bil"))
        .collect();
    v.sort();
    v
}

#[test]
fn domain_examples_emit_verifying_verus() {
    let Some(verus) = verus_bin() else {
        eprintln!("verus: skipped (no Verus binary; set $VERUS)");
        return;
    };
    let mut failures = Vec::new();
    for path in domain_examples() {
        let name = path.file_stem().unwrap().to_string_lossy().to_string();
        if ALLOWLIST.iter().any(|(n, _)| *n == name) {
            continue;
        }
        if let Err(why) = emit_and_verify(&verus, &path) {
            failures.push(format!("--- {name}\n{why}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} example(s) do not verify:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[test]
fn allowlist_entries_name_a_reason_and_a_real_example() {
    let names: Vec<String> = domain_examples()
        .iter()
        .map(|p| p.file_stem().unwrap().to_string_lossy().to_string())
        .collect();
    for (n, reason) in ALLOWLIST {
        assert!(names.contains(&n.to_string()), "unknown example {n}");
        assert!(!reason.is_empty(), "{n} needs a reason");
    }
}
