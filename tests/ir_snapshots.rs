//! Golden-file snapshots of `bil dump-ir --level all` and `bil vm --dump-bytecode`.
//!
//! These cover the HIR/VIR/LIR and bytecode `Display` impls, and catch unintended changes to
//! lowering. After an intended change, regenerate with:
//!   BIL_UPDATE_SNAPSHOTS=1 cargo test --test ir_snapshots
//! and review the diff in tests/snapshots/.

use std::path::PathBuf;
use std::process::Command;

const BIL: &str = env!("CARGO_BIN_EXE_bil");

fn check_snapshot(name: &str, args: &[&str]) {
    let out = Command::new(BIL).args(args).output().expect("run bil");
    assert!(
        out.status.success(),
        "bil {:?} failed: {}",
        args,
        String::from_utf8_lossy(&out.stderr)
    );
    let actual = String::from_utf8(out.stdout).expect("utf-8 output");
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/snapshots")
        .join(format!("{name}.txt"));
    if std::env::var_os("BIL_UPDATE_SNAPSHOTS").is_some() {
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, &actual).unwrap();
        return;
    }
    let expected = std::fs::read_to_string(&path).unwrap_or_else(|e| {
        panic!(
            "missing snapshot {}: {e}; run BIL_UPDATE_SNAPSHOTS=1 cargo test --test ir_snapshots",
            path.display()
        )
    });
    if actual != expected {
        let first_diff = actual
            .lines()
            .zip(expected.lines())
            .position(|(a, e)| a != e)
            .unwrap_or_else(|| actual.lines().count().min(expected.lines().count()));
        panic!(
            "snapshot {} differs at line {}:\n  expected: {:?}\n  actual:   {:?}\n\
             If the change is intended, run BIL_UPDATE_SNAPSHOTS=1 cargo test --test ir_snapshots",
            path.display(),
            first_diff + 1,
            expected.lines().nth(first_diff),
            actual.lines().nth(first_diff),
        );
    }
}

#[test]
fn dump_ir_gcd_refinement() {
    check_snapshot(
        "dump_ir_gcd_refinement",
        &["dump-ir", "examples/gcd_refinement.bil", "--level", "all"],
    );
}

#[test]
fn dump_ir_smart_grid() {
    check_snapshot(
        "dump_ir_smart_grid",
        &["dump-ir", "examples/smart_grid.bil", "--level", "all"],
    );
}

#[test]
fn dump_bytecode_gcd_refinement() {
    check_snapshot(
        "bytecode_gcd_refinement",
        &["vm", "examples/gcd_refinement.bil", "--dump-bytecode"],
    );
}

#[test]
fn dump_bytecode_smart_grid() {
    check_snapshot(
        "bytecode_smart_grid",
        &["vm", "examples/smart_grid.bil", "--dump-bytecode"],
    );
}
