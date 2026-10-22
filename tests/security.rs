use bil::codegen::emit_native_rust_aot;
use bil::ontology::transpile_ontologic_sexpr;
use bil::smt::{find_solver_binary, run_smt_prover, Prover, Verdict};
use bil::{
    build_native_source, emit_verus_source, lower_ir_source, parse_source, run_source,
    run_vm_source,
};
use std::fs;
use std::process::Command;

#[test]
fn test_sec_1_string_and_identifier_escaping_in_verus_and_aot_codegen() {
    // `unsafe`, `async`, `crate`, `self`, `impl` are valid BIL identifiers that are Rust keywords,
    // and string literals contain quotes, backslashes, and Rust format braces `{}`.
    let src = r#"
fn unsafe(self: Int) -> Int
  requires self >= 0
  ensures result == self + 1
=
  self + 1

fn quote_msg(x: Int) -> String =
  "quote: \" backslash: \\ braces: {not_a_fmt_arg}"

let crate: Int = unsafe(41)
let msg: String = quote_msg(crate)
"#;

    let verus_rs = emit_verus_source(src).expect("emit_verus_source should succeed");
    assert!(
        verus_rs.contains(r#""quote: \" backslash: \\ braces: {not_a_fmt_arg}".to_string()"#),
        "Verus codegen must escape quotes and backslashes in string literals, got:\n{}",
        verus_rs
    );

    let ir = lower_ir_source(src).expect("lower_ir_source should succeed");
    let aot_rs = emit_native_rust_aot(&ir.lir, &ir.hir);
    assert!(
        aot_rs.contains("fn bil_fn_r_unsafe("),
        "AOT codegen must sanitize Rust keyword function names, got:\n{}",
        aot_rs
    );

    let bin_path = std::env::temp_dir().join(format!("bil_sec1_bin_{}", std::process::id()));
    let report = build_native_source(src, &bin_path)
        .expect("rustc must compile AOT output with Rust keyword identifiers and special strings");
    assert!(report.output_path.exists());

    let out = Command::new(&bin_path)
        .output()
        .expect("compiled binary should execute");
    let _ = fs::remove_file(&bin_path);
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("crate = 42"), "stdout was: {}", stdout);
    assert!(
        stdout.contains(r#"msg = "quote: " backslash: \ braces: {not_a_fmt_arg}""#),
        "stdout was: {}",
        stdout
    );
}

#[test]
fn test_sec_2_exclusive_temp_file_creation_in_aot_compilation() {
    let src = "let x: Int = 7 * 6\n";
    let handles: Vec<_> = (0..4)
        .map(|i| {
            let s = src.to_string();
            std::thread::spawn(move || {
                let out_bin = std::env::temp_dir()
                    .join(format!("bil_sec2_bin_{}_{}", std::process::id(), i));
                let res = build_native_source(&s, &out_bin);
                let _ = fs::remove_file(&out_bin);
                res.expect("concurrent AOT build should succeed without temp file race");
            })
        })
        .collect();

    for h in handles {
        h.join().expect("thread should not panic");
    }
}

#[test]
fn test_sec_3_solver_wall_clock_timeout_kills_hung_subprocess() {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;

        let script_path =
            std::env::temp_dir().join(format!("bil_fake_hung_solver_{}.sh", std::process::id()));
        fs::write(&script_path, "#!/bin/sh\nexec sleep 10\n").expect("write fake solver script");
        let mut perms = fs::metadata(&script_path).unwrap().permissions();
        perms.set_mode(0o755);
        fs::set_permissions(&script_path, perms).unwrap();

        // Point BIL_VAMPIRE_PATH at the hanging script and set a short 80ms timeout
        std::env::set_var("BIL_VAMPIRE_PATH", &script_path);
        std::env::set_var("BIL_SOLVER_TIMEOUT_MS", "80");

        let res = run_smt_prover(Prover::Vampire, "(set-logic ALL)\n(check-sat)\n");

        std::env::remove_var("BIL_VAMPIRE_PATH");
        std::env::remove_var("BIL_SOLVER_TIMEOUT_MS");
        let _ = fs::remove_file(&script_path);

        assert_eq!(res.verdict, Verdict::Unknown);
        assert!(
            res.detail.contains("killed after wall-clock timeout"),
            "Expected timeout kill detail, got: {}",
            res.detail
        );
        assert!(
            res.elapsed_ms < 2000,
            "Hung solver should be killed promptly, took {} ms",
            res.elapsed_ms
        );
    }
}

#[test]
fn test_sec_4_bounded_recursion_depth_and_vm_fuel() {
    // 1. Deeply nested BIL expression (> 256 levels) rejected cleanly by parser
    let nested_expr = format!("let x: Int = {}1{}", "(".repeat(300), ")".repeat(300));
    let parse_err = parse_source(&nested_expr).expect_err("deeply nested expr should fail cleanly");
    assert!(
        parse_err.contains("nesting depth exceeded maximum"),
        "Unexpected parse error: {}",
        parse_err
    );

    // 2. Deeply nested S-expression (> 256 levels) rejected cleanly by OntoLogic transpiler
    let nested_sexpr = format!("{}atom{}", "(".repeat(300), ")".repeat(300));
    let sexpr_err = transpile_ontologic_sexpr(&nested_sexpr)
        .expect_err("deeply nested sexpr should fail cleanly");
    assert!(
        sexpr_err.contains("nesting depth exceeded maximum"),
        "Unexpected sexpr error: {}",
        sexpr_err
    );

    // 3. Unbounded recursion in BIL function rejected cleanly in both Interpreter and BytecodeVm
    let rec_src = r#"
fn inf(n: Int) -> Int =
  inf(n + 1)

let boom: Int = inf(0)
"#;
    let eval_err = run_source(rec_src, 0, false).expect_err("infinite recursion must fail in eval");
    assert!(
        eval_err.contains("Call stack depth exceeded maximum"),
        "Unexpected eval error: {}",
        eval_err
    );

    let vm_err = run_vm_source(rec_src, 0).expect_err("infinite recursion must fail in VM");
    assert!(
        vm_err.contains("call stack depth exceeded maximum"),
        "Unexpected VM error: {}",
        vm_err
    );
}

#[test]
fn test_sec_5_solver_binary_env_override_resolution() {
    let dummy_bin =
        std::env::temp_dir().join(format!("bil_dummy_solver_{}", std::process::id()));
    fs::write(&dummy_bin, "").expect("create dummy solver file");

    std::env::set_var("BIL_CUSTOMSOLVER_PATH", &dummy_bin);
    let resolved = find_solver_binary("customsolver");
    std::env::remove_var("BIL_CUSTOMSOLVER_PATH");

    let _ = fs::remove_file(&dummy_bin);
    assert_eq!(resolved.as_deref(), Some(dummy_bin.as_path()));
}

/// Builds `src` natively and runs it with a wall-clock limit, returning (exit code, stderr).
/// A `None` exit code means the binary was killed by a signal (e.g. stack overflow) or hung.
fn run_native_bounded(name: &str, src: &str) -> (Option<i32>, String) {
    use std::time::{Duration, Instant};
    let bin_path = std::env::temp_dir().join(format!("bil_sec_{}_{}", name, std::process::id()));
    build_native_source(src, &bin_path).expect("native AOT build");
    let mut child = Command::new(&bin_path)
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::piped())
        .spawn()
        .expect("run native binary");
    let start = Instant::now();
    let status = loop {
        if let Some(st) = child.try_wait().unwrap() {
            break Some(st);
        }
        if start.elapsed() > Duration::from_secs(20) {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        std::thread::sleep(Duration::from_millis(20));
    };
    let mut err = String::new();
    use std::io::Read as _;
    let _ = child.stderr.take().unwrap().read_to_string(&mut err);
    let _ = fs::remove_file(&bin_path);
    (status.and_then(|s| s.code()), err)
}

#[test]
fn test_sec_6_native_aot_bounds_recursion_like_eval_and_vm() {
    let rec_src = r#"
fn inf(n: Int) -> Int =
  inf(n + 1)

let boom: Int = inf(0)
"#;
    let (code, err) = run_native_bounded("recursion", rec_src);
    assert_eq!(
        code,
        Some(101),
        "expected a clean panic exit, got {code:?}: {err}"
    );
    assert!(
        err.contains("Call stack depth exceeded maximum (64)"),
        "Unexpected native error: {err}"
    );

    // Recursion within the limit still works.
    let ok_src = r#"
fn down(n: Int) -> Int =
  if n <= 0 -> 0 [] n > 0 -> down(n - 1) fi

let fine: Int = down(50)
"#;
    let (code, err) = run_native_bounded("recursion_ok", ok_src);
    assert_eq!(code, Some(0), "{err}");
}

#[test]
fn test_sec_7_native_aot_bounds_do_od_steps_like_eval() {
    let loop_src = r#"
fn spin(n: Int) -> Int =
  do i = n : i >= 0 -> i := i + 1 od then i

let forever: Int = spin(0)
"#;
    let eval_err = run_source(loop_src, 0, false).expect_err("eval must stop the loop");
    assert!(
        eval_err.contains("exceeded maximum step bound (100,000)"),
        "{eval_err}"
    );

    let (code, err) = run_native_bounded("loop", loop_src);
    assert_eq!(
        code,
        Some(101),
        "expected a clean panic exit, got {code:?}: {err}"
    );
    assert!(
        err.contains("exceeded maximum step bound (100,000)"),
        "Unexpected native error: {err}"
    );

    // A loop that runs exactly 100,000 steps is still allowed, as in eval.
    let edge_src = r#"
fn count_to(n: Int) -> Int =
  do i = 0 : i < n -> i := i + 1 od then i

let edge: Int = count_to(100000)
"#;
    assert!(run_source(edge_src, 0, false).is_ok());
    let (code, err) = run_native_bounded("loop_edge", edge_src);
    assert_eq!(code, Some(0), "{err}");
}
