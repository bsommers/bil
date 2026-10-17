//! P2.7: Differential Multi-Backend Equivalence Test Suite.
//! Verifies that Tree-Walk Evaluator (`eval`), Bytecode VM (`vm`), and Standalone Native AOT (`codegen`)
//! produce bit-identical outputs across all example programs and edge-case expression suites.

use bil::{build_native_source, run_source, run_vm_source};
use std::fs;
use std::process::Command;

fn assert_three_way_equivalence(name: &str, src: &str, seed: u64) {
    // 1. Tree-walk interpreter
    let (eval_out, _) =
        run_source(src, seed, false).unwrap_or_else(|e| panic!("[{}] eval failed: {}", name, e));
    let eval_formatted: String = eval_out
        .iter()
        .map(|(k, v)| format!("{} = {}\n", k, v))
        .collect();

    // 2. Ghost-erased LIR Bytecode VM
    let (vm_out, _) =
        run_vm_source(src, seed).unwrap_or_else(|e| panic!("[{}] vm failed: {}", name, e));
    let vm_formatted: String = vm_out
        .iter()
        .map(|(k, v)| format!("{} = {}\n", k, v))
        .collect();

    assert_eq!(
        eval_out, vm_out,
        "[{}] Tree-walk Eval and Bytecode VM Value outputs diverged",
        name
    );

    // 3. Standalone Native ELF Binary (compiled via LIR -> Rust -> rustc)
    let bin_path = std::env::temp_dir().join(format!(
        "bil_diff_test_{}_{}",
        name,
        std::process::id()
    ));
    let _rep = build_native_source(src, &bin_path)
        .unwrap_or_else(|e| panic!("[{}] native AOT build failed: {}", name, e));
    let output = Command::new(&bin_path)
        .output()
        .unwrap_or_else(|e| panic!("[{}] failed to execute native binary: {}", name, e));
    let _ = fs::remove_file(&bin_path);

    assert!(
        output.status.success(),
        "[{}] native binary exited with non-zero status: {}",
        name,
        String::from_utf8_lossy(&output.stderr)
    );
    let aot_stdout = String::from_utf8_lossy(&output.stdout).to_string();

    assert_eq!(
        eval_formatted, vm_formatted,
        "[{}] Formatted Eval and VM outputs diverged",
        name
    );
    assert_eq!(
        eval_formatted, aot_stdout,
        "[{}] Native AOT stdout diverged from Eval/VM",
        name
    );
}

#[test]
fn test_differential_equivalence_across_all_examples() {
    let examples = [
        ("gcd_refinement", "examples/gcd_refinement.bil"),
        ("mutex_protocol", "examples/mutex_protocol.bil"),
        ("arbiter_controller", "examples/arbiter_controller.bil"),
        ("smart_grid", "examples/smart_grid.bil"),
        ("security_policy", "examples/security_policy.bil"),
    ];

    for (name, path) in examples {
        let src = fs::read_to_string(path).expect("read example file");
        assert_three_way_equivalence(name, &src, 42);
    }
}

#[test]
fn test_differential_equivalence_edge_case_expressions() {
    let src = r#"
        concept Boxed {
            val: Int
            tag: String
        }

        type Outcome = Ok(Int) | Fallback(String, Int) | Empty

        fn compute_edge_cases(x: Int, y: Int) -> Int
            requires y != 0
            ensures true
        =
            let q = x / y in
            let r = x % y in
            if q * y + r == x -> q * 100 + r
            [] q * y + r != x -> 0
            fi

        fn loop_collatz_steps(n: Int) -> Int
            requires n >= 1
            ensures result >= 0
        =
            do cur = n, steps = 0
                invariant cur >= 1 && steps >= 0
                variant cur
            :
                cur > 1 && cur % 2 == 0 -> cur := cur / 2, steps := steps + 1
            [] cur > 1 && cur % 2 != 0 -> cur := cur - 1, steps := steps + 1
            od
            then steps

        let neg_div_1 = compute_edge_cases(-7, 3)
        let neg_div_2 = compute_edge_cases(-7, -3)
        let neg_div_3 = compute_edge_cases(7, -3)
        let collatz_12 = loop_collatz_steps(12)

        let b1 = Boxed { val: 10, tag: "alpha" }
        let b2 = b1 with { val: 25, tag: "beta" }
        let out_adt = match Fallback("warn", b2.val) {
            | Ok(v) -> v
            | Fallback(_, v) -> v + b1.val
            | Empty -> 0
        }

        let pipeline_res = [1, 2, 3, 4, 5, 6]
            |> where(_ % 2 != 0)
            |> map(_ * _)
            |> sum()
    "#;

    assert_three_way_equivalence("edge_cases", src, 42);
}
