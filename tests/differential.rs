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

#[test]
fn test_v050_p0_1_directional_subtyping_and_join_types() {
    // 1. Sibling concepts sharing a common ancestor (Continuant) must NOT be assignable to each other
    let sibling_assign = r#"
        concept Continuant {}
        concept Pipeline <: Continuant { pressure: Int }
        concept Valve <: Continuant { open: Bool }
        let v: Pipeline = Valve { open: true }
    "#;
    let err = bil::check_source(sibling_assign).unwrap_err();
    assert!(
        err.contains("not a subconcept"),
        "expected directional subtyping error for sibling concepts, got: {:?}",
        err
    );

    // 2. Superconcept must NOT be assignable to subconcept
    let down_assign = r#"
        concept Continuant {}
        concept Asset <: Continuant { id: Int }
        concept Pump <: Asset { rpm: Int }
        let a: Asset = Asset { id: 1 }
        let p: Pump = a
    "#;
    let err2 = bil::check_source(down_assign).unwrap_err();
    assert!(
        err2.contains("not a subconcept"),
        "expected directional subtyping error for downcast, got: {:?}",
        err2
    );

    // 3. Upcast (subconcept -> superconcept) and heterogeneous list join (`[Pipeline, Valve]`) MUST succeed
    let valid_upcast_and_join = r#"
        concept Continuant {}
        concept Pipeline <: Continuant { pressure: Int }
        concept Valve <: Continuant { open: Bool }
        let p = Pipeline { pressure: 80 }
        let v = Valve { open: true }
        let c: Continuant = p
        let items: List<Continuant> = [p, v]
        let n = count(items)
    "#;
    bil::check_source(valid_upcast_and_join).expect("upcast and list join should typecheck");
}

#[test]
fn test_v050_p0_2_numeric_and_comparable_operator_constraints() {
    let invalid_cases = [
        ("let x = true + false", "Operator '+'"),
        ("let x = \"a\" - \"b\"", "Arithmetic operator '-'"),
        ("let x = true * false", "Arithmetic operator '*'"),
        ("let x = true < false", "Comparison operator '<'"),
        ("let x = 3.5 % 1.5", "Type mismatch"),
    ];
    for (src, expected_msg) in invalid_cases {
        let err = bil::check_source(src).unwrap_err();
        assert!(
            err.contains(expected_msg),
            "for `{}` expected error containing `{}`, got: {:?}",
            src,
            expected_msg,
            err
        );
    }
}

#[test]
fn test_v050_p0_3_and_p1_3_top_level_assert_and_concept_store_three_way_parity() {
    // 1. Concept domain quantifier (`forall b in Boxed`) and `is_a` across Eval, VM, and Native AOT
    let valid_concept_domain_src = r#"
        concept Continuant {}
        concept Boxed <: Continuant {
            val: Int
        }
        concept SubBoxed <: Boxed {
            extra: Int
        }

        let b1 = Boxed { val: 10 }
        let b2 = SubBoxed { val: 20, extra: 5 }
        let all_positive = forall b in Boxed : b.val > 0 && is_a(b, "Continuant")
        let instance_cnt = count(Boxed)
        assert all_positive
        assert instance_cnt == 2
    "#;
    assert_three_way_equivalence("concept_domain_and_asserts", valid_concept_domain_src, 42);

    // 2. Failing top-level assertion MUST fail in Eval, VM, AND Native AOT
    let failing_assert_src = r#"
        let x = 10
        assert x > 100
    "#;
    assert!(
        run_source(failing_assert_src, 42, false).is_err(),
        "eval must reject failing top-level assert"
    );
    assert!(
        run_vm_source(failing_assert_src, 42).is_err(),
        "vm must reject failing top-level assert"
    );
    let bin_path = std::env::temp_dir().join(format!(
        "bil_diff_fail_assert_{}",
        std::process::id()
    ));
    build_native_source(failing_assert_src, &bin_path).expect("build failing_assert_src");
    let out = Command::new(&bin_path)
        .output()
        .expect("run failing_assert binary");
    let _ = fs::remove_file(&bin_path);
    assert!(
        !out.status.success(),
        "native AOT binary must fail when top-level assert evaluates to false"
    );
}

#[test]
fn test_v050_p1_1_p1_2_p2_1_expr_utils_incremental_vc_and_cli_bmc() {
    // 1. P1.1: Verify expr_utils works directly without wp coupling
    let parsed = bil::parse_source("let z = x + y + 10").unwrap();
    if let bil::ast::Item::Let(l) = &parsed.items[0] {
        let fvs = bil::expr_utils::free_vars(&l.value);
        assert!(fvs.contains("x") && fvs.contains("y"));
        let mut ints = std::collections::BTreeSet::new();
        bil::expr_utils::extract_int_constants(&l.value, &mut ints);
        assert!(ints.contains(&10));
    }

    // 2. P1.2: Verify multi-obligation GCL functions (if..fi & do..od) discharge via incremental SMT batching
    let gcl_src = r#"
        fn abs_val(x: Int) -> Int
            ensures result >= 0
        = if
            x >= 0 -> x
            [] x < 0 -> -x
          fi

        fn count_down(n: Int) -> Int
            requires n >= 0
            ensures result == 0
        = do r = n
            invariant r >= 0
            variant r
            r > 0 -> r := r - 1
          od then r
    "#;
    let obs = bil::verify_source(gcl_src).expect("verify gcl_src");
    assert_eq!(obs.len(), 3 + 5);
    assert!(obs.iter().all(|o| o.verified));

    // 3. P2.1: Verify CLI `bil model-check <file.bil> --bmc 3` and `--bmc=3 --json`
    let exit_code = bil::cli::run_cli(&[
        "bil".into(),
        "model-check".into(),
        "examples/mutex_protocol.bil".into(),
        "--bmc".into(),
        "3".into(),
    ]);
    assert_eq!(exit_code, 0);

    let exit_code_json = bil::cli::run_cli(&[
        "bil".into(),
        "model-check".into(),
        "examples/mutex_protocol.bil".into(),
        "--bmc=3".into(),
        "--json".into(),
    ]);
    assert_eq!(exit_code_json, 0);
}


#[test]
fn test_differential_floats_logic_ranges_strings_and_pipelines() {
    // Beyond Int/Bool arithmetic: Float ops and comparisons, => / <=>, `in` over ranges and
    // lists, exclusive/inclusive/empty ranges, string +, and every pipeline built-in.
    let src = r#"
        concept Item {
            id: String
            w: Int
            on: Bool
        }

        let f_add = 1.5 + 2.25
        let f_mul = 1.5 * -2.0
        let f_div = 7.0 / 2.0
        let f_sub = 0.1 - 0.3
        let f_whole = 1.5 * -2.0
        let f_list = [1.0, 2.5, 0.0]
        let f_lt = 1.5 < 2.5
        let f_eq = 0.5 == 0.5
        let imp_ff = false => false
        let imp_tf = true => false
        let iff_tt = true <=> true
        let iff_tf = true <=> false
        let in_range = 3 in 1..5
        let in_excl = 5 in 1..5
        let in_incl = 5 in 1..=5
        let in_list = 4 in [1, 2, 3]
        let r_excl = 2..6
        let r_incl = 2..=6
        let r_empty = 5..2
        let s_cat = "ab" + "cd"
        let s_eq = "x" + "y" == "xy"
        let p_sum = 1..=10 |> where(_ % 2 == 0) |> map(_ * 3) |> sum()
        let p_count = [5, 1, 4] |> count()
        let p_all = [2, 4, 6] |> all(_ % 2 == 0)
        let p_any = [1, 3, 5] |> any(_ > 4)
        let p_sorted = [Item { id: "b", w: 3, on: true }, Item { id: "a", w: 1, on: false }, Item { id: "c", w: 2, on: true }] |> sort_by(_.w) |> map(_.id)
        let p_where = [Item { id: "b", w: 3, on: true }, Item { id: "a", w: 1, on: false }] |> where(_.on) |> map(_.w) |> sum()
    "#;
    assert_three_way_equivalence("floats_logic_ranges_pipelines", src, 7);

    // Spot-check values so the three backends cannot agree on a wrong answer.
    let (out, _) = run_source(src, 7, false).expect("eval");
    let get = |k: &str| {
        out.iter()
            .find(|(name, _)| name == k)
            .map(|(_, v)| v.to_string())
            .unwrap_or_else(|| panic!("missing {k}"))
    };
    assert_eq!(get("f_add"), "3.75");
    // A whole-valued Float keeps its decimal point so it is not mistaken for an Int.
    assert_eq!(get("f_whole"), "-3.0");
    assert_eq!(get("f_list"), "[1.0, 2.5, 0.0]");
    assert_eq!(get("imp_ff"), "true");
    assert_eq!(get("imp_tf"), "false");
    assert_eq!(get("in_excl"), "false");
    assert_eq!(get("in_incl"), "true");
    assert_eq!(get("r_empty"), "[]");
    assert_eq!(get("s_cat"), "\"abcd\"");
    assert_eq!(get("p_sum"), "90");
    assert_eq!(get("p_sorted"), "[\"a\", \"c\", \"b\"]");
    assert_eq!(get("p_where"), "3");
}

#[test]
fn test_differential_range_cap_is_an_error_in_every_backend() {
    let src = "let big = 0..200001\nlet n = big |> count()\n";
    let cap = "exceeds maximum materialized length (100000)";

    let eval_err = run_source(src, 0, false).expect_err("eval must reject the range");
    assert!(eval_err.to_string().contains(cap), "{eval_err}");
    let vm_err = run_vm_source(src, 0).expect_err("vm must reject the range");
    assert!(vm_err.to_string().contains(cap), "{vm_err}");

    let bin_path =
        std::env::temp_dir().join(format!("bil_diff_test_range_cap_{}", std::process::id()));
    build_native_source(src, &bin_path).expect("native AOT build");
    let output = Command::new(&bin_path).output().expect("run native binary");
    let _ = fs::remove_file(&bin_path);
    assert!(!output.status.success(), "native binary must fail");
    assert!(
        String::from_utf8_lossy(&output.stderr).contains(cap),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}
