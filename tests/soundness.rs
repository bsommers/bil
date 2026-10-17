use bil::{ model_check_source, smt::Verdict, verify_source };

#[test]
fn test_p0_1_false_lemma_not_proved_and_not_assumed() {
    let src = r#"
        proof bogus()
          requires true
          ensures  false
        {
          true
        }

        fn bad(x: Int) -> Int
          requires x > 0
          ensures  result < 0
        =
          x
    "#;
    let obligations = verify_source(src).expect("should typecheck");
    let bogus_ob = obligations
        .iter()
        .find(|o| o.fn_name == "bogus")
        .expect("bogus lemma obligation");
    assert!(
        !bogus_ob.verified,
        "false lemma `bogus` must not verify, got: {:?}",
        bogus_ob
    );
    assert_ne!(
        bogus_ob.smt_verdict,
        Some(Verdict::Inconsistent),
        "false lemma `bogus` must not be SMT-proved via self-assumption"
    );

    let bad_ob = obligations
        .iter()
        .find(|o| o.fn_name == "bad")
        .expect("bad fn obligation");
    assert!(
        !bad_ob.verified,
        "bad(x) must not be proved via unverified bogus lemma, got: {:?}",
        bad_ob
    );

    // Vacuity check: inconsistent domain axioms must not allow proving a false function contract
    let vacuous_src = r#"
        concept Tank { level: Int, cap: Int }
        axiom A1: forall t in Tank : t.level > t.cap
        axiom A2: forall t in Tank : t.cap >= t.level

        fn impossible(t: Tank) -> Int
          requires t.level >= 0
          ensures  result < 0
        =
          t.level
    "#;
    let vac_obs = verify_source(vacuous_src).expect("should typecheck");
    let imp_ob = vac_obs
        .iter()
        .find(|o| o.fn_name == "impossible")
        .expect("impossible fn obligation");
    assert!(
        !imp_ob.verified,
        "inconsistent axioms must not vacuously prove false postcondition"
    );
}

#[test]
fn test_p0_2_concrete_counterexample_beats_smt_and_honest_status() {
    use bil::smt::{ProverResult, Verdict};
    use bil::wp::{decide_status, Status};

    // 1. Concrete counterexample from bounded search ALWAYS wins over any SMT verdict
    let fake_unsat = ProverResult {
        prover: "z3".into(),
        verdict: Verdict::Inconsistent,
        stdout: "unsat".into(),
        stderr: String::new(),
        elapsed_ms: 1,
        detail: "unsat".into(),
    };
    let st = decide_status(Some("{ x = 1 }".into()), 8, Some(&fake_unsat));
    assert_eq!(
        st,
        Status::Refuted {
            counterexample: "{ x = 1 }".into()
        }
    );

    // 2. Function contract that passes the 8-sample bounded check (x == 7 is not in sample set)
    //    but is refuted by SMT (sat on negation) MUST be Refuted (verified == false)
    let missed_by_bounded_src = r#"
        fn sneaky(x: Int) -> Int
          requires x == 7
          ensures  result == 0
        =
          x
    "#;
    let obs = verify_source(missed_by_bounded_src).expect("typecheck sneaky");
    let ob = obs.iter().find(|o| o.fn_name == "sneaky").unwrap();
    if ob.smt_verdict == Some(Verdict::Consistent) {
        assert!(
            !ob.verified,
            "FunctionContract refuted by SMT (x == 7) must not be marked verified: {:?}",
            ob
        );
        assert!(matches!(ob.status, Status::Refuted { .. }));
        assert!(ob.counterexample.is_some());
    }

    // 3. Obligation that cannot be lowered to SMT (uses ADT with payload) is BoundedOnly, not Proved
    let grid_src = std::fs::read_to_string("examples/smart_grid.bil").unwrap();
    let grid_obs = verify_source(&grid_src).expect("verify smart_grid");
    let classify_br = grid_obs
        .iter()
        .find(|o| o.fn_name == "classify_pipeline" && o.smt2_script.is_none())
        .expect("classify_pipeline obligation with non-SMT ADT payload");
    assert!(matches!(classify_br.status, Status::BoundedOnly { .. }));
}

#[test]
fn test_p0_6_ir_lowering_and_vm_do_not_invoke_smt_solver() {
    let grid_src = std::fs::read_to_string("examples/smart_grid.bil").unwrap();
    let ir = bil::lower_ir_source(&grid_src).expect("lower IR without invoking SMT solver");
    assert_eq!(ir.vir.proof_obligations.len(), 12);
    for ob in &ir.vir.proof_obligations {
        assert!(
            ob.smt_prover.is_none() && ob.smt_verdict.is_none(),
            "VIR lowering must not spawn external SMT solvers during IR lowering/VM/build, got: {:?}",
            ob
        );
    }
}

#[test]
fn test_p0_3_euclidean_div_mod_and_checked_overflow_parity() {
    let src = r#"
        proof euclid_mod()
          requires true
          ensures  (-7) % 2 == 1 && (-7) / 2 == -4
        {
          true
        }

        fn neg_mod(x: Int) -> Int
          requires x == -7
          ensures  result == 1
        =
          x % 2

        fn neg_div(x: Int) -> Int
          requires x == -7
          ensures  result == -4
        =
          x / 2

        let r_mod = neg_mod(-7)
        let r_div = neg_div(-7)
        assert r_mod == 1
        assert r_div == -4
    "#;

    // 1. Formal verification (bounded + SMT) agrees on Euclidean div/mod
    let obs = verify_source(src).expect("verify euclid div/mod");
    for ob in &obs {
        assert!(ob.verified, "obligation failed: {:?}", ob);
    }

    // 2. AST Interpreter produces r_mod = 1, r_div = -4
    let (interp_out, _) = bil::run_source(src, 42, false).expect("interp euclid div/mod");
    assert_eq!(interp_out[0], ("r_mod".into(), bil::eval::Value::Int(1)));
    assert_eq!(interp_out[1], ("r_div".into(), bil::eval::Value::Int(-4)));

    // 3. Bytecode VM produces identical results
    let (vm_out, _) = bil::run_vm_source(src, 42).expect("vm euclid div/mod");
    assert_eq!(interp_out, vm_out);

    // 4. Native AOT binary produces identical results
    let out_bin = std::env::temp_dir().join("bil_test_p0_3_euclid_aot");
    bil::build_native_source(src, &out_bin).expect("build native euclid div/mod");
    let out = std::process::Command::new(&out_bin)
        .output()
        .expect("run native euclid binary");
    let _ = std::fs::remove_file(&out_bin);
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("r_mod = 1"), "stdout: {}", stdout);
    assert!(stdout.contains("r_div = -4"), "stdout: {}", stdout);

    // 5. Checked i64 overflow returns clean error instead of panicking or wrapping
    let overflow_src = r#"
        let max_int = 9223372036854775807
        let boom = max_int + 1
    "#;
    let interp_err = bil::run_source(overflow_src, 42, false).unwrap_err();
    assert!(
        interp_err.to_lowercase().contains("overflow"),
        "expected overflow error from interpreter, got: {}",
        interp_err
    );
    let vm_err = bil::run_vm_source(overflow_src, 42).unwrap_err();
    assert!(
        vm_err.to_lowercase().contains("overflow"),
        "expected overflow error from VM, got: {}",
        vm_err
    );
}

#[test]
fn test_p0_4_capture_avoiding_complete_subst_and_eval_error_refutes() {
    use bil::ast::{BinOp, Expr, MatchArm, Pattern, QuantifierKind};
    use bil::wp::subst_expr;
    use std::collections::BTreeMap;

    // 1. Capture-avoiding substitution under Quantifier:
    //    (forall y in 0..=1 : y != result)[result := y]
    //    must alpha-rename bound `y` so free `y` in replacement is not captured!
    let src = r#"
        fn add_ten(y: Int) -> Int
          requires y == 10
          ensures  forall y in 0..=1 : y != result
        =
          y
    "#;
    let obs = verify_source(src).expect("verify add_ten with quantifier capture");
    let ob = obs.iter().find(|o| o.fn_name == "add_ten").unwrap();
    assert!(
        ob.verified,
        "Variable capture in subst_expr corrupted quantifier postcondition: {:?}",
        ob
    );

    // 2. Complete substitution inside Match arms:
    let match_expr = Expr::Match {
        scrutinee: Box::new(Expr::Var("x".into())),
        arms: vec![MatchArm {
            pattern: Pattern::Wildcard,
            body: Expr::Binary {
                op: BinOp::Add,
                left: Box::new(Expr::Var("target".into())),
                right: Box::new(Expr::Int(1)),
            },
        }],
    };
    let mut map = BTreeMap::new();
    map.insert("target".to_string(), Expr::Int(41));
    let sub_match = subst_expr(&match_expr, &map);
    if let Expr::Match { arms, .. } = sub_match {
        assert_eq!(
            arms[0].body,
            Expr::Binary {
                op: BinOp::Add,
                left: Box::new(Expr::Int(41)),
                right: Box::new(Expr::Int(1)),
            },
            "subst_expr must substitute inside Match.arms"
        );
    } else {
        panic!("expected Expr::Match");
    }

    // 3. Complete substitution inside Quantifier with direct AST check
    let q_expr = Expr::Quantifier {
        kind: QuantifierKind::Forall,
        var: "y".into(),
        domain: Box::new(Expr::Var("dom".into())),
        body: Box::new(Expr::Binary {
            op: BinOp::Neq,
            left: Box::new(Expr::Var("y".into())),
            right: Box::new(Expr::Var("result".into())),
        }),
    };
    let mut q_map = BTreeMap::new();
    q_map.insert("result".into(), Expr::Var("y".into()));
    let sub_q = subst_expr(&q_expr, &q_map);
    if let Expr::Quantifier { var, body, .. } = sub_q {
        assert_ne!(
            var, "y",
            "bound variable `y` must be alpha-renamed when replacement contains free `y`"
        );
        if let Expr::Binary { left, right, .. } = *body {
            assert_eq!(*left, Expr::Var(var));
            assert_eq!(*right, Expr::Var("y".into()));
        }
    }

    // 4. Division-by-zero during bounded VC evaluation must refute (fail-closed), not pass!
    let div_zero_vc_src = r#"
        fn unsafe_div_guard(x: Int) -> Int
          requires x >= 0
          ensures  result >= 0
        =
          if 10 / x >= 0 -> 1
          [] 10 / x < 0  -> 0
          fi
    "#;
    let div_obs = verify_source(div_zero_vc_src).expect("typecheck unsafe_div_guard");
    let totality_ob = div_obs
        .iter()
        .find(|o| o.fn_name == "unsafe_div_guard" && o.kind.to_string().contains("Guard Totality"))
        .expect("Guard Totality obligation");
    assert!(
        !totality_ob.verified,
        "Guard Totality with division by zero at x = 0 must be refuted, got: {:?}",
        totality_ob
    );

    // 5. LetIn wrapping IfFi must still generate IfFiGuardTotality obligation
    let let_iffi_src = r#"
        fn let_wrapped_bad_if(x: Int) -> Int
          requires x >= 0
          ensures  result > 0
        =
          let shifted = x + 1 in
          if shifted > 10 -> shifted
          fi
    "#;
    let let_obs = verify_source(let_iffi_src).expect("typecheck let_wrapped_bad_if");
    let let_totality = let_obs
        .iter()
        .find(|o| o.fn_name == "let_wrapped_bad_if" && o.kind.to_string().contains("Guard Totality"))
        .expect("LetIn wrapping IfFi must still emit Guard Totality obligation");
    assert!(!let_totality.verified);
}

#[test]
fn test_p0_5_model_checker_truncation_completeness_and_linear_scaling() {
    // 1. Truncated state space (max_states = 5 on a 21-state chain) must report
    //    complete == false, truncated_at == Some(5), and must NOT report a bogus
    //    "Halted in ¬Q terminal state" violation on the unexpanded frontier state.
    let chain_src = r#"
        system LongChain {
          state c: Int = 0
          invariant bounded: c <= 20
          temporal reaches_goal: eventually(c == 20)
          terminal: c == 20

          transition:
            c < 20 -> c := c + 1
        }
    "#;
    let truncated_reports = model_check_source(chain_src, 5).expect("model_check truncated");
    assert_eq!(truncated_reports.len(), 1);
    let tr_rep = &truncated_reports[0];
    assert_eq!(tr_rep.states_explored, 5);
    assert!(
        !tr_rep.complete,
        "State space truncated at max_states=5 must set complete = false"
    );
    assert_eq!(tr_rep.truncated_at, Some(5));
    assert!(
        tr_rep.violations.is_empty(),
        "Truncated frontier must not fabricate a false terminal ¬Q LTL violation, got: {:?}",
        tr_rep.violations
    );

    // Full exploration with max_states = 50 must complete and verify
    let full_reports = model_check_source(chain_src, 50).expect("model_check full");
    let full_rep = &full_reports[0];
    assert_eq!(full_rep.states_explored, 21);
    assert!(full_rep.complete);
    assert_eq!(full_rep.truncated_at, None);
    assert!(full_rep.violations.is_empty());

    // 2. Collision resistance: two distinct states whose naive "k=v; k=v" strings
    //    are identical ("a=x; b=1; b=2") must NOT collide in visited state table.
    let collision_src = r#"
        system KeyCollision {
          state a: String = "x"
          state b: String = "1; b=2"

          invariant no_shifted_delim: a != "x; b=1"
          terminal: a == "x; b=1"

          transition:
            a == "x" -> a := "x; b=1", b := "2"
        }
    "#;
    let col_reports = model_check_source(collision_src, 50).expect("model_check collision");
    let col_rep = &col_reports[0];
    assert!(
        !col_rep.violations.is_empty(),
        "State (a=\"x; b=1\", b=\"2\") must not collide with (a=\"x\", b=\"1; b=2\") and must trigger invariant violation"
    );
    assert_eq!(col_rep.violations[0].trace.len(), 2);
}

#[test]
fn test_p2_1_nested_do_od_under_let_and_boundary_constant_sampling() {
    use bil::wp::{ObligationKind, Status};

    // 1. A `do..od` nested inside `let start = n in do ... od` must generate full
    //    Dijkstra loop obligations (Initialization, Preservation, VariantNonNegative, VariantDecrease, ExitPostcondition)
    let nested_loop_src = r#"
        fn countdown(n: Int) -> Int
          requires n >= 0
          ensures  result == 0
        =
          let start = n in
          do c = start
            invariant c >= 0
            variant c
            c > 0 -> c := c - 1
          od then c
    "#;
    let obs = verify_source(nested_loop_src).expect("verify nested do..od under let");
    assert!(
        obs.iter()
            .any(|o| matches!(o.kind, ObligationKind::DoOdInitialization)),
        "do..od nested under let must generate DoOdInitialization obligation, got: {:?}",
        obs
    );
    assert!(
        obs.iter().all(|o| o.verified),
        "all countdown obligations must verify: {:?}",
        obs
    );

    // 2. Constant-guided boundary sampling must catch a bug that only triggers at x == 4321
    //    (outside the static [-1, 0, 1, 2, 6, 12, 800, 950, 1250] list) even without SMT:
    let threshold_src = r#"
        fn buggy_threshold(x: Int) -> Int
          requires x >= 0
          ensures  result > 0
        =
          if x == 4321 -> 0
          [] x != 4321 -> 1
          fi
    "#;
    let thresh_obs = verify_source(threshold_src).expect("verify buggy_threshold");
    let branch_0 = thresh_obs
        .iter()
        .find(|o| matches!(o.kind, ObligationKind::IfFiBranchPostcondition(0)))
        .expect("Branch #1 obligation");
    assert!(
        matches!(branch_0.status, Status::Refuted { .. }),
        "Constant-guided boundary sampling must find x = 4321 counterexample, got: {:?}",
        branch_0
    );
}

#[test]
fn test_p3_2_and_p3_3_symbolic_bmc_and_compilation_session() {
    use bil::model_check::symbolic_bmc_program;
    use bil::smt::{Prover, Verdict};
    use bil::CompilationSession;

    let safe_counter_src = r#"
        system BoundedCounter {
            state count: Int = 0
            state locked: Bool = false

            invariant CountWithinBounds:
                count >= 0 && count <= 3

            transition
                !locked && count < 3 -> count := count + 1
            []  !locked && count == 3 -> locked := true
            []  locked && count > 0 -> count := count - 1
            []  locked && count == 0 -> locked := false
        }

        let init_ok = 1
    "#;

    let mut session = CompilationSession::from_source(safe_counter_src).expect("session from_source");
    let mc_reports = session.model_check(500).expect("explicit model check");
    assert_eq!(mc_reports.len(), 1);
    assert!(mc_reports[0].violations.is_empty());

    let ir = session.lower_ir();
    assert_eq!(ir.lir.globals.len(), 1);

    let bmc_reports = symbolic_bmc_program(&session.program, &session.ontology, 6, Prover::Auto);
    assert_eq!(bmc_reports.len(), 1);
    assert!(bmc_reports[0].smt2_script.contains("(declare-const count__0 Int)"));
    assert!(bmc_reports[0].smt2_script.contains("(declare-const count__6 Int)"));
    if bmc_reports[0].verdict != Verdict::Skipped {
        assert!(bmc_reports[0].safe_up_to_k);
    }

    // Buggy system that violates invariant at depth 3 must be caught by symbolic BMC:
    let buggy_counter_src = r#"
        system OverflowCounter {
            state count: Int = 0

            invariant MaxTwo:
                count <= 2

            transition
                count < 5 -> count := count + 1
            []  count >= 5 -> count := 0
        }
    "#;
    let buggy_session = CompilationSession::from_source(buggy_counter_src).expect("buggy session");
    let buggy_bmc = symbolic_bmc_program(&buggy_session.program, &buggy_session.ontology, 4, Prover::Auto);
    assert_eq!(buggy_bmc.len(), 1);
    if buggy_bmc[0].verdict != Verdict::Skipped {
        assert_eq!(buggy_bmc[0].verdict, Verdict::Consistent);
        assert!(!buggy_bmc[0].safe_up_to_k);
    }
}

