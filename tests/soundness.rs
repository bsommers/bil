use bil::{ smt::Verdict, verify_source };

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


