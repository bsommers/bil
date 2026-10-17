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
