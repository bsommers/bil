use bil::{check_source, model_check_source, ontology::transpile_ontologic_sexpr, run_source, verify_source};

#[test]
fn test_ontologic_dag_cycle_detection() {
    let src = r#"
        concept A <: B
        concept B <: C
        concept C <: A
    "#;
    let err = check_source(src).unwrap_err();
    assert!(err.contains("Circular inheritance detected"));
}

#[test]
fn test_ontologic_inheritance_and_hm_subtyping() {
    let src = r#"
        concept Entity { id: String }
        concept Device <: Entity { active: Bool }
        concept Sensor <: Device { reading: Int }

        fn get_id(e: Entity) -> String = e.id

        let s = Sensor { id: "S-1", active: true, reading: 42 }
        let sid = get_id(s)
        assert sid == "S-1"
    "#;
    let (outputs, _) = run_source(src, 1, false).expect("should run");
    assert_eq!(outputs.len(), 2);
}

#[test]
fn test_gcl_nondeterminism_and_abort_on_no_guard() {
    let abort_src = r#"
        fn bad_if(x: Int) -> Int =
          if x > 10 -> 1
          [] x < 0  -> -1
          fi
        let y = bad_if(5)
    "#;
    let err = run_source(abort_src, 1, false).unwrap_err();
    assert!(err.contains("ABORT: no guard evaluated to true"));

    // Verify WP catches non-total guards statically
    let wp_src = r#"
        fn bad_if(x: Int) -> Int
          requires x >= 0
          ensures  result != 0
        =
          if x > 10 -> 1
          [] x < 0  -> -1
          fi
    "#;
    let obligations = verify_source(wp_src).expect("should typecheck");
    let totality = obligations
        .iter()
        .find(|o| o.kind.to_string().contains("Guard Totality"))
        .unwrap();
    assert!(!totality.verified);
    assert!(totality.counterexample.is_some());
}

#[test]
fn test_dijkstra_wp_and_refinement_verification() {
    let src = std::fs::read_to_string("examples/gcd_refinement.bil").unwrap();
    let obligations = verify_source(&src).expect("verify gcd_refinement.bil");
    assert!(!obligations.is_empty());
    for ob in &obligations {
        assert!(
            ob.verified,
            "Obligation {} failed: {:?}",
            ob.kind, ob.counterexample
        );
    }
}

#[test]
fn test_explicit_state_model_checker_peterson_and_buggy_mutex() {
    let peterson = std::fs::read_to_string("examples/mutex_protocol.bil").unwrap();
    let reports = model_check_source(&peterson, 1000).expect("model check peterson");
    assert_eq!(reports.len(), 1);
    assert!(reports[0].violations.is_empty());
    assert_eq!(reports[0].states_explored, 10);

    // Naive buggy mutex without `turn` variable must be caught violating MutualExclusion
    let buggy = r#"
        type Phase = Idle | Critical
        system NaiveMutex {
          state p0: Phase = Idle
          state p1: Phase = Idle

          invariant MutualExclusion:
            !(p0 == Critical && p1 == Critical)

          transition
            p0 == Idle     -> p0 := Critical
          [] p0 == Critical -> p0 := Idle
          [] p1 == Idle     -> p1 := Critical
          [] p1 == Critical -> p1 := Idle
        }
    "#;
    let buggy_reports = model_check_source(buggy, 1000).expect("model check naive");
    assert!(!buggy_reports[0].violations.is_empty());
    assert!(buggy_reports[0].violations[0]
        .kind
        .to_string()
        .contains("MutualExclusion"));
}

#[test]
fn test_all_five_practical_examples() {
    for file in [
        "examples/gcd_refinement.bil",
        "examples/mutex_protocol.bil",
        "examples/arbiter_controller.bil",
        "examples/smart_grid.bil",
        "examples/security_policy.bil",
    ] {
        let src = std::fs::read_to_string(file).unwrap();
        let ob = verify_source(&src).expect(file);
        for o in ob {
            assert!(o.verified, "{} failed in {}", o.kind, file);
        }
        let mc = model_check_source(&src, 5000).expect(file);
        for r in mc {
            assert!(r.violations.is_empty(), "violation in {}", file);
        }
        run_source(&src, 42, true).expect(file);
    }
}

#[test]
fn test_ontologic_sexpr_transpiler() {
    let logic = r#"
        (def-concept Entity)
        (def-concept Pump Entity)
        (def-property vibration Pump Integer)
        (forall (p) (implies (Pump p) (le vibration 50)))
    "#;
    let bil_code = transpile_ontologic_sexpr(logic).expect("transpile");
    assert!(bil_code.contains("concept Pump <: Entity"));
    assert!(bil_code.contains("forall p in Pump : (p.vibration <= 50)"));
    check_source(&bil_code).expect("generated bil code should typecheck");
}

#[test]
fn test_verus_rust_codegen() {
    let src = std::fs::read_to_string("examples/smart_grid.bil").unwrap();
    let verus_rs = bil::emit_verus_source(&src).expect("emit verus for smart_grid.bil");
    assert!(verus_rs.contains("verus! {"));
    assert!(verus_rs.contains("pub open spec fn axiom_ActivePipelineSafety"));
    assert!(verus_rs.contains("decreases"));
    assert!(verus_rs.contains("invariant"));

    let gcd_src = std::fs::read_to_string("examples/gcd_refinement.bil").unwrap();
    let gcd_verus = bil::emit_verus_source(&gcd_src).expect("emit verus for gcd_refinement.bil");
    assert!(gcd_verus.contains("pub open spec fn gcd_spec_contract"));
    assert!(gcd_verus.contains("gcd_spec_contract(a, b, result)"));
}

#[test]
fn test_three_level_ir_lowering_and_ghost_erasure() {
    let src = std::fs::read_to_string("examples/smart_grid.bil").unwrap();
    let ir = bil::lower_ir_source(&src).expect("lower 3-level IR");

    // HIR checks: 6 flattened BFO concepts, 2 axioms, 2 functions
    assert_eq!(ir.hir.concepts.len(), 6);
    assert_eq!(ir.hir.axioms.len(), 2);
    assert_eq!(ir.hir.functions.len(), 2);

    // VIR checks: 2 spec items, 12 proof obligations (all verified)
    assert_eq!(ir.vir.spec_items.len(), 2);
    assert_eq!(ir.vir.proof_obligations.len(), 12);
    assert!(ir.vir.proof_obligations.iter().all(|o| o.verified));

    // LIR checks: Ghost erasure strips 2 axioms + 4 requires/ensures + 2 loop invariant/variant = 8 ghost items
    assert_eq!(ir.lir.erased_ghost_count, 8);
    assert_eq!(ir.lir.functions.len(), 2);
}
