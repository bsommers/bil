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

#[test]
fn test_ontologic_static_contradiction_linter() {
    let bad_range = r#"
        concept Sensor { reading: Int }
        axiom ImpossibleRange:
          forall s in Sensor : s.reading > 100 && s.reading < 50
    "#;
    let err = check_source(bad_range).unwrap_err();
    assert!(
        err.contains("Property contradiction"),
        "Expected Property contradiction, got: {}",
        err
    );

    let bad_prop = r#"
        concept Node { active: Bool }
        axiom ContradictoryBool:
          forall n in Node : n.active && !(n.active)
    "#;
    let err2 = check_source(bad_prop).unwrap_err();
    assert!(
        err2.contains("Axiom contradiction"),
        "Expected Axiom contradiction, got: {}",
        err2
    );
}

#[test]
fn test_clif2ontologic_smt_solver_consistency_and_subsumption() {
    use bil::smt::{Prover, SubsumptionResult, Verdict};

    let grid_src = std::fs::read_to_string("examples/smart_grid.bil").unwrap();
    let (res, smt2) = bil::solve_ontology_source(&grid_src, Prover::Auto).expect("solve smart_grid");
    assert!(smt2.contains("(declare-sort Entity 0)"));
    assert!(smt2.contains("(declare-fun subClassOf (Entity Entity) Bool)"));
    if res.verdict != Verdict::Skipped {
        assert_eq!(res.verdict, Verdict::Consistent);
    }

    // Transitive subsumption: Pipeline <: Equipment <: MaterialEntity <: Continuant <: Entity
    let sub_ok =
        bil::prove_subsumption_source(&grid_src, "Pipeline", "Continuant", Prover::Auto)
            .expect("prove subsumption");
    if !matches!(sub_ok, SubsumptionResult::Unknown { .. }) {
        assert!(matches!(sub_ok, SubsumptionResult::Subsumed { .. }));
    }

    // Non-subsumption: Pipeline is NOT subsumed by sibling concept Valve
    let sub_no =
        bil::prove_subsumption_source(&grid_src, "Pipeline", "Valve", Prover::Auto)
            .expect("refute subsumption");
    if !matches!(sub_no, SubsumptionResult::Unknown { .. }) {
        assert!(matches!(sub_no, SubsumptionResult::NotSubsumed { .. }));
    }

    // Multi-axiom indirect SMT contradiction (passes pairwise linter, caught by Z3/CVC5)
    let indirect_unsat = r#"
        concept Tank { level: Int, cap: Int }
        axiom A1: forall t in Tank : t.level > t.cap
        axiom A2: forall t in Tank : t.cap >= t.level
    "#;
    let (unsat_res, _) =
        bil::solve_ontology_source(indirect_unsat, Prover::Auto).expect("solve indirect_unsat");
    if unsat_res.verdict != Verdict::Skipped {
        assert_eq!(unsat_res.verdict, Verdict::Inconsistent);
    }
}

#[test]
fn test_verus_proof_lemma_and_smt_agreement() {
    use bil::smt::{AgreementOutcome, Verdict};

    let gcd_src = std::fs::read_to_string("examples/gcd_refinement.bil").unwrap();
    let obligations = verify_source(&gcd_src).expect("verify gcd_refinement");
    let lemma_ob = obligations
        .iter()
        .find(|o| o.fn_name == "gcd_variant_step")
        .expect("should contain gcd_variant_step proof obligation");
    assert!(lemma_ob.verified);
    if lemma_ob.smt_verdict != Some(Verdict::Skipped) && lemma_ob.smt_verdict.is_some() {
        assert_eq!(lemma_ob.smt_verdict, Some(Verdict::Inconsistent));
        assert_eq!(lemma_ob.agreement, Some(AgreementOutcome::Match));
    }

    // Verify Verus codegen emits `pub proof fn gcd_variant_step`
    let verus_code = bil::emit_verus_source(&gcd_src).expect("emit verus");
    assert!(verus_code.contains("pub proof fn gcd_variant_step(x: i64, y: i64)"));

    // Verify LIR ghost erasure removes `proof` block
    let ir = bil::lower_ir_source(&gcd_src).expect("lower ir");
    assert_eq!(ir.hir.proofs.len(), 1);
    assert!(ir.lir.functions.iter().all(|f| f.name != "gcd_variant_step"));
}

#[test]
fn test_ltl_temporal_model_checking_and_fairness() {
    // 1. Peterson's Mutex satisfies both StarvationFreeP0 and StarvationFreeP1 (p_i == Trying ~> p_i == Critical)
    let mutex_src = std::fs::read_to_string("examples/mutex_protocol.bil").unwrap();
    let mutex_reps = model_check_source(&mutex_src, 10_000).expect("model check mutex");
    assert_eq!(mutex_reps.len(), 1);
    let mrep = &mutex_reps[0];
    assert!(mrep.violations.is_empty());
    assert_eq!(mrep.temporal_results.len(), 2);
    assert!(mrep.temporal_results.iter().all(|t| t.verified));

    // 2. DualBusArbiter satisfies BusReleaseAfterGrant (~>) and ArbitrationCompletes (eventually)
    let arb_src = std::fs::read_to_string("examples/arbiter_controller.bil").unwrap();
    let arb_reps = model_check_source(&arb_src, 10_000).expect("model check arbiter");
    assert_eq!(arb_reps.len(), 1);
    let arep = &arb_reps[0];
    assert!(arep.violations.is_empty());
    assert_eq!(arep.temporal_results.len(), 2);
    assert!(arep.temporal_results.iter().all(|t| t.verified));

    // 3. Unfair / Starving Lock: P1 can cycle Idle <-> Critical forever while P0 is stuck in Trying
    let starving_src = r#"
        type Phase = Idle | Trying | Critical
        system StarvingLock {
          state p0: Phase = Idle
          state p1: Phase = Idle
          state lock_held: Bool = false

          temporal NoStarvationP0:
            (p0 == Trying) ~> (p0 == Critical)

          transition
            p0 == Idle -> p0 := Trying
          [] p0 == Trying && !lock_held -> p0 := Critical, lock_held := true
          [] p0 == Critical -> p0 := Idle, lock_held := false
          [] p1 == Idle && !lock_held -> p1 := Critical, lock_held := true
          [] p1 == Critical -> p1 := Idle, lock_held := false
        }
    "#;
    let st_reps = model_check_source(starving_src, 10_000).expect("model check starving lock");
    assert_eq!(st_reps.len(), 1);
    assert!(!st_reps[0].violations.is_empty());
    assert!(!st_reps[0].temporal_results[0].verified);
}

#[test]
fn test_bytecode_vm_execution_parity() {
    for path in [
        "examples/smart_grid.bil",
        "examples/gcd_refinement.bil",
        "examples/arbiter_controller.bil",
        "examples/security_policy.bil",
    ] {
        let src = std::fs::read_to_string(path).unwrap();
        let (interp_out, _) = run_source(&src, 42, false).expect("interp run");
        let (vm_out, bc) = bil::run_vm_source(&src, 42).expect("vm run");
        assert!(bc.total_instructions() > 0);
        assert_eq!(
            interp_out, vm_out,
            "Bytecode VM output mismatch with AST interpreter on {}",
            path
        );
    }
}

#[test]
fn test_native_aot_build_and_binary_execution() {
    use std::process::Command;

    let gcd_src = std::fs::read_to_string("examples/gcd_refinement.bil").unwrap();
    let out_bin = std::env::temp_dir().join("bil_test_gcd_aot");
    let report = bil::build_native_source(&gcd_src, &out_bin).expect("compile native AOT binary");
    assert_eq!(report.functions_compiled, 3);
    assert_eq!(report.erased_ghost_count, 9);

    let output = Command::new(&out_bin)
        .output()
        .expect("execute compiled native AOT binary");
    let _ = std::fs::remove_file(&out_bin);
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains("g1 = 6"), "stdout was: {}", stdout);
    assert!(stdout.contains("g2 = 21"), "stdout was: {}", stdout);
    assert!(stdout.contains("m1 = 42"), "stdout was: {}", stdout);

    let grid_src = std::fs::read_to_string("examples/smart_grid.bil").unwrap();
    let grid_bin = std::env::temp_dir().join("bil_test_grid_aot");
    let grid_rep = bil::build_native_source(&grid_src, &grid_bin).expect("compile smart_grid AOT");
    assert_eq!(grid_rep.erased_ghost_count, 8);
    let grid_out = Command::new(&grid_bin).output().expect("execute smart_grid binary");
    let _ = std::fs::remove_file(&grid_bin);
    assert!(grid_out.status.success());
    let grid_stdout = String::from_utf8_lossy(&grid_out.stdout);
    assert!(
        grid_stdout.contains("stabilized_fleet = [Pipeline")
            && grid_stdout.contains("total_stabilized_pressure = 2080"),
        "grid_stdout was: {}",
        grid_stdout
    );
}


