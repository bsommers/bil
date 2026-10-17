use bil::{
    build_native_source, check_source, emit_verus_source, lower_ir_source, model_check_source,
    ontology::transpile_ontologic_sexpr, prove_subsumption_source, run_source, run_vm_source,
    smt::{Prover, SubsumptionResult, Verdict},
    solve_ontology_source, verify_source,
};
use std::env;
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;
use std::process;

fn print_usage() {
    eprintln!("bil v0.2.0 — Bounded Invariant Logic (OntoLogic + FOL + Dijkstra GCL + 3-Level IR + Verus + Native AOT)");
    eprintln!();
    eprintln!("USAGE:");
    eprintln!("  bil check <file.bil>                   Run OntoLogic DAG linter & Hindley-Milner typechecker");
    eprintln!("  bil solve <file.bil> [--prover z3|cvc5|auto] [--subsumes Child Parent] [--emit-smt2]");
    eprintln!("  bil verify <file.bil>                  Generate & prove Dijkstra WP, Refinement & Proof obligations");
    eprintln!("  bil model-check <file.bil>             Exhaustively verify safety invariants & LTL temporal liveness");
    eprintln!("  bil run <file.bil> [--seed N] [--trace] Execute program, axioms, GCL & functional pipelines");
    eprintln!("  bil vm <file.bil> [--dump-bytecode]    Execute Ghost-Erased LIR on the Register/Stack Bytecode VM");
    eprintln!("  bil build <file.bil> [-o <out_bin>]    Compile Ghost-Erased LIR to a standalone native ELF binary");
    eprintln!("  bil all <file.bil> [--seed N] [--trace] Run check + verify + model-check + run");
    eprintln!("  bil dump-ir <file.bil> [--level hir|vir|lir|all] Inspect 3-Level IR (HIR -> VIR -> LIR)");
    eprintln!("  bil emit-verus <file.bil>              Emit provably correct Verus Rust code (verus! {{ ... }})");
    eprintln!("  bil import-ontologic <file.logic>      Convert OntoLogic S-expression (.logic) to .bil");
    eprintln!("  bil repl                               Start interactive bil shell");
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        print_usage();
        process::exit(1);
    }

    let cmd = args[1].as_str();
    match cmd {
        "repl" => run_repl(),
        "vm" => {
            if args.len() < 3 {
                eprintln!("Usage: bil vm <file.bil> [--dump-bytecode]");
                process::exit(1);
            }
            let path = &args[2];
            let dump_bc = args.iter().any(|a| a == "--dump-bytecode");
            let src = fs::read_to_string(path).unwrap_or_else(|e| {
                eprintln!("Failed to read {}: {}", path, e);
                process::exit(1);
            });
            match run_vm_source(&src, 42) {
                Ok((outputs, bc)) => {
                    if dump_bc {
                        print!("{}", bc);
                    }
                    for (name, val) in outputs {
                        println!("{} = {}", name, val);
                    }
                }
                Err(e) => {
                    eprintln!("{}", e);
                    process::exit(1);
                }
            }
        }
        "build" => {
            if args.len() < 3 {
                eprintln!("Usage: bil build <file.bil> [-o <output_bin>]");
                process::exit(1);
            }
            let path = &args[2];
            let mut out_bin = PathBuf::from(path).with_extension("");
            if out_bin == PathBuf::from(path) {
                out_bin = PathBuf::from(format!("{}.out", path));
            }
            let mut i = 3;
            while i < args.len() {
                if (args[i] == "-o" || args[i] == "--output") && i + 1 < args.len() {
                    out_bin = PathBuf::from(&args[i + 1]);
                    i += 1;
                }
                i += 1;
            }
            let src = fs::read_to_string(path).unwrap_or_else(|e| {
                eprintln!("Failed to read {}: {}", path, e);
                process::exit(1);
            });
            match build_native_source(&src, &out_bin) {
                Ok(rep) => {
                    println!(
                        "✅ Native AOT Binary compiled: {} ({} functions, {} globals, {} ghost items erased, {} ms)",
                        rep.output_path.display(),
                        rep.functions_compiled,
                        rep.globals_compiled,
                        rep.erased_ghost_count,
                        rep.elapsed_ms
                    );
                }
                Err(e) => {
                    eprintln!("{}", e);
                    process::exit(1);
                }
            }
        }
        "solve" => {
            if args.len() < 3 {
                eprintln!("Usage: bil solve <file.bil> [--prover z3|cvc5|auto] [--subsumes Child Parent] [--emit-smt2]");
                process::exit(1);
            }
            let path = &args[2];
            let mut prover = Prover::Auto;
            let mut subsumes: Option<(String, String)> = None;
            let mut emit_smt2 = false;
            let mut i = 3;
            while i < args.len() {
                match args[i].as_str() {
                    "--prover" | "-p" if i + 1 < args.len() => {
                        prover = Prover::parse(&args[i + 1]);
                        i += 1;
                    }
                    "--subsumes" if i + 2 < args.len() => {
                        subsumes = Some((args[i + 1].clone(), args[i + 2].clone()));
                        i += 2;
                    }
                    "--emit-smt2" => emit_smt2 = true,
                    _ => {}
                }
                i += 1;
            }
            let src = fs::read_to_string(path).unwrap_or_else(|e| {
                eprintln!("Failed to read {}: {}", path, e);
                process::exit(1);
            });
            if let Some((child, parent)) = subsumes {
                match prove_subsumption_source(&src, &child, &parent, prover) {
                    Ok(SubsumptionResult::Subsumed { prover: p }) => {
                        println!(
                            "✅ Subsumption PROVED by {}: {} <: {} (refutation unsat)",
                            p, child, parent
                        );
                    }
                    Ok(SubsumptionResult::NotSubsumed { prover: p, .. }) => {
                        println!(
                            "❌ Subsumption REFUTED by {}: {} is NOT subsumed by {}",
                            p, child, parent
                        );
                        process::exit(1);
                    }
                    Ok(SubsumptionResult::Unknown { detail }) => {
                        println!("⚠️  Subsumption Unknown: {}", detail);
                    }
                    Err(e) => {
                        eprintln!("{}", e);
                        process::exit(1);
                    }
                }
            } else {
                match solve_ontology_source(&src, prover) {
                    Ok((res, smt2)) => {
                        if emit_smt2 {
                            println!("{}", smt2);
                        }
                        match res.verdict {
                            Verdict::Consistent => {
                                println!(
                                    "✅ SMT Satisfiable (SAT) via {} ({} ms) — Ontology & axioms are logically consistent.",
                                    res.prover, res.elapsed_ms
                                );
                            }
                            Verdict::Inconsistent => {
                                println!(
                                    "❌ SMT Unsatisfiable (UNSAT) via {} ({} ms) — Logical contradiction detected!",
                                    res.prover, res.elapsed_ms
                                );
                                process::exit(1);
                            }
                            Verdict::Unknown | Verdict::Skipped => {
                                println!("⚠️  SMT Solver Result ({}): {}", res.prover, res.detail);
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!("{}", e);
                        process::exit(1);
                    }
                }
            }
        }
        "dump-ir" => {
            if args.len() < 3 {
                eprintln!("Usage: bil dump-ir <file.bil> [--level hir|vir|lir|all]");
                process::exit(1);
            }
            let path = &args[2];
            let mut level = "all";
            if args.len() >= 5 && args[3] == "--level" {
                level = args[4].as_str();
            }
            let src = fs::read_to_string(path).unwrap_or_else(|e| {
                eprintln!("Failed to read {}: {}", path, e);
                process::exit(1);
            });
            match lower_ir_source(&src) {
                Ok(ir) => match level {
                    "hir" => print!("{}", ir.hir),
                    "vir" => print!("{}", ir.vir),
                    "lir" => print!("{}", ir.lir),
                    _ => {
                        print!("{}\n{}\n{}", ir.hir, ir.vir, ir.lir);
                    }
                },
                Err(e) => {
                    eprintln!("{}", e);
                    process::exit(1);
                }
            }
        }
        "emit-verus" => {
            if args.len() < 3 {
                eprintln!("Usage: bil emit-verus <file.bil>");
                process::exit(1);
            }
            let path = &args[2];
            let src = fs::read_to_string(path).unwrap_or_else(|e| {
                eprintln!("Failed to read {}: {}", path, e);
                process::exit(1);
            });
            match emit_verus_source(&src) {
                Ok(verus_code) => print!("{}", verus_code),
                Err(e) => {
                    eprintln!("{}", e);
                    process::exit(1);
                }
            }
        }
        "import-ontologic" => {
            if args.len() < 3 {
                eprintln!("Usage: bil import-ontologic <file.logic>");
                process::exit(1);
            }
            let path = &args[2];
            let src = fs::read_to_string(path).unwrap_or_else(|e| {
                eprintln!("Failed to read {}: {}", path, e);
                process::exit(1);
            });
            match transpile_ontologic_sexpr(&src) {
                Ok(bil_code) => print!("{}", bil_code),
                Err(e) => {
                    eprintln!("Error importing OntoLogic file: {}", e);
                    process::exit(1);
                }
            }
        }
        "check" | "verify" | "model-check" | "run" | "all" => {
            if args.len() < 3 {
                print_usage();
                process::exit(1);
            }
            let path = &args[2];
            let mut seed = 42u64;
            let mut trace = false;
            let mut i = 3;
            while i < args.len() {
                match args[i].as_str() {
                    "--trace" => trace = true,
                    "--seed" => {
                        if i + 1 < args.len() {
                            seed = args[i + 1].parse().unwrap_or(42);
                            i += 1;
                        }
                    }
                    _ => {}
                }
                i += 1;
            }

            let src = fs::read_to_string(path).unwrap_or_else(|e| {
                eprintln!("Failed to read {}: {}", path, e);
                process::exit(1);
            });

            if cmd == "check" || cmd == "all" {
                match check_source(&src) {
                    Ok((_, ontology, tenv)) => {
                        println!(
                            "[OK] OntoLogic DAG & HM Typecheck passed ({} concepts, {} ADTs, {} specs)",
                            ontology.concepts.len(),
                            tenv.adts.len(),
                            tenv.specs.len()
                        );
                    }
                    Err(e) => {
                        eprintln!("{}", e);
                        process::exit(1);
                    }
                }
            }

            if cmd == "verify" || cmd == "all" {
                match verify_source(&src) {
                    Ok(obligations) => {
                        println!(
                            "=== Formal Verification (Dijkstra WP, Refinement & SMT Solver): {} obligations ===",
                            obligations.len()
                        );
                        let mut all_ok = true;
                        for ob in &obligations {
                            if !ob.verified {
                                all_ok = false;
                            }
                            let smt_badge = match (&ob.smt_prover, &ob.smt_verdict, &ob.agreement) {
                                (Some(p), Some(Verdict::Inconsistent), Some(agr)) => {
                                    format!(" [SMT {}: refutation UNSAT | Agreement: {}]", p, agr)
                                }
                                (Some(p), Some(v), Some(agr)) => {
                                    format!(" [SMT {}: {} | Agreement: {}]", p, v, agr)
                                }
                                _ => String::new(),
                            };
                            println!("  [{}] fn `{}` — {}{}", ob.status, ob.fn_name, ob.kind, smt_badge);
                            println!("           VC: {}", ob.formula_desc);
                            if let Some(ce) = &ob.counterexample {
                                println!("           Counterexample: {}", ce);
                            }
                        }
                        if !all_ok {
                            process::exit(1);
                        }
                    }
                    Err(e) => {
                        eprintln!("{}", e);
                        process::exit(1);
                    }
                }
            }

            if cmd == "model-check" || cmd == "all" {
                match model_check_source(&src, 50_000) {
                    Ok(reports) => {
                        for rep in reports {
                            println!(
                                "=== Explicit-State & LTL Model Checker: system `{}` ===",
                                rep.system_name
                            );
                            println!(
                                "  States explored: {} | Transitions fired: {} | Max depth: {} | Max nondeterministic branching: {}",
                                rep.states_explored,
                                rep.transitions_fired,
                                rep.max_depth,
                                rep.max_branching_factor
                            );
                            for tr in &rep.temporal_results {
                                let badge = if tr.verified { "PROVED" } else { "FAILED" };
                                println!(
                                    "  [LTL {}] temporal `{}`: {}",
                                    badge, tr.name, tr.formula_desc
                                );
                            }
                            if rep.violations.is_empty() {
                                if rep.complete {
                                    println!("  [VERIFIED] All safety invariants, LTL temporal properties, deadlock-freedom (BB), and variant bounds hold.");
                                } else {
                                    println!(
                                        "  [BOUNDED / INCOMPLETE (truncated at {} states)] No violations found within state bound.",
                                        rep.truncated_at.unwrap_or(rep.states_explored)
                                    );
                                }
                            } else {
                                for v in &rep.violations {
                                    println!("  [VIOLATION] {} at state {}", v.kind, v.state_str);
                                    println!("  Counterexample Trace ({} steps):", v.trace.len());
                                    for line in &v.trace {
                                        println!("    {}", line);
                                    }
                                }
                                process::exit(1);
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!("{}", e);
                        process::exit(1);
                    }
                }
            }

            if cmd == "run" || cmd == "all" {
                match run_source(&src, seed, trace) {
                    Ok((outputs, trace_log)) => {
                        if trace && !trace_log.is_empty() {
                            println!("=== Nondeterministic Execution Trace (seed={}) ===", seed);
                            for t in &trace_log {
                                println!("  {}", t);
                            }
                        }
                        for (name, val) in outputs {
                            println!("{} = {}", name, val);
                        }
                    }
                    Err(e) => {
                        eprintln!("{}", e);
                        process::exit(1);
                    }
                }
            }
        }
        _ => {
            print_usage();
            process::exit(1);
        }
    }
}

fn run_repl() {
    println!("bil v0.1.0 REPL — Enter declarations or expressions (:q to quit)");
    let mut accumulated = String::new();
    let stdin = io::stdin();
    loop {
        print!("bil> ");
        let _ = io::stdout().flush();
        let mut line = String::new();
        if stdin.read_line(&mut line).unwrap_or(0) == 0 {
            break;
        }
        let trimmed = line.trim();
        if trimmed == ":q" || trimmed == "exit" {
            break;
        }
        if trimmed.is_empty() {
            continue;
        }
        let candidate = if trimmed.starts_with("concept ")
            || trimmed.starts_with("type ")
            || trimmed.starts_with("axiom ")
            || trimmed.starts_with("spec ")
            || trimmed.starts_with("fn ")
            || trimmed.starts_with("let ")
            || trimmed.starts_with("assert ")
        {
            format!("{}\n{}", accumulated, trimmed)
        } else {
            format!("{}\nlet _repl = {}", accumulated, trimmed)
        };

        match run_source(&candidate, 42, false) {
            Ok((outputs, _)) => {
                if !trimmed.starts_with("let _repl") && candidate.contains("let _repl =") {
                    if let Some((_, val)) = outputs.last() {
                        println!("=> {}", val);
                    }
                } else {
                    accumulated = candidate;
                    if let Some((k, v)) = outputs.last() {
                        if trimmed.starts_with("let ") {
                            println!("{} = {}", k, v);
                        }
                    }
                }
            }
            Err(e) => eprintln!("{}", e),
        }
    }
}
