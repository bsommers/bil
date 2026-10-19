//! Command-line interface dispatcher and interactive REPL for `bil`.

use crate::{
    build_native_source, emit_verus_source, lower_ir_source, ontology::transpile_ontologic_sexpr,
    prove_subsumption_source, run_source, run_vm_source,
    smt::{Prover, SubsumptionResult, Verdict},
    solve_ontology_source, CompilationSession,
};
use std::fs;
use std::io::{self, Write};
use std::path::PathBuf;

pub fn print_usage() {
    eprintln!(
        "bil v{} — Bounded Invariant Logic (OntoLogic + FOL + Dijkstra GCL + 3-Level IR + Verus + Native AOT)",
        env!("CARGO_PKG_VERSION")
    );
    eprintln!();
    eprintln!("USAGE:");
    eprintln!("  bil check <file.bil>                   Run OntoLogic DAG linter & Hindley-Milner typechecker");
    eprintln!("  bil solve <file.bil> [--prover z3|cvc5|vampire|auto] [--subsumes Child Parent] [--emit-smt2]");
    eprintln!("  bil verify <file.bil> [--format json]  Generate & prove Dijkstra WP, Refinement & Proof obligations");
    eprintln!("  bil model-check <file.bil> [--max-states N] [--bmc K] [--format json] Exhaustively or symbolically verify system models");
    eprintln!("  bil run <file.bil> [--seed N] [--trace] Execute program, axioms, GCL & functional pipelines");
    eprintln!("  bil vm <file.bil> [--seed N] [--dump-bytecode] Execute Ghost-Erased LIR on the Register/Stack Bytecode VM");
    eprintln!("  bil build <file.bil> [-o <out_bin>]    Compile Ghost-Erased LIR to a standalone native ELF binary");
    eprintln!("  bil all <file.bil> [--seed N] [--trace] Run check + verify + model-check + run");
    eprintln!("  bil dump-ir <file.bil> [--level hir|vir|lir|all] Inspect 3-Level IR (HIR -> VIR -> LIR)");
    eprintln!("  bil emit-verus <file.bil>              Emit provably correct Verus Rust code (verus! {{ ... }})");
    eprintln!("  bil import-ontologic <file.logic>      Convert OntoLogic S-expression (.logic) to .bil");
    eprintln!("  bil repl                               Start interactive bil shell");
}

fn read_source_file(path: &str) -> Result<String, i32> {
    fs::read_to_string(path).map_err(|e| {
        eprintln!("Failed to read {}: {}", path, e);
        1
    })
}

/// Returns the value after the flag at `args[*i]`, advancing `i` onto it.
fn flag_value<'a>(args: &'a [String], i: &mut usize) -> Result<&'a str, i32> {
    let flag = &args[*i];
    *i += 1;
    args.get(*i).map(String::as_str).ok_or_else(|| {
        eprintln!("error: `{}` requires a value", flag);
        1
    })
}

fn parse_flag<T: std::str::FromStr>(flag: &str, value: &str) -> Result<T, i32> {
    value.parse().map_err(|_| {
        eprintln!("error: invalid value `{}` for `{}`", value, flag);
        1
    })
}

fn unknown_flag(cmd: &str, flag: &str) -> i32 {
    eprintln!("error: unknown option `{}` for `bil {}`", flag, cmd);
    1
}

fn parse_prover(value: &str) -> Result<Prover, i32> {
    match value.to_ascii_lowercase().as_str() {
        "z3" | "cvc5" | "vampire" | "auto" => Ok(Prover::parse(value)),
        _ => {
            eprintln!(
                "error: invalid value `{}` for `--prover` (expected z3, cvc5, vampire or auto)",
                value
            );
            Err(1)
        }
    }
}

/// Options shared by `check`, `verify`, `model-check`, `run` and `all`.
struct PipelineOpts {
    seed: u64,
    trace: bool,
    max_states: usize,
    bmc_k: Option<usize>,
    json_output: bool,
}

fn parse_pipeline_opts(cmd: &str, args: &[String]) -> Result<PipelineOpts, i32> {
    let mut opts = PipelineOpts {
        seed: 42,
        trace: false,
        max_states: 50_000,
        bmc_k: None,
        json_output: false,
    };
    let mut i = 3;
    while i < args.len() {
        match args[i].as_str() {
            "--trace" => opts.trace = true,
            "--seed" => opts.seed = parse_flag("--seed", flag_value(args, &mut i)?)?,
            "--max-states" => {
                opts.max_states = parse_flag("--max-states", flag_value(args, &mut i)?)?
            }
            "--bmc" => opts.bmc_k = Some(parse_flag("--bmc", flag_value(args, &mut i)?)?),
            s if s.starts_with("--bmc=") => {
                opts.bmc_k = Some(parse_flag("--bmc", &s["--bmc=".len()..])?)
            }
            "--format" => match flag_value(args, &mut i)? {
                "json" => opts.json_output = true,
                "text" => opts.json_output = false,
                other => {
                    eprintln!(
                        "error: invalid value `{}` for `--format` (expected json or text)",
                        other
                    );
                    return Err(1);
                }
            },
            "--json" => opts.json_output = true,
            other => return Err(unknown_flag(cmd, other)),
        }
        i += 1;
    }
    Ok(opts)
}

/// Runs the CLI with the provided `args` and returns a process exit code (`0` on success).
pub fn run_cli(args: &[String]) -> i32 {
    if args.len() < 2 {
        print_usage();
        return 1;
    }

    let cmd = args[1].as_str();
    match cmd {
        "repl" => {
            run_repl();
            0
        }
        "vm" => {
            if args.len() < 3 {
                eprintln!("Usage: bil vm <file.bil> [--seed N] [--dump-bytecode]");
                return 1;
            }
            let path = &args[2];
            let mut dump_bc = false;
            let mut seed = 42u64;
            let mut i = 3;
            while i < args.len() {
                match args[i].as_str() {
                    "--dump-bytecode" => dump_bc = true,
                    "--seed" => {
                        match flag_value(args, &mut i).and_then(|v| parse_flag("--seed", v)) {
                            Ok(v) => seed = v,
                            Err(code) => return code,
                        }
                    }
                    other => return unknown_flag(cmd, other),
                }
                i += 1;
            }
            let Ok(src) = read_source_file(path) else {
                return 1;
            };
            match run_vm_source(&src, seed) {
                Ok((outputs, bc)) => {
                    if dump_bc {
                        print!("{}", bc);
                    }
                    for (name, val) in outputs {
                        println!("{} = {}", name, val);
                    }
                    0
                }
                Err(e) => {
                    eprintln!("{}", e);
                    1
                }
            }
        }
        "build" => {
            if args.len() < 3 {
                eprintln!("Usage: bil build <file.bil> [-o <output_bin>]");
                return 1;
            }
            let path = &args[2];
            let mut out_bin = PathBuf::from(path).with_extension("");
            if out_bin == PathBuf::from(path) {
                out_bin = PathBuf::from(format!("{}.out", path));
            }
            let mut i = 3;
            while i < args.len() {
                match args[i].as_str() {
                    "-o" | "--output" => match flag_value(args, &mut i) {
                        Ok(v) => out_bin = PathBuf::from(v),
                        Err(code) => return code,
                    },
                    other => return unknown_flag(cmd, other),
                }
                i += 1;
            }
            let Ok(src) = read_source_file(path) else {
                return 1;
            };
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
                    0
                }
                Err(e) => {
                    eprintln!("{}", e);
                    1
                }
            }
        }
        "solve" => {
            if args.len() < 3 {
                eprintln!("Usage: bil solve <file.bil> [--prover z3|cvc5|vampire|auto] [--subsumes Child Parent] [--emit-smt2]");
                return 1;
            }
            let path = &args[2];
            let mut prover = Prover::Auto;
            let mut subsumes: Option<(String, String)> = None;
            let mut emit_smt2 = false;
            let mut i = 3;
            while i < args.len() {
                match args[i].as_str() {
                    "--prover" | "-p" => match flag_value(args, &mut i).and_then(parse_prover) {
                        Ok(p) => prover = p,
                        Err(code) => return code,
                    },
                    "--subsumes" => {
                        if i + 2 >= args.len() {
                            eprintln!("error: `--subsumes` requires two concept names");
                            return 1;
                        }
                        subsumes = Some((args[i + 1].clone(), args[i + 2].clone()));
                        i += 2;
                    }
                    "--emit-smt2" => emit_smt2 = true,
                    other => return unknown_flag(cmd, other),
                }
                i += 1;
            }
            let Ok(src) = read_source_file(path) else {
                return 1;
            };
            if let Some((child, parent)) = subsumes {
                match prove_subsumption_source(&src, &child, &parent, prover) {
                    Ok(SubsumptionResult::Subsumed { prover: p }) => {
                        println!(
                            "✅ Subsumption PROVED by {}: {} <: {} (refutation unsat)",
                            p, child, parent
                        );
                        0
                    }
                    Ok(SubsumptionResult::NotSubsumed { prover: p, .. }) => {
                        println!(
                            "❌ Subsumption REFUTED by {}: {} is NOT subsumed by {}",
                            p, child, parent
                        );
                        1
                    }
                    Ok(SubsumptionResult::Unknown { detail }) => {
                        println!("⚠️  Subsumption Unknown: {}", detail);
                        0
                    }
                    Err(e) => {
                        eprintln!("{}", e);
                        1
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
                                0
                            }
                            Verdict::Inconsistent => {
                                println!(
                                    "❌ SMT Unsatisfiable (UNSAT) via {} ({} ms) — Logical contradiction detected!",
                                    res.prover, res.elapsed_ms
                                );
                                1
                            }
                            Verdict::Unknown | Verdict::Skipped => {
                                println!("⚠️  SMT Solver Result ({}): {}", res.prover, res.detail);
                                0
                            }
                        }
                    }
                    Err(e) => {
                        eprintln!("{}", e);
                        1
                    }
                }
            }
        }
        "dump-ir" => {
            if args.len() < 3 {
                eprintln!("Usage: bil dump-ir <file.bil> [--level hir|vir|lir|all]");
                return 1;
            }
            let path = &args[2];
            let mut level = "all";
            let mut i = 3;
            while i < args.len() {
                match args[i].as_str() {
                    "--level" => match flag_value(args, &mut i) {
                        Ok(v @ ("hir" | "vir" | "lir" | "all")) => level = v,
                        Ok(v) => {
                            eprintln!(
                                "error: invalid value `{}` for `--level` (expected hir, vir, lir or all)",
                                v
                            );
                            return 1;
                        }
                        Err(code) => return code,
                    },
                    other => return unknown_flag(cmd, other),
                }
                i += 1;
            }
            let Ok(src) = read_source_file(path) else {
                return 1;
            };
            match lower_ir_source(&src) {
                Ok(ir) => {
                    match level {
                        "hir" => print!("{}", ir.hir),
                        "vir" => print!("{}", ir.vir),
                        "lir" => print!("{}", ir.lir),
                        _ => {
                            print!("{}\n{}\n{}", ir.hir, ir.vir, ir.lir);
                        }
                    }
                    0
                }
                Err(e) => {
                    eprintln!("{}", e);
                    1
                }
            }
        }
        "emit-verus" => {
            if args.len() < 3 {
                eprintln!("Usage: bil emit-verus <file.bil>");
                return 1;
            }
            let path = &args[2];
            let Ok(src) = read_source_file(path) else {
                return 1;
            };
            match emit_verus_source(&src) {
                Ok(verus_code) => {
                    print!("{}", verus_code);
                    0
                }
                Err(e) => {
                    eprintln!("{}", e);
                    1
                }
            }
        }
        "import-ontologic" => {
            if args.len() < 3 {
                eprintln!("Usage: bil import-ontologic <file.logic>");
                return 1;
            }
            let path = &args[2];
            let Ok(src) = read_source_file(path) else {
                return 1;
            };
            match transpile_ontologic_sexpr(&src) {
                Ok(bil_code) => {
                    print!("{}", bil_code);
                    0
                }
                Err(e) => {
                    eprintln!("Error importing OntoLogic file: {}", e);
                    1
                }
            }
        }
        "check" | "verify" | "model-check" | "run" | "all" => {
            if args.len() < 3 {
                print_usage();
                return 1;
            }
            let path = &args[2];
            let PipelineOpts {
                seed,
                trace,
                max_states,
                bmc_k,
                json_output,
            } = match parse_pipeline_opts(cmd, args) {
                Ok(opts) => opts,
                Err(code) => return code,
            };

            let Ok(src) = read_source_file(path) else {
                return 1;
            };

            let session = match CompilationSession::from_source(&src) {
                Ok(s) => s,
                Err(e) => {
                    eprintln!("{}", e);
                    return 1;
                }
            };

            if cmd == "check" || cmd == "all" {
                println!(
                    "[OK] OntoLogic DAG & HM Typecheck passed ({} concepts, {} ADTs, {} specs)",
                    session.ontology.concepts.len(),
                    session.tenv.adts.len(),
                    session.tenv.specs.len()
                );
            }

            if cmd == "verify" || cmd == "all" {
                let obligations = session.verify();
                let all_ok = obligations.iter().all(|ob| ob.verified);
                if json_output && cmd == "verify" {
                    if let Ok(js) = serde_json::to_string_pretty(&obligations) {
                        println!("{}", js);
                    }
                } else {
                    println!(
                        "=== Formal Verification (Dijkstra WP, Refinement & SMT Solver): {} obligations ===",
                        obligations.len()
                    );
                    for ob in &obligations {
                        let smt_badge = match (&ob.smt_prover, &ob.smt_verdict, &ob.agreement) {
                            (Some(p), Some(Verdict::Inconsistent), Some(agr)) => {
                                format!(" [SMT {}: refutation UNSAT | Agreement: {}]", p, agr)
                            }
                            (Some(p), Some(v), Some(agr)) => {
                                format!(" [SMT {}: {} | Agreement: {}]", p, v, agr)
                            }
                            _ => String::new(),
                        };
                        println!(
                            "  [{}] fn `{}` — {}{}",
                            ob.status, ob.fn_name, ob.kind, smt_badge
                        );
                        println!("           VC: {}", ob.formula_desc);
                        if let Some(ce) = &ob.counterexample {
                            println!("           Counterexample: {}", ce);
                        }
                    }
                }
                if !all_ok {
                    return 1;
                }
            }

            if cmd == "model-check" || cmd == "all" {
                if let Some(k) = bmc_k {
                    let bmc_reports = session.symbolic_bmc(k, Prover::Auto);
                    let any_unsat_violation = bmc_reports
                        .iter()
                        .any(|r| r.verdict == Verdict::Consistent);
                    if json_output && cmd == "model-check" {
                        if let Ok(js) = serde_json::to_string_pretty(&bmc_reports) {
                            println!("{}", js);
                        }
                    } else {
                        for rep in &bmc_reports {
                            println!(
                                "=== Symbolic Bounded Model Checker (BMC): system `{}` (depth k = {}) ===",
                                rep.system_name, rep.depth_k
                            );
                            if rep.safe_up_to_k {
                                println!(
                                    "  [BMC PROVED SAFE (k={})] Prover `{}` proved no invariant violation up to {} steps (refutation UNSAT).",
                                    rep.depth_k, rep.prover, rep.depth_k
                                );
                            } else if rep.verdict == Verdict::Consistent {
                                println!(
                                    "  [BMC VIOLATION (k={})] Prover `{}` found an invariant violation within {} steps (SAT).",
                                    rep.depth_k, rep.prover, rep.depth_k
                                );
                            } else {
                                println!(
                                    "  [BMC INCONCLUSIVE (k={})] Prover `{}` verdict: {}.",
                                    rep.depth_k, rep.prover, rep.verdict
                                );
                            }
                        }
                    }
                    if any_unsat_violation {
                        return 1;
                    }
                } else {
                    match session.model_check(max_states) {
                        Ok(reports) => {
                            let any_violation = reports.iter().any(|r| !r.violations.is_empty());
                            if json_output && cmd == "model-check" {
                                if let Ok(js) = serde_json::to_string_pretty(&reports) {
                                    println!("{}", js);
                                }
                                if any_violation {
                                    return 1;
                                }
                            } else {
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
                                        return 1;
                                    }
                                }
                            }
                        }
                        Err(e) => {
                            eprintln!("{}", e);
                            return 1;
                        }
                    }
                }
            }

            if cmd == "run" || cmd == "all" {
                match session.run(seed, trace) {
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
                        return 1;
                    }
                }
            }
            0
        }
        _ => {
            print_usage();
            1
        }
    }
}

pub fn run_repl() {
    println!(
        "bil v{} REPL — Enter declarations or expressions (:q to quit)",
        env!("CARGO_PKG_VERSION")
    );
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
            Err(e) => eprintln!("Error: {}", e),
        }
    }
}
