use crate::ast::Program;
use crate::ir::hir::{HirFn, HirProgram, HirSpec, HirSystem};
use crate::ontology::OntologyRegistry;
use crate::types::Type;
use crate::wp::{generate_obligations, ProofObligation};
use std::fmt;

/// Verus-inspired execution & verification stratification mode
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VirMode {
    /// Ghost specification (`axiom`, `spec`, `requires`, `ensures`, `invariant`, `variant`) — erased in LIR
    Spec,
    /// Deductive proof obligation (`wp` VC, `refines`, guard totality `BB`) — discharged at verification time
    Proof,
    /// Executable runtime code (`fn`, `|>` pipelines, state transitions) — lowered to LIR
    Exec,
}

impl fmt::Display for VirMode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VirMode::Spec => write!(f, "ghost(spec)"),
            VirMode::Proof => write!(f, "ghost(proof)"),
            VirMode::Exec => write!(f, "exec"),
        }
    }
}

/// Level 2 IR: Verification & Guarded Transition IR (VIR).
/// Stratifies the program into `Spec` (ghost contracts & axioms), `Proof` (WP & refinement VCs),
/// and `Exec` (verified functions & transition systems).
#[derive(Debug, Clone)]
pub struct VirProgram {
    pub spec_items: Vec<VirSpecItem>,
    pub proof_obligations: Vec<ProofObligation>,
    pub exec_functions: Vec<HirFn>,
    pub transition_systems: Vec<HirSystem>,
}

#[derive(Debug, Clone)]
#[allow(clippy::large_enum_variant)]
pub enum VirSpecItem {
    DomainAxiom {
        name: String,
        ty: Type,
    },
    ContractSpec(HirSpec),
}

impl VirProgram {
    pub fn lower(program: &Program, ontology: &OntologyRegistry, hir: &HirProgram) -> Self {
        let mut spec_items = Vec::new();
        for ax in &hir.axioms {
            spec_items.push(VirSpecItem::DomainAxiom {
                name: ax.name.clone(),
                ty: ax.formula.ty.clone(),
            });
        }
        for sp in &hir.specs {
            spec_items.push(VirSpecItem::ContractSpec(sp.clone()));
        }

        let proof_obligations = generate_obligations(program, ontology);

        VirProgram {
            spec_items,
            proof_obligations,
            exec_functions: hir.functions.clone(),
            transition_systems: hir.systems.clone(),
        }
    }
}

impl fmt::Display for VirProgram {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(
            f,
            "=== Level 2: VIR (Verification & Guarded Transition IR — Spec / Proof / Exec) ==="
        )?;
        for s in &self.spec_items {
            match s {
                VirSpecItem::DomainAxiom { name, ty } => {
                    writeln!(f, "  [{}] axiom {} : {}", VirMode::Spec, name, ty)?;
                }
                VirSpecItem::ContractSpec(sp) => {
                    writeln!(f, "  [{}] spec {} -> {}", VirMode::Spec, sp.name, sp.ret_ty)?;
                }
            }
        }
        for ob in &self.proof_obligations {
            writeln!(
                f,
                "  [{}] fn `{}` :: {} [{}] => {}",
                VirMode::Proof,
                ob.fn_name,
                ob.kind,
                ob.status,
                ob.formula_desc
            )?;
        }
        for func in &self.exec_functions {
            writeln!(
                f,
                "  [{}] fn {} -> {}",
                VirMode::Exec,
                func.name,
                func.ret_ty
            )?;
        }
        for sys in &self.transition_systems {
            writeln!(
                f,
                "  [{}] system {} ({} guarded transitions)",
                VirMode::Exec,
                sys.name,
                sys.transitions.len()
            )?;
        }
        Ok(())
    }
}
