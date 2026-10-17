pub mod hir;
pub mod lir;
pub mod vir;

use crate::ast::Program;
use crate::ontology::OntologyRegistry;
use crate::types::TypeEnv;
use hir::HirProgram;
use lir::LirProgram;
use vir::VirProgram;

#[derive(Debug, Clone)]
pub struct MultiLevelIr {
    pub hir: HirProgram,
    pub vir: VirProgram,
    pub lir: LirProgram,
}

impl MultiLevelIr {
    pub fn build(program: &Program, ontology: &OntologyRegistry, tenv: &mut TypeEnv) -> Self {
        let hir = HirProgram::lower(program, ontology, tenv);
        let vir = VirProgram::lower(program, ontology, &hir);
        let lir = LirProgram::lower_with_ghost_erasure(&hir);
        Self { hir, vir, lir }
    }
}
