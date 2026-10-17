//! Shared identifier interner (`Symbol`) for `O(1)` identifier comparison and compact storage.

use std::collections::BTreeMap;
use std::fmt;
use std::sync::{Mutex, OnceLock};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Symbol(pub u32);

#[derive(Debug, Default, Clone)]
pub struct SymbolInterner {
    to_id: BTreeMap<String, Symbol>,
    to_str: Vec<String>,
}

impl SymbolInterner {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(&mut self, name: &str) -> Symbol {
        if let Some(&sym) = self.to_id.get(name) {
            return sym;
        }
        let sym = Symbol(self.to_str.len() as u32);
        let owned = name.to_string();
        self.to_str.push(owned.clone());
        self.to_id.insert(owned, sym);
        sym
    }

    pub fn get(&self, name: &str) -> Option<Symbol> {
        self.to_id.get(name).copied()
    }

    pub fn resolve(&self, sym: Symbol) -> Option<&str> {
        self.to_str.get(sym.0 as usize).map(String::as_str)
    }

    pub fn len(&self) -> usize {
        self.to_str.len()
    }

    pub fn is_empty(&self) -> bool {
        self.to_str.is_empty()
    }
}

fn global_interner() -> &'static Mutex<SymbolInterner> {
    static INTERNER: OnceLock<Mutex<SymbolInterner>> = OnceLock::new();
    INTERNER.get_or_init(|| Mutex::new(SymbolInterner::new()))
}

impl Symbol {
    pub fn intern(name: &str) -> Self {
        global_interner()
            .lock()
            .expect("SymbolInterner lock poisoned")
            .intern(name)
    }

    pub fn as_str(&self) -> String {
        global_interner()
            .lock()
            .expect("SymbolInterner lock poisoned")
            .resolve(*self)
            .unwrap_or("<invalid-symbol>")
            .to_string()
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.as_str())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_symbol_interner_idempotence_and_resolution() {
        let mut interner = SymbolInterner::new();
        let s1 = interner.intern("Account");
        let s2 = interner.intern("Transaction");
        let s3 = interner.intern("Account");
        assert_eq!(s1, s3);
        assert_ne!(s1, s2);
        assert_eq!(interner.resolve(s1), Some("Account"));
        assert_eq!(interner.resolve(s2), Some("Transaction"));

        let g1 = Symbol::intern("global_ident");
        let g2 = Symbol::intern("global_ident");
        assert_eq!(g1, g2);
        assert_eq!(g1.to_string(), "global_ident");
    }
}
