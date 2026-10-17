use crate::ast::*;
use crate::lexer::Span;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub struct OntologyError {
    pub message: String,
    pub span: Span,
}

impl fmt::Display for OntologyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "[OntologyError at {}] {}", self.span, self.message)
    }
}

#[derive(Debug, Clone)]
pub struct ConceptInfo {
    pub name: String,
    pub parent: Option<String>,
    pub own_fields: Vec<FieldDecl>,
    pub all_fields: BTreeMap<String, TypeExpr>,
    pub span: Span,
}

#[derive(Debug, Clone, Default)]
pub struct OntologyRegistry {
    pub concepts: BTreeMap<String, ConceptInfo>,
}

impl OntologyRegistry {
    pub fn build(program: &Program) -> Result<Self, Vec<OntologyError>> {
        let mut concepts = BTreeMap::new();
        let mut errors = Vec::new();

        for item in &program.items {
            if let Item::Concept(c) = item {
                if concepts.contains_key(&c.name) {
                    errors.push(OntologyError {
                        message: format!("Duplicate concept definition '{}'", c.name),
                        span: c.span,
                    });
                } else {
                    concepts.insert(
                        c.name.clone(),
                        ConceptInfo {
                            name: c.name.clone(),
                            parent: c.parent.clone(),
                            own_fields: c.fields.clone(),
                            all_fields: BTreeMap::new(),
                            span: c.span,
                        },
                    );
                }
            }
        }

        // Verify parent existence and detect DAG cycles (OntoLogic Linter equivalent)
        for (name, info) in &concepts {
            if let Some(parent) = &info.parent {
                if !concepts.contains_key(parent) {
                    errors.push(OntologyError {
                        message: format!(
                            "Concept '{}' inherits from undefined parent concept '{}'",
                            name, parent
                        ),
                        span: info.span,
                    });
                }
            }

            let mut visited = BTreeSet::new();
            let mut curr = info.parent.clone();
            visited.insert(name.clone());
            while let Some(p) = curr {
                if !visited.insert(p.clone()) {
                    errors.push(OntologyError {
                        message: format!(
                            "Circular inheritance detected in concept hierarchy involving '{}'",
                            name
                        ),
                        span: info.span,
                    });
                    break;
                }
                curr = concepts.get(&p).and_then(|ci| ci.parent.clone());
            }
        }

        if !errors.is_empty() {
            return Err(errors);
        }

        // Resolve inherited fields top-down along the concept hierarchy
        let names: Vec<String> = concepts.keys().cloned().collect();
        for name in names {
            let mut chain = Vec::new();
            let mut curr = Some(name.clone());
            while let Some(c) = curr {
                chain.push(c.clone());
                curr = concepts.get(&c).and_then(|ci| ci.parent.clone());
            }
            chain.reverse();

            let mut resolved = BTreeMap::new();
            for ancestor in chain {
                if let Some(anc_info) = concepts.get(&ancestor) {
                    for f in &anc_info.own_fields {
                        resolved.insert(f.name.clone(), f.ty.clone());
                    }
                }
            }
            if let Some(info) = concepts.get_mut(&name) {
                info.all_fields = resolved;
            }
        }

        Ok(Self { concepts })
    }

    /// Returns true if `sub` is `sup` or a transitive subconcept (`sub <: sup`)
    pub fn is_subconcept(&self, sub: &str, sup: &str) -> bool {
        if sub == sup {
            return true;
        }
        let mut curr = self.concepts.get(sub).and_then(|c| c.parent.clone());
        let mut guard = 0;
        while let Some(p) = curr {
            if p == sup {
                return true;
            }
            curr = self.concepts.get(&p).and_then(|c| c.parent.clone());
            guard += 1;
            if guard > self.concepts.len() + 1 {
                break;
            }
        }
        false
    }

    /// Least upper bound (common ancestor) of two concepts in the BFO/OntoLogic taxonomy
    pub fn common_ancestor(&self, a: &str, b: &str) -> Option<String> {
        if self.is_subconcept(a, b) {
            return Some(b.to_string());
        }
        if self.is_subconcept(b, a) {
            return Some(a.to_string());
        }
        let mut curr = self.concepts.get(a).and_then(|c| c.parent.clone());
        while let Some(p) = curr {
            if self.is_subconcept(b, &p) {
                return Some(p);
            }
            curr = self.concepts.get(&p).and_then(|c| c.parent.clone());
        }
        None
    }
}

/// Transpiles OntoLogic S-expression `.logic` files into `.bil` source code
pub fn transpile_ontologic_sexpr(logic_src: &str) -> Result<String, String> {
    let sexprs = parse_sexprs(logic_src)?;
    let mut concepts: Vec<(String, Option<String>)> = Vec::new();
    let mut props: BTreeMap<String, Vec<(String, String)>> = BTreeMap::new();
    let mut prop_domains: BTreeMap<String, String> = BTreeMap::new();
    let mut axioms: Vec<SExpr> = Vec::new();

    for expr in sexprs {
        if let SExpr::List(items) = &expr {
            if items.is_empty() {
                continue;
            }
            match items[0].as_atom() {
                Some("def-concept") => {
                    let name = items
                        .get(1)
                        .and_then(|s| s.as_atom())
                        .ok_or("def-concept missing name")?
                        .to_string();
                    let parent = items
                        .get(2)
                        .and_then(|s| s.as_atom())
                        .map(|s| s.to_string());
                    concepts.push((name, parent));
                }
                Some("def-property") => {
                    let pname = items
                        .get(1)
                        .and_then(|s| s.as_atom())
                        .ok_or("def-property missing name")?
                        .to_string();
                    let domain = items
                        .get(2)
                        .and_then(|s| s.as_atom())
                        .ok_or("def-property missing domain")?
                        .to_string();
                    let range = items
                        .get(3)
                        .and_then(|s| s.as_atom())
                        .ok_or("def-property missing range")?;
                    let bil_ty = match range {
                        "Integer" | "Int" => "Int",
                        "Boolean" | "Bool" => "Bool",
                        "Float" | "Double" => "Float",
                        "String" => "String",
                        other => other,
                    };
                    prop_domains.insert(pname.clone(), domain.clone());
                    props
                        .entry(domain)
                        .or_default()
                        .push((pname, bil_ty.to_string()));
                }
                _ => {
                    axioms.push(expr);
                }
            }
        }
    }

    let mut out = String::new();
    out.push_str("// Auto-imported from OntoLogic (.logic) into bil\n\n");

    let concept_names: BTreeSet<String> = concepts.iter().map(|(n, _)| n.clone()).collect();

    for (name, parent) in &concepts {
        out.push_str(&format!("concept {}", name));
        if let Some(p) = parent {
            out.push_str(&format!(" <: {}", p));
        }
        if let Some(fields) = props.get(name) {
            out.push_str(" {\n");
            for (i, (fname, fty)) in fields.iter().enumerate() {
                let comma = if i + 1 < fields.len() { "," } else { "" };
                out.push_str(&format!("  {}: {}{}\n", fname, fty, comma));
            }
            out.push_str("}\n");
        } else {
            out.push('\n');
        }
    }

    if !axioms.is_empty() {
        out.push('\n');
    }

    for (idx, ax) in axioms.iter().enumerate() {
        let rendered = render_fol_sexpr(ax, &concept_names, &prop_domains, None);
        out.push_str(&format!("axiom OntoAxiom_{}:\n  {}\n\n", idx + 1, rendered));
    }

    Ok(out)
}

#[derive(Debug, Clone)]
enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

impl SExpr {
    fn as_atom(&self) -> Option<&str> {
        match self {
            SExpr::Atom(s) => Some(s.as_str()),
            _ => None,
        }
    }
}

fn parse_sexprs(src: &str) -> Result<Vec<SExpr>, String> {
    let mut tokens = Vec::new();
    let mut chars = src.chars().peekable();
    while let Some(&c) = chars.peek() {
        if c == ';' {
            while let Some(&ch) = chars.peek() {
                chars.next();
                if ch == '\n' {
                    break;
                }
            }
        } else if c.is_whitespace() {
            chars.next();
        } else if c == '(' || c == ')' {
            tokens.push(c.to_string());
            chars.next();
        } else {
            let mut atom = String::new();
            while let Some(&ch) = chars.peek() {
                if ch.is_whitespace() || ch == '(' || ch == ')' || ch == ';' {
                    break;
                }
                atom.push(ch);
                chars.next();
            }
            tokens.push(atom);
        }
    }

    let mut pos = 0;
    let mut out = Vec::new();
    while pos < tokens.len() {
        out.push(parse_one_sexpr(&tokens, &mut pos)?);
    }
    Ok(out)
}

fn parse_one_sexpr(tokens: &[String], pos: &mut usize) -> Result<SExpr, String> {
    if *pos >= tokens.len() {
        return Err("Unexpected EOF in S-expression".into());
    }
    let tok = &tokens[*pos];
    *pos += 1;
    if tok == "(" {
        let mut list = Vec::new();
        while *pos < tokens.len() && tokens[*pos] != ")" {
            list.push(parse_one_sexpr(tokens, pos)?);
        }
        if *pos >= tokens.len() {
            return Err("Unclosed '(' in S-expression".into());
        }
        *pos += 1; // consume ')'
        Ok(SExpr::List(list))
    } else if tok == ")" {
        Err("Unexpected ')'".into())
    } else {
        Ok(SExpr::Atom(tok.clone()))
    }
}

fn render_fol_sexpr(
    sexpr: &SExpr,
    concepts: &BTreeSet<String>,
    prop_domains: &BTreeMap<String, String>,
    bound_var: Option<&str>,
) -> String {
    match sexpr {
        SExpr::Atom(a) => match a.as_str() {
            "True" => "true".to_string(),
            "False" => "false".to_string(),
            _ => {
                if prop_domains.contains_key(a) {
                    if let Some(v) = bound_var {
                        return format!("{}.{}", v, a);
                    }
                }
                a.clone()
            }
        },
        SExpr::List(items) => {
            if items.is_empty() {
                return "true".to_string();
            }
            let head = items[0].as_atom().unwrap_or("");
            match head {
                "forall" | "exists" => {
                    let var = match items.get(1) {
                        Some(SExpr::List(v)) => v.first().and_then(|x| x.as_atom()).unwrap_or("x"),
                        Some(SExpr::Atom(v)) => v.as_str(),
                        None => "x",
                    };
                    let body = items.get(2);
                    // Extract concept domain if body is (implies (Concept var) Q)
                    if let Some(SExpr::List(b_items)) = body {
                        if b_items.first().and_then(|x| x.as_atom()) == Some("implies") {
                            if let Some(SExpr::List(ant)) = b_items.get(1) {
                                if ant.len() == 2 {
                                    if let (Some(cname), Some(vname)) =
                                        (ant[0].as_atom(), ant[1].as_atom())
                                    {
                                        if concepts.contains(cname) && vname == var {
                                            let cons = b_items
                                                .get(2)
                                                .map(|c| {
                                                    render_fol_sexpr(
                                                        c,
                                                        concepts,
                                                        prop_domains,
                                                        Some(var),
                                                    )
                                                })
                                                .unwrap_or_else(|| "true".into());
                                            return format!("{} {} in {} : {}", head, var, cname, cons);
                                        }
                                    }
                                } else if ant.first().and_then(|x| x.as_atom()) == Some("and") {
                                    if let Some(SExpr::List(first_conj)) = ant.get(1) {
                                        if first_conj.len() == 2 {
                                            if let (Some(cname), Some(vname)) =
                                                (first_conj[0].as_atom(), first_conj[1].as_atom())
                                            {
                                                if concepts.contains(cname) && vname == var {
                                                    let rest_ant = ant
                                                        .get(2)
                                                        .map(|c| {
                                                            render_fol_sexpr(
                                                                c,
                                                                concepts,
                                                                prop_domains,
                                                                Some(var),
                                                            )
                                                        })
                                                        .unwrap_or_else(|| "true".into());
                                                    let cons = b_items
                                                        .get(2)
                                                        .map(|c| {
                                                            render_fol_sexpr(
                                                                c,
                                                                concepts,
                                                                prop_domains,
                                                                Some(var),
                                                            )
                                                        })
                                                        .unwrap_or_else(|| "true".into());
                                                    return format!(
                                                        "{} {} in {} : ({} => {})",
                                                        head, var, cname, rest_ant, cons
                                                    );
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        } else if b_items.len() == 2 {
                            if let (Some(cname), Some(vname)) =
                                (b_items[0].as_atom(), b_items[1].as_atom())
                            {
                                if concepts.contains(cname) && vname == var {
                                    return format!("{} {} in {} : true", head, var, cname);
                                }
                            }
                        }
                    }
                    let rendered_body = body
                        .map(|b| render_fol_sexpr(b, concepts, prop_domains, Some(var)))
                        .unwrap_or_else(|| "true".into());
                    format!("{} {} in Entity : {}", head, var, rendered_body)
                }
                "implies" => {
                    let p = items
                        .get(1)
                        .map(|x| render_fol_sexpr(x, concepts, prop_domains, bound_var))
                        .unwrap_or_default();
                    let q = items
                        .get(2)
                        .map(|x| render_fol_sexpr(x, concepts, prop_domains, bound_var))
                        .unwrap_or_default();
                    format!("({} => {})", p, q)
                }
                "iff" => {
                    let p = items
                        .get(1)
                        .map(|x| render_fol_sexpr(x, concepts, prop_domains, bound_var))
                        .unwrap_or_default();
                    let q = items
                        .get(2)
                        .map(|x| render_fol_sexpr(x, concepts, prop_domains, bound_var))
                        .unwrap_or_default();
                    format!("({} <=> {})", p, q)
                }
                "and" => {
                    let p = items
                        .get(1)
                        .map(|x| render_fol_sexpr(x, concepts, prop_domains, bound_var))
                        .unwrap_or_default();
                    let q = items
                        .get(2)
                        .map(|x| render_fol_sexpr(x, concepts, prop_domains, bound_var))
                        .unwrap_or_default();
                    format!("({} && {})", p, q)
                }
                "or" => {
                    let p = items
                        .get(1)
                        .map(|x| render_fol_sexpr(x, concepts, prop_domains, bound_var))
                        .unwrap_or_default();
                    let q = items
                        .get(2)
                        .map(|x| render_fol_sexpr(x, concepts, prop_domains, bound_var))
                        .unwrap_or_default();
                    format!("({} || {})", p, q)
                }
                "not" => {
                    let p = items
                        .get(1)
                        .map(|x| render_fol_sexpr(x, concepts, prop_domains, bound_var))
                        .unwrap_or_default();
                    format!("!({})", p)
                }
                "eq" | "gt" | "lt" | "ge" | "le" => {
                    let op = match head {
                        "eq" => "==",
                        "gt" => ">",
                        "lt" => "<",
                        "ge" => ">=",
                        "le" => "<=",
                        _ => "==",
                    };
                    let lhs = items
                        .get(1)
                        .map(|x| render_fol_sexpr(x, concepts, prop_domains, bound_var))
                        .unwrap_or_default();
                    let rhs = items
                        .get(2)
                        .map(|x| render_fol_sexpr(x, concepts, prop_domains, bound_var))
                        .unwrap_or_default();
                    format!("({} {} {})", lhs, op, rhs)
                }
                _ => {
                    if concepts.contains(head) && items.len() == 2 {
                        let arg = render_fol_sexpr(&items[1], concepts, prop_domains, bound_var);
                        format!("is_a({}, \"{}\")", arg, head)
                    } else {
                        let args: Vec<String> = items[1..]
                            .iter()
                            .map(|x| render_fol_sexpr(x, concepts, prop_domains, bound_var))
                            .collect();
                        format!("{}({})", head, args.join(", "))
                    }
                }
            }
        }
    }
}
