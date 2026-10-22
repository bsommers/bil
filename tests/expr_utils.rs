//! Free-variable and capture-avoiding substitution laws for every `Expr` variant.
//!
//! For any `e`, variable `x` and replacement `r`:
//!   fv(e[x := r]) = (fv(e) \ {x}) ∪ fv(r)   if x ∈ fv(e)
//!   fv(e[x := r]) = fv(e)                   otherwise
//! A binder that captures a free variable of `r` breaks the first equation.

use bil::ast::{BinOp, Expr, GclBody, GuardedBranch, MatchArm, Pattern, QuantifierKind, UnaryOp};
use bil::expr_utils::{free_vars, subst_expr};
use std::collections::{BTreeMap, BTreeSet};

fn v(name: &str) -> Expr {
    Expr::Var(name.into())
}

fn add(l: Expr, r: Expr) -> Expr {
    Expr::Binary {
        op: BinOp::Add,
        left: Box::new(l),
        right: Box::new(r),
    }
}

fn set(names: &[&str]) -> BTreeSet<String> {
    names.iter().map(|s| s.to_string()).collect()
}

fn subst1(e: &Expr, x: &str, r: &Expr) -> Expr {
    let mut m = BTreeMap::new();
    m.insert(x.to_string(), r.clone());
    subst_expr(e, &m)
}

fn assert_subst_law(label: &str, e: &Expr, x: &str, r: &Expr) {
    let fv = free_vars(e);
    let expected: BTreeSet<String> = if fv.contains(x) {
        fv.iter()
            .filter(|n| n.as_str() != x)
            .cloned()
            .chain(free_vars(r))
            .collect()
    } else {
        fv.clone()
    };
    let out = subst1(e, x, r);
    assert_eq!(
        free_vars(&out),
        expected,
        "{label}: fv({e:?}[{x} := {r:?}]) = fv({out:?})"
    );
}

/// One expression per `Expr` variant (and per binder form), each mentioning `x` free,
/// and where a binder exists, binding `y` so that `x := y` would be captured.
fn corpus() -> Vec<(&'static str, Expr)> {
    vec![
        ("var", v("x")),
        ("int", Expr::Int(1)),
        ("float", Expr::Float(1.5)),
        ("bool", Expr::Bool(true)),
        ("str", Expr::Str("s".into())),
        ("placeholder", Expr::Placeholder),
        (
            "unary",
            Expr::Unary {
                op: UnaryOp::Neg,
                expr: Box::new(v("x")),
            },
        ),
        ("binary", add(v("x"), v("z"))),
        (
            "forall binds y",
            Expr::Quantifier {
                kind: QuantifierKind::Forall,
                var: "y".into(),
                domain: Box::new(v("d")),
                body: Box::new(add(v("x"), v("y"))),
            },
        ),
        (
            "exists shadows x",
            Expr::Quantifier {
                kind: QuantifierKind::Exists,
                var: "x".into(),
                domain: Box::new(v("x")),
                body: Box::new(add(v("x"), v("z"))),
            },
        ),
        (
            "if-fi expr and updates",
            Expr::IfFi {
                branches: vec![
                    GuardedBranch {
                        guard: v("x"),
                        body: GclBody::Expr(v("z")),
                    },
                    GuardedBranch {
                        guard: v("g"),
                        body: GclBody::Updates(vec![("s".into(), v("x"))]),
                    },
                    GuardedBranch {
                        guard: v("h"),
                        body: GclBody::Skip,
                    },
                ],
            },
        ),
        (
            "do-od binds y",
            Expr::DoOd {
                inits: vec![("y".into(), Expr::Int(0))],
                invariant: Some(Box::new(add(v("x"), v("y")))),
                variant: Some(Box::new(v("y"))),
                branches: vec![GuardedBranch {
                    guard: add(v("y"), v("x")),
                    body: GclBody::Updates(vec![("y".into(), add(v("y"), v("x")))]),
                }],
                then_expr: Box::new(add(v("y"), v("x"))),
            },
        ),
        (
            "do-od shadows x after its init",
            Expr::DoOd {
                inits: vec![("x".into(), v("x"))],
                invariant: None,
                variant: None,
                branches: vec![GuardedBranch {
                    guard: v("x"),
                    body: GclBody::Expr(v("x")),
                }],
                then_expr: Box::new(v("x")),
            },
        ),
        (
            "match var pattern binds y",
            Expr::Match {
                scrutinee: Box::new(v("s")),
                arms: vec![MatchArm {
                    pattern: Pattern::Var("y".into()),
                    body: add(v("x"), v("y")),
                }],
            },
        ),
        (
            "match variant pattern binds y",
            Expr::Match {
                scrutinee: Box::new(v("x")),
                arms: vec![
                    MatchArm {
                        pattern: Pattern::Variant("Some".into(), vec!["y".into(), "_".into()]),
                        body: add(v("x"), v("y")),
                    },
                    MatchArm {
                        pattern: Pattern::Wildcard,
                        body: v("x"),
                    },
                ],
            },
        ),
        (
            "match arm shadows x",
            Expr::Match {
                scrutinee: Box::new(v("s")),
                arms: vec![MatchArm {
                    pattern: Pattern::Variant("Some".into(), vec!["x".into()]),
                    body: v("x"),
                }],
            },
        ),
        (
            "record init",
            Expr::RecordInit {
                concept: "P".into(),
                fields: vec![("a".into(), v("x")), ("b".into(), v("z"))],
            },
        ),
        (
            "record with",
            Expr::RecordWith {
                base: Box::new(v("r")),
                updates: vec![("a".into(), v("x"))],
            },
        ),
        (
            "field access",
            Expr::FieldAccess {
                base: Box::new(v("x")),
                field: "a".into(),
            },
        ),
        (
            "call",
            Expr::Call {
                func: "f".into(),
                args: vec![v("x"), v("z")],
            },
        ),
        ("list", Expr::List(vec![v("x"), Expr::Int(2)])),
        (
            "let binds y",
            Expr::LetIn {
                name: "y".into(),
                value: Box::new(v("x")),
                body: Box::new(add(v("x"), v("y"))),
            },
        ),
        (
            "let shadows x",
            Expr::LetIn {
                name: "x".into(),
                value: Box::new(v("x")),
                body: Box::new(v("x")),
            },
        ),
    ]
}

#[test]
fn free_vars_respects_every_binder() {
    let expect: BTreeMap<&str, BTreeSet<String>> = [
        ("var", set(&["x"])),
        ("int", set(&[])),
        ("unary", set(&["x"])),
        ("binary", set(&["x", "z"])),
        ("forall binds y", set(&["d", "x"])),
        ("exists shadows x", set(&["x", "z"])), // the domain's x is outside the binder
        ("if-fi expr and updates", set(&["g", "h", "x", "z"])),
        ("do-od binds y", set(&["x"])),
        ("do-od shadows x after its init", set(&["x"])),
        ("match var pattern binds y", set(&["s", "x"])),
        ("match variant pattern binds y", set(&["x"])),
        ("match arm shadows x", set(&["s"])),
        ("record init", set(&["x", "z"])),
        ("record with", set(&["r", "x"])),
        ("field access", set(&["x"])),
        ("call", set(&["x", "z"])),
        ("list", set(&["x"])),
        ("let binds y", set(&["x"])),
        ("let shadows x", set(&["x"])),
    ]
    .into_iter()
    .collect();
    for (label, e) in corpus() {
        if let Some(want) = expect.get(label) {
            assert_eq!(&free_vars(&e), want, "{label}: {e:?}");
        }
    }
}

#[test]
fn subst_obeys_free_variable_law_for_every_variant() {
    // y is bound somewhere in most of the corpus, so x := y exercises capture avoidance;
    // x := y + w also brings in a variable no binder mentions.
    let replacements = [v("y"), add(v("y"), v("w")), Expr::Int(7)];
    for (label, e) in corpus() {
        for r in &replacements {
            assert_subst_law(label, &e, "x", r);
            // Substituting a variable that is not free must not change the free set.
            assert_subst_law(label, &e, "absent", r);
        }
    }
}

#[test]
fn subst_renames_match_binder_instead_of_capturing() {
    // match s { Some(y) -> x + y }  with x := y  must not become  Some(y) -> y + y
    let e = Expr::Match {
        scrutinee: Box::new(v("s")),
        arms: vec![MatchArm {
            pattern: Pattern::Variant("Some".into(), vec!["y".into()]),
            body: add(v("x"), v("y")),
        }],
    };
    let out = subst1(&e, "x", &v("y"));
    let Expr::Match { arms, .. } = &out else {
        panic!("{out:?}")
    };
    let Pattern::Variant(_, binds) = &arms[0].pattern else {
        panic!("{out:?}")
    };
    assert_ne!(binds[0], "y", "binder was not renamed: {out:?}");
    assert_eq!(arms[0].body, add(v("y"), v(&binds[0])), "{out:?}");
}

#[test]
fn subst_renames_do_od_loop_variable_including_update_targets() {
    // do y = 0 : y < x -> y := y + 1 od then y   with x := y
    let e = Expr::DoOd {
        inits: vec![("y".into(), Expr::Int(0))],
        invariant: None,
        variant: None,
        branches: vec![GuardedBranch {
            guard: Expr::Binary {
                op: BinOp::Lt,
                left: Box::new(v("y")),
                right: Box::new(v("x")),
            },
            body: GclBody::Updates(vec![("y".into(), add(v("y"), Expr::Int(1)))]),
        }],
        then_expr: Box::new(v("y")),
    };
    let out = subst1(&e, "x", &v("y"));
    let Expr::DoOd {
        inits,
        branches,
        then_expr,
        ..
    } = &out
    else {
        panic!("{out:?}")
    };
    let fresh = inits[0].0.clone();
    assert_ne!(fresh, "y", "loop variable was not renamed: {out:?}");
    assert_eq!(
        branches[0].guard,
        Expr::Binary {
            op: BinOp::Lt,
            left: Box::new(v(&fresh)),
            right: Box::new(v("y")),
        }
    );
    assert_eq!(
        branches[0].body,
        GclBody::Updates(vec![(fresh.clone(), add(v(&fresh), Expr::Int(1)))])
    );
    assert_eq!(**then_expr, v(&fresh));
}

#[test]
fn field_access_over_record_update_projects_the_updated_field() {
    let r_with = |field: &str| Expr::FieldAccess {
        base: Box::new(Expr::RecordWith {
            base: Box::new(v("r")),
            updates: vec![("a".into(), v("x")), ("a".into(), v("z"))],
        }),
        field: field.into(),
    };
    let mut m = BTreeMap::new();
    m.insert("q".to_string(), Expr::Int(0));
    // The last update to a field wins.
    assert_eq!(subst_expr(&r_with("a"), &m), v("z"));
    // Other fields read through to the base record.
    assert_eq!(
        subst_expr(&r_with("b"), &m),
        Expr::FieldAccess {
            base: Box::new(v("r")),
            field: "b".into()
        }
    );
    // A record literal projects its field directly.
    let lit = Expr::FieldAccess {
        base: Box::new(Expr::RecordInit {
            concept: "P".into(),
            fields: vec![("a".into(), v("x"))],
        }),
        field: "a".into(),
    };
    assert_eq!(subst1(&lit, "x", &Expr::Int(3)), Expr::Int(3));
}
