//! Per-expression source spans: type errors point at the offending subexpression, and the
//! parser's span table lines up node-for-node with `Program::for_each_expr_postorder`.

use bil::ast::Expr;
use bil::{check_source, parse_source};

fn text_at(src: &str, line: usize, col: usize) -> String {
    src.lines()
        .nth(line - 1)
        .map(|l| l.chars().skip(col - 1).collect())
        .unwrap_or_default()
}

/// Every node gets exactly one span, in walk order, and leaf spans point at their own text.
fn assert_spans_align(label: &str, src: &str) {
    let program = parse_source(src).unwrap_or_else(|e| panic!("{label}: {e}"));
    let mut nodes = Vec::new();
    program.for_each_expr_postorder(&mut |e| nodes.push(e.clone()));
    assert_eq!(
        program.expr_spans.len(),
        nodes.len(),
        "{label}: span table and expression walk disagree on node count"
    );
    for (node, span) in nodes.iter().zip(&program.expr_spans) {
        let text = text_at(src, span.line, span.col);
        let ok = match node {
            // A `do … od` without `then` yields its first loop variable, spanned at `od`.
            Expr::Var(name) => text.starts_with(name.as_str()) || text.starts_with("od"),
            Expr::Int(v) => text.starts_with(&v.to_string()),
            Expr::Bool(b) => text.starts_with(&b.to_string()),
            Expr::Str(_) => text.starts_with('"'),
            Expr::Call { func, .. } => text.starts_with(func.as_str()),
            Expr::RecordInit { concept, .. } => text.starts_with(concept.as_str()),
            Expr::IfFi { .. } => text.starts_with("if"),
            Expr::DoOd { .. } => text.starts_with("do"),
            Expr::Match { .. } => text.starts_with("match"),
            Expr::LetIn { .. } => text.starts_with("let"),
            Expr::FieldAccess { .. } => text.starts_with('.'),
            Expr::RecordWith { .. } => text.starts_with("with"),
            _ => !text.is_empty(),
        };
        assert!(
            ok,
            "{label}: {node:?} spanned at {}:{} which reads {text:?}",
            span.line, span.col
        );
    }
}

#[test]
fn span_table_aligns_with_every_example() {
    for dir in ["examples", "examples/domains", "examples/domains/seeded_bugs"] {
        for entry in std::fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.extension().is_some_and(|x| x == "bil") {
                let src = std::fs::read_to_string(&path).unwrap();
                assert_spans_align(&path.display().to_string(), &src);
            }
        }
    }
}

#[test]
fn span_table_aligns_for_interleaved_system_members_and_binders() {
    // System members are parsed in source order but stored grouped by kind, and the
    // `variant` clause is given twice (the last one wins).
    let src = r#"
concept Box { w: Int }
type Opt = Some(Int) | None

system S {
  state a: Int = 0
  invariant ia: a >= 0
  variant: 10 - a
  state b: Bool = true
  transition
     a < 3 -> a := a + 1
  [] b -> b := false, a := 0
  temporal t: (a == 1) ~> (a == 2)
  variant: 9 - a
  terminal: a == 3
  invariant ib: b || a > 0
}

fn loop_no_then(n: Int) -> Int
  requires n >= 0
  ensures result >= 0
=
  do i = n, j = 0 invariant i >= 0 variant i : i > 0 -> i := i - 1, j := j + 1 od

fn shapes(o: Opt, x: Int) -> Int =
  let r = Box { w: x } with { w: x + 1 } in
  match o { Some(v) -> v + r.w | None -> 0 }

axiom ax: forall k in 1..=3 : exists m in [1, 2, 3] : m >= k
let g = shapes(Some(2), 4) + loop_no_then(3)
assert g > 0
"#;
    assert_spans_align("inline", src);
}

#[test]
fn type_error_points_at_the_offending_subexpression() {
    let src = "fn f(x: Int) -> Int
  requires true
  ensures true
=
  let a = x + 1 in
  let b = a * 2 in
  let c = b + true in
  c
";
    let err = check_source(src).expect_err("Int + Bool must not type-check");
    assert!(
        err.contains("at 7:13"),
        "expected the `+` on line 7, got: {err}"
    );
}

#[test]
fn type_errors_in_contracts_and_system_members_are_located() {
    let src = "fn g(x: Int) -> Int
  requires x > 0
  ensures result + false
= x
";
    let err = check_source(src).expect_err("ensures Int + Bool");
    assert!(
        err.contains("at 3:18"),
        "expected the `+` on line 3, got: {err}"
    );

    let src = "system T {
  state n: Int = 0
  invariant ok: n >= 0
  transition
     n < 2 -> n := n + true
}
";
    let err = check_source(src).expect_err("update Int + Bool");
    assert!(
        err.contains("at 5:22"),
        "expected the `+` on line 5, got: {err}"
    );
}
