//! This test demonstrates a reduce-reduce conflict.

enum Token {
    Lit(i32),
    Var(i32),
    Minus,
}
type Span = ();
enum Expr {
    Lit(i32),
    Var(i32),
    Negate(Box<Expr>),
}
#[allow(unused_imports)]
use self::Token::*;
plex::parser! {
    fn parse_(Token, Span);

    expr: Expr {
        Var(i) => Expr::Var(i),
        Lit(i) => Expr::Lit(i),
        // These rules induce a reduce-reduce conflict.
        // The intent here is to create a special case where `Minus` followed by a `Lit` is parsed as a negative literal,
        // rather than a negation expression.
        // To implement that, use the attribute:
        // #[overriding]
        Minus Lit(i) => Expr::Lit(-i),
        Minus expr[e] => Expr::Negate(Box::new(e)),
    }
}

fn main() {}
