//! This test demonstrates the classic if/else ambiguity in C,
//! which results in a shift-reduce conflict in the LR(1) grammar.

enum Token {
    If,
    Else,
    Var(i32),
    Semi,
    LParen,
    RParen,
}
type Span = ();
enum Expr {
    Var(i32),
}
enum Statement {
    If(Expr, Box<Statement>),
    IfElse(Expr, Box<Statement>, Box<Statement>),
}
#[allow(unused_imports)]
use self::Token::*;
plex::parser! {
    fn parse_(Token, Span);

    statements: Vec<Statement> {
        => vec![],
        statements[mut st] statement[e] Semi => {
            st.push(e);
            st
        }
    }

    statement: Statement {
        // The shift-reduce conflict applies here.
        // To resolve this conflict, add the following attribute, which effectively causes the ambiguity
        // to be resolved in favour of attaching the "else" to the inner "if" statement:
        // #[no_reduce(Else)]
        If LParen expr[head] RParen statement[then] => Statement::If(
            head,
            Box::new(then),
        ),
        If LParen expr[head] RParen statement[then] Else statement[else_] => Statement::IfElse(
            head,
            Box::new(then),
            Box::new(else_),
        ),
    }

    expr: Expr {
        Var(i) => Expr::Var(i),
    }
}

fn main() {
}
