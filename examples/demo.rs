use std::io::Read;

mod lexer {
    use plex::lexer;

    #[derive(Debug, Clone)]
    pub enum Token {
        Ident(String),

        Print,

        Integer(i64),
        Equals,
        Plus,
        Minus,
        Star,
        Slash,
        LParen,
        RParen,
        Semi,

        Whitespace,
        Comment,
    }

    lexer! {
        fn next_token(text: 'a) -> Token;

        r#"[ \t\r\n]+"# => Token::Whitespace,
        // "C-style" comments (/* .. */) - can't contain "*/"
        r#"/[*](~(.*[*]/.*))[*]/"# => Token::Comment,
        // "C++-style" comments (// ...)
        r#"//[^\n]*"# => Token::Comment,

        r#"print"# => Token::Print,

        r#"[0-9]+"# => {
            if let Ok(i) = text.parse() {
                Token::Integer(i)
            } else {
                panic!("integer {} is out of range", text)
            }
        }

        r#"[a-zA-Z_][a-zA-Z0-9_]*"# => Token::Ident(text.to_owned()),

        r#"="# => Token::Equals,
        r#"\+"# => Token::Plus,
        r#"-"# => Token::Minus,
        r#"\*"# => Token::Star,
        r#"/"# => Token::Slash,
        r#"\("# => Token::LParen,
        r#"\)"# => Token::RParen,
        r#";"# => Token::Semi,

        r#"."# => panic!("unexpected character: {}", text),
    }

    pub struct Lexer<'a> {
        original: &'a str,
        remaining: &'a str,
    }

    impl<'a> Lexer<'a> {
        pub fn new(s: &'a str) -> Lexer<'a> {
            Lexer {
                original: s,
                remaining: s,
            }
        }
    }

    #[derive(Debug, Clone, Copy)]
    pub struct Span {
        pub lo: usize,
        pub hi: usize,
    }

    impl<'a> Iterator for Lexer<'a> {
        type Item = (Token, Span);
        fn next(&mut self) -> Option<(Token, Span)> {
            loop {
                let (tok, span) = if let Some((tok, new_remaining)) = next_token(self.remaining) {
                    let lo = self.original.len() - self.remaining.len();
                    let hi = self.original.len() - new_remaining.len();
                    self.remaining = new_remaining;
                    (tok, Span { lo, hi })
                } else {
                    return None;
                };
                match tok {
                    Token::Whitespace | Token::Comment => {
                        continue;
                    }
                    tok => {
                        return Some((tok, span));
                    }
                }
            }
        }
    }
}

mod ast {
    use crate::lexer::Span;

    #[derive(Debug)]
    pub struct Program {
        pub stmts: Vec<Expr>,
    }

    #[derive(Debug)]
    pub struct Expr {
        pub span: Span,
        pub node: Expr_,
    }

    #[derive(Debug)]
    pub enum Expr_ {
        Add(Box<Expr>, Box<Expr>),
        Sub(Box<Expr>, Box<Expr>),
        Mul(Box<Expr>, Box<Expr>),
        Div(Box<Expr>, Box<Expr>),
        Var(String),
        Assign(String, Box<Expr>),
        Print(Box<Expr>),
        Literal(i64),
    }
}

mod parser {
    use crate::ast::*;
    use crate::lexer::Token::*;
    use crate::lexer::*;
    use plex::parser;
    parser! {
        fn parse_(Token, Span);

        // combine two spans
        (a, b) {
            Span {
                lo: a.lo,
                hi: b.hi,
            }
        }

        program: Program {
            statements[s] => Program { stmts: s }
        }

        statements: Vec<Expr> {
            => vec![],
            statements[mut st] assign[e] Semi => {
                st.push(e);
                st
            }
        }

        assign: Expr {
            Print assign[a] => Expr {
                span: span!(),
                node: Expr_::Print(Box::new(a)),
            },
            Ident(var) Equals assign[rhs] => Expr {
                span: span!(),
                node: Expr_::Assign(var, Box::new(rhs)),
            },
            term[t] => t,
        }

        term: Expr {
            term[lhs] Plus fact[rhs] => Expr {
                span: span!(),
                node: Expr_::Add(Box::new(lhs), Box::new(rhs)),
            },
            term[lhs] Minus fact[rhs] => Expr {
                span: span!(),
                node: Expr_::Sub(Box::new(lhs), Box::new(rhs)),
            },
            fact[x] => x
        }

        fact: Expr {
            fact[lhs] Star atom[rhs] => Expr {
                span: span!(),
                node: Expr_::Mul(Box::new(lhs), Box::new(rhs)),
            },
            fact[lhs] Slash atom[rhs] => Expr {
                span: span!(),
                node: Expr_::Div(Box::new(lhs), Box::new(rhs)),
            },
            atom[x] => x
        }

        atom: Expr {
            // round brackets to destructure tokens
            Ident(i) => Expr {
                span: span!(),
                node: Expr_::Var(i),
            },
            Integer(i) => Expr {
                span: span!(),
                node: Expr_::Literal(i),
            },
            LParen assign[a] RParen => a
        }
    }

    pub fn parse<I: Iterator<Item = (Token, Span)>>(
        i: I,
    ) -> Result<Program, (Option<(Token, Span)>, &'static str)> {
        parse_(i)
    }
}

mod interp {
    use crate::ast::*;
    use std::collections::HashMap;

    pub fn interp<'a>(p: &'a Program) {
        let mut env = HashMap::new();
        for expr in &p.stmts {
            interp_expr(&mut env, expr);
        }
    }
    fn interp_expr<'a>(env: &mut HashMap<&'a str, i64>, expr: &'a Expr) -> i64 {
        use crate::ast::Expr_::*;
        match expr.node {
            Add(ref a, ref b) => interp_expr(env, a) + interp_expr(env, b),
            Sub(ref a, ref b) => interp_expr(env, a) - interp_expr(env, b),
            Mul(ref a, ref b) => interp_expr(env, a) * interp_expr(env, b),
            Div(ref a, ref b) => interp_expr(env, a) / interp_expr(env, b),
            Assign(ref var, ref b) => {
                let val = interp_expr(env, b);
                env.insert(var, val);
                val
            }
            Var(ref var) => *env.get(&var[..]).unwrap(),
            Literal(lit) => lit,
            Print(ref e) => {
                let val = interp_expr(env, e);
                println!("{}", val);
                val
            }
        }
    }
}

fn main() {
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    let lexer = lexer::Lexer::new(&s).inspect(|tok| eprintln!("tok: {:?}", tok));
    let program = parser::parse(lexer).unwrap();
    interp::interp(&program);
}
