#![feature(plugin)]
#![plugin(plex)]

extern crate serde_json;

use std::io::Read;

mod lexer {
    use std::char;

    #[derive(Debug, Clone)]
    pub enum Token {
        LBrace,
        RBrace,
        LBracket,
        RBracket,
        Colon,
        Comma,
        Null,
        Bool(bool),
        I64(i64),
        U64(u64),
        F64(f64),
        Str(String),
        Whitespace,
        Error(String),
    }

    fn parse_escape<'a>(s: &'a str) -> (u16, &'a str) {
        let mut it = s.chars();
        let backslash = it.next();
        debug_assert!(backslash == Some('\\'));
        let c = match it.next().expect("impossible: dangling escape") {
            '\\' => '\\',
            '/' => '/',
            '"' => '"',
            'b' => '\x08',
            'f' => '\x0c',
            'n' => '\n',
            'r' => '\r',
            't' => '\t',
            'u' => {
                let (hex, rest) = it.as_str().split_at(4);
                return (u16::from_str_radix(hex, 16).expect("impossible: invalid hex escape"), rest);
            },
            x => panic!("impossible: unknown escape char {}", x),
        };
        (c as u16, it.as_str())
    }

    fn unescape_string(mut escaped: &str) -> Result<String, String> {
        let mut unescaped = String::with_capacity(escaped.len());
        while let Some(index) = escaped.find('\\') {
            let (prefix, escape) = escaped.split_at(index);
            unescaped.push_str(prefix);
            let (escaped_codepoint, rest) = parse_escape(escape);
            if escaped_codepoint & 0xFC00 == 0xD800 {
                if !rest.starts_with("\\u") {
                    return Err("unpaired surrogate".into());
                }
                let (next_codepoint, rest) = parse_escape(rest);
                if next_codepoint & 0xFC00 != 0xDC00 {
                    return Err("unpaired surrogate".into());
                }
                let cp = ((escaped_codepoint & 0x3FF) as u32) << 10 | ((next_codepoint & 0x3FF) as u32);
                if let Some(c) = char::from_u32(cp) {
                    unescaped.push(c);
                } else {
                    return Err(format!("invalid Unicode codepoint: \\u{:4x}", escaped_codepoint));
                }
                escaped = rest;
            } else if let Some(c) = char::from_u32(escaped_codepoint as u32) {
                unescaped.push(c);
                escaped = rest;
            } else {
                return Err(format!("invalid Unicode codepoint: \\u{:4x}", escaped_codepoint));
            }
        }
        unescaped.push_str(escaped);
        Ok(unescaped)
    }

    lexer! {
        fn next_token(text: 'a) -> Token;

        r#"[ \t\r\n]+"# => Token::Whitespace,
        // integers
        r#"-?(0|[1-9][0-9]*)"# => {
            if let Ok(num) = text.parse() {
                Token::I64(num)
            } else if let Ok(num) = text.parse() {
                Token::U64(num)
            } else if let Ok(num) = text.parse() {
                // possible loss of precision... ok?
                Token::F64(num)
            } else {
                Token::Error(format!("integer {} is out of range", text))
            }
        },
        // all numbers
        r#"-?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][-+]?[0-9]+)?"# => {
            if let Ok(num) = text.parse() {
                Token::F64(num)
            } else {
                Token::Error(format!("integer {} is out of range", text))
            }
        },
        r#""(\\(["\\/bfnrt]|u[0-9a-fA-F][0-9a-fA-F][0-9a-fA-F][0-9a-fA-F])|[^\\"])*""# => {
            match unescape_string(&text[1..(text.len()-1)]) {
                Ok(s) => Token::Str(s),
                Err(s) => Token::Error(s),
            }
        }

        r#"{"# => Token::LBrace,
        r#"}"# => Token::RBrace,
        r#"\["# => Token::LBracket,
        r#"\]"# => Token::RBracket,
        r#":"# => Token::Colon,
        r#","# => Token::Comma,

        r#"null"# => Token::Null,
        r#"true"# => Token::Bool(true),
        r#"false"# => Token::Bool(false),

        r#"."# => Token::Error(format!("unexpected character: {}", text)),
    }

    pub struct Lexer<'a> {
        remaining: &'a str,
    }

    impl<'a> Lexer<'a> {
        pub fn new(s: &'a str) -> Lexer<'a> {
            Lexer { remaining: s }
        }
    }

    impl<'a> Iterator for Lexer<'a> {
        type Item = Token;
        fn next(&mut self) -> Option<Token> {
            loop {
                let tok = if let Some(tok) = next_token(&mut self.remaining) {
                    tok
                } else {
                    return None
                };
                match tok {
                    Token::Whitespace => {
                        continue;
                    }
                    tok => {
                        return Some(tok);
                    }
                }
            }
        }
    }
}

mod parser {
    use serde_json::value::{Value, Map};
    use ::lexer::Token::*;
    use ::lexer::*;
    parser! {
        fn parse_(Token, ());

        value: Value {
            Null => Value::Null,
            Bool(b) => Value::Bool(b),
            I64(n) => Value::I64(n),
            U64(n) => Value::U64(n),
            F64(n) => Value::F64(n),
            Str(s) => Value::String(s),
            LBracket RBracket => Value::Array(vec![]),
            LBracket values[vals] RBracket => Value::Array(vals),
            LBrace RBrace => Value::Object(Map::new()),
            LBrace pairs[vals] RBrace => Value::Object(vals),
        }

        values: Vec<Value> {
            value[v] => vec![v],
            values[mut vs] Comma value[v] => {
                vs.push(v);
                vs
            }
        }

        pairs: Map<String, Value> {
            Str(k) Colon value[v] => {
                let mut m = Map::new();
                m.insert(k, v);
                m
            }
            pairs[mut m] Comma Str(k) Colon value[v] => {
                m.insert(k, v);
                m
            }
        }
    }

    pub fn parse<I: Iterator<Item=Token>>(i: I) -> Result<Value, (Option<Token>, &'static str)> {
        parse_(i.map(|x| (x, ()))).map_err(|(tok, expected)| (tok.map(|(tok, ())| tok), expected))
    }
}

fn main() {
    let mut s = String::new();
    std::io::stdin().read_to_string(&mut s).unwrap();
    let lexer = lexer::Lexer::new(&s);
    match parser::parse(lexer) {
        Err((Some(lexer::Token::Error(s)), _)) => {
            println!("Lexer error: {}", s);
        }
        Err((Some(tok), msg)) => {
            println!("Parse error: {}, but got {:?}", msg, tok);
        }
        Err((None, msg)) => {
            println!("Parse error: {}, but got EOF", msg);
        }
        Ok(json) => {
            println!("{}", json);
        }
    }
}
