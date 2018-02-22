use syntax::ptr::P;
use syntax::util::ThinVec;
use syntax::util::small_vector::SmallVector;
use syntax::{codemap, ast};
use syntax::ast::Ident;
use syntax::parse::{self, parser, classify, PResult};
use syntax::parse::token;
use syntax::symbol::keywords;
use syntax::ext::base;
use syntax::ext::build::AstBuilder;
use redfa::Dfa;
use redfa::regex::Regex;
use syntax::codemap::DUMMY_SP;
use syntax::ast::DUMMY_NODE_ID;
use syntax::tokenstream::TokenTree;
use std::collections::{BTreeSet, VecDeque};

pub fn dfa_fn<T>(cx: &base::ExtCtxt, dfa: &Dfa<char, T>, state_enum: Ident, state_paths: &[ast::Path], ident: ast::Ident) -> P<ast::Item> {
    let char_ty = quote_ty!(cx, char);
    let state_arg = cx.arg(DUMMY_SP, Ident::from_str("state"), cx.ty_ident(DUMMY_SP, state_enum));
    let char_arg = cx.arg(DUMMY_SP, Ident::from_str("ch"), char_ty.clone());
    let mut arms = Vec::with_capacity(dfa.states.len());
    for (tr, state_name) in dfa.states.iter().zip(state_paths) {
        let mut subarms = Vec::new();
        let mut iter = tr.by_char.iter().peekable();
        while let Some((&ch, &target)) = iter.next() {
            let mut end = ch;
            while let Some(&(&nextc, &nextt)) = iter.peek() {
                if nextc as u32 != (end as u32) + 1 || nextt != target {
                    break;
                }
                end = nextc;
                iter.next();
            }
            let pat = if ch == end {
                cx.pat_lit(DUMMY_SP, cx.expr_lit(DUMMY_SP, ast::LitKind::Char(ch)))
            } else {
                cx.pat(DUMMY_SP, ast::PatKind::Range(
                        cx.expr_lit(DUMMY_SP, ast::LitKind::Char(ch)),
                        cx.expr_lit(DUMMY_SP, ast::LitKind::Char(end)),
                        ast::RangeEnd::Included(ast::RangeSyntax::DotDotDot)
                        ))
            };
            subarms.push(ast::Arm {
                attrs: Vec::new(),
                pats: vec![pat],
                guard: None,
                body: cx.expr_path(state_paths[target as usize].clone()),
                beginning_vert: None,
            });
        }
        subarms.push(cx.arm(DUMMY_SP, vec![quote_pat!(cx, _)], cx.expr_path(state_paths[tr.default as usize].clone())));
        let body = cx.expr_match(DUMMY_SP, quote_expr!(cx, ch), subarms);
        arms.push(quote_arm!(cx, $state_name => $body,));
    }
    let block = cx.block_expr(cx.expr_match(DUMMY_SP, quote_expr!(cx, state), arms));
    cx.item_fn(DUMMY_SP, ident, vec![state_arg, char_arg], cx.ty_ident(DUMMY_SP, state_enum), block)
}

fn parse_str_interior<'a>(parser: &mut parser::Parser<'a>) -> PResult<'a, String> {
    let (re_str, style) = try!(parser.parse_str());
    Ok(match style {
        ast::StrStyle::Cooked => parse::str_lit(&re_str.as_str(), None),
        ast::StrStyle::Raw(_) => parse::raw_str_lit(&re_str.as_str()),
    })
}

fn first_nullable<T>(vec: &[Regex<T>]) -> Option<usize> {
    vec.iter().position(Regex::nullable)
}

pub fn expand_lexer<'cx>(cx: &'cx mut base::ExtCtxt, sp: codemap::Span, args: &[TokenTree]) -> Box<base::MacResult+'cx> {
    parse_lexer(cx, sp, args).unwrap_or_else(|_| base::DummyResult::any(sp))
}

fn dfa_make_names<V>(dfa: &Dfa<char, V>) -> Vec<String> {
    let mut names = vec![String::new(); dfa.states.len()];
    let mut seen = BTreeSet::new();
    seen.insert(0);
    let mut worklist = VecDeque::new();
    worklist.push_back((0, "S_".into()));
    while let Some((i, name)) = worklist.pop_front() {
        for (&c, &next) in &dfa.states[i as usize].by_char {
            if seen.insert(next) {
                let new_name = if c.is_alphanumeric() {
                    format!("{}{}", name, c)
                } else {
                    format!("{}_{:x}_", name, c as u32)
                };
                worklist.push_back((next, new_name));
            }
        }
        let default = dfa.states[i as usize].default;
        if seen.insert(default) {
            let new_name = format!("{}__", name);
            worklist.push_back((default, new_name));
        }
        names[i as usize] = name;
    }
    names
}

fn parse_lexer<'a>(cx: &mut base::ExtCtxt<'a>, sp: codemap::Span, args: &[TokenTree]) -> PResult<'a, Box<base::MacResult+'static>>  {
    let mut parser = cx.new_parser_from_tts(args);

    // first: parse 'fn name_of_lexer(text_variable) -> ResultType;'
    let visibility = if parser.eat_keyword(keywords::Pub) {
        ast::Visibility::Public
    } else {
        ast::Visibility::Inherited
    };
    try!(parser.expect_keyword(keywords::Fn));
    let fn_name = try!(parser.parse_ident());
    try!(parser.expect(&token::OpenDelim(token::Paren)));
    let text_pat = try!(parser.parse_pat());
    let text_lt = if parser.eat(&token::Colon) {
        match parser.token {
            token::Lifetime(ident) => {
                parser.bump();
                (ast::Lifetime {
                    id: ast::DUMMY_NODE_ID,
                    span: parser.prev_span,
                    ident: ident
                })
            }
            _ => {
                parser.expected_tokens.push(parser::TokenType::Lifetime);
                return Err(parser.fatal("expected a lifetime"));
            }
        }
    } else {
        cx.lifetime(DUMMY_SP, Ident::from_str("text"))
    };
    try!(parser.expect(&token::CloseDelim(token::Paren)));
    try!(parser.expect(&token::RArrow));
    let ret_ty = try!(parser.parse_ty());
    try!(parser.expect(&token::Semi));

    // now parse the token arms
    let mut re_vec = Vec::new();
    let mut actions = Vec::new();
    while parser.token != token::Eof {
        // parse '"regex" =>'
        let re_str = try!(parse_str_interior(&mut parser));
        let sp = parser.prev_span;
        let re = match re_str.parse() {
            Ok(r) => r,
            Err(e) => {
                cx.span_err(sp, &*format!("invalid regular expression: {}", e));
                Regex::Null // dummy
            }
        };
        if re.nullable() {
            cx.span_err(sp, "token must not match the empty string");
        }

        try!(parser.expect(&token::FatArrow));

        // start parsing the expr
        let expr = try!(parser.parse_expr_res(parser::Restrictions::STMT_EXPR, None));
        let optional_comma =
            // don't need a comma for blocks...
            !classify::expr_requires_semi_to_be_stmt(&*expr)
            // or for the last arm
            || parser.token == token::Eof;

        if optional_comma {
            // consume optional comma
            parser.eat(&token::Comma);
        } else {
            // comma required
            try!(parser.expect_one_of(&[token::Comma], &[token::CloseDelim(token::Brace)]));
        }

        re_vec.push(re);
        actions.push(expr);
    }

    let (dfa, _) = Dfa::from_derivatives(vec![re_vec]);
    let dfa = dfa.map(|vec| first_nullable(&vec)).minimize().map(|&x| x);
    let error_state_ix = dfa.states.iter().enumerate()
        .position(|(ix, state)| state.value.is_none() && state.by_char.is_empty() && state.default as usize == ix);
    if error_state_ix.is_none() {
        cx.span_warn(sp, "this DFA has no error state; it will always scan the entire input");
    }
    let mut names: Vec<_> = dfa_make_names(&dfa).into_iter().map(|x| Ident::from_str(&x)).collect();
    if let Some(ix) = error_state_ix {
        names[ix] = Ident::from_str("Error");
    }
    let state_enum = Ident::from_str("State");
    let state_paths: Vec<_> = names.iter().map(|name| cx.path(DUMMY_SP, vec![state_enum, *name])).collect();
    let initial_state = &state_paths[0];
    let error_state = error_state_ix.map(|ix| &state_paths[ix]);

    let dfa_transition_fn = Ident::from_str(&*format!("transition"));
    let dfa_acceptance_fn = Ident::from_str(&*format!("accepting"));

    let input = Ident::from_str("input");

    let mut helpers = Vec::new();
    helpers.push(dfa_fn(cx, &dfa, state_enum, &state_paths, dfa_transition_fn));
    helpers.push({
        let mut arms: Vec<_> = dfa.states.iter()
            .map(|state| state.value)
            .zip(&state_paths)
            .filter_map(|(maybe_act, state)| maybe_act.map(|act| {
                let act = act as u32;
                quote_arm!(cx, $state => Some($act),)
            })).collect();
        arms.push(quote_arm!(cx, _ => None,));
        quote_item!(cx, fn $dfa_acceptance_fn(state: $state_enum) -> Option<u32> {
            match state {
                $arms
            }
        }).unwrap()
    });

    let compute_arms: Vec<_> = actions.into_iter().enumerate().map(|(i, expr)| {
        let i = i as u32;
        quote_arm!(cx, $i => $expr,)
    }).collect();
    let compute_result = quote_expr!(cx, match which {
        $compute_arms
        _ => unreachable!(),
    });
    let break_on_error = error_state.map(|state| quote_stmt!(cx,
                                                             if let $state = state {
                                                                 break;
                                                             }).unwrap());
    let final_fn = cx.item_fn_poly(DUMMY_SP,
        fn_name,
        vec![cx.arg(DUMMY_SP, input,
                    cx.ty_rptr(DUMMY_SP,
                               cx.ty_rptr(DUMMY_SP,
                                          cx.ty_ident(DUMMY_SP, Ident::from_str("str")),
                                          Some(text_lt), ast::Mutability::Immutable),
                               None, ast::Mutability::Mutable))],
        quote_ty!(cx, Option<$ret_ty>),
        ast::Generics {
            span: DUMMY_SP,
            params: vec![ast::GenericParam::Lifetime(ast::LifetimeDef {
                attrs: ThinVec::new(),
                lifetime: text_lt,
                bounds: Vec::new(),
            })],
            where_clause: ast::WhereClause {
                id: DUMMY_NODE_ID,
                span: DUMMY_SP,
                predicates: Vec::new(),
            },
        },
        cx.block(DUMMY_SP,
                 Some(cx.stmt_item(DUMMY_SP, cx.item(DUMMY_SP, state_enum, vec![
                     quote_attr!(cx, #[derive(Copy, Clone)]),
                     quote_attr!(cx, #[allow(non_camel_case_types)]),
                 ], ast::ItemKind::Enum(ast::EnumDef {
                     variants: names.iter().map(|&name| cx.variant(DUMMY_SP, name, vec![])).collect()
                 }, ast::Generics::default())))).into_iter()
                 .chain(helpers.into_iter().map(|x| cx.stmt_item(DUMMY_SP, x)))
                 .chain(Some(cx.stmt_expr(quote_expr!(cx, {
                     let mut state = $initial_state;
                     let mut remaining = input.char_indices();
                     let mut last_match = None;
                     loop {
                         if let Some(which) = $dfa_acceptance_fn(state) {
                             last_match = Some((which, remaining.clone()));
                         }
                         $break_on_error
                         if let Some((_, ch)) = remaining.next() {
                             state = $dfa_transition_fn(state, ch);
                         } else {
                             break;
                         }
                     }
                     if let Some((which, mut remaining)) = last_match {
                         let ix = if let Some((ix, _)) = remaining.next() {
                             ix
                         } else {
                             input.len()
                         };
                         let $text_pat = &input[..ix];
                         *input = &input[ix..];
                         Some($compute_result)
                     } else {
                         None
                     }
                 }))))
                 .collect())
    ).map(|mut item| { item.vis = visibility; item });
    Ok(base::MacEager::items(SmallVector::one(final_fn)))
}
