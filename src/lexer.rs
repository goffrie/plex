use syntax::ptr::P;
use syntax::util::small_vector::SmallVector;
use syntax::{codemap, ast, owned_slice};
use syntax::parse::{self, parser, token, classify, PResult};
use syntax::ext::base;
use syntax::ext::build::AstBuilder;
use regex_dfa::Dfa;
use regex_dfa::regex::Regex;
use syntax::codemap::DUMMY_SP;
use syntax::ast::DUMMY_NODE_ID;

fn expr_u32(cx: &base::ExtCtxt, u: u32) -> P<ast::Expr> {
    cx.expr_lit(DUMMY_SP, ast::LitInt(u as u64, ast::UnsignedIntLit(ast::TyU32)))
}

pub fn dfa_fn<T>(cx: &base::ExtCtxt, dfa: &Dfa<char, T>, ident: ast::Ident) -> P<ast::Item> {
    let u32_ty = quote_ty!(cx, u32);
    let char_ty = quote_ty!(cx, char);
    let state_arg = cx.arg(DUMMY_SP, token::str_to_ident("state"), u32_ty.clone());
    let char_arg = cx.arg(DUMMY_SP, token::str_to_ident("ch"), char_ty.clone());
    let mut arms = Vec::with_capacity(dfa.states.len());
    for (i, tr) in dfa.states.iter().enumerate() {
        let arm_pat = cx.pat_lit(DUMMY_SP, expr_u32(cx, i as u32));
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
                cx.pat_lit(DUMMY_SP, cx.expr_lit(DUMMY_SP, ast::LitChar(ch)))
            } else {
                cx.pat(DUMMY_SP, ast::PatRange(
                        cx.expr_lit(DUMMY_SP, ast::LitChar(ch)),
                        cx.expr_lit(DUMMY_SP, ast::LitChar(end))
                        ))
            };
            subarms.push(ast::Arm {
                attrs: Vec::new(),
                pats: vec![pat],
                guard: None,
                body: expr_u32(cx, target as u32),
            });
        }
        subarms.push(cx.arm(DUMMY_SP, vec![quote_pat!(cx, _)], expr_u32(cx, tr.default as u32)));
        let body = cx.expr_match(DUMMY_SP, quote_expr!(cx, ch), subarms);
        arms.push(cx.arm(DUMMY_SP, vec![arm_pat], body));
    }
    arms.push(quote_arm!(cx, _ => state,));
    let block = cx.block(DUMMY_SP, vec![], Some(cx.expr_match(DUMMY_SP, quote_expr!(cx, state), arms)));
    cx.item_fn(DUMMY_SP, ident, vec![state_arg, char_arg], u32_ty.clone(), block)
}

fn parse_str_interior(parser: &mut parser::Parser) -> PResult<String> {
    let (re_str, style) = try!(parser.parse_str());
    Ok(match style {
        ast::CookedStr => parse::str_lit(&re_str),
        ast::RawStr(_) => parse::raw_str_lit(&re_str),
    })
}

fn first_nullable<T>(vec: &[Regex<T>]) -> Option<usize> {
    vec.iter().position(Regex::nullable)
}

pub fn expand_lexer<'cx>(cx: &'cx mut base::ExtCtxt, sp: codemap::Span, args: &[ast::TokenTree]) -> Box<base::MacResult+'cx> {
    parse_lexer(cx, sp, args).unwrap_or_else(|_| base::DummyResult::any(sp))
}

fn parse_lexer(cx: &mut base::ExtCtxt, sp: codemap::Span, args: &[ast::TokenTree]) -> PResult<Box<base::MacResult+'static>>  {
    let mut parser = cx.new_parser_from_tts(args);

    // first: parse 'fn name_of_lexer(text_variable) -> ResultType;'
    try!(parser.expect_keyword(token::keywords::Fn));
    let fn_name = try!(parser.parse_ident());
    try!(parser.expect(&token::OpenDelim(token::Paren)));
    let text_pat = try!(parser.parse_pat_nopanic());
    let text_lt = if try!(parser.eat(&token::Colon)) {
        try!(parser.parse_lifetime())
    } else {
        cx.lifetime(DUMMY_SP, token::gensym("text"))
    };
    try!(parser.expect(&token::CloseDelim(token::Paren)));
    try!(parser.expect(&token::RArrow));
    let ret_ty = try!(parser.parse_ty_nopanic());
    try!(parser.expect(&token::Semi));

    // now parse the token arms
    let mut re_vec = Vec::new();
    let mut actions = Vec::new();
    while parser.token != token::Eof {
        // parse '"regex" =>'
        let re_str = try!(parse_str_interior(&mut parser));
        let sp = parser.last_span;
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
        let expr = try!(parser.parse_expr_res(parser::Restrictions::RESTRICTION_STMT_EXPR));
        let optional_comma =
            // don't need a comma for blocks...
            classify::expr_is_simple_block(&*expr)
            // or for the last arm
            || parser.token == token::Eof;

        if optional_comma {
            // consume optional comma
            try!(parser.eat(&token::Comma));
        } else {
            // comma required
            // `expr` may not be complete, so continue parsing until the comma (or eof)
            try!(parser.commit_expr(&*expr, &[token::Comma], &[token::Eof]));
        }

        re_vec.push(re);
        actions.push(expr);
    }

    let (dfa, map) = Dfa::from_derivatives(vec![re_vec]);
    let dfa = dfa.map(|vec| first_nullable(&vec));
    let fail_ix = match map.get(&vec![Regex::Null; actions.len()]) {
        Some(&ix) => ix,
        None => {
            // XXX
            cx.span_warn(sp, "some rule (?) has .* as a prefix");
            dfa.states.len() as u32
        }
    };

    let dfa_transition_fn = token::str_to_ident(&*format!("transition"));
    let dfa_acceptance_fn = token::str_to_ident(&*format!("accepting"));

    let input = token::str_to_ident("input");
    let fail_ix_lit = cx.expr_lit(DUMMY_SP, ast::LitInt(fail_ix as u64, ast::UnsignedIntLit(ast::TyU32)));

    let mut helpers = Vec::new();
    helpers.push(dfa_fn(cx, &dfa, dfa_transition_fn));
    helpers.push({
        let mut arms: Vec<_> = dfa.states.iter()
            .map(|state| state.value)
            .enumerate().filter_map(|(ix, maybe_act)| maybe_act.map(|act| {
                let ix = ix as u32;
                let act = act as u32;
                quote_arm!(cx, $ix => Some($act),)
            })).collect();
        arms.push(quote_arm!(cx, _ => None,));
        quote_item!(cx, fn $dfa_acceptance_fn(state: u32) -> Option<u32> {
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
    let final_fn = cx.item_fn_poly(DUMMY_SP,
        fn_name,
        vec![cx.arg(DUMMY_SP, input,
                    cx.ty_rptr(DUMMY_SP,
                               cx.ty_rptr(DUMMY_SP,
                                          cx.ty_ident(DUMMY_SP, token::str_to_ident("str")),
                                          Some(text_lt), ast::MutImmutable),
                               None, ast::MutMutable))],
        quote_ty!(cx, Option<$ret_ty>),
        ast::Generics {
            lifetimes: vec![ast::LifetimeDef {
                lifetime: text_lt,
                bounds: Vec::new(),
            }],
            ty_params: owned_slice::OwnedSlice::empty(),
            where_clause: ast::WhereClause {
                id: DUMMY_NODE_ID,
                predicates: Vec::new(),
            },
        },
        cx.block(DUMMY_SP,
            helpers.map_in_place(|x| cx.stmt_item(DUMMY_SP, x)),
            Some(quote_expr!(cx, {
                let mut state = 0;
                let mut remaining = input.char_indices();
                let mut last_match = None;
                loop {
                    if let Some(which) = $dfa_acceptance_fn(state) {
                        last_match = Some((which, remaining.clone()));
                    }
                    if state == $fail_ix_lit {
                        break;
                    }
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
            }))
        )
    );
    Ok(base::MacEager::items(SmallVector::one(final_fn)))
}
