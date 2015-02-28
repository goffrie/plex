#![crate_type="dylib"]
#![feature(plugin_registrar)]
#![feature(quote)]
#![allow(unstable)]

extern crate regex_dfa;
extern crate syntax;
extern crate rustc;

use std::iter;
use syntax::ptr::P;
use syntax::{codemap, ast, owned_slice};
use syntax::parse::{self, parser, token, classify};
use syntax::ext::base;
use syntax::ext::build::AstBuilder;
use regex_dfa::Dfa;
use regex_dfa::regex::Regex;
use syntax::codemap::DUMMY_SP;
use syntax::ast::DUMMY_NODE_ID;

fn expr_u32(cx: &base::ExtCtxt, u: u32) -> P<ast::Expr> {
    cx.expr_lit(DUMMY_SP, ast::LitInt(u as u64, ast::UnsignedIntLit(ast::TyU32)))
}

pub fn dfa_fn(cx: &base::ExtCtxt, dfa: &Dfa, ident: ast::Ident) -> P<ast::Item> {
    let u32_ty = quote_ty!(cx, u32);
    let char_ty = quote_ty!(cx, char);
    let state_arg = cx.arg(DUMMY_SP, token::str_to_ident("state"), u32_ty.clone());
    let char_arg = cx.arg(DUMMY_SP, token::str_to_ident("ch"), char_ty.clone());
    let mut arms = Vec::with_capacity(dfa.transitions.len());
    for (i, tr) in dfa.transitions.iter().enumerate() {
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

fn parse_str_interior(parser: &mut parser::Parser) -> String {
    let (re_str, style) = parser.parse_str();
    match style {
        ast::CookedStr => parse::str_lit(re_str.as_slice()),
        ast::RawStr(_) => parse::raw_str_lit(re_str.as_slice()),
    }
}

fn first_nullable(vec: &[Regex]) -> Option<usize> {
    vec.iter().position(Regex::nullable)
}

pub fn expand_scanner(cx: &mut base::ExtCtxt, sp: codemap::Span, args: &[ast::TokenTree]) -> Box<base::MacResult+'static> {
    let mut parser = cx.new_parser_from_tts(args);

    // first: parse 'name_of_scanner(text_variable) -> ResultType;'
    let fn_name = parser.parse_ident();
    parser.expect(&token::OpenDelim(token::Paren));
    let text_pat = parser.parse_pat();
    let text_lt = if parser.eat(&token::Colon) {
        Some(parser.parse_lifetime())
    } else {
        None
    };
    parser.expect(&token::CloseDelim(token::Paren));
    parser.expect(&token::RArrow);
    let ret_ty = parser.parse_ty();
    parser.expect(&token::Semi);

    // now parse the token arms
    let mut re_vec = Vec::new();
    let mut actions = Vec::new();
    while parser.token != token::Eof {
        // parse '"regex" =>'
        let re_str = parse_str_interior(&mut parser);
        let sp = parser.last_span;
        let re = match Regex::new(re_str.as_slice()) {
            Ok(r) => r,
            Err(e) => {
                cx.span_err(sp, &*format!("invalid regular expression: {:?}", e));
                Regex::Null // dummy
            }
        };
        if re.nullable() {
            cx.span_err(sp, "token must not match the empty string");
        }

        parser.expect(&token::FatArrow);

        // start parsing the expr
        let expr = parser.parse_expr_res(parser::RESTRICTION_STMT_EXPR);
        let optional_comma =
            // don't need a comma for blocks...
            classify::expr_is_simple_block(&*expr)
            // or for the last arm
            || parser.token == token::Eof;

        if optional_comma {
            // consume optional comma
            parser.eat(&token::Comma);
        } else {
            // comma required
            // `expr` may not be complete, so continue parsing until the comma (or eof)
            parser.commit_expr(&*expr, &[token::Comma], &[token::Eof]);
        }

        re_vec.push(re);
        actions.push(expr);
    }

    let (dfa, map) = Dfa::from_derivatives(vec![re_vec]);
    let fail_ix = match map.get(&iter::repeat(Regex::Null).take(actions.len()).collect::<Vec<_>>()) {
        Some(&ix) => ix,
        None => {
            // XXX
            cx.span_warn(sp, "some rule (?) has .* as a prefix");
            dfa.transitions.len() as u32
        }
    };
    let mut action_by_state: Vec<_> = iter::repeat(None).take(dfa.transitions.len()).collect();
    for (res, ix) in map.into_iter() {
        action_by_state[ix as usize] = first_nullable(&*res);
    }

    let dfa_transition_fn = token::str_to_ident(&*format!("transition"));
    let dfa_acceptance_fn = token::str_to_ident(&*format!("accepting"));

    let input = token::str_to_ident("input");
    let state = token::str_to_ident("state");
    let fail_ix_lit = cx.expr_lit(DUMMY_SP, ast::LitInt(fail_ix as u64, ast::UnsignedIntLit(ast::TyU32)));

    let mut helpers = Vec::new();
    helpers.push(dfa_fn(cx, &dfa, dfa_transition_fn));
    helpers.push(cx.item_fn(
        DUMMY_SP,
        dfa_acceptance_fn,
        vec![cx.arg(DUMMY_SP, state, quote_ty!(cx, u32))],
        quote_ty!(cx, Option<u32>),
        {
            let mut arms: Vec<_> = action_by_state.into_iter().enumerate().filter_map(|(ix, maybe_act)| maybe_act.map(|act| {
                cx.arm(DUMMY_SP,
                       vec![cx.pat_lit(DUMMY_SP, cx.expr_lit(DUMMY_SP, ast::LitInt(ix as u64, ast::UnsignedIntLit(ast::TyU32))))],
                       cx.expr_some(DUMMY_SP, cx.expr_lit(DUMMY_SP, ast::LitInt(act as u64, ast::UnsignedIntLit(ast::TyU32)))))
            })).collect();
            arms.push(cx.arm(DUMMY_SP, vec![cx.pat_wild(DUMMY_SP)], cx.expr_none(DUMMY_SP)));
            cx.block(DUMMY_SP, vec![], Some(cx.expr_match(DUMMY_SP, quote_expr!(cx, state), arms)))
        }
    ));

    let compute_result = cx.expr_match(DUMMY_SP, quote_expr!(cx, which),
        actions.into_iter().enumerate().map(|(i, expr)|
            cx.arm(DUMMY_SP,
                   vec![cx.pat_lit(DUMMY_SP, cx.expr_lit(DUMMY_SP, ast::LitInt(i as u64, ast::UnsuffixedIntLit(ast::Plus))))],
                   expr)).collect::<Vec<_>>() + &[cx.arm_unreachable(DUMMY_SP)]);
    let final_fn = cx.item_fn_poly(DUMMY_SP,
        fn_name,
        vec![cx.arg(DUMMY_SP, input,
                    cx.ty_rptr(DUMMY_SP,
                               cx.ty_rptr(DUMMY_SP,
                                          cx.ty_ident(DUMMY_SP, token::str_to_ident("str")),
                                          text_lt, ast::MutImmutable),
                               None, ast::MutMutable))],
        quote_ty!(cx, Option<$ret_ty>),
        ast::Generics {
            lifetimes: match text_lt {
                Some(lt) => vec![ast::LifetimeDef {
                    lifetime: lt,
                    bounds: Vec::new(),
                }],
                None => Vec::new()
            },
            ty_params: owned_slice::OwnedSlice::empty(),
            where_clause: ast::WhereClause {
                id: DUMMY_NODE_ID,
                predicates: Vec::new(),
            },
        },
        cx.block(DUMMY_SP,
            helpers.map_in_place(|x| cx.stmt_item(DUMMY_SP, x)) + &[
                quote_stmt!(cx, let mut state = 0;),
                quote_stmt!(cx, let mut remaining = *input;),
                quote_stmt!(cx, let mut last_match = None;),
                quote_stmt!(cx, loop {
                    if let Some(which) = $dfa_acceptance_fn(state) {
                        last_match = Some((which, remaining));
                    }
                    if state == $fail_ix_lit {
                        break;
                    }
                    if let Some((ch, rest)) = remaining.slice_shift_char() {
                        remaining = rest;
                        state = $dfa_transition_fn(state, ch);
                    } else {
                        break;
                    }
                }),
            ],
            Some(cx.expr(DUMMY_SP, ast::ExprIfLet(quote_pat!(cx, Some((which, remaining))), quote_expr!(cx, last_match),
                cx.block(DUMMY_SP, vec![
                    quote_stmt!(cx, let $text_pat = input.slice_to(input.subslice_offset(remaining));),
                    quote_stmt!(cx, *input = remaining;),
                ], Some(cx.expr_some(DUMMY_SP, compute_result))),
                Some(cx.expr_none(DUMMY_SP)))))
        )
    );
    base::MacItems::new(Some(final_fn).into_iter())
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut rustc::plugin::Registry) {
    reg.register_macro("scanner", expand_scanner);
}
