#![crate_type="dylib"]
#![feature(plugin_registrar)]
#![feature(quote)]
#![allow(unstable)]

extern crate regex_dfa;
extern crate syntax;
extern crate rustc;

use syntax::ptr::P;
use syntax::{codemap, ast, abi, owned_slice};
use syntax::parse::{parser, token, classify};
use syntax::ext::base;
use syntax::ext::build::AstBuilder;
use regex_dfa::{Regex, Dfa};
use syntax::codemap::DUMMY_SP;
use syntax::ast::DUMMY_NODE_ID;

fn expr(node: ast::Expr_) -> ast::Expr {
    ast::Expr {
        id: ast::DUMMY_NODE_ID,
        node: node,
        span: codemap::DUMMY_SP,
    }
}

fn pat(node: ast::Pat_) -> ast::Pat {
    ast::Pat {
        id: ast::DUMMY_NODE_ID,
        node: node,
        span: codemap::DUMMY_SP,
    }
}

fn spanned<T>(node: T) -> codemap::Spanned<T> {
    codemap::Spanned {
        node: node,
        span: codemap::DUMMY_SP,
    }
}

pub fn dfagen(dfa: &Dfa, ident: ast::Ident, vis: ast::Visibility, span: codemap::Span) -> ast::Item {
    let u32_ty = ast::Ty {
        id: ast::DUMMY_NODE_ID,
        node: ast::TyPath(ast::Path {
            span: codemap::DUMMY_SP,
            global: true,
            segments: vec![ast::PathSegment {
                identifier: token::str_to_ident("u32"),
                parameters: ast::PathParameters::none(),
            }],
        }, ast::DUMMY_NODE_ID),
        span: codemap::DUMMY_SP,
    };
    let char_ty = ast::Ty {
        id: ast::DUMMY_NODE_ID,
        node: ast::TyPath(ast::Path {
            span: codemap::DUMMY_SP,
            global: true,
            segments: vec![ast::PathSegment {
                identifier: token::str_to_ident("char"),
                parameters: ast::PathParameters::none(),
            }],
        }, ast::DUMMY_NODE_ID),
        span: codemap::DUMMY_SP,
    };
    let state_arg = ast::Arg {
        ty: P(u32_ty.clone()),
        pat: P(pat(ast::PatIdent(ast::BindByValue(ast::MutImmutable), codemap::Spanned {
            node: token::str_to_ident("state"),
            span: codemap::DUMMY_SP,
        }, None))),
        id: ast::DUMMY_NODE_ID,
    };
    let char_arg = ast::Arg {
        ty: P(char_ty.clone()),
        pat: P(pat(ast::PatIdent(ast::BindByValue(ast::MutImmutable), codemap::Spanned {
            node: token::str_to_ident("ch"),
            span: codemap::DUMMY_SP,
        }, None))),
        id: ast::DUMMY_NODE_ID,
    };
    let decl = ast::FnDecl {
        inputs: vec![state_arg, char_arg],
        output: ast::Return(P(u32_ty.clone())),
        variadic: false,
    };
    let mut arms = Vec::with_capacity(dfa.transitions.len());
    for (i, tr) in dfa.transitions.iter().enumerate() {
        let arm_pat = pat(ast::PatLit(P(expr(ast::ExprLit(P(spanned(ast::LitInt(i as u64, ast::UnsignedIntLit(ast::TyU32)))))))));
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
                pat(ast::PatLit(P(expr(ast::ExprLit(P(spanned(ast::LitChar(ch))))))))
            } else {
                pat(ast::PatRange(
                        P(expr(ast::ExprLit(P(spanned(ast::LitChar(ch)))))),
                        P(expr(ast::ExprLit(P(spanned(ast::LitChar(end))))))
                        ))
            };
            subarms.push(ast::Arm {
                attrs: Vec::new(),
                pats: vec![P(pat)],
                guard: None,
                body: P(expr(ast::ExprLit(P(spanned(ast::LitInt(target as u64, ast::UnsignedIntLit(ast::TyU32))))))),
            });
        }
        subarms.push(ast::Arm {
            attrs: Vec::new(),
            pats: vec![P(pat(ast::PatWild(ast::PatWildSingle)))],
            guard: None,
            body: P(expr(ast::ExprLit(P(spanned(ast::LitInt(tr.default as u64, ast::UnsignedIntLit(ast::TyU32))))))),
        });
        let body = expr(ast::ExprMatch(P(expr(ast::ExprPath(ast::Path {
            span: codemap::DUMMY_SP,
            global: false,
            segments: vec![ast::PathSegment {
                identifier: token::str_to_ident("ch"),
                parameters: ast::PathParameters::none(),
            }],
        }))), subarms, ast::MatchSource::Normal));
        arms.push(ast::Arm {
            attrs: Vec::new(),
            pats: vec![P(arm_pat)],
            guard: None,
            body: P(body),
        });
    }
    arms.push(ast::Arm {
        attrs: Vec::new(),
        pats: vec![P(pat(ast::PatWild(ast::PatWildSingle)))],
        guard: None,
        body: P(expr(ast::ExprPath(ast::Path {
            span: codemap::DUMMY_SP,
            global: false,
            segments: vec![ast::PathSegment {
                identifier: token::str_to_ident("state"),
                parameters: ast::PathParameters::none(),
            }],
        }))),
    });
    let block = ast::Block {
        view_items: Vec::new(),
        stmts: Vec::new(),
        expr: Some(P(expr(ast::ExprMatch(P(expr(ast::ExprPath(ast::Path {
            span: codemap::DUMMY_SP,
            global: false,
            segments: vec![ast::PathSegment {
                identifier: token::str_to_ident("state"),
                parameters: ast::PathParameters::none(),
            }],
        }))), arms, ast::MatchSource::Normal)))),
        id: ast::DUMMY_NODE_ID,
        rules: ast::BlockCheckMode::DefaultBlock,
        span: codemap::DUMMY_SP,
    };
    let node = ast::ItemFn(
        P(decl),
        ast::Unsafety::Normal,
        abi::Abi::Rust,
        ast::Generics {
            lifetimes: Vec::new(),
            ty_params: owned_slice::OwnedSlice::empty(),
            where_clause: ast::WhereClause {
                id: ast::DUMMY_NODE_ID,
                predicates: Vec::new(),
            },
        },
        P(block)
    );
    ast::Item {
        ident: ident,
        attrs: Vec::new(),
        id: ast::DUMMY_NODE_ID,
        node: node,
        vis: vis,
        span: span,
    }
}

struct SingleItem<T> {
    item: Option<T>
}
fn single_item<T>(item: T) -> SingleItem<T> {
    SingleItem {
        item: Some(item)
    }
}
impl<T> Iterator for SingleItem<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        std::mem::replace(&mut self.item, None)
    }
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
    let mut arms = Vec::new();
    while parser.token != token::Eof {
        // parse '"regex" =>'
        let (re_str, _) = parser.parse_str(); // don't care what style of string literal
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

        arms.push((Dfa::from_regex(re), expr));
    }

    let dfa_transition_fns: Vec<_> = (0..arms.len())
        .map(|i| token::str_to_ident(&format!("transition_{}", i)[]))
        .collect();
    let dfa_acceptance_fns: Vec<_> = (0..arms.len())
        .map(|i| token::str_to_ident(&format!("accepting_{}", i)[]))
        .collect();

    let mut helpers = Vec::new();
    for (i, &(ref dfa, _)) in arms.iter().enumerate() {
        helpers.push(P(dfagen(dfa, dfa_transition_fns[i], ast::Visibility::Inherited, sp)));
        helpers.push(cx.item_fn(
            DUMMY_SP,
            dfa_acceptance_fns[i],
            vec![cx.arg(DUMMY_SP,
                        token::str_to_ident("state"),
                        cx.ty_path(cx.path_global(DUMMY_SP, vec![token::str_to_ident("u32")])))],
            cx.ty_path(cx.path_global(DUMMY_SP, vec![token::str_to_ident("bool")])),
            cx.block(DUMMY_SP, Vec::new(), Some(
                cx.expr_match(DUMMY_SP,
                              cx.expr_ident(DUMMY_SP, token::str_to_ident("state")),
                              vec![
                                cx.arm(DUMMY_SP,
                                       dfa.transitions.iter().enumerate()
                                        .filter(|&(_, x)| x.accepting)
                                        .map(|(i, _)|
                                                cx.pat_lit(DUMMY_SP,
                                                           cx.expr_lit(DUMMY_SP, ast::LitInt(i as u64,
                                                                                             ast::UnsignedIntLit(ast::TyU32)))))
                                        .collect(),
                                       cx.expr_bool(DUMMY_SP, true)),
                                cx.arm(DUMMY_SP, vec![cx.pat_wild(DUMMY_SP)], cx.expr_bool(DUMMY_SP, false))
                              ])))
        ));
    }

    let vec_size = cx.expr_lit(DUMMY_SP, ast::LitInt(arms.len() as u64, ast::UnsuffixedIntLit(ast::Plus)));
    let input = token::gensym_ident("input");
    let remaining = token::gensym_ident("remaining");
    let states = token::gensym_ident("states");
    let last_match = token::gensym_ident("last_match");
    let fail = token::gensym_ident("fail");
    let which = token::gensym_ident("which");
    let st = token::gensym_ident("st");
    let ch = token::gensym_ident("ch");
    let rest = token::gensym_ident("rest");
    let check_matches = (0..arms.len()).rev().fold(
        cx.expr_block(cx.block(DUMMY_SP, Vec::new(), None)),
        |acc, i| {
            let accepting = dfa_acceptance_fns[i];
            let ix = cx.expr_lit(DUMMY_SP, ast::LitInt(i as u64, ast::UnsuffixedIntLit(ast::Plus)));
            cx.expr_if(DUMMY_SP, quote_expr!(cx, $accepting($states[$ix])),
                       quote_expr!(cx, $last_match = Some(($ix, $remaining))),
                       Some(acc))
        });
    let advance_dfas = cx.expr_block(cx.block(DUMMY_SP, (0..arms.len()).map(
        |i| {
            let transition = dfa_transition_fns[i];
            let ix = cx.expr_lit(DUMMY_SP, ast::LitInt(i as u64, ast::UnsuffixedIntLit(ast::Plus)));
            quote_stmt!(cx, $states[$ix] = $transition($states[$ix], $ch);)
        }).collect(), None));
    let compute_result = cx.expr_match(DUMMY_SP, cx.expr_ident(DUMMY_SP, which),
        arms.into_iter().enumerate().map(|(i, (_, expr))|
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
                quote_stmt!(cx, let mut $states = [0; $vec_size];),
                quote_stmt!(cx, let mut $remaining = *$input;),
                quote_stmt!(cx, let mut $last_match = None;),
                quote_stmt!(cx, loop {
                    $check_matches
                    let mut $fail = true;
                    for &$st in $states.iter() {
                        if $st != 1 {
                            $fail = false;
                            break;
                        }
                    }
                    if $fail {
                        break;
                    }
                    if let Some(($ch, $rest)) = $remaining.slice_shift_char() {
                        $remaining = $rest;
                        $advance_dfas
                    } else {
                        break;
                    }
                }),
            ],
            Some(quote_expr!(cx,
                if let Some(($which, $remaining)) = $last_match {
                    let $text_pat = $input.slice_to($input.subslice_offset($remaining));
                    *$input = $remaining;
                    Some($compute_result)
                } else {
                    None
                }))
        )
    );
    base::MacItems::new(single_item(final_fn))
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut rustc::plugin::Registry) {
    reg.register_macro("scanner", expand_scanner);
}
