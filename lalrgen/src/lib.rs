#![crate_type="dylib"]
#![feature(plugin_registrar)]
#![feature(quote)]
#![allow(unstable)]

extern crate lalr;
extern crate syntax;
extern crate rustc;

use std::collections::BTreeMap;
use std::fmt;
use std::fmt::Writer;
use syntax::ptr::P;
use syntax::{ast, owned_slice};
use syntax::parse::token;
use syntax::ext::base;
use syntax::ext::build::AstBuilder;
use lalr::*;
use syntax::codemap::DUMMY_SP;
use syntax::ast::DUMMY_NODE_ID;

fn lit_u32(cx: &base::ExtCtxt, val: u32) -> P<ast::Expr> {
    cx.expr_lit(DUMMY_SP, ast::LitInt(val as u64, ast::UnsignedIntLit(ast::TyU32)))
}
fn pat_u32(cx: &base::ExtCtxt, val: u32) -> P<ast::Pat> {
    cx.pat_lit(DUMMY_SP, lit_u32(cx, val))
}

pub fn lr1_machine<T, N, A, FM, FA>(
    cx: &mut base::ExtCtxt,
    grammar: Grammar<T, N, A>,
    types: &BTreeMap<N, P<ast::Ty>>,
    token_ty: P<ast::Ty>,
    name: ast::Ident,
    vis: ast::Visibility,
    mut to_pat: FM,
    mut to_block: FA,
) -> P<ast::Item>
where T: Ord + fmt::Show + fmt::String,
      N: Ord + fmt::Show,
      A: Ord + fmt::Show,
      FM: FnMut(&T, &base::ExtCtxt) -> P<ast::Pat>,
      FA: FnMut(&A, &base::ExtCtxt, &[Symbol<T, N>]) -> (P<ast::Block>, Vec<P<ast::Pat>>),
{
    let actual_start = match grammar.rules.get(&grammar.start).unwrap()[0].syms[0] {
        Terminal(_) => panic!("bad grammar"),
        Nonterminal(ref x) => x,
    };
    let table: LR1ParseTable<T, N, A> = grammar.lalr1();
    let it_ty_id = token::gensym_ident("I");
    let it_ty = cx.ty_ident(DUMMY_SP, it_ty_id);
    let generics = ast::Generics {
        lifetimes: vec![],
        ty_params: owned_slice::OwnedSlice::from_vec(vec![
            cx.typaram(DUMMY_SP, it_ty_id, owned_slice::OwnedSlice::from_vec(vec![
                cx.typarambound(cx.path_all(DUMMY_SP, true, vec![
                    cx.ident_of("std"),
                    cx.ident_of("iter"),
                    cx.ident_of("Iterator"),
                ], vec![], vec![], vec![
                    P(ast::TypeBinding {
                        id: DUMMY_NODE_ID,
                        ident: cx.ident_of("Item"),
                        ty: token_ty.clone(),
                        span: DUMMY_SP,
                    })
                ]))
            ]), None)
        ]),
        where_clause: ast::WhereClause {
            id: DUMMY_NODE_ID,
            predicates: vec![]
        },
    };
    let it_arg_id = token::gensym_ident("it");
    let st_ty_id = token::gensym_ident("St");
    let args = vec![
        ast::Arg {
            ty: it_ty,
            pat: cx.pat_ident_binding_mode(DUMMY_SP, it_arg_id, ast::BindByValue(ast::MutMutable)),
            id: DUMMY_NODE_ID,
        }
    ];
    let st_variant_ids: BTreeMap<_, _> = grammar.rules.keys()
        // Skip the (fake) start state since it's never going to be used anyway
        .filter(|&lhs| *lhs != grammar.start)
        .enumerate()
        .map(|(i, k)| (k, token::gensym_ident(&format!("Variant{}", i)[])))
        .collect();
    let st_token_id = token::gensym_ident("Token");
    let rule_fn_ids: BTreeMap<_, _> = grammar.rules.iter()
        .filter(|&(lhs, _)| *lhs != grammar.start)
        .flat_map(|(_, rhss)| {
            // Identify rules by their RHS, which should have unique addresses
            rhss.iter().map(|rhs| rhs as *const _)
        })
        .enumerate()
        .map(|(i, k)| (k, token::gensym_ident(&format!("reduce_{}", i)[])))
        .collect();
    let goto_fn_ids: BTreeMap<_, _> = grammar.rules.keys()
        .filter(|&lhs| *lhs != grammar.start)
        .enumerate()
        .map(|(i, lhs)| (lhs, token::gensym_ident(&format!("goto_{}", i)[])))
        .collect();
    let stack_id = token::gensym_ident("stack");
    let state_id = token::gensym_ident("state");
    let token_id = token::gensym_ident("token");
    let next_state_id = token::gensym_ident("next_state");
    let mut stmts = Vec::new();
    stmts.push(cx.stmt_item(DUMMY_SP, cx.item_enum(DUMMY_SP, st_ty_id, ast::EnumDef {
        variants: st_variant_ids.iter()
            .map(|(k, &id)| {
                cx.variant(DUMMY_SP, id, vec![
                    types.get(*k).unwrap().clone()
                ])
            })
            .chain(Some(cx.variant(DUMMY_SP, st_token_id, vec![
                token_ty.clone()
            ])).into_iter())
            .map(|x| P(x))
            .collect(),
    })));
    for (lhs, rhss) in grammar.rules.iter() {
        if *lhs == grammar.start {
            continue;
        }
        let t = types.get(lhs).unwrap();
        for rhs in rhss.iter() {
            let (ret, arg_pats) = to_block(&rhs.act, cx, &rhs.syms[]);
            let args: Vec<_> = rhs.syms.iter().zip(arg_pats.into_iter()).map(|(s, pat)| ast::Arg {
                ty: match *s {
                    Terminal(_) => token_ty.clone(),
                    Nonterminal(ref n) => types.get(n).unwrap().clone(),
                },
                pat: pat,
                id: DUMMY_NODE_ID,
            }).collect();
            let fn_id = rule_fn_ids.get(&(rhs as *const _)).unwrap().clone();
            let f = cx.item_fn(DUMMY_SP, fn_id, args, t.clone(), ret);
            stmts.push(cx.stmt_item(DUMMY_SP, f));
        }
    }
    stmts.extend(goto_fn_ids.iter().map(|(lhs, id)| cx.stmt_item(DUMMY_SP, cx.item_fn(
        DUMMY_SP, *id,
        vec![cx.arg(DUMMY_SP, state_id, quote_ty!(cx, u32))],
        quote_ty!(cx, u32),
        cx.block_expr(cx.expr_match(DUMMY_SP, cx.expr_ident(DUMMY_SP, state_id),
            table.states.iter().enumerate().filter_map(|(ix, state)| state.goto.get(lhs).map(|&dest|
                cx.arm(DUMMY_SP, vec![pat_u32(cx, ix as u32)],
                lit_u32(cx, dest as u32))))
            .chain(Some(quote_arm!(cx, _ => unreachable!(),)).into_iter())
            .collect()))))));
    stmts.push(cx.stmt_let(DUMMY_SP, true, stack_id, quote_expr!(cx, Vec::new())));
    stmts.push(cx.stmt_let(DUMMY_SP, true, state_id, quote_expr!(cx, 0)));
    stmts.push(cx.stmt_let(DUMMY_SP, true, token_id, quote_expr!(cx, $it_arg_id.next())));
    stmts.push(cx.stmt_expr(cx.expr_loop(DUMMY_SP, cx.block(DUMMY_SP, vec![
        cx.stmt_let(DUMMY_SP, false, next_state_id, cx.expr_match(DUMMY_SP, cx.expr_ident(DUMMY_SP, state_id),
            table.states.iter().enumerate().map(|(ix, state)| {
                let mut err_msg: String = "expected".to_string();
                let count = state.lookahead.len() + if state.eof.is_some() { 1 } else { 0 };
                let mut arms: Vec<_> = state.lookahead.iter()
                .map(|(tok, action)| (Some(tok), action))
                .chain(state.eof.iter().map(|action| (None, action)))
                .enumerate()
                .map(|(i, (maybe_tok, action))| {
                    if i == 0 {
                        let _ = write!(&mut err_msg, " ");
                    } else if i == count-1 {
                        if i == 1 {
                            let _ = write!(&mut err_msg, " or ");
                        } else {
                            let _ = write!(&mut err_msg, ", or ");
                        }
                    } else {
                        let _ = write!(&mut err_msg, ", ");
                    }
                    if let Some(t) = maybe_tok {
                        let _ = write!(&mut err_msg, "`{}`", t);
                    } else {
                        let _ = write!(&mut err_msg, "end of file");
                    }
                    let block = match *action {
                        LRAction::Shift(dest) => lit_u32(cx, dest as u32),
                        LRAction::Reduce(lhs, rhs) => {
                            let vars: Vec<_> = (0..rhs.syms.len())
                                .map(|i| token::gensym_ident(&format!("s{}", i)[]))
                                .collect();
                            let mut r = Vec::new();
                            for (sym, (i, var)) in rhs.syms.iter().zip(vars.iter().enumerate()).rev() {
                                 // FIXME: deduplicate this code
                                let variant = match *sym {
                                    Terminal(_) => st_token_id,
                                    Nonterminal(ref n) => *st_variant_ids.get(n).unwrap(),
                                };
                                let arm = if i == 0 {
                                    quote_arm!(cx, Some((prev, $st_ty_id::$variant(x))) => {
                                        $state_id = prev;
                                        x
                                    })
                                } else {
                                    quote_arm!(cx, Some((_, $st_ty_id::$variant(x))) => x,)
                                };
                                r.push(cx.stmt_let(DUMMY_SP, false, *var,
                                    quote_expr!(cx, match $stack_id.pop() {
                                        $arm
                                        _ => unreachable!()
                                    })));
                            }
                            let lvariant = *st_variant_ids.get(lhs).unwrap();
                            let call = cx.expr_call(DUMMY_SP,
                                cx.expr_ident(DUMMY_SP, *rule_fn_ids.get(&(rhs as *const _)).unwrap()),
                                vars.into_iter().map(|id| cx.expr_ident(DUMMY_SP, id)).collect());
                            r.push(quote_stmt!(cx, $stack_id.push(($state_id, $st_ty_id::$lvariant($call)));));
                            let goto_fn = *goto_fn_ids.get(lhs).unwrap();
                            r.push(quote_stmt!(cx, $state_id = $goto_fn($state_id);));
                            cx.expr_block(cx.block(DUMMY_SP, r, Some(cx.expr(DUMMY_SP, ast::ExprAgain(None)))))
                        }
                        LRAction::Accept => {
                            let variant = *st_variant_ids.get(actual_start).unwrap();
                            quote_expr!(cx, match $stack_id.pop().unwrap() {
                                (_, $st_ty_id::$variant(x)) => return Ok(x),
                                _ => unreachable!()
                            })
                        }
                    };
                    cx.arm(DUMMY_SP, vec![match maybe_tok {
                        Some(&tok) => cx.pat_some(DUMMY_SP, to_pat(tok, cx)),
                        None => cx.pat_none(DUMMY_SP),
                    }], block)
                }).collect();
                let err_msg_lit = cx.expr_str(DUMMY_SP, token::intern_and_get_ident(&err_msg[]));
                arms.push(quote_arm!(cx, _ => return Err(($token_id, $err_msg_lit)),));
                cx.arm(DUMMY_SP,
                    vec![pat_u32(cx, ix as u32)],
                    cx.expr_match(DUMMY_SP, cx.expr_ident(DUMMY_SP, token_id),
                    arms))
            }).chain(Some(quote_arm!(cx, _ => unreachable!(),)).into_iter()).collect())),
        quote_stmt!(cx, $stack_id.push(($state_id, $st_ty_id::$st_token_id($token_id.unwrap())));),
        quote_stmt!(cx, $token_id = $it_arg_id.next();),
        quote_stmt!(cx, $state_id = $next_state_id;),
    ], None))));
    let body = cx.block(DUMMY_SP, stmts, None);
    let out_ty = cx.ty_path(cx.path_all(DUMMY_SP,
                                        true,
                                        vec![cx.ident_of("std"), cx.ident_of("result"), cx.ident_of("Result")],
                                        vec![],
                                        vec![types.get(actual_start).unwrap().clone(),
                                             quote_ty!(cx, (Option<$token_ty>, &'static str))],
                                        vec![]));
    cx.item_fn_poly(DUMMY_SP, name, args, out_ty, generics, body)
}
