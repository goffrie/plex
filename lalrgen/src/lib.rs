#![crate_type="dylib"]
#![feature(plugin_registrar)]
#![feature(quote)]
#![allow(unstable)]

extern crate lalr;
extern crate syntax;
extern crate rustc;

use std::collections::{BTreeMap, BTreeSet};
use std::{iter, fmt, cmp};
use std::fmt::Writer;
use syntax::ptr::P;
use syntax::{ast, owned_slice, codemap};
use syntax::parse::{parser, token, classify};
use syntax::parse::attr::ParserAttr;
use syntax::ext::base;
use syntax::ext::build::AstBuilder;
use syntax::diagnostic::FatalError;
use lalr::*;
use syntax::codemap::DUMMY_SP;
use syntax::ast::DUMMY_NODE_ID;

fn lit_u32(cx: &base::ExtCtxt, val: u32) -> P<ast::Expr> {
    cx.expr_lit(DUMMY_SP, ast::LitInt(val as u64, ast::UnsignedIntLit(ast::TyU32)))
}
fn pat_u32(cx: &base::ExtCtxt, val: u32) -> P<ast::Pat> {
    cx.pat_lit(DUMMY_SP, lit_u32(cx, val))
}

fn variant(name: ast::Ident, tys: Vec<P<ast::Ty>> ) -> ast::Variant {
    let args = tys.into_iter().map(|ty| {
        ast::VariantArg { ty: ty, id: DUMMY_NODE_ID }
    }).collect();

    codemap::respan(DUMMY_SP,
        ast::Variant_ {
            name: name,
            attrs: vec![],
            kind: ast::TupleVariantKind(args),
            id: DUMMY_NODE_ID,
            disr_expr: None,
            vis: ast::Inherited,
        })
}


fn most_frequent<T: Ord, I: Iterator<Item=T>>(mut it: I) -> Option<T> {
    let mut freq = BTreeMap::new();
    for x in it {
        *freq.entry(x).get().unwrap_or_else(|v| v.insert(0)) += 1;
    }
    freq.into_iter().fold(None, |best, (x, f)| match best {
        None => Some((x, f)),
        Some((x2, f2)) => if f > f2 { Some((x, f)) } else { Some((x2, f2)) },
    }).map(|(x, _)| x)
}

fn expected_one_of<S: fmt::String>(xs: &[S]) -> String {
    let mut err_msg: String = "expected".to_string();
    for (i, x) in xs.iter().enumerate() {
        if i == 0 {
            let _ = write!(&mut err_msg, " ");
        } else if i == xs.len()-1 {
            if i == 1 {
                let _ = write!(&mut err_msg, " or ");
            } else {
                let _ = write!(&mut err_msg, ", or ");
            }
        } else {
            let _ = write!(&mut err_msg, ", ");
        }
        let _ = write!(&mut err_msg, "{}", x);
    }
    err_msg
}

pub fn lr1_machine<'a, T, N, A, FM, FA, FR>(
    cx: &mut base::ExtCtxt,
    grammar: &'a Grammar<T, N, A>,
    types: &BTreeMap<N, P<ast::Ty>>,
    token_ty: P<ast::Ty>,
    name: ast::Ident,
    mut to_pat: FM,
    mut to_expr: FA,
    reduce_on: FR,
) -> Result<P<ast::Item>, LR1Conflict<'a, T, N, A>>
where T: Ord + fmt::Show + fmt::String,
      N: Ord + fmt::Show,
      A: Ord + fmt::Show,
      FM: FnMut(&T, &base::ExtCtxt) -> P<ast::Pat>,
      FA: FnMut(&A, &base::ExtCtxt, &[Symbol<T, N>]) -> (P<ast::Expr>, Vec<P<ast::Pat>>, codemap::Span),
      FR: FnMut(&A, Option<&T>) -> bool,
{
    let actual_start = match grammar.rules.get(&grammar.start).unwrap()[0].syms[0] {
        Terminal(_) => panic!("bad grammar"),
        Nonterminal(ref x) => x,
    };
    let table: LR1ParseTable<T, N, A> = try!(grammar.lalr1(reduce_on));
    let it_ty_id = token::gensym_ident("I");
    let it_ty = cx.ty_ident(DUMMY_SP, it_ty_id);
    let u32_ty = quote_ty!(cx, u32);
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
            .map(|(k, &id)| variant(id, vec![
                types.get(*k).unwrap().clone()
            ]))
            .chain(Some(variant(st_token_id, vec![
                token_ty.clone()
            ])).into_iter())
            .map(|x| P(x))
            .collect(),
    })));
    let stack_ty = cx.ty_path(cx.path_all(DUMMY_SP, true, vec![
        cx.ident_of("std"), cx.ident_of("vec"), cx.ident_of("Vec"),
    ], vec![], vec![cx.ty(DUMMY_SP, ast::TyTup(vec![
        u32_ty.clone(),
        cx.ty_ident(DUMMY_SP, st_ty_id),
    ]))], vec![]));
    for (lhs, rhss) in grammar.rules.iter() {
        if *lhs == grammar.start {
            continue;
        }
        for rhs in rhss.iter() {
            let (result, arg_pats, span) = to_expr(&rhs.act, cx, &rhs.syms[]);
            let args = vec![ast::Arg {
                ty: cx.ty_rptr(DUMMY_SP, stack_ty.clone(), None, ast::MutMutable),
                pat: cx.pat_ident(DUMMY_SP, stack_id),
                id: DUMMY_NODE_ID,
            }, ast::Arg {
                ty: cx.ty_rptr(DUMMY_SP, u32_ty.clone(), None, ast::MutMutable),
                pat: cx.pat_ident(DUMMY_SP, state_id),
                id: DUMMY_NODE_ID,
            }];
            let mut reduce_stmts: Vec<_> =
            rhs.syms.iter()
            .zip(arg_pats.into_iter())
            .enumerate()
            .rev()
            .map(|(i, (sym, pat))| {
                // FIXME: deduplicate this code
                let variant = match *sym {
                    Terminal(_) => st_token_id,
                    Nonterminal(ref n) => *st_variant_ids.get(n).unwrap(),
                };
                let arm = if i == 0 {
                    quote_arm!(cx, Some((prev, $st_ty_id::$variant(x))) => {
                        *$state_id = prev;
                        x
                    })
                } else {
                    quote_arm!(cx, Some((_, $st_ty_id::$variant(x))) => x,)
                };
                let local = P(ast::Local {
                    pat: pat,
                    ty: Some(match *sym {
                        Terminal(_) => token_ty.clone(),
                        Nonterminal(ref n) => types.get(n).unwrap().clone(),
                    }),
                    init: Some(quote_expr!(cx, match $stack_id.pop() {
                        $arm
                        _ => unsafe { ::std::intrinsics::unreachable() }
                    })),
                    id: DUMMY_NODE_ID,
                    span: DUMMY_SP,
                    source: ast::LocalLet,
                });
                P(codemap::respan(DUMMY_SP, ast::StmtDecl(P(codemap::respan(DUMMY_SP, ast::DeclLocal(local))), DUMMY_NODE_ID)))
            }).collect();
            let rspan = result.span;
            let lvariant = *st_variant_ids.get(lhs).unwrap();
            reduce_stmts.push(cx.stmt_expr(cx.expr_method_call(
                DUMMY_SP,
                quote_expr!(cx, $stack_id),
                cx.ident_of("push"),
                vec![cx.expr_tuple(DUMMY_SP, vec![
                    quote_expr!(cx, *$state_id),
                    cx.expr_call(DUMMY_SP, quote_expr!(cx, $st_ty_id::$lvariant), vec![result]),
                ])]
            )));
            let goto_fn = *goto_fn_ids.get(lhs).unwrap();
            reduce_stmts.push(quote_stmt!(cx, *$state_id = $goto_fn(*$state_id);));
            let block = cx.block(rspan, reduce_stmts, None);
            let fn_id = rule_fn_ids.get(&(rhs as *const _)).unwrap().clone();
            let f = cx.item_fn(span, fn_id, args, quote_ty!(cx, ()), block);
            stmts.push(cx.stmt_item(span, f));
        }
    }
    for (lhs, id) in goto_fn_ids.iter() {
        let expr = if let Some(&most_freq) = most_frequent(table.states.iter()
                                               .filter_map(|state| state.goto.get(lhs))) {
            let most_freq = most_freq as u32;
            let mut pats_by_dest = BTreeMap::new();
            for (ix, state) in table.states.iter().enumerate() {
                if let Some(&dest) = state.goto.get(lhs) {
                    let dest = dest as u32;
                    if dest != most_freq {
                        pats_by_dest.entry(dest).get()
                            .unwrap_or_else(|v| v.insert(vec![]))
                            .push(pat_u32(cx, ix as u32));
                    }
                }
            }
            let mut arms: Vec<_> = pats_by_dest.into_iter()
                .map(|(dest, pats)| cx.arm(DUMMY_SP, pats, lit_u32(cx, dest)))
                .collect();
            arms.push(cx.arm(DUMMY_SP, vec![cx.pat_wild(DUMMY_SP)], lit_u32(cx, most_freq)));
            cx.expr_match(DUMMY_SP, cx.expr_ident(DUMMY_SP, state_id), arms)
        } else {
            // This shouldn't normally happen, but it can when `lhs` is unused in the
            // grammar.
            quote_expr!(cx, unreachable!())
        };
        let f = cx.item_fn(DUMMY_SP, *id, vec![
            cx.arg(DUMMY_SP, state_id, u32_ty.clone())
        ], u32_ty.clone(), cx.block_expr(expr));
        stmts.push(cx.stmt_item(DUMMY_SP, f));
    }
    stmts.push(cx.stmt_let(DUMMY_SP, true, stack_id, quote_expr!(cx, ::std::vec::Vec::new())));
    stmts.push(cx.stmt_let(DUMMY_SP, true, state_id, quote_expr!(cx, 0)));
    stmts.push(cx.stmt_let(DUMMY_SP, true, token_id, quote_expr!(cx, $it_arg_id.next())));
    stmts.push(cx.stmt_expr(cx.expr_loop(DUMMY_SP, cx.block(DUMMY_SP, vec![
        cx.stmt_let(DUMMY_SP, false, next_state_id, cx.expr_match(DUMMY_SP, cx.expr_ident(DUMMY_SP, state_id),
            table.states.iter().enumerate().map(|(ix, state)| {
                let mut arms = vec![];
                let mut reduce_arms = BTreeMap::new();
                let mut expected = vec![];
                for (&tok, action) in state.lookahead.iter() {
                    expected.push(format!("`{}`", tok));
                    let pat = cx.pat_some(DUMMY_SP, to_pat(tok, cx));
                    let arm_expr = match *action {
                        LRAction::Shift(dest) => lit_u32(cx, dest as u32),
                        LRAction::Reduce(_, rhs) => {
                            reduce_arms.entry(rhs as *const _).get().unwrap_or_else(|v| v.insert(vec![])).push(pat);
                            continue;
                        }
                        LRAction::Accept => unreachable!(),
                    };
                    arms.push(cx.arm(DUMMY_SP, vec![pat], arm_expr))
                }
                if let Some(ref action) = state.eof {
                    expected.push("end of file".to_string());
                    let pat = cx.pat_none(DUMMY_SP);
                    match *action {
                        LRAction::Shift(_) => unreachable!(),
                        LRAction::Reduce(_, rhs) => {
                            reduce_arms.entry(rhs as *const _).get().unwrap_or_else(|v| v.insert(vec![])).push(pat);
                        }
                        LRAction::Accept => {
                            let variant = *st_variant_ids.get(actual_start).unwrap();
                            let arm_expr = quote_expr!(cx, match $stack_id.pop().unwrap() {
                                (_, $st_ty_id::$variant(x)) => return Ok(x),
                                _ => unsafe { ::std::intrinsics::unreachable() }
                            });
                            arms.push(cx.arm(DUMMY_SP, vec![pat], arm_expr));
                        }
                    };
                }
                for (rhs_ptr, pats) in reduce_arms.into_iter() {
                    let reduce_fn = *rule_fn_ids.get(&rhs_ptr).unwrap();
                    arms.push(cx.arm(DUMMY_SP, pats, quote_expr!(cx, {
                        $reduce_fn(&mut $stack_id, &mut $state_id);
                        continue
                    })));
                }
                let err_msg_lit = cx.expr_str(DUMMY_SP, token::intern_and_get_ident(&*expected_one_of(&*expected)));
                arms.push(quote_arm!(cx, _ => return Err(($token_id, $err_msg_lit)),));
                cx.arm(DUMMY_SP,
                    vec![pat_u32(cx, ix as u32)],
                    cx.expr_match(DUMMY_SP, cx.expr_ident(DUMMY_SP, token_id),
                    arms))
            }).chain(Some(quote_arm!(cx, _ => unsafe { ::std::intrinsics::unreachable() },)).into_iter()).collect())),
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
    Ok(cx.item_fn_poly(DUMMY_SP, name, args, out_ty, generics, body))
}

fn expand_parser<'a>(
    cx: &'a mut base::ExtCtxt,
    sp: codemap::Span,
    name: ast::Ident,
    tts: Vec<ast::TokenTree>
) -> Box<base::MacResult + 'a> {
    #[derive(Show)]
    enum Binding {
        Pat(P<ast::Pat>),
        Enum(codemap::Span, Vec<P<ast::Pat>>),
        None,
    }

    #[derive(Show)]
    struct Action {
        binds: Vec<Binding>,
        expr: P<ast::Expr>,
        span: codemap::Span,
        exclusions: BTreeSet<String>,
        exclude_eof: bool,
    }

    // These are hacks, necessary because of a bug in Rust deriving
    impl PartialEq for Action {
        fn eq(&self, _: &Action) -> bool { unreachable!() }
    }
    impl Eq for Action { }
    impl PartialOrd for Action {
        fn partial_cmp(&self, _: &Action) -> Option<cmp::Ordering> { unreachable!() }
    }
    impl Ord for Action {
        fn cmp(&self, _: &Action) -> cmp::Ordering { unreachable!() }
    }

    // Pretty-print an item set, for error messages.
    fn pretty(x: &ItemSet<ast::Ident, ast::Name, Action>, pad: &str) -> String {
        let mut r = String::new();
        let mut first = true;
        for item in x.items.iter() {
            if first {
                first = false;
            } else {
                let _ = write!(&mut r, "\n{}", pad);
            }
            let _ = write!(&mut r, "{} ->", item.lhs);
            for j in 0..item.pos {
                let _ = write!(&mut r, " {}", item.rhs.syms[j]);
            }
            let _ = write!(&mut r, " •");
            for j in item.pos..item.rhs.syms.len() {
                let _ = write!(&mut r, " {}", item.rhs.syms[j]);
            }
        }
        r
    }

    let mut parser = cx.new_parser_from_tts(&*tts);
    let token_ty = parser.parse_ty();
    if parser.eat(&token::OpenDelim(token::Brace)) {
        // TODO
        parser.expect(&token::CloseDelim(token::Brace));
    } else {
        parser.expect(&token::Semi);
    }
    let mut rules = BTreeMap::new();
    let mut types = BTreeMap::new();
    let mut start = None;
    while !parser.check(&token::Eof) {
        // parse "LHS: Type {"
        let lhs = parser.parse_ident().name;
        if start.is_none() {
            start = Some(lhs);
        }
        if rules.contains_key(&lhs) {
            let sp = parser.last_span;
            parser.span_err(sp, "duplicate nonterminal");
        }
        parser.expect(&token::Colon);
        let ty = parser.parse_ty();
        types.insert(lhs, ty);
        parser.expect(&token::OpenDelim(token::Brace));
        let mut rhss = Vec::new();
        while !parser.check(&token::CloseDelim(token::Brace)) {
            let mut exclusions = BTreeSet::new();
            while parser.check(&token::Pound) {
                // attributes
                let attr = parser.parse_attribute(false); // don't allow "#![..]" syntax
                match attr.node.value.node {
                    ast::MetaList(ref name, ref tokens) if name == &"no_reduce" => {
                        for token in tokens.iter() {
                            if let ast::MetaWord(ref name) = token.node {
                                exclusions.insert(name.to_string());
                            } else {
                                parser.span_err(token.span, "not the name of a token");
                            }
                        }
                    }
                    _ => parser.span_err(attr.span, "unknown attribute"),
                }
            }
            let lo = parser.span.lo;
            let (rule, binds): (Vec<_>, Vec<_>) = iter::Unfold::new((), |_| {
                if parser.check(&token::FatArrow) {
                    return None;
                }
                let lo = parser.span.lo;
                let name = parser.parse_ident();
                let bind = if parser.eat(&token::OpenDelim(token::Bracket)) {
                    let r = parser.parse_pat();
                    parser.expect(&token::CloseDelim(token::Bracket));
                    Binding::Pat(r)
                } else if parser.eat(&token::OpenDelim(token::Paren)) {
                    let mut pats = vec![];
                    while !parser.eat(&token::CloseDelim(token::Paren)) {
                        pats.push(parser.parse_pat());
                        if !parser.eat(&token::Comma) {
                            parser.expect(&token::CloseDelim(token::Paren));
                            break;
                        }
                    }
                    Binding::Enum(codemap::mk_sp(lo, parser.last_span.hi), pats)
                } else {
                    Binding::None
                };
                Some((name, bind))
            }).unzip();

            parser.expect(&token::FatArrow);

            // start parsing the expr
            let expr = parser.parse_expr_res(parser::RESTRICTION_STMT_EXPR);
            let optional_comma =
                // don't need a comma for blocks...
                classify::expr_is_simple_block(&*expr)
                // or for the last arm
                || parser.check(&token::CloseDelim(token::Brace));

            if optional_comma {
                // consume optional comma
                parser.eat(&token::Comma);
            } else {
                // comma required
                // `expr` may not be complete, so continue parsing until the comma or close-brace
                parser.commit_expr(&*expr, &[token::Comma], &[token::CloseDelim(token::Brace)]);
            }
            let sp = codemap::mk_sp(lo, parser.last_span.hi);

            rhss.push((rule, Action {
                binds: binds,
                expr: expr,
                span: sp,
                exclusions: exclusions,
                exclude_eof: false,
            }));
        }
        parser.expect(&token::CloseDelim(token::Brace));
        rules.insert(lhs, rhss);
    }
    let mut rules: BTreeMap<ast::Name, Vec<_>> = rules.into_iter().map(|(lhs, rhss)| {
        let rhss = rhss.into_iter().map(|(rule, act)| {
            // figure out which symbols in `rule` are nonterminals vs terminals
            let syms = rule.into_iter().map(|ident| {
                if types.contains_key(&ident.name) {
                    Nonterminal(ident.name)
                } else {
                    Terminal(ident)
                }
            }).collect();
            Rhs {
                syms: syms,
                act: act,
            }
        }).collect();
        (lhs, rhss)
    }).collect();
    let start = start.expect("need at least one nonterminal");
    let fake_start = token::gensym("start");
    rules.insert(fake_start, vec![Rhs {
        syms: vec![Nonterminal(start)],
        act: Action {
            binds: vec![],
            expr: cx.expr_unreachable(DUMMY_SP),
            span: DUMMY_SP,
            exclusions: BTreeSet::new(),
            exclude_eof: false,
        },
    }]);
    let grammar = Grammar {
        rules: rules,
        start: fake_start,
    };
    let r = lr1_machine(cx, &grammar, &types, token_ty, name,
        |&ident, cx| {
            cx.pat(DUMMY_SP, ast::PatEnum(cx.path_ident(DUMMY_SP, ident), None))
        },
        |act, cx, syms| {
            let mut expr = act.expr.clone();
            let mut args = vec![];
            for (i, (x, sym)) in act.binds.iter().zip(syms.iter()).enumerate() {
                args.push(match *x {
                    Binding::Pat(ref y) => y.clone(),
                    Binding::Enum(sp, ref pats) => {
                        let id = token::gensym_ident(&*format!("s{}", i));
                        let terminal = match *sym {
                            Nonterminal(..) => {
                                cx.span_err(sp, "can't bind enum case to a nonterminal");
                                token::gensym_ident("error")
                            }
                            Terminal(x) => x
                        };
                        expr = cx.expr_match(act.span, cx.expr_ident(sp, id), vec![
                            cx.arm(sp, vec![cx.pat(sp, ast::PatEnum(cx.path_ident(sp, terminal), Some(pats.clone())))], expr),
                            quote_arm!(cx, _ => unsafe { ::std::intrinsics::unreachable() },),
                        ]);
                        cx.pat_ident(sp, id)
                    }
                    Binding::None => cx.pat_wild(DUMMY_SP),
                });
            }
            (expr, args, act.span)
        },
        |act, token| {
            match token {
                Some(id) => !act.exclusions.contains(id.as_str()),
                None => !act.exclude_eof,
            }
        }
        ).unwrap_or_else(|conflict| {
            match conflict {
                LR1Conflict::ReduceReduce { state, token, r1, r2 } => {
                    cx.span_err(sp, &*format!("reduce-reduce conflict:
state: {}
token: {}", pretty(&state, "       "), token.map(ast::Ident::as_str).unwrap_or("EOF")));
                    cx.span_note(r1.1.act.span, "conflicting rule");
                    cx.span_note(r2.1.act.span, "conflicting rule");
                    panic!(FatalError)
                }
                LR1Conflict::ShiftReduce { state, token, rule } => {
                    cx.span_fatal(rule.1.act.span, &*format!("shift-reduce conflict:
state: {}
token: {}", pretty(&state, "       "), token.map(ast::Ident::as_str).unwrap_or("EOF")))
                }
            }
        });
    base::MacItems::new(Some(r).into_iter())
}

#[plugin_registrar]
pub fn plugin_registrar(reg: &mut rustc::plugin::Registry) {
    reg.register_syntax_extension(token::intern("parser"), base::SyntaxExtension::IdentTT(Box::new(expand_parser) as Box<base::IdentMacroExpander + 'static>, None));
}
