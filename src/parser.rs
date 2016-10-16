use std::collections::{BTreeMap, BTreeSet};
use std::{fmt,cmp};
use std::fmt::Write;
use syntax::ptr::P;
use syntax::util::small_vector::SmallVector;
use syntax::util::ThinVec;
use syntax::{ast, ptr, codemap};
use syntax::parse::{parser, token, classify, PResult};
use syntax::ext::base;
use syntax::ext::build::AstBuilder;
use lalr::*;
use syntax::codemap::DUMMY_SP;
use syntax::ast::DUMMY_NODE_ID;
use syntax::tokenstream::TokenTree;

fn lit_u32(cx: &base::ExtCtxt, val: u32) -> P<ast::Expr> {
    cx.expr_lit(DUMMY_SP, ast::LitKind::Int(val as u64, ast::LitIntType::Unsigned(ast::UintTy::U32)))
}
fn lit_usize(cx: &base::ExtCtxt, val: usize) -> P<ast::Expr> {
    cx.expr_lit(DUMMY_SP, ast::LitKind::Int(val as u64, ast::LitIntType::Unsigned(ast::UintTy::Us)))
}
fn pat_u32(cx: &base::ExtCtxt, val: u32) -> P<ast::Pat> {
    cx.pat_lit(DUMMY_SP, lit_u32(cx, val))
}

fn chop_string(s: &str) -> (String, char) {
    let mut n = s.to_owned();
    let n_len = n.len();
    let last_char = n.as_bytes()[n_len - 1] as char;
    n.truncate(n_len - 1);
    (n, last_char)
}

fn chop_ident(cx: &base::ExtCtxt, ident: ast::Ident) -> (ast::Ident, char) {
    let (s, last_char) = chop_string(&*ident.name.as_str());
    (cx.ident_of(&s), last_char)
}

#[derive(PartialEq, Eq, Copy, Clone)]
struct UnhygienicIdent(ast::Ident);

impl PartialOrd for UnhygienicIdent {
    fn partial_cmp(&self, other: &UnhygienicIdent) -> Option<cmp::Ordering> {
        self.0.name.partial_cmp(&other.0.name)
    }
}

impl Ord for UnhygienicIdent {
    fn cmp(&self, other: &UnhygienicIdent) -> cmp::Ordering {
        self.0.name.cmp(&other.0.name)
    }
}

impl fmt::Debug for UnhygienicIdent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl fmt::Display for UnhygienicIdent {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.0.fmt(f)
    }
}

fn most_frequent<T: Ord, I: Iterator<Item=T>>(it: I) -> Option<T> {
    let mut freq = BTreeMap::new();
    for x in it {
        *freq.entry(x).or_insert(0) += 1;
    }
    freq.into_iter().fold(None, |best, (x, f)| match best {
        None => Some((x, f)),
        Some((x2, f2)) => if f > f2 { Some((x, f)) } else { Some((x2, f2)) },
    }).map(|(x, _)| x)
}

fn expected_one_of<S: fmt::Display>(xs: &[S]) -> String {
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

pub fn lr1_machine<'a, T, N, A, FM, FA, FR, FO, FF>(
    cx: &mut base::ExtCtxt,
    grammar: &'a Grammar<T, N, A>,
    types: &BTreeMap<N, P<ast::Ty>>,
    token_ty: P<ast::Ty>,
    span_ty: P<ast::Ty>,
    range_fn_id: ast::Ident,
    range_fn: P<ast::Item>,
    name: ast::Ident,
    mut to_pat: FM,
    mut to_expr: FA,
    reduce_on: FR,
    priority_of: FO,
    format_terminal: FF,
) -> Result<P<ast::Item>, LR1Conflict<'a, T, N, A>>
where T: Ord + fmt::Debug + fmt::Display,
      N: Ord + fmt::Debug,
      A: fmt::Debug,
      FM: FnMut(&T, &base::ExtCtxt) -> P<ast::Pat>,
      FA: FnMut(&N, &A, &base::ExtCtxt, &[Symbol<T, N>]) -> (P<ast::Expr>, Vec<Option<P<ast::Pat>>>, codemap::Span),
      FR: FnMut(&Rhs<T, N, A>, Option<&T>) -> bool,
      FO: FnMut(&Rhs<T, N, A>, Option<&T>) -> i32,
      FF: Fn(&T) -> String,
{
    let actual_start = match grammar.rules.get(&grammar.start).unwrap()[0].syms[0] {
        Terminal(_) => panic!("bad grammar"),
        Nonterminal(ref x) => x,
    };
    let table: LR1ParseTable<T, N, A> = try!(grammar.lalr1(reduce_on, priority_of));
    let it_ty_id = token::gensym_ident("I");
    let it_ty = cx.ty_ident(DUMMY_SP, it_ty_id);
    let u32_ty = quote_ty!(cx, u32);
    let token_span_ty = cx.ty(DUMMY_SP, ast::TyKind::Tup(vec![
        token_ty.clone(),
        span_ty.clone(),
    ]));
    let generics = ast::Generics {
        lifetimes: vec![],
        ty_params: ptr::P::from_vec(vec![
            cx.typaram(DUMMY_SP, it_ty_id, vec![], ptr::P::from_vec(vec![
                cx.typarambound(cx.path_all(DUMMY_SP, true, vec![
                    cx.ident_of("std"),
                    cx.ident_of("iter"),
                    cx.ident_of("Iterator"),
                ], vec![], vec![], vec![
                    ast::TypeBinding {
                        id: DUMMY_NODE_ID,
                        ident: cx.ident_of("Item"),
                        ty: token_span_ty.clone(),
                        span: DUMMY_SP,
                    }
                ]))
            ]), None)
        ]),
        where_clause: ast::WhereClause {
            id: DUMMY_NODE_ID,
            predicates: vec![]
        },
        span: DUMMY_SP,
    };
    let it_arg_id = token::gensym_ident("it");
    let args = vec![
        ast::Arg {
            ty: it_ty,
            pat: cx.pat_ident_binding_mode(DUMMY_SP, it_arg_id,
                                           ast::BindingMode::ByValue(ast::Mutability::Mutable)),
            id: DUMMY_NODE_ID,
        }
    ];
    let rule_fn_ids: BTreeMap<_, _> = grammar.rules.iter()
        .filter(|&(lhs, _)| *lhs != grammar.start)
        .flat_map(|(_, rhss)| {
            // Identify rules by their RHS, which should have unique addresses
            rhss.iter().map(|rhs| rhs as *const _)
        })
        .enumerate()
        .map(|(i, k)| (k, token::gensym_ident(&format!("reduce_{}", i))))
        .collect();
    let goto_fn_ids: BTreeMap<_, _> = grammar.rules.keys()
        .filter(|&lhs| *lhs != grammar.start)
        .enumerate()
        .map(|(i, lhs)| (lhs, token::gensym_ident(&format!("goto_{}", i))))
        .collect();
    let stack_id = token::gensym_ident("stack");
    let span_stack_id = token::gensym_ident("span_stack");
    let state_stack_id = token::gensym_ident("state_stack");
    let state_id = token::gensym_ident("state");
    let token_id = token::gensym_ident("token");
    let span_id = token::gensym_ident("current_span");
    let token_span_id = token::gensym_ident("token_span");
    let next_state_id = token::gensym_ident("next_state");
    let unreachable = cx.expr_unreachable(DUMMY_SP);

    let mut stmts = Vec::new();

    stmts.push(cx.stmt_item(DUMMY_SP, range_fn));
    let range_array_fn_id = token::gensym_ident("range_array");
    stmts.push(quote_stmt!(cx, fn $range_array_fn_id(x: &[Option<$span_ty>]) -> Option<$span_ty> {
        if let Some(lo) = x.iter().filter_map(|&x| x).next() {
            let hi = x.iter().rev().filter_map(|&x| x).next().unwrap();
            Some($range_fn_id(lo, hi))
        } else {
            None
        }
    }).unwrap());
    let stack_ty = quote_ty!(cx, Vec<Box<::std::any::Any> >);
    let span_stack_ty = quote_ty!(cx, Vec<Option<$span_ty> >);
    let state_stack_ty = quote_ty!(cx, Vec<u32>);
    for (lhs, rhss) in grammar.rules.iter() {
        if *lhs == grammar.start {
            continue;
        }
        let goto_fn = *goto_fn_ids.get(lhs).unwrap();
        let lhs_ty = types.get(lhs).unwrap();
        for rhs in rhss.iter() {
            let (result, arg_pats, span) = to_expr(lhs, &rhs.act, cx, &rhs.syms);
            let args = vec![ast::Arg {
                ty: cx.ty_rptr(DUMMY_SP, stack_ty.clone(), None, ast::Mutability::Mutable),
                pat: cx.pat_ident(DUMMY_SP, stack_id),
                id: DUMMY_NODE_ID,
            }, ast::Arg {
                ty: cx.ty_rptr(DUMMY_SP, span_stack_ty.clone(), None, ast::Mutability::Mutable),
                pat: cx.pat_ident(DUMMY_SP, span_stack_id),
                id: DUMMY_NODE_ID,
            }, ast::Arg {
                ty: cx.ty_rptr(DUMMY_SP, state_stack_ty.clone(), None, ast::Mutability::Mutable),
                pat: cx.pat_ident(DUMMY_SP, state_stack_id),
                id: DUMMY_NODE_ID,
            }, ast::Arg {
                ty: cx.ty_rptr(DUMMY_SP, u32_ty.clone(), None, ast::Mutability::Mutable),
                pat: cx.pat_ident(DUMMY_SP, state_id),
                id: DUMMY_NODE_ID,
            }];
            let len = lit_usize(cx, rhs.syms.len());
            let mut reduce_stmts: Vec<_> = vec![ ];
            if rhs.syms.len() > 0 {
                reduce_stmts.push(quote_stmt!(cx, let $span_id = $range_array_fn_id(&$span_stack_id[($span_stack_id.len() - $len)..]);).unwrap());
                // XXX: Annoying syntax :(
                reduce_stmts.push(quote_stmt!(cx, match $span_stack_id.len() - $len { x => $span_stack_id.truncate(x) };).unwrap());
                // Make the current_span available to the user by exposing it through a macro
                reduce_stmts.push(quote_stmt!(cx, macro_rules! span {
                    () => { $span_id.unwrap() }
                }).unwrap());
            } else {
                reduce_stmts.push(quote_stmt!(cx, let $span_id = None;).unwrap());
            }
            reduce_stmts.extend(rhs.syms.iter()
            .zip(arg_pats.into_iter())
            .rev()
            .map(|(sym, maybe_pat)| match maybe_pat {
                Some(pat) => {
                    let ty = match *sym {
                        Terminal(_) => token_ty.clone(),
                        Nonterminal(ref n) => types.get(n).unwrap().clone(),
                    };
                    let local = P(ast::Local {
                        pat: pat,
                        ty: Some(ty.clone()),
                        init: Some(quote_expr!(cx, *$stack_id.pop().unwrap().downcast::<$ty>().unwrap())),
                        id: DUMMY_NODE_ID,
                        span: DUMMY_SP,
                        attrs: ThinVec::new(),
                    });
                    ast::Stmt {
                        id: DUMMY_NODE_ID,
                        span: DUMMY_SP,
                        node: ast::StmtKind::Local(local),
                    }
                }
                None => cx.stmt_semi(cx.expr_method_call(DUMMY_SP,
                                                         cx.expr_ident(DUMMY_SP, stack_id),
                                                         cx.ident_of("pop"),
                                                         vec![])),
            }));
            if rhs.syms.len() > 1 {
                let len_minus_one = lit_usize(cx, rhs.syms.len() - 1);
                // XXX: Annoying syntax :(
                reduce_stmts.push(quote_stmt!(cx, match $state_stack_id.len() - $len_minus_one { x => unsafe { $state_stack_id.set_len(x) } };).unwrap());
            } else if rhs.syms.len() == 0 {
                reduce_stmts.push(quote_stmt!(cx, $state_stack_id.push(*$state_id);).unwrap());
            }
            reduce_stmts.push(quote_stmt!(cx, *$state_id = $goto_fn(*$state_stack_id.last().unwrap());).unwrap());
            let rspan = result.span;

            let tmp = token::gensym_ident("result");
            reduce_stmts.push(cx.stmt_let_typed(DUMMY_SP, false, tmp, lhs_ty.clone(), result));
            reduce_stmts.push(quote_stmt!(cx,
                $stack_id.push(Box::new($tmp) as Box<::std::any::Any>);
            ).unwrap());
            reduce_stmts.push(quote_stmt!(cx, $span_stack_id.push($span_id);).unwrap());

            let block = cx.block(rspan, reduce_stmts);
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
                        pats_by_dest.entry(dest)
                            .or_insert(vec![])
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
            unreachable.clone()
        };
        let f = cx.item_fn(DUMMY_SP, *id, vec![
            cx.arg(DUMMY_SP, state_id, u32_ty.clone())
        ], u32_ty.clone(), cx.block_expr(expr));
        stmts.push(cx.stmt_item(DUMMY_SP, f));
    }
    stmts.push(cx.stmt_let(DUMMY_SP, true, stack_id, quote_expr!(cx, ::std::vec::Vec::new())));
    stmts.push(cx.stmt_let(DUMMY_SP, true, span_stack_id, quote_expr!(cx, ::std::vec::Vec::new())));
    stmts.push(cx.stmt_let(DUMMY_SP, true, state_stack_id, quote_expr!(cx, ::std::vec::Vec::new())));
    stmts.push(cx.stmt_let(DUMMY_SP, true, state_id, quote_expr!(cx, 0)));
    stmts.push(cx.stmt_let(DUMMY_SP, true, token_span_id, quote_expr!(cx, $it_arg_id.next())));
    stmts.push(cx.stmt_semi(cx.expr_loop(DUMMY_SP, cx.block(DUMMY_SP, vec![
        cx.stmt_let(DUMMY_SP, false, next_state_id, cx.expr_match(DUMMY_SP, cx.expr_ident(DUMMY_SP, state_id),
            table.states.iter().enumerate().map(|(ix, state)| {
                let mut arms = vec![];
                let mut reduce_arms = BTreeMap::new();
                let mut expected = vec![];
                for (&tok, action) in state.lookahead.iter() {
                    expected.push(format!("`{}`", format_terminal(tok)));
                    let pat = cx.pat_some(DUMMY_SP, cx.pat_tuple(DUMMY_SP, vec![to_pat(tok, cx), cx.pat_wild(DUMMY_SP)]));
                    let arm_expr = match *action {
                        LRAction::Shift(dest) => lit_u32(cx, dest as u32),
                        LRAction::Reduce(_, rhs) => {
                            reduce_arms.entry(rhs as *const _).or_insert(vec![]).push(pat);
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
                            reduce_arms.entry(rhs as *const _).or_insert(vec![]).push(pat);
                        }
                        LRAction::Accept => {
                            let ty = types.get(actual_start).unwrap();
                            let arm_expr = quote_expr!(cx,
                                return Ok(*$stack_id.pop().unwrap().downcast::<$ty>().unwrap()));
                            arms.push(cx.arm(DUMMY_SP, vec![pat], arm_expr));
                        }
                    };
                }
                for (rhs_ptr, pats) in reduce_arms.into_iter() {
                    let reduce_fn = *rule_fn_ids.get(&rhs_ptr).unwrap();
                    arms.push(cx.arm(DUMMY_SP, pats, quote_expr!(cx, {
                        $reduce_fn(&mut $stack_id, &mut $span_stack_id, &mut $state_stack_id, &mut $state_id);
                        continue
                    })));
                }
                let err_msg_lit = cx.expr_str(DUMMY_SP, token::intern_and_get_ident(&*expected_one_of(&*expected)));
                arms.push(quote_arm!(cx, _ => return Err(($token_span_id, $err_msg_lit)),));
                cx.arm(DUMMY_SP,
                    vec![pat_u32(cx, ix as u32)],
                    cx.expr_match(DUMMY_SP, cx.expr_ident(DUMMY_SP, token_span_id),
                    arms))
            }).chain(Some(quote_arm!(cx, _ => $unreachable,)).into_iter()).collect())),
        quote_stmt!(cx, match $token_span_id {
            Some(($token_id, $span_id)) => {
                $stack_id.push(Box::new($token_id) as Box<::std::any::Any>);
                $span_stack_id.push(Some($span_id));
            }
            None => $unreachable,
        };).unwrap(),
        quote_stmt!(cx, $state_stack_id.push($state_id);).unwrap(),
        quote_stmt!(cx, $token_span_id = $it_arg_id.next();).unwrap(),
        quote_stmt!(cx, $state_id = $next_state_id;).unwrap(),
    ]))));
    let body = cx.block(DUMMY_SP, stmts);
    let out_ty = cx.ty_path(cx.path_all(DUMMY_SP,
                                        true,
                                        vec![cx.ident_of("std"), cx.ident_of("result"), cx.ident_of("Result")],
                                        vec![],
                                        vec![types.get(actual_start).unwrap().clone(),
                                             quote_ty!(cx, (Option<$token_span_ty>, &'static str))],
                                        vec![]));
    Ok(cx.item_fn_poly(DUMMY_SP, name, args, out_ty, generics, body))
}

pub fn expand_parser<'a>(
    cx: &'a mut base::ExtCtxt,
    sp: codemap::Span,
    tts: &[TokenTree]
) -> Box<base::MacResult + 'a> {
    parse_parser(cx, sp, tts).unwrap_or_else(|_| base::DummyResult::any(sp))
}

fn parse_parser<'a>(
    cx: &mut base::ExtCtxt<'a>,
    sp: codemap::Span,
    tts: &[TokenTree]
) -> PResult<'a, Box<base::MacResult + 'a>> {
    #[derive(Debug)]
    enum Binding {
        Pat(P<ast::Pat>),
        Enum(codemap::Span, Vec<P<ast::Pat>>),
        None,
    }

    #[derive(Debug)]
    struct Action {
        binds: Vec<Binding>,
        expr: P<ast::Expr>,
        span: codemap::Span,
        exclusions: BTreeSet<String>,
        exclude_eof: bool,
        priority: i32,
    }

    fn pretty_rule(lhs: ast::Name, syms: &[Symbol<UnhygienicIdent, ast::Name>]) -> String {
        let mut r = String::new();
        let _ = write!(&mut r, "{} ->", lhs);
        for sym in syms.iter() {
            let _ = write!(&mut r, " {}", sym);
        }
        r
    }
    // Pretty-print an item set, for error messages.
    fn pretty(x: &ItemSet<UnhygienicIdent, ast::Name, Action>, pad: &str) -> String {
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

    let mut parser = cx.new_parser_from_tts(tts);

    // parse 'fn name_of_parser(Token, Span);'
    let visibility = if parser.eat_keyword(token::keywords::Pub) {
        ast::Visibility::Public
    } else {
        ast::Visibility::Inherited
    };
    try!(parser.expect_keyword(token::keywords::Fn));
    let name = try!(parser.parse_ident());
    try!(parser.expect(&token::OpenDelim(token::Paren)));
    let token_ty = try!(parser.parse_ty());
    try!(parser.expect(&token::Comma));
    let span_ty = try!(parser.parse_ty());
    try!(parser.expect(&token::CloseDelim(token::Paren)));
    try!(parser.expect(&token::Semi));

    let range_fn_id = token::gensym_ident("range");
    let range_fn = {
        let lo = parser.span.lo;
        try!(parser.expect(&token::OpenDelim(token::Paren)));
        let p1_sp = parser.span;
        let p1 = try!(parser.parse_ident());
        try!(parser.expect(&token::Comma));
        let p2_sp = parser.span;
        let p2 = try!(parser.parse_ident());
        try!(parser.expect(&token::CloseDelim(token::Paren)));
        let body = try!(parser.parse_block());
        let hi = parser.last_span.hi;
        cx.item_fn(codemap::mk_sp(lo, hi), range_fn_id, vec![
            cx.arg(p1_sp, p1, span_ty.clone()),
            cx.arg(p2_sp, p2, span_ty.clone()),
        ], span_ty.clone(), body)
    };

    let mut rules = BTreeMap::new();
    let mut types = BTreeMap::new();
    let mut start = None;
    while !parser.check(&token::Eof) {
        // parse "LHS: Type {"
        let mut lhs_str = (*try!(parser.parse_ident()).name.as_str()).to_owned();
        lhs_str = lhs_str + "(";
        let lhs = cx.ident_of(&lhs_str).name;
        if start.is_none() {
            start = Some(lhs);
        }
        if rules.contains_key(&lhs) {
            let sp = parser.last_span;
            parser.span_err(sp, "duplicate nonterminal");
        }
        try!(parser.expect(&token::Colon));
        let ty = try!(parser.parse_ty());
        types.insert(lhs, ty);
        try!(parser.expect(&token::OpenDelim(token::Brace)));
        let mut rhss = Vec::new();
        while !parser.check(&token::CloseDelim(token::Brace)) {
            let mut exclusions = BTreeSet::new();
            let mut priority = 0;
            while parser.check(&token::Pound) {
                // attributes
                let attr = try!(parser.parse_attribute(false)); // don't allow "#![..]" syntax
                match attr.node.value.node {
                    ast::MetaItemKind::List(ref name, ref tokens) if name == &"no_reduce" => {
                        for token in tokens.iter() {
                            if let ast::NestedMetaItemKind::MetaItem(ref meta_item) = token.node {
                                if let ast::MetaItemKind::Word(ref name) = meta_item.node {
                                    exclusions.insert(name.to_string());
                                    continue;
                                }
                            }
                            parser.span_err(token.span, "not the name of a token");
                        }
                    }
                    ast::MetaItemKind::Word(ref name) if name == &"overriding" => {
                        priority = 1;
                    }
                    _ => parser.span_err(attr.span, "unknown attribute"),
                }
            }
            let lo = parser.span.lo;
            let (mut rule, mut binds) = (vec![], vec![]);
            while !parser.check(&token::FatArrow) {
                let lo = parser.span.lo;
                let mut name = (*try!(parser.parse_ident()).name.as_str()).to_owned();
                let bind = if parser.eat(&token::OpenDelim(token::Bracket)) {
                    let r = try!(parser.parse_pat());
                    try!(parser.expect(&token::CloseDelim(token::Bracket)));
                    name += "(";
                    Binding::Pat(r)
                } else if parser.eat(&token::OpenDelim(token::Paren)) {
                    let mut pats = vec![];
                    while !parser.eat(&token::CloseDelim(token::Paren)) {
                        pats.push(try!(parser.parse_pat()));
                        if !parser.eat(&token::Comma) {
                            try!(parser.expect(&token::CloseDelim(token::Paren)));
                            break;
                        }
                    }
                    name += "(";
                    Binding::Enum(codemap::mk_sp(lo, parser.last_span.hi), pats)
                } else {
                    name += ")";
                    Binding::None
                };
                rule.push(UnhygienicIdent(cx.ident_of(&name)));
                binds.push(bind);
            }
            let (rule, binds) = (rule, binds);

            try!(parser.expect(&token::FatArrow));

            // start parsing the expr
            let expr = try!(parser.parse_expr_res(parser::Restrictions::RESTRICTION_STMT_EXPR, None));
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
                try!(parser.expect_one_of(&[token::Comma], &[token::CloseDelim(token::Brace)]));
            }
            let sp = codemap::mk_sp(lo, parser.last_span.hi);

            rhss.push((rule, Action {
                binds: binds,
                expr: expr,
                span: sp,
                exclusions: exclusions,
                exclude_eof: false,
                priority: priority,
            }));
        }
        try!(parser.expect(&token::CloseDelim(token::Brace)));
        rules.insert(lhs, rhss);
    }
    let mut rules: BTreeMap<ast::Name, Vec<_>> = rules.into_iter().map(|(lhs, rhss)| {
        let rhss = rhss.into_iter().map(|(rule, act)| {
            // figure out which symbols in `rule` are nonterminals vs terminals
            let syms = rule.into_iter().map(|ident| {
                if types.contains_key(&ident.0.name) {
                    Nonterminal(ident.0.name)
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
    let unreachable = cx.expr_unreachable(DUMMY_SP);
    rules.insert(fake_start, vec![Rhs {
        syms: vec![Nonterminal(start)],
        act: Action {
            binds: vec![],
            expr: unreachable.clone(),
            span: DUMMY_SP,
            exclusions: BTreeSet::new(),
            exclude_eof: false,
            priority: -1,
        },
    }]);
    let grammar = Grammar {
        rules: rules,
        start: fake_start,
    };
    let r = try!(lr1_machine(cx, &grammar, &types, token_ty, span_ty, range_fn_id, range_fn, name,
        |&ident, cx| {
            let (nident, last_char) = chop_ident(cx, ident.0);
            match last_char {
                '(' => {
                    cx.pat(DUMMY_SP, ast::PatKind::TupleStruct(cx.path_ident(DUMMY_SP, nident), vec![], Some(0)))
                }
                ')' => {
                    cx.pat(DUMMY_SP, ast::PatKind::Ident(ast::BindingMode::ByValue(ast::Mutability::Immutable), codemap::Spanned { node: nident, span: DUMMY_SP }, None))
                }
                _ => {
                    unreachable!("didn't end in ( or !; got {}", name)
                }

            }
        },
        |lhs, act, cx, syms| {
            let mut expr = act.expr.clone();
            let mut args = vec![];
            for (i, (x, sym)) in act.binds.iter().zip(syms.iter()).enumerate() {
                args.push(match *x {
                    Binding::Pat(ref y) => Some(y.clone()),
                    Binding::Enum(sp, ref pats) => {
                        let id = token::gensym_ident(&*format!("s{}", i));
                        let terminal = match *sym {
                            Nonterminal(..) => {
                                cx.span_err(sp, "can't bind enum case to a nonterminal");
                                token::gensym_ident("error")
                            }
                            Terminal(x) => {
                                let (ident, _) = chop_ident(cx, x.0);
                                ident
                            }
                        };
                        expr = cx.expr_match(act.span, cx.expr_ident(sp, id), vec![
                            cx.arm(sp, vec![cx.pat(sp, ast::PatKind::TupleStruct(cx.path_ident(sp, terminal), pats.clone(), None))], expr),
                            quote_arm!(cx, _ => $unreachable,),
                        ]);
                        Some(cx.pat_ident(sp, id))
                    }
                    Binding::None => None,
                });
            }

            // XXX: should be a cargo feature (?)
            if false {
                let rule_str = pretty_rule(*lhs, syms);
                let rule_str = &*rule_str;
                expr = P(quote_expr!(cx, {
                    println!("reduce by {}", $rule_str);
                    $expr
                }).unwrap());
            }

            (expr, args, act.span)
        },
        |rhs, token| {
            match token {
                Some(id) => !rhs.act.exclusions.contains(&id.0.name.to_string()),
                None => !rhs.act.exclude_eof,
            }
        },
        |rhs, _| rhs.act.priority,
        |&ident| {
            chop_string(&*ident.0.name.as_str()).0
        },
    ).or_else(|conflict| {
            match conflict {
                LR1Conflict::ReduceReduce { state, token, r1, r2 } => {
                    let mut err = parser.diagnostic().struct_span_err(
                        sp, &*format!("reduce-reduce conflict:
state: {}
token: {}", pretty(&state, "       "),
            match token { Some(id) => id.0.name.to_string(),
                          None     => "EOF".to_string() }));
                    err.span_note(r1.1.act.span, "conflicting rule");
                    err.span_note(r2.1.act.span, "conflicting rule");
                    Err(err)
                }
                LR1Conflict::ShiftReduce { state, token, rule } => {
                    cx.span_err(rule.1.act.span, &*format!("shift-reduce conflict:
state: {}
token: {}", pretty(&state, "       "),
            match token { Some(id) => id.0.name.to_string(),
                          None     => "EOF".to_string() }));
                    Err(cx.struct_span_err(rule.1.act.span, "shift-reduce"))
                }
            }
        })).map(|mut item| { item.vis = visibility; item} );
    Ok(base::MacEager::items(SmallVector::one(r)))
}
