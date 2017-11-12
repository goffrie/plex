use std::collections::{BTreeMap, BTreeSet};
use std::collections::btree_map::Entry;
use std::fmt::{self, Write};

use lalr::*;

use syn::buffer::Cursor;
use syn::synom::{PResult, Synom};
use syn::{self, Attribute, Block, Expr, Ident, Meta, NestedMeta, Pat, Type, Visibility};
use quote::{ToTokens, Tokens};
use proc_macro2::{Delimiter, Span};
use proc_macro::{self, TokenStream};

/// Return the most frequent item in the given iterator, or None if it is empty.
/// Picks an arbitrary item in case of a tie.
fn most_frequent<T: Ord, I: Iterator<Item = T>>(it: I) -> Option<T> {
    let mut freq = BTreeMap::new();
    for x in it {
        *freq.entry(x).or_insert(0) += 1;
    }
    freq.into_iter().max_by_key(|&(_, f)| f).map(|(x, _)| x)
}

fn expected_one_of<S: fmt::Display>(xs: &[S]) -> String {
    let mut err_msg: String = "expected".to_string();
    for (i, x) in xs.iter().enumerate() {
        if i == 0 {
            let _ = write!(&mut err_msg, " ");
        } else if i == xs.len() - 1 {
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

pub fn lr1_machine<'a, T, N, A, FM, FA, FR, FO>(
    grammar: &'a Grammar<T, N, A>,
    types: &BTreeMap<N, Type>,
    token_ty: Type,
    span_ty: Type,
    range_fn: Option<(Ident, Ident, Block)>,
    vis: Visibility,
    name: Ident,
    mut to_pat: FM,
    mut to_expr: FA,
    reduce_on: FR,
    priority_of: FO,
) -> Result<Tokens, LR1Conflict<'a, T, N, A>>
where
    T: Ord + fmt::Debug + fmt::Display,
    N: Ord + fmt::Debug,
    A: fmt::Debug,
    FM: FnMut(&T) -> Tokens,
    FA: FnMut(&N, &A, &[Symbol<T, N>]) -> (Tokens, Vec<Option<Tokens>>, Span),
    FR: FnMut(&Rhs<T, N, A>, Option<&T>) -> bool,
    FO: FnMut(&Rhs<T, N, A>, Option<&T>) -> i32,
{
    let actual_start = match grammar
        .rules
        .get(&grammar.start)
        .expect("Grammar didn't contain its start nonterminal")[0]
        .syms[0]
    {
        Terminal(_) => panic!("bad grammar"),
        Nonterminal(ref x) => x,
    };
    let any_ty = quote_spanned!(Span::call_site() => ::std::any::Any);
    let start_ty = &types[actual_start];
    let table: LR1ParseTable<T, N, A> = grammar.lalr1(reduce_on, priority_of)?;
    let rule_fn_ids: BTreeMap<_, _> = grammar
        .rules
        .iter()
        .filter(|&(lhs, _)| *lhs != grammar.start)
        .flat_map(|(_, rhss)| {
            // Identify rules by their RHS, which should have unique addresses
            // FIXME: maybe not the best idea
            rhss.iter().map(|rhs| rhs as *const _)
        })
        .enumerate()
        .map(|(i, k)| (k, Ident::from(format!("reduce_{}", i))))
        .collect();
    let goto_fn_ids: BTreeMap<_, _> = grammar
        .rules
        .keys()
        .filter(|&lhs| *lhs != grammar.start)
        .enumerate()
        .map(|(i, lhs)| (lhs, Ident::from(format!("goto_{}", i))))
        .collect();

    let mut stmts = Vec::new();

    stmts.push(if let Some((a, b, body)) = range_fn {
        quote!(fn range(#a: #span_ty, #b: #span_ty) -> #span_ty {
            #body
        })
    } else {
        quote!(fn range(_a: (), _b: ()) {})
    });
    stmts.push(
        quote!(fn range_array(x: &[Option<#span_ty>]) -> Option<#span_ty> {
            if let Some(lo) = x.iter().filter_map(|&x| x).next() {
                let hi = x.iter().rev().filter_map(|&x| x).next().unwrap();
                Some(range(lo, hi))
            } else {
                None
            }
        }),
    );
    // The `lhs`s which are actually unreachable; as such, their associated code should not be generated.
    let mut lhs_unreachable = BTreeSet::new();
    for (lhs, id) in &goto_fn_ids {
        let expr = if let Some(&most_freq) =
            most_frequent(table.states.iter().filter_map(|state| state.goto.get(lhs)))
        {
            let most_freq = most_freq as u32;
            let mut pats_by_dest = BTreeMap::new();
            for (ix, state) in table.states.iter().enumerate() {
                let ix = ix as u32;
                if let Some(&dest) = state.goto.get(lhs) {
                    let dest = dest as u32;
                    if dest != most_freq {
                        pats_by_dest.entry(dest).or_insert(vec![]).push(quote!(#ix));
                    }
                }
            }
            let mut arms: Vec<_> = pats_by_dest
                .into_iter()
                .map(|(dest, pats)| quote!(#(#pats)|* => #dest,))
                .collect();
            arms.push(quote!(_ => #most_freq,));
            quote!(match state { #(#arms)* })
        } else {
            // This shouldn't normally happen, but it can when `lhs` is unused in the
            // grammar.
            lhs_unreachable.insert(lhs);
            continue;
        };
        stmts.push(quote!(fn #id(state: u32) -> u32 {
            #expr
        }));
    }
    for (lhs, rhss) in &grammar.rules {
        if *lhs == grammar.start || lhs_unreachable.contains(&lhs) {
            continue;
        }
        let goto_fn = goto_fn_ids[lhs];
        let lhs_ty = &types[lhs];
        for rhs in rhss.iter() {
            let (result, arg_pats, rhs_span) = to_expr(lhs, &rhs.act, &rhs.syms);
            let span = rhs_span.resolved_at(Span::def_site());
            let len = rhs.syms.len();
            let current_span_stmt = if rhs.syms.len() > 0 {
                let current_span_ident = quote_spanned!(span => current_span);
                // Make the current_span available to the user by exposing it through a macro whose name is unhygienic.
                let span_macro = quote_spanned!(rhs_span.resolved_at(Span::call_site()) =>
                    #[allow(unused_macros)] macro_rules! span {
                        () => { #current_span_ident.unwrap() }
                    });
                quote_spanned!(span =>
                    let current_span: Option<#span_ty> = {
                        let sp = range_array(&span_stack[(span_stack.len() - #len)..]);
                        let newlen = span_stack.len() - #len;
                        span_stack.truncate(newlen);
                        sp
                    };
                    #span_macro
                )
            } else {
                quote_spanned!(span =>
                    let current_span: Option<#span_ty> = None;
                )
            };
            let mut reduce_stmts = vec![current_span_stmt];
            reduce_stmts.extend(rhs.syms.iter().zip(arg_pats.iter().cloned()).rev().map(
                |(sym, maybe_pat)| match maybe_pat {
                    // TODO: maybe use an even more precise span
                    Some(pat) => {
                        let ty = match *sym {
                            Terminal(_) => token_ty.clone(),
                            Nonterminal(ref n) => types[n].clone(),
                        };
                        quote_spanned!(span =>
                            let #pat: #ty = *stack.pop().unwrap().downcast().unwrap();
                        )
                    }
                    None => quote_spanned!(span => stack.pop();),
                },
            ));
            if rhs.syms.len() > 1 {
                let len_minus_one = rhs.syms.len() - 1;
                // XXX: Annoying syntax :(
                reduce_stmts.push(
                    quote_spanned!(span => match state_stack.len() - #len_minus_one { x => state_stack.truncate(x) };),
                );
            } else if rhs.syms.len() == 0 {
                reduce_stmts.push(quote_spanned!(span => state_stack.push(*state);));
            }
            reduce_stmts.push(quote_spanned!(
                span =>
                *state = #goto_fn(*state_stack.last().unwrap());
                let result: #lhs_ty = ( || -> #lhs_ty { #result } )();
                stack.push(Box::new(result) as Box<#any_ty>);
                span_stack.push(current_span);
            ));

            let fn_id = rule_fn_ids.get(&(rhs as *const _)).unwrap().clone();
            stmts.push(quote_spanned!(
                span =>
                fn #fn_id(
                    stack: &mut Vec<Box<#any_ty>>,
                    span_stack: &mut Vec<Option<#span_ty>>,
                    state_stack: &mut Vec<u32>,
                    state: &mut u32,
                ) {
                    #(#reduce_stmts)*
                }
            ));
        }
    }
    stmts.push(quote!(
        let mut stack = Vec::new();
        let mut span_stack = Vec::new();
        let mut state_stack = Vec::new();
        let mut state: u32 = 0;
        let mut token_span = it.next();
    ));
    stmts.push({
        let state_arms = table.states.iter().enumerate().map(|(ix, state)| {
            let mut arms = vec![];
            let mut reduce_arms = BTreeMap::new();
            let mut expected = vec![];
            for (&tok, action) in &state.lookahead {
                expected.push(format!("`{}`", tok));
                let tok_pat = to_pat(tok);
                let pat = quote!(Some((#tok_pat, _)));
                let arm_expr = match *action {
                    LRAction::Shift(dest) => dest as u32,
                    LRAction::Reduce(_, rhs) => {
                        reduce_arms
                            .entry(rhs as *const _)
                            .or_insert(vec![])
                            .push(pat);
                        continue;
                    }
                    LRAction::Accept => unreachable!(),
                };
                arms.push(quote!(#pat => #arm_expr,));
            }
            if let Some(ref action) = state.eof {
                expected.push("end of file".into());
                let pat = quote!(None);
                match *action {
                    LRAction::Shift(_) => unreachable!(),
                    LRAction::Reduce(_, rhs) => {
                        reduce_arms
                            .entry(rhs as *const _)
                            .or_insert(vec![])
                            .push(pat);
                    }
                    LRAction::Accept => {
                        arms.push(
                            quote!(#pat => return Ok(*stack.pop().unwrap().downcast::<#start_ty>().unwrap()),),
                        );
                    }
                };
            }
            for (rhs_ptr, pats) in reduce_arms.into_iter() {
                let reduce_fn = rule_fn_ids[&rhs_ptr];
                arms.push(quote!(#(#pats)|* => {
                    #reduce_fn(&mut stack, &mut span_stack, &mut state_stack, &mut state);
                    continue
                }));
            }
            let err_msg = expected_one_of(&expected);
            arms.push(quote!(_ => return Err((token_span, #err_msg)),));
            let ix = ix as u32;
            quote!(#ix => match token_span { #(#arms)* })
        });
        quote!(
            loop {
                let next_state = match state {
                    #(#state_arms)*
                    _ => unreachable!(),
                };
                match token_span {
                    Some((token, span)) => {
                        stack.push(Box::new(token) as Box<#any_ty>);
                        span_stack.push(Some(span));
                    }
                    None => unreachable!(),
                };
                state_stack.push(state);
                token_span = it.next();
                state = next_state;
            }
        )
    });
    Ok(quote!(
        #vis fn #name<I: Iterator<Item=(#token_ty, #span_ty)>>(mut it: I) -> Result<#start_ty, (Option<(#token_ty, #span_ty)>, &'static str)> {
            #(#stmts)*
        }
    ))
}

#[derive(Debug)]
enum RuleRhsItem {
    Symbol(Ident),
    SymbolPat(Ident, Pat),
    Destructure(Ident, Span, Vec<Pat>),
}

impl RuleRhsItem {
    fn ident(&self) -> Ident {
        match *self {
            RuleRhsItem::Symbol(ident)
            | RuleRhsItem::SymbolPat(ident, _)
            | RuleRhsItem::Destructure(ident, _, _) => ident,
        }
    }
}

#[derive(Debug)]
struct Rule {
    rhs: Vec<RuleRhsItem>,
    rhs_span: proc_macro::Span,
    action: Tokens,
    exclusions: BTreeSet<Ident>,
    exclude_eof: bool,
    priority: i32,
}

fn parse_rules(mut input: Cursor) -> PResult<Vec<Rule>> {
    let mut rules = vec![];
    while !input.eof() {
        // FIXME: Make some nicer error messages, preferably when syn supports it.
        let mut exclusions = BTreeSet::new();
        let mut exclude_eof = false;
        let mut priority = 0;
        let (attrs, input_) = many0!(input, call!(Attribute::parse_outer))?;
        input = input_;
        for attr in attrs {
            let meta = attr.interpret_meta().unwrap();
            match meta {
                Meta::List(ref list) if list.ident == "no_reduce" => {
                    for token in &list.nested {
                        if let NestedMeta::Meta(Meta::Word(ident)) = *token {
                            if ident == "EOF" {
                                exclude_eof = true;
                            } else {
                                exclusions.insert(ident);
                            }
                        } else {
                            // FIXME bad span here
                            list.paren_token
                                .0
                                .unstable()
                                .error("invalid syntax: no_reduce list includes a non-token")
                                .emit();
                        }
                    }
                }
                Meta::Word(ref ident) if ident == "overriding" => {
                    priority = 1;
                }
                _ => {
                    // FIXME non-ideal span
                    meta.name()
                        .span
                        .unstable()
                        .error("unknown attribute")
                        .emit();
                }
            }
        }
        let mut rhs = vec![];
        let sp_lo = input.span();
        let mut sp_hi = sp_lo;
        while let Ok((ident, input_)) = Ident::parse(input) {
            input = input_;
            rhs.push(
                if let Some((inner, span, input_)) = input.group(Delimiter::Bracket) {
                    sp_hi = span;
                    input = input_;
                    let (pat, inner_) = Pat::parse(inner)?;
                    input_end!(inner_,)?;
                    RuleRhsItem::SymbolPat(ident, pat)
                } else if let Some((mut inner, span, input_)) = input.group(Delimiter::Parenthesis) {
                    sp_hi = span;
                    input = input_;
                    let mut pats = vec![];
                    while !inner.eof() {
                        let (pat, inner_) = Pat::parse(inner)?;
                        pats.push(pat);
                        inner = inner_;
                        if !inner.eof() {
                            let (_, inner_) = <Token![,]>::parse(inner)?;
                            inner = inner_;
                        }
                    }
                    RuleRhsItem::Destructure(ident, span, pats)
                } else {
                    sp_hi = ident.span;
                    RuleRhsItem::Symbol(ident)
                },
            );
        }
        let rhs_span = sp_lo
            .unstable()
            .join(sp_hi.unstable())
            .expect("FIXME: you did something bad");
        let (_, input_) = <Token![=>]>::parse(input)?;
        input = input_;
        // Like in a `match` expression, braced block doesn't require a comma before the next rule.
        let optional_comma = input.group(Delimiter::Brace).is_some();
        let (action, input_) = Expr::parse(input)?;
        input = input_;
        rules.push(Rule {
            rhs,
            rhs_span,
            action: action.into_tokens(),
            exclusions,
            exclude_eof,
            priority,
        });
        match <Token![,]>::parse(input) {
            Ok((_, input_)) => {
                input = input_;
            }
            Err(e) => {
                if !input.eof() && !optional_comma {
                    return Err(e);
                }
            }
        }
    }
    Ok((rules, input))
}

struct RuleSet {
    lhs: Ident,
    return_ty: Type,
    rules: Vec<Rule>,
}

impl Synom for RuleSet {
    named!(parse -> Self, do_parse!(
        lhs: syn!(Ident) >>
        punct!(:) >>
        return_ty: syn!(Type) >>
        rules: braces!(call!(parse_rules)) >>
        ({
            let (_, rules) = rules;
            RuleSet { lhs, return_ty, rules }
        })
    ));
}

struct Parser {
    vis: Visibility,
    name: Ident,
    token_ty: Type,
    span_ty: Type,
    range_fn: Option<(Ident, Ident, Block)>,
    rule_sets: Vec<RuleSet>,
}

impl Synom for Parser {
    named!(parse -> Self, do_parse!(
        vis: syn!(Visibility) >>
        keyword!(fn) >>
        name: syn!(Ident) >>
        token_and_span: parens!(tuple!(
            syn!(Type),
            punct!(,),
            syn!(Type)
        )) >>
        punct!(;) >>
        range_fn: option!(do_parse!(
            args: parens!(tuple!(syn!(Ident), punct!(,), syn!(Ident))) >>
            body: syn!(Block) >>
            ({
                let (_, (a, _, b)) = args;
                (a, b, body)
            })
        )) >>
        rule_sets: many0!(syn!(RuleSet)) >>
        ({
            let (_, (token_ty, _, span_ty)) = token_and_span;
            Parser { vis, name, token_ty, span_ty, range_fn, rule_sets }
        })
    ));
}

fn pretty_rule(lhs: Ident, syms: &[Symbol<Ident, Ident>]) -> String {
    let mut r = String::new();
    let _ = write!(&mut r, "{} ->", lhs);
    for sym in syms.iter() {
        let _ = write!(&mut r, " {}", sym);
    }
    r
}

// Pretty-print an item set, for error messages.
fn pretty(x: &ItemSet<Ident, Ident, &Rule>, pad: &str) -> String {
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

pub fn parser(input: TokenStream) -> TokenStream {
    let parser: Parser = syn::parse(input).expect("parse error");
    let fake_rule; // N.B. must go before `rules` to appease dropck
    let mut rules = BTreeMap::new();
    let mut types = BTreeMap::new();
    let mut start = None;
    for rule_set in &parser.rule_sets {
        // parse "LHS: Type {"
        let lhs = rule_set.lhs;
        if start.is_none() {
            start = Some(lhs);
        }
        match rules.entry(lhs) {
            Entry::Occupied(ent) => {
                lhs.span
                    .unstable()
                    .error("duplicate nonterminal")
                    .span_note(ent.key().span.unstable(), "first definition here")
                    .emit();
            }
            Entry::Vacant(ent) => {
                types.insert(lhs, rule_set.return_ty.clone());
                ent.insert(&rule_set.rules);
            }
        }
    }
    let start = if let Some(start) = start {
        start
    } else {
        Span::call_site()
            .unstable()
            .error("at least one nonterminal is required")
            .emit();
        return TokenStream::empty();
    };
    let mut rules: BTreeMap<Ident, Vec<_>> = rules
        .into_iter()
        .map(|(lhs, rules)| {
            let rhss = rules
                .iter()
                .map(|rule| {
                    // figure out which symbols in `rule` are nonterminals vs terminals
                    let syms = rule.rhs
                        .iter()
                        .map(|tok| {
                            let ident = tok.ident();
                            if types.contains_key(&ident) {
                                Nonterminal(ident)
                            } else {
                                Terminal(ident)
                            }
                        })
                        .collect();
                    Rhs {
                        syms: syms,
                        act: rule,
                    }
                })
                .collect();
            (lhs, rhss)
        })
        .collect();
    let fake_start = Ident::from("__FIXME__start");
    fake_rule = Rule {
        rhs: vec![],
        rhs_span: Span::def_site().unstable(),
        action: quote!(),
        exclusions: BTreeSet::new(),
        exclude_eof: false,
        priority: -1,
    };
    rules.insert(
        fake_start,
        vec![
            Rhs {
                syms: vec![Nonterminal(start)],
                act: &fake_rule,
            },
        ],
    );
    let grammar = Grammar {
        rules: rules,
        start: fake_start,
    };
    lr1_machine(
        &grammar,
        &types,
        parser.token_ty,
        parser.span_ty,
        parser.range_fn,
        parser.vis,
        parser.name,
        |ident| quote!(#ident { .. }),
        |lhs, act, syms| {
            let mut expr = act.action.clone().into_tokens();
            let mut args = vec![];
            debug_assert_eq!(syms.len(), act.rhs.len());
            for (i, (sym, x)) in syms.iter().zip(&act.rhs).enumerate() {
                args.push(match *x {
                    RuleRhsItem::SymbolPat(_, ref pat) => Some(pat.clone().into_tokens()),
                    RuleRhsItem::Destructure(ref ident, sp, ref pats) => {
                        let id = Ident::from(format!("s{}", i));
                        let terminal = match *sym {
                            Nonterminal(_) => {
                                sp.unstable()
                                    .error("can't bind enum case to a nonterminal")
                                    .emit();
                                Ident::from("__error")
                            }
                            Terminal(x) => x,
                        };
                        debug_assert_eq!(terminal, ident);
                        expr = quote_spanned!(
                                act.rhs_span.into() =>
                                {
                                    // force a by-move capture
                                    match {#id} {
                                        #terminal(#(#pats),*) => #expr,
                                        _ => unreachable!(),
                                    }
                                });
                        Some(id.into_tokens())
                    }
                    RuleRhsItem::Symbol(_) => None,
                });
            }

            // XXX: should be a cargo feature (?)
            if false {
                let rule_str = pretty_rule(*lhs, syms);
                expr = quote!({
                        println!("reduce by {}", #rule_str);
                        #expr
                    });
            }

            (expr, args, act.rhs_span.into())
        },
        |rhs, token| match token {
            Some(id) => !rhs.act.exclusions.contains(&id),
            None => !rhs.act.exclude_eof,
        },
        |rhs, _| rhs.act.priority,
    ).unwrap_or_else(|conflict| {
        match conflict {
            LR1Conflict::ReduceReduce {
                state,
                token,
                r1,
                r2,
            } => {
                // FIXME: wtf this span
                Span::call_site()
                    .unstable()
                    .error(format!(
                        "reduce-reduce conflict:
state: {}
token: {}",
                        pretty(&state, "       "),
                        match token {
                            Some(id) => id.to_string(),
                            None => "EOF".to_string(),
                        }
                    ))
                    .span_note(r1.1.act.rhs_span, "conflicting rule")
                    .span_note(r2.1.act.rhs_span, "conflicting rule")
                    .emit();
            }
            LR1Conflict::ShiftReduce { state, token, rule } => {
                rule.1
                    .act
                    .rhs_span
                    .error(format!(
                        "shift-reduce conflict:
state: {}
token: {}",
                        pretty(&state, "       "),
                        match token {
                            Some(id) => id.to_string(),
                            None => "EOF".to_string(),
                        }
                    ))
                    .emit();
            }
        };
        Tokens::new()
    })
        .into()
}
