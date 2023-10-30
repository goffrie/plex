use std::collections::btree_map::Entry;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write};

use lalr::*;

use proc_macro2::{Span, TokenStream};
use quote::{quote, quote_spanned, ToTokens};
use syn::parse::{Parse, ParseStream};
use syn::punctuated::Punctuated;
use syn::spanned::Spanned;
use syn::token::{Bracket, Paren};
use syn::{
    self, braced, bracketed, parenthesized, parse_macro_input, token, Attribute, Block, Error,
    Expr, Ident, Meta, Pat, Token, Type, Visibility,
};

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
) -> Result<TokenStream, LR1Conflict<'a, T, N, A>>
where
    T: Ord + fmt::Debug + fmt::Display,
    N: Ord + fmt::Debug,
    A: fmt::Debug,
    FM: FnMut(&T) -> TokenStream,
    FA: FnMut(&N, &A, &[Symbol<T, N>]) -> (TokenStream, Vec<Option<TokenStream>>, Span),
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
    let any_ty = quote!(::std::any::Any);
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
        .map(|(i, k)| (k, Ident::new(&format!("reduce_{}", i), Span::call_site())))
        .collect();
    let goto_fn_ids: BTreeMap<_, _> = grammar
        .rules
        .keys()
        .filter(|&lhs| *lhs != grammar.start)
        .enumerate()
        .map(|(i, lhs)| (lhs, Ident::new(&format!("goto_{}", i), Span::call_site())))
        .collect();

    let mut stmts = Vec::new();

    stmts.push(if let Some((a, b, body)) = range_fn {
        quote!(fn range(#a: #span_ty, #b: #span_ty) -> #span_ty {
            #body
        })
    } else {
        quote!(
            fn range(_a: (), _b: ()) {}
        )
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
        let goto_fn = goto_fn_ids[lhs].clone();
        let lhs_ty = &types[lhs];
        for rhs in rhss.iter() {
            let (result, arg_pats, rhs_span) = to_expr(lhs, &rhs.act, &rhs.syms);
            let len = rhs.syms.len();
            let current_span_stmt = if rhs.syms.len() > 0 {
                // Make the current_span available to the user by exposing it through a macro whose name is unhygienic.
                let current_span_ident = quote_spanned!(rhs_span => current_span);
                let span_macro = quote!(
                    #[allow(unused_macros)]
                    macro_rules! span {
                        () => { #current_span_ident.unwrap() }
                    }
                );
                quote_spanned!(rhs_span =>
                    let current_span: Option<#span_ty> = {
                        let sp = range_array(&span_stack[(span_stack.len() - #len)..]);
                        let newlen = span_stack.len() - #len;
                        span_stack.truncate(newlen);
                        sp
                    };
                    #span_macro
                )
            } else {
                quote_spanned!(rhs_span =>
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
                        quote_spanned!(rhs_span =>
                            let #pat: #ty = *stack.pop().unwrap().downcast().unwrap();
                        )
                    }
                    None => quote_spanned!(rhs_span => stack.pop();),
                },
            ));
            if rhs.syms.len() > 1 {
                let len_minus_one = rhs.syms.len() - 1;
                // XXX: Annoying syntax :(
                reduce_stmts.push(
                    quote_spanned!(rhs_span => match state_stack.len() - #len_minus_one { x => state_stack.truncate(x) };),
                );
            } else if rhs.syms.len() == 0 {
                reduce_stmts.push(quote_spanned!(rhs_span => state_stack.push(*state);));
            }
            reduce_stmts.push(quote_spanned!(
                rhs_span =>
                *state = #goto_fn(*state_stack.last().unwrap());
                let result: #lhs_ty = ( || -> #lhs_ty { #result } )();
                stack.push(Box::new(result) as Box<#any_ty>);
                span_stack.push(current_span);
            ));

            let fn_id = rule_fn_ids.get(&(rhs as *const _)).unwrap().clone();
            stmts.push(quote_spanned!(
                rhs_span =>
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
        let mut stack: Vec<Box<#any_ty>> = Vec::new();
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
                let reduce_fn = rule_fn_ids[&rhs_ptr].clone();
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
    // `quote` bug: can't quote `'static`, so use `&'a str` for any `'a`. hopefully this is fine.
    Ok(quote!(
        #vis fn #name<'a, I: Iterator<Item=(#token_ty, #span_ty)>>(mut it: I) -> Result<#start_ty, (Option<(#token_ty, #span_ty)>, &'a str)> {
            #(#stmts)*
        }
    ))
}

#[derive(Debug)]
enum RuleRhsItem {
    Symbol(Ident),
    SymbolPat(Ident, Bracket, Pat),
    Destructure(Ident, Paren, Punctuated<Pat, Token![,]>),
}

impl ToTokens for RuleRhsItem {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        match self {
            RuleRhsItem::Symbol(ident) => ident.to_tokens(tokens),
            RuleRhsItem::SymbolPat(ident, bracket, pat) => {
                ident.to_tokens(tokens);
                bracket.surround(tokens, |tokens| pat.to_tokens(tokens));
            }
            RuleRhsItem::Destructure(ident, paren, pats) => {
                ident.to_tokens(tokens);
                paren.surround(tokens, |tokens| pats.to_tokens(tokens));
            }
        }
    }
}

impl RuleRhsItem {
    fn ident(&self) -> &Ident {
        match *self {
            RuleRhsItem::Symbol(ref ident)
            | RuleRhsItem::SymbolPat(ref ident, _, _)
            | RuleRhsItem::Destructure(ref ident, _, _) => ident,
        }
    }
}

#[derive(Debug)]
struct Rule {
    rhs: Vec<RuleRhsItem>,
    arrow: Token![=>],
    action: TokenStream,
    exclusions: BTreeSet<Ident>,
    exclude_eof: bool,
    priority: i32,
}

impl Rule {
    fn head(&self) -> proc_macro2::TokenStream {
        let rhs = &self.rhs;
        let arrow = &self.arrow;
        quote!(#(#rhs)* #arrow)
    }
}

fn parse_rules(input: ParseStream) -> syn::Result<Vec<Rule>> {
    let mut rules = vec![];
    while !input.is_empty() {
        // FIXME: Make some nicer error messages.
        let mut exclusions = BTreeSet::new();
        let mut exclude_eof = false;
        let mut priority = 0;
        let attrs = Attribute::parse_outer(input)?;
        for attr in attrs {
            match attr.meta {
                Meta::List(_) if attr.path().is_ident("no_reduce") => {
                    attr.parse_nested_meta(|nested| {
                        if let Some(ident) = nested.path.get_ident() {
                            if ident == "EOF" {
                                exclude_eof = true;
                            } else {
                                exclusions.insert(ident.clone());
                            }
                            Ok(())
                        } else {
                            Err(nested.error("invalid syntax: no_reduce list includes a non-token"))
                        }
                    })?;
                }
                Meta::Path(_) if attr.path().is_ident("overriding") => {
                    priority = 1;
                }
                _ => {
                    return Err(Error::new_spanned(attr, "unknown attribute"));
                }
            }
        }
        let mut rhs = vec![];
        while !input.peek(Token![=>]) {
            let ident: Ident = input.parse()?;
            rhs.push(if input.peek(token::Bracket) {
                let inner;
                let bracket = bracketed!(inner in input);
                let pat = Pat::parse_single(&inner)?;
                if !inner.is_empty() {
                    return Err(inner.error("unexpected token after pattern"));
                }
                RuleRhsItem::SymbolPat(ident, bracket, pat)
            } else if input.peek(token::Paren) {
                let inner;
                let paren = parenthesized!(inner in input);
                let pats = inner.parse_terminated(Pat::parse_single, Token![,])?;
                RuleRhsItem::Destructure(
                    ident,
                    paren,
                    pats.into_pairs().map(|p| p.into_value()).collect(),
                )
            } else {
                RuleRhsItem::Symbol(ident)
            });
        }
        let arrow = input.parse::<Token![=>]>()?;
        // Like in a `match` expression, braced block doesn't require a comma before the next rule.
        let optional_comma = input.peek(token::Brace);
        let action: Expr = input.parse()?;
        rules.push(Rule {
            rhs,
            arrow,
            action: action.into_token_stream(),
            exclusions,
            exclude_eof,
            priority,
        });
        match <Token![,]>::parse(input) {
            Ok(_) => {}
            Err(e) => {
                if !input.is_empty() && !optional_comma {
                    return Err(e);
                }
            }
        }
    }
    Ok(rules)
}

struct RuleSet {
    lhs: Ident,
    return_ty: Type,
    rules: Vec<Rule>,
}

impl Parse for RuleSet {
    fn parse(input: ParseStream) -> syn::Result<RuleSet> {
        Ok(RuleSet {
            lhs: input.parse()?,
            return_ty: {
                input.parse::<Token![:]>()?;
                input.parse()?
            },
            rules: {
                let rule_content;
                braced!(rule_content in input);
                parse_rules(&rule_content)?
            },
        })
    }
}

struct Parser {
    vis: Visibility,
    name: Ident,
    token_ty: Type,
    span_ty: Type,
    range_fn: Option<(Ident, Ident, Block)>,
    rule_sets: Vec<RuleSet>,
}

impl Parse for Parser {
    fn parse(input: ParseStream) -> syn::Result<Parser> {
        let span_ty;
        Ok(Parser {
            vis: input.parse()?,
            name: {
                input.parse::<Token![fn]>()?;
                input.parse()?
            },
            token_ty: {
                let inner;
                parenthesized!(inner in input);
                let token = inner.parse()?;
                inner.parse::<Token![,]>()?;
                span_ty = inner.parse()?;
                if !inner.is_empty() {
                    return Err(inner.error("unexpected token after span type"));
                }
                input.parse::<Token![;]>()?;
                token
            },
            span_ty,
            range_fn: {
                if input.peek(token::Paren) {
                    let inner;
                    parenthesized!(inner in input);
                    let a = inner.parse()?;
                    inner.parse::<Token![,]>()?;
                    let b = inner.parse()?;
                    if !inner.is_empty() {
                        return Err(inner.error("unexpected token after second range"));
                    }
                    let body = input.parse::<Block>()?;
                    Some((a, b, body))
                } else {
                    None
                }
            },
            rule_sets: {
                let mut r = vec![];
                while !input.is_empty() {
                    r.push(input.parse()?);
                }
                r
            },
        })
    }
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

pub fn parser(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
    let parser = parse_macro_input!(input as Parser);
    let fake_rule; // N.B. must go before `rules` to appease dropck
    let mut rules = BTreeMap::new();
    let mut types = BTreeMap::new();
    let mut start = None;
    let mut errors = vec![];
    for rule_set in &parser.rule_sets {
        // parse "LHS: Type {"
        let lhs = &rule_set.lhs;
        if start.is_none() {
            start = Some(lhs.clone());
        }
        match rules.entry(lhs.clone()) {
            Entry::Occupied(ent) => {
                errors.push(Error::new_spanned(lhs, "duplicate nonterminal"));
                errors.push(Error::new_spanned(
                    ent.key(),
                    "the first definition is here",
                ));
            }
            Entry::Vacant(ent) => {
                types.insert(lhs.clone(), rule_set.return_ty.clone());
                ent.insert(&rule_set.rules);
            }
        }
    }
    let start = if let Some(start) = start {
        start
    } else {
        return Error::new(Span::call_site(), "at least one nonterminal is required")
            .into_compile_error()
            .into();
    };
    let mut rules: BTreeMap<Ident, Vec<_>> = rules
        .into_iter()
        .map(|(lhs, rules)| {
            let rhss = rules
                .iter()
                .map(|rule| {
                    // figure out which symbols in `rule` are nonterminals vs terminals
                    let syms = rule
                        .rhs
                        .iter()
                        .map(|tok| {
                            let ident = tok.ident().clone();
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
    let fake_start = Ident::new("__FIXME__start", Span::call_site());
    fake_rule = Rule {
        rhs: vec![],
        arrow: Default::default(),
        action: quote!(),
        exclusions: BTreeSet::new(),
        exclude_eof: false,
        priority: -1,
    };
    rules.insert(
        fake_start.clone(),
        vec![Rhs {
            syms: vec![Nonterminal(start)],
            act: &fake_rule,
        }],
    );
    let grammar = Grammar {
        rules: rules,
        start: fake_start,
    };
    let result = lr1_machine(
        &grammar,
        &types,
        parser.token_ty,
        parser.span_ty,
        parser.range_fn,
        parser.vis,
        parser.name,
        |ident| quote!(#ident { .. }),
        |lhs, act, syms| {
            let mut expr = act.action.clone().into_token_stream();
            let mut args = vec![];
            debug_assert_eq!(syms.len(), act.rhs.len());
            for (i, (sym, x)) in syms.iter().zip(&act.rhs).enumerate() {
                args.push(match *x {
                    RuleRhsItem::SymbolPat(_, _, ref pat) => Some(pat.clone().into_token_stream()),
                    RuleRhsItem::Destructure(ref ident, _, ref pats) => {
                        let id = Ident::new(&format!("s{}", i), Span::call_site());
                        let terminal = match *sym {
                            Nonterminal(_) => {
                                errors.push(Error::new_spanned(
                                    x,
                                    "can't bind enum case to a nonterminal",
                                ));
                                Ident::new("__error", Span::call_site())
                            }
                            Terminal(ref x) => {
                                debug_assert_eq!(*x, ident.to_string());
                                x.clone()
                            }
                        };
                        expr = quote_spanned!(act.head().span() =>
                        {
                            // force a by-move capture
                            match {#id} {
                                #terminal(#pats) => #expr,
                                _ => unreachable!(),
                            }
                        });
                        Some(id.into_token_stream())
                    }
                    RuleRhsItem::Symbol(_) => None,
                });
            }

            // XXX: should be a cargo feature (?)
            if false {
                let rule_str = pretty_rule(lhs.clone(), syms);
                expr = quote!({
                    println!("reduce by {}", #rule_str);
                    #expr
                });
            }

            (expr, args, act.head().span())
        },
        |rhs, token| match token {
            Some(id) => !rhs.act.exclusions.contains(&id),
            None => !rhs.act.exclude_eof,
        },
        |rhs, _| rhs.act.priority,
    )
    .unwrap_or_else(|conflict| {
        // Finds a shortest sequence of symbols that reaches the given `state` in the LR(0) state machine.
        let find_path = |state| {
            let lr0_state_machine = grammar.lr0_state_machine();
            let mut prev_state = vec![None; lr0_state_machine.states.len()];
            // BFS
            let mut q = vec![0];
            let mut qi = 0;
            let state_index = lr0_state_machine
                .states
                .iter()
                .position(|(st, _)| *st == state)
                .expect("state must be present in state machine");
            while qi < q.len() {
                let state = q[qi];
                qi += 1;
                for (&symbol, &next_state) in &lr0_state_machine.states[state].1 {
                    if prev_state[next_state].is_none() {
                        prev_state[next_state] = Some((symbol, state));
                        if next_state == state_index {
                            break;
                        }
                        q.push(next_state);
                    }
                }
            }
            let mut path = vec![];
            let mut cur = state_index;
            while let Some((sym, next)) = prev_state[cur] {
                path.push(match sym {
                    Terminal(t) => t.to_string(),
                    Nonterminal(nt) => nt.to_string(),
                });
                cur = next;
            }
            path.reverse();
            path
        };
        match conflict {
            LR1Conflict::ReduceReduce {
                state,
                token,
                r1,
                r2,
            } => {
                let mut error = Error::new_spanned(
                    r1.1.act.head(),
                    format!(
                        "reduce-reduce conflict:
state: {}
token: {}
path: {}",
                        pretty(&state, "       "),
                        match token {
                            Some(id) => id.to_string(),
                            None => "EOF".to_string(),
                        },
                        find_path(state).join(" ")
                    ),
                );
                error.combine(Error::new_spanned(
                    r2.1.act.head(),
                    "this is the conflicting rule",
                ));
                error
            }
            LR1Conflict::ShiftReduce { state, token, rule } => Error::new_spanned(
                rule.1.act.head(),
                format!(
                    "shift-reduce conflict:
state: {}
token: {}
path: {}",
                    pretty(&state, "       "),
                    match token {
                        Some(id) => id.to_string(),
                        None => "EOF".to_string(),
                    },
                    find_path(state).join(" ")
                ),
            ),
        }
        .into_compile_error()
    });

    let errors = errors
        .into_iter()
        .map(|e| e.into_compile_error())
        .collect::<TokenStream>();
    quote!(#errors #result).into()
}
