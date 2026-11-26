//! What the executable rules are verified against, for tables of any size.
//!
//! These definitions are the trusted part: a proof only shows that the code
//! agrees with them. `theorems.rs` derives the release properties from them.

use core::cmp::Ordering;

use vstd::prelude::*;

use super::{Component, Fact, State};

verus! {

/// Where a component stands on its own facts. `None` when its source is below
/// its newest release.
pub open spec fn own_state(fact: Fact) -> Option<State> {
    match fact {
        Fact::Unreleased => Some(State::Ready),
        Fact::Released { source, changed } => match source {
            Ordering::Less => None,
            Ordering::Greater => Some(State::Ready),
            Ordering::Equal => Some(if changed { State::NeedsBump } else { State::UpToDate }),
        },
    }
}

/// The `k`th component that `i` ships inside.
pub open spec fn outer_of(layout: Seq<Component>, i: int, k: int) -> int {
    layout[i].inside@[k] as int
}

/// It is listed after `i` and is not manual.
pub open spec fn edge_ok(layout: Seq<Component>, i: int, k: int) -> bool {
    i < outer_of(layout, i, k) < layout.len() && !layout[outer_of(layout, i, k)].manual
}

pub open spec fn valid_layout(layout: Seq<Component>) -> bool {
    forall|i: int, k: int|
        0 <= i < layout.len() && 0 <= k < layout[i].inside@.len() ==> #[trigger] edge_ok(layout, i, k)
}

/// `outer` is among the first `bound` components that `inner` ships inside.
pub open spec fn listed_below(layout: Seq<Component>, inner: int, outer: int, bound: int) -> bool {
    exists|k: int| 0 <= k < bound && #[trigger] outer_of(layout, inner, k) == outer
}

pub open spec fn ships_inside(layout: Seq<Component>, inner: int, outer: int) -> bool {
    0 <= inner < layout.len() && listed_below(layout, inner, outer, layout[inner].inside@.len() as int)
}

/// Component `i` is heading to users: ahead of its newest release, or changed
/// and bumped without being named.
pub open spec fn outgoing(layout: Seq<Component>, states: Seq<State>, i: int) -> bool {
    states[i] is Ready || (states[i] is NeedsBump && !layout[i].manual)
}

/// Nothing heading to users ships inside a component that stays as released.
pub open spec fn settled(layout: Seq<Component>, states: Seq<State>) -> bool {
    forall|i: int, k: int|
        0 <= i < layout.len() && 0 <= k < layout[i].inside@.len() && outgoing(layout, states, i)
            ==> !(states[#[trigger] outer_of(layout, i, k)] is UpToDate)
}

/// What `Layout::plan` promises: each state is the component's own, except
/// that an up-to-date component needs a bump exactly when something heading to
/// users ships inside it, and `reasons` names one such component.
pub open spec fn planned(
    layout: Seq<Component>,
    facts: Seq<Fact>,
    states: Seq<State>,
    reasons: Seq<Option<usize>>,
) -> bool {
    &&& valid_layout(layout)
    &&& facts.len() == layout.len()
    &&& states.len() == layout.len()
    &&& reasons.len() == layout.len()
    &&& forall|i: int|
        0 <= i < layout.len() ==> (own_state(#[trigger] facts[i]) matches Some(own) && (states[i] == own
            || (own is UpToDate && states[i] is NeedsBump)))
    &&& forall|i: int|
        0 <= i < layout.len() ==> (#[trigger] reasons[i] is Some <==> own_state(facts[i]) != Some(states[i]))
    &&& forall|i: int|
        0 <= i < layout.len() ==> (#[trigger] reasons[i] matches Some(inner) ==> ships_inside(
            layout,
            inner as int,
            i,
        ) && outgoing(layout, states, inner as int))
    &&& settled(layout, states)
}

/// `name` is among the first `bound` names.
pub open spec fn named_below(names: Seq<usize>, name: int, bound: int) -> bool {
    exists|k: int| 0 <= k < bound && #[trigger] names[k] == name
}

/// One flag per table position: whether `names` holds it.
pub open spec fn names_mask(names: Seq<usize>, len: int) -> Seq<bool> {
    Seq::new(len as nat, |i: int| named_below(names, i, names.len() as int))
}

/// A bump is asked to raise component `i` itself.
pub open spec fn asked(
    layout: Seq<Component>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    i: int,
) -> bool {
    match named {
        Some(named) => named[i],
        None => states[i] is NeedsBump && !layout[i].manual,
    }
}

/// A bump reaches component `i`: it is asked for, or something a bump reaches
/// ships inside it.
pub open spec fn wanted(
    layout: Seq<Component>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    i: int,
) -> bool
    decreases i,
{
    asked(layout, states, named, i) || exists|p: int|
        0 <= p < i && #[trigger] ships_inside(layout, p, i) && wanted(layout, states, named, p)
}

/// Something among the first `bound` components that a bump reaches ships
/// inside `i`.
pub open spec fn pulled_below(
    layout: Seq<Component>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    i: int,
    bound: int,
) -> bool {
    exists|p: int|
        0 <= p < bound && #[trigger] ships_inside(layout, p, i) && wanted(layout, states, named, p)
}

/// A bump raises component `i`.
pub open spec fn bumped(
    layout: Seq<Component>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    i: int,
) -> bool {
    wanted(layout, states, named, i) && !(states[i] is Ready)
}

pub open spec fn bump_mask(
    layout: Seq<Component>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
) -> Seq<bool> {
    Seq::new(layout.len(), |i: int| bumped(layout, states, named, i))
}

/// A publish is asked to release component `i`.
pub open spec fn chosen(states: Seq<State>, named: Option<Seq<bool>>, i: int) -> bool {
    match named {
        Some(named) => named[i],
        None => states[i] is Ready,
    }
}

pub open spec fn chosen_mask(states: Seq<State>, named: Option<Seq<bool>>) -> Seq<bool> {
    Seq::new(states.len(), |i: int| chosen(states, named, i))
}

pub open spec fn not_ready(states: Seq<State>, named: Option<Seq<bool>>, i: int) -> bool {
    chosen(states, named, i) && !(states[i] is Ready)
}

/// Releasing `i` would leave it without a release of the `k`th component it
/// ships inside.
pub open spec fn stranded(
    layout: Seq<Component>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    i: int,
    k: int,
) -> bool {
    chosen(states, named, i) && !(states[outer_of(layout, i, k)] is Ready)
}

/// `order` holds exactly the positions `mask` marks, lowest first. Strict, so
/// no position appears twice.
pub open spec fn lists(order: Seq<usize>, mask: Seq<bool>) -> bool {
    &&& forall|p: int| 0 <= p < order.len() ==> #[trigger] order[p] < mask.len()
    &&& forall|p: int, q: int| 0 <= p < q < order.len() ==> #[trigger] order[p] < #[trigger] order[q]
    &&& forall|i: int| 0 <= i < mask.len() ==> (order.contains(i as usize) <==> #[trigger] mask[i])
}

}
