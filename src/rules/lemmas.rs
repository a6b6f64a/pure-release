//! Proof steps the executable rules call. Verus checks every one, so nothing
//! here adds to what has to be trusted.

use vstd::prelude::*;

use super::spec::{
    asked, edge_ok, listed_below, named_below, outer_of, pulled_below, ships_inside, valid_layout,
    wanted,
};
use super::{Component, State};

verus! {

pub proof fn lemma_named_step(names: Seq<usize>, name: int, bound: int)
    requires
        bound >= 0,
    ensures
        named_below(names, name, bound + 1) <==> named_below(names, name, bound) || names[bound] == name,
{
    if named_below(names, name, bound + 1) {
        let k = choose|k: int| 0 <= k < bound + 1 && #[trigger] names[k] == name;
        if k < bound {
            assert(named_below(names, name, bound));
        }
    }
    if named_below(names, name, bound) {
        let k = choose|k: int| 0 <= k < bound && #[trigger] names[k] == name;
        assert(0 <= k < bound + 1 && names[k] == name);
    }
    if names[bound] == name {
        assert(named_below(names, name, bound + 1));
    }
}

pub proof fn lemma_listed_step(layout: Seq<Component>, inner: int, outer: int, bound: int)
    requires
        bound >= 0,
    ensures
        listed_below(layout, inner, outer, bound + 1) <==> listed_below(layout, inner, outer, bound)
            || outer_of(layout, inner, bound) == outer,
{
    if listed_below(layout, inner, outer, bound + 1) {
        let k = choose|k: int| 0 <= k < bound + 1 && #[trigger] outer_of(layout, inner, k) == outer;
        if k < bound {
            assert(listed_below(layout, inner, outer, bound));
        }
    }
    if listed_below(layout, inner, outer, bound) {
        let k = choose|k: int| 0 <= k < bound && #[trigger] outer_of(layout, inner, k) == outer;
        assert(0 <= k < bound + 1 && outer_of(layout, inner, k) == outer);
    }
    if outer_of(layout, inner, bound) == outer {
        assert(listed_below(layout, inner, outer, bound + 1));
    }
}

/// A component is listed before whatever it ships inside, and that is never
/// manual.
pub proof fn lemma_inner_first(layout: Seq<Component>, inner: int, outer: int)
    requires
        valid_layout(layout),
        ships_inside(layout, inner, outer),
    ensures
        0 <= inner < outer < layout.len(),
        !layout[outer].manual,
{
    let k = choose|k: int|
        0 <= k < layout[inner].inside@.len() && #[trigger] outer_of(layout, inner, k) == outer;
    assert(edge_ok(layout, inner, k));
}

pub proof fn lemma_wanted_unfolds(
    layout: Seq<Component>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    i: int,
)
    ensures
        wanted(layout, states, named, i) <==> asked(layout, states, named, i) || pulled_below(
            layout,
            states,
            named,
            i,
            i,
        ),
{
}

pub proof fn lemma_pulled_step(
    layout: Seq<Component>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    i: int,
    bound: int,
)
    requires
        bound >= 0,
    ensures
        pulled_below(layout, states, named, i, bound + 1) <==> pulled_below(layout, states, named, i, bound)
            || (ships_inside(layout, bound, i) && wanted(layout, states, named, bound)),
{
    if pulled_below(layout, states, named, i, bound + 1) {
        let p = choose|p: int|
            0 <= p < bound + 1 && #[trigger] ships_inside(layout, p, i) && wanted(layout, states, named, p);
        if p < bound {
            assert(pulled_below(layout, states, named, i, bound));
        }
    }
    if pulled_below(layout, states, named, i, bound) {
        let p = choose|p: int|
            0 <= p < bound && #[trigger] ships_inside(layout, p, i) && wanted(layout, states, named, p);
        assert(0 <= p < bound + 1 && ships_inside(layout, p, i));
    }
    if ships_inside(layout, bound, i) && wanted(layout, states, named, bound) {
        assert(pulled_below(layout, states, named, i, bound + 1));
    }
}

/// Only earlier components ship inside `i`, so looking past `i` finds nothing
/// more.
pub proof fn lemma_pulled_saturates(
    layout: Seq<Component>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    i: int,
    bound: int,
)
    requires
        valid_layout(layout),
        i <= bound,
    ensures
        pulled_below(layout, states, named, i, bound) <==> pulled_below(layout, states, named, i, i),
{
    if pulled_below(layout, states, named, i, bound) {
        let p = choose|p: int|
            0 <= p < bound && #[trigger] ships_inside(layout, p, i) && wanted(layout, states, named, p);
        lemma_inner_first(layout, p, i);
        assert(pulled_below(layout, states, named, i, i));
    }
    if pulled_below(layout, states, named, i, i) {
        let p = choose|p: int|
            0 <= p < i && #[trigger] ships_inside(layout, p, i) && wanted(layout, states, named, p);
        assert(0 <= p < bound && ships_inside(layout, p, i));
    }
}

/// When a bump is asked for nothing, it reaches nothing.
pub proof fn lemma_nothing_asked_nothing_wanted(
    layout: Seq<Component>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    i: int,
)
    requires
        0 <= i,
        forall|j: int| 0 <= j <= i ==> !asked(layout, states, named, j),
    ensures
        !wanted(layout, states, named, i),
    decreases i,
{
    if wanted(layout, states, named, i) {
        let p = choose|p: int|
            0 <= p < i && #[trigger] ships_inside(layout, p, i) && wanted(layout, states, named, p);
        lemma_nothing_asked_nothing_wanted(layout, states, named, p);
    }
}

/// Whatever a bump reaches, it also reaches everything that ships it.
pub proof fn lemma_wanted_spreads(
    layout: Seq<Component>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    inner: int,
    outer: int,
)
    requires
        valid_layout(layout),
        ships_inside(layout, inner, outer),
        wanted(layout, states, named, inner),
    ensures
        wanted(layout, states, named, outer),
{
    lemma_inner_first(layout, inner, outer);
}

}
