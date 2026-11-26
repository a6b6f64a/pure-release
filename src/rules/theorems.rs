//! The release properties, each checked for tables of any size.

use core::cmp::Ordering;

use vstd::prelude::*;

use super::lemmas::{lemma_inner_first, lemma_nothing_asked_nothing_wanted, lemma_wanted_spreads};
use super::spec::{
    asked, bump_mask, bumped, chosen_mask, lists, named_below, names_mask, outer_of, outgoing,
    own_state, planned, settled, ships_inside, valid_layout, wanted,
};
use super::{Component, Fact, Layout, Plan, State, own};

verus! {

fn a_changed_component_is_never_up_to_date_and_a_regression_is_refused(fact: Fact) {
    let result = own(fact);
    match fact {
        Fact::Unreleased => {
            assert(result == Some(State::Ready));
        },
        Fact::Released { source, changed } => {
            assert(result is None <==> source == Ordering::Less);
            assert(changed ==> result != Some(State::UpToDate));
            assert(source == Ordering::Equal && !changed ==> result == Some(State::UpToDate));
            assert(source == Ordering::Greater ==> result == Some(State::Ready));
        },
    }
}

fn planning_strands_nothing_and_forces_only_what_carries_something_outgoing<'a, const N: usize>(
    table: &Layout<'a, N>,
    facts: &[Fact; N],
) {
    let plan = match table.plan(facts) {
        Ok(plan) => plan,
        Err(_) => return ,
    };
    let states = plan.states();
    let reasons = plan.forced_by();
    assert forall|inner: int, outer: int|
        ships_inside(table@, inner, outer) && outgoing(table@, states@, inner) implies !(states@[outer] is UpToDate) by {
        let k = choose|k: int|
            0 <= k < table@[inner].inside@.len() && #[trigger] outer_of(table@, inner, k) == outer;
    }
    assert forall|i: int| 0 <= i < N && own_state(facts@[i]) != Some(states@[i]) implies own_state(facts@[i])
        == Some(State::UpToDate) && states@[i] is NeedsBump && (exists|inner: int|
        #[trigger] ships_inside(table@, inner, i) && outgoing(table@, states@, inner)) by {
        assert(reasons@[i] is Some);
        let inner = reasons@[i]->Some_0 as int;
        assert(ships_inside(table@, inner, i));
    }
}

/// Planning the facts as they are after a bump raises no component that the
/// bump left alone.
proof fn lemma_a_bump_leaves_nothing_to_force(
    layout: Seq<Component>,
    facts: Seq<Fact>,
    states: Seq<State>,
    reasons: Seq<Option<usize>>,
    after: Seq<Fact>,
    states_after: Seq<State>,
    reasons_after: Seq<Option<usize>>,
    i: int,
)
    requires
        0 <= i < layout.len(),
        planned(layout, facts, states, reasons),
        planned(layout, after, states_after, reasons_after),
        bumps_applied(layout, facts, states, after),
    ensures
        own_state(after[i]) == Some(states_after[i]),
    decreases i,
{
    if own_state(after[i]) != Some(states_after[i]) {
        assert(reasons_after[i] is Some);
        let inner = reasons_after[i]->Some_0 as int;
        lemma_inner_first(layout, inner, i);
        lemma_a_bump_leaves_nothing_to_force(
            layout,
            facts,
            states,
            reasons,
            after,
            states_after,
            reasons_after,
            inner,
        );
        if bumped(layout, states, None, inner) {
            lemma_wanted_spreads(layout, states, None, inner, i);
        } else {
            assert(outgoing(layout, states, inner));
            let k = choose|k: int|
                0 <= k < layout[inner].inside@.len() && #[trigger] outer_of(layout, inner, k) == i;
            assert(!(states[i] is UpToDate));
            assert(asked(layout, states, None, i));
        }
    }
}

/// `after` is `facts` once every component a bump raises is ahead of its
/// newest release.
spec fn bumps_applied(
    layout: Seq<Component>,
    facts: Seq<Fact>,
    states: Seq<State>,
    after: Seq<Fact>,
) -> bool {
    forall|i: int|
        0 <= i < layout.len() ==> own_state(#[trigger] after[i]) == (if bumped(layout, states, None, i) {
            Some(State::Ready)
        } else {
            own_state(facts[i])
        })
}

fn one_bump_leaves_nothing_to_bump_and_publish_then_accepts_everything_ready<'a, const N: usize>(
    table: &Layout<'a, N>,
    facts: &[Fact; N],
    plan: &Plan<'a, N>,
    after: &[Fact; N],
)
    requires
        plan.layout() == table@,
        planned(table@, facts@, plan.states_view(), plan.reasons()),
        bumps_applied(table@, facts@, plan.states_view(), after@),
{
    let ghost layout = table@;
    let ghost states = plan.states_view();
    let next = match table.plan(after) {
        Ok(next) => next,
        Err(regressed) => {
            assert(own_state(after@[regressed.component as int]) is None);
            assert(false);
            return ;
        },
    };
    let ghost states_after = next.states_view();
    assert forall|i: int| 0 <= i < N implies own_state(after@[i]) == Some(#[trigger] states_after[i]) by {
        lemma_a_bump_leaves_nothing_to_force(
            layout,
            facts@,
            states,
            plan.reasons(),
            after@,
            states_after,
            next.reasons(),
            i,
        );
    }
    assert forall|i: int| 0 <= i < N implies !asked(layout, states_after, None, i) by {
        if asked(layout, states_after, None, i) {
            assert(asked(layout, states, None, i));
        }
    }
    let again = next.bump();
    assert(again@.len() == 0) by {
        if again@.len() > 0 {
            let first = again@[0] as int;
            assert(again@.contains(first as usize));
            assert(bump_mask(layout, states_after, None)[first]);
            lemma_nothing_asked_nothing_wanted(layout, states_after, None, first);
        }
    }
    let published = next.publish();
    match published {
        Ok(order) => {
            let released = order.as_slice();
            assert forall|i: int| 0 <= i < N implies (released@.contains(i as usize) <==> states_after[i] is Ready) by {
                assert(chosen_mask(states_after, None)[i] == (states_after[i] is Ready));
            }
        },
        Err(super::Refusal::NotReady { component }) => {
            assert(false);
        },
        Err(super::Refusal::Stranded { component, inside }) => {
            proof {
                let inner = component as int;
                let outer = inside as int;
                lemma_inner_first(layout, inner, outer);
                if bumped(layout, states, None, inner) {
                    lemma_wanted_spreads(layout, states, None, inner, outer);
                } else {
                    assert(outgoing(layout, states, inner));
                    let k = choose|k: int|
                        0 <= k < layout[inner].inside@.len() && #[trigger] outer_of(layout, inner, k) == outer;
                    assert(!(states[outer] is UpToDate));
                    assert(states[outer] is NeedsBump ==> asked(layout, states, None, outer));
                }
                assert(states_after[outer] is Ready);
                assert(false);
            }
        },
    }
}

fn a_named_bump_brings_everything_its_components_ship_inside<'a, const N: usize>(
    table: &Layout<'a, N>,
    facts: &[Fact; N],
    names: &[usize],
)
    requires
        forall|k: int| 0 <= k < names@.len() ==> #[trigger] names@[k] < N,
{
    let plan = match table.plan(facts) {
        Ok(plan) => plan,
        Err(_) => return ,
    };
    let states = plan.states();
    let order = plan.bump_only(names);
    let raised = order.as_slice();
    let ghost named = Some(names_mask(names@, N as int));
    assert forall|i: int|
        0 <= i < N && named_below(names@, i, names@.len() as int) && !(states@[i] is Ready) implies raised@.contains(
        i as usize,
    ) by {
        assert(asked(table@, states@, named, i));
        assert(bump_mask(table@, states@, named)[i]);
    }
    assert forall|inner: int, outer: int|
        0 <= inner < N && 0 <= outer < N && raised@.contains(inner as usize) && ships_inside(
            table@,
            inner,
            outer,
        ) implies raised@.contains(outer as usize) || states@[outer] is Ready by {
        assert(bump_mask(table@, states@, named)[inner]);
        lemma_wanted_spreads(table@, states@, named, inner, outer);
        assert(bump_mask(table@, states@, named)[outer] == bumped(table@, states@, named, outer));
    }
    assert forall|p: int| 0 <= p < raised@.len() implies !(states@[#[trigger] raised@[p] as int] is Ready) by {
        assert(raised@.contains(raised@[p]));
        assert(bump_mask(table@, states@, named)[raised@[p] as int]);
    }
}

fn publish_releases_only_what_is_ready_with_what_carries_it_and_inner_first<'a, const N: usize>(
    table: &Layout<'a, N>,
    facts: &[Fact; N],
    names: Option<&[usize]>,
)
    requires
        names matches Some(names) ==> forall|k: int| 0 <= k < names@.len() ==> #[trigger] names@[k] < N,
{
    let plan = match table.plan(facts) {
        Ok(plan) => plan,
        Err(_) => return ,
    };
    let states = plan.states();
    let published = match names {
        Some(names) => plan.publish_only(names),
        None => plan.publish(),
    };
    let ghost named = match names {
        Some(names) => Some(names_mask(names@, N as int)),
        None => None,
    };
    if let Ok(order) = published {
        let released = order.as_slice();
        assert(lists(released@, chosen_mask(states@, named)));
        assert forall|p: int| 0 <= p < released@.len() implies states@[#[trigger] released@[p] as int] is Ready by {
            assert(released@.contains(released@[p]));
            assert(chosen_mask(states@, named)[released@[p] as int]);
            assert(!super::spec::not_ready(states@, named, released@[p] as int));
        }
        assert forall|inner: int, outer: int|
            0 <= inner < N && released@.contains(inner as usize) && ships_inside(table@, inner, outer) implies states@[outer] is Ready
            && (names is None ==> released@.contains(outer as usize)) by {
            lemma_inner_first(table@, inner, outer);
            assert(chosen_mask(states@, named)[inner]);
            let k = choose|k: int|
                0 <= k < table@[inner].inside@.len() && #[trigger] outer_of(table@, inner, k) == outer;
            assert(!super::spec::stranded(table@, states@, named, inner, k));
            if names is None {
                assert(chosen_mask(states@, named)[outer]);
            }
        }
        assert forall|p: int, q: int|
            0 <= p < released@.len() && 0 <= q < released@.len() && ships_inside(
                table@,
                #[trigger] released@[p] as int,
                #[trigger] released@[q] as int,
            ) implies p < q by {
            lemma_inner_first(table@, released@[p] as int, released@[q] as int);
        }
    }
}

}
