//! Kani checks of the release properties, written against the public API
//! alone so they do not lean on the Verus specifications. Every table of
//! [`COMPONENTS`] entries with up to [`INSIDE`] outer components each, every
//! combination of facts and every choice of names is covered.

use core::cmp::Ordering;

use super::{Component, Fact, Layout, Refusal, State};

const COMPONENTS: usize = 5;
const INSIDE: usize = 2;
/// `#[kani::unwind]` takes a literal: one more than the longest loop.
const _: () = {
    assert!(COMPONENTS + 1 == 6);
};

fn any_fact() -> Fact {
    if kani::any() {
        return Fact::Unreleased;
    }
    let source = match kani::any::<u8>() % 3 {
        0 => Ordering::Less,
        1 => Ordering::Equal,
        _ => Ordering::Greater,
    };
    Fact::Released {
        source,
        changed: kani::any(),
    }
}

fn any_table(outer: &[[usize; INSIDE]; COMPONENTS]) -> [Component<'_>; COMPONENTS] {
    core::array::from_fn(|i| {
        let len: usize = kani::any();
        kani::assume(len <= INSIDE);
        Component {
            inside: &outer[i][..len],
            manual: kani::any(),
        }
    })
}

fn heading_out(
    table: &[Component<'_>; COMPONENTS],
    states: &[State; COMPONENTS],
    i: usize,
) -> bool {
    states[i] == State::Ready || (states[i] == State::NeedsBump && !table[i].manual)
}

fn own(fact: Fact) -> State {
    match fact {
        Fact::Unreleased
        | Fact::Released {
            source: Ordering::Greater,
            ..
        } => State::Ready,
        Fact::Released { changed: true, .. } => State::NeedsBump,
        Fact::Released { changed: false, .. } => State::UpToDate,
    }
}

#[kani::proof]
#[kani::unwind(6)]
fn a_layout_lists_every_component_before_what_it_ships_inside() {
    let outer: [[usize; INSIDE]; COMPONENTS] = kani::any();
    let table = any_table(&outer);
    let accepted = Layout::new(table).is_ok();
    let mut sound = true;
    for (i, component) in table.iter().enumerate() {
        for &inside in component.inside {
            if inside <= i || inside >= COMPONENTS || table[inside].manual {
                sound = false;
            }
        }
    }
    assert_eq!(accepted, sound);
}

#[kani::proof]
#[kani::unwind(6)]
fn planning_strands_nothing_and_forces_only_what_carries_something_outgoing() {
    let outer: [[usize; INSIDE]; COMPONENTS] = kani::any();
    let table = any_table(&outer);
    let Ok(layout) = Layout::new(table) else {
        return;
    };
    let facts: [Fact; COMPONENTS] = core::array::from_fn(|_| any_fact());
    let regressed = facts.iter().any(|fact| {
        matches!(
            fact,
            Fact::Released {
                source: Ordering::Less,
                ..
            }
        )
    });
    let Ok(plan) = layout.plan(&facts) else {
        assert!(regressed);
        return;
    };
    assert!(!regressed);
    let states = plan.states();
    for i in 0..COMPONENTS {
        for &inside in table[i].inside {
            if heading_out(&table, states, i) {
                assert!(states[inside] != State::UpToDate);
            }
        }
        match plan.forced_by()[i] {
            Some(inner) => {
                assert!(own(facts[i]) == State::UpToDate && states[i] == State::NeedsBump);
                assert!(table[inner].inside.contains(&i));
                assert!(heading_out(&table, states, inner));
            }
            None => assert!(states[i] == own(facts[i])),
        }
    }
}

#[kani::proof]
#[kani::unwind(6)]
fn one_bump_leaves_nothing_to_bump_and_publish_then_accepts_everything_ready() {
    let outer: [[usize; INSIDE]; COMPONENTS] = kani::any();
    let table = any_table(&outer);
    let Ok(layout) = Layout::new(table) else {
        return;
    };
    let facts: [Fact; COMPONENTS] = core::array::from_fn(|_| any_fact());
    let Ok(plan) = layout.plan(&facts) else {
        return;
    };
    let mut after = facts;
    for &raised in plan.bump().as_slice() {
        after[raised] = Fact::Released {
            source: Ordering::Greater,
            changed: true,
        };
    }
    let Ok(next) = layout.plan(&after) else {
        panic!("a bump made a component regress");
    };
    assert!(next.bump().as_slice().is_empty());
    let Ok(order) = next.publish() else {
        panic!("publish refused a plan that a bump had settled");
    };
    let mut ready = 0;
    for i in 0..COMPONENTS {
        if next.states()[i] == State::Ready {
            ready += 1;
            assert!(order.as_slice().contains(&i));
        }
    }
    assert_eq!(order.as_slice().len(), ready);
}

#[kani::proof]
#[kani::unwind(6)]
fn a_named_bump_brings_everything_its_components_ship_inside() {
    let outer: [[usize; INSIDE]; COMPONENTS] = kani::any();
    let table = any_table(&outer);
    let Ok(layout) = Layout::new(table) else {
        return;
    };
    let facts: [Fact; COMPONENTS] = core::array::from_fn(|_| any_fact());
    let Ok(plan) = layout.plan(&facts) else {
        return;
    };
    let name: usize = kani::any();
    kani::assume(name < COMPONENTS);
    let order = plan.bump_only(&[name]);
    let raised = order.as_slice();
    let states = plan.states();
    assert_eq!(raised.contains(&name), states[name] != State::Ready);
    for &i in raised {
        assert!(states[i] != State::Ready);
        for &inside in table[i].inside {
            assert!(raised.contains(&inside) || states[inside] == State::Ready);
        }
    }
}

#[kani::proof]
#[kani::unwind(6)]
fn publish_releases_only_what_is_ready_with_what_carries_it_and_inner_first() {
    let outer: [[usize; INSIDE]; COMPONENTS] = kani::any();
    let table = any_table(&outer);
    let Ok(layout) = Layout::new(table) else {
        return;
    };
    let facts: [Fact; COMPONENTS] = core::array::from_fn(|_| any_fact());
    let Ok(plan) = layout.plan(&facts) else {
        return;
    };
    let states = plan.states();
    let name: usize = kani::any();
    kani::assume(name < COMPONENTS);
    let everything: bool = kani::any();
    let published = if everything {
        plan.publish()
    } else {
        plan.publish_only(&[name])
    };
    match published {
        Ok(order) => {
            let released = order.as_slice();
            for (position, &i) in released.iter().enumerate() {
                assert!(states[i] == State::Ready);
                assert!(position == 0 || released[position - 1] < i);
                for &inside in table[i].inside {
                    assert!(states[inside] == State::Ready);
                    assert!(inside > i);
                    assert!(!everything || released.contains(&inside));
                }
            }
            for i in 0..COMPONENTS {
                let wanted = if everything {
                    states[i] == State::Ready
                } else {
                    i == name
                };
                assert_eq!(released.contains(&i), wanted);
            }
        }
        Err(Refusal::NotReady { component }) => {
            assert!(!everything && component == name && states[name] != State::Ready);
        }
        Err(Refusal::Stranded { component, inside }) => {
            assert!(table[component].inside.contains(&inside));
            assert!(states[component] == State::Ready && states[inside] != State::Ready);
        }
    }
}
