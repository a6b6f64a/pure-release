//! Release planning over a validated layout of components.

use core::cmp::Ordering;
use core::fmt;

#[cfg(verus_only)]
use vstd::prelude::*;

#[cfg(verus_only)]
mod lemmas;
#[cfg(verus_only)]
mod spec;
#[cfg(verus_only)]
mod theorems;

#[cfg(kani)]
mod bounded;
#[cfg(test)]
mod tests;

#[cfg(verus_only)]
use lemmas::{
    lemma_listed_step, lemma_named_step, lemma_pulled_saturates, lemma_pulled_step,
    lemma_wanted_unfolds,
};
#[cfg(verus_only)]
use spec::{
    asked, bump_mask, chosen, chosen_mask, edge_ok, listed_below, lists, named_below, names_mask,
    not_ready, outer_of, outgoing, own_state, planned, pulled_below, settled, ships_inside,
    stranded, valid_layout, wanted,
};

/// Verus proof blocks are erased from ordinary builds.
#[cfg(not(verus_only))]
macro_rules! proof {
    ($($tokens:tt)*) => {};
}

/// Ghost declarations shared by later proof blocks are erased as well.
#[cfg(not(verus_only))]
macro_rules! proof_decl {
    ($($tokens:tt)*) => {};
}

/// One thing you version and release. Its position in the table given to
/// [`Layout::new`] is its identity everywhere else.
#[cfg_attr(verus_only, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Component<'a> {
    /// Table positions of the components this one ships inside. Users only
    /// receive it through a release of each of them.
    pub inside: &'a [usize],
    /// Bumped only when named, never just because it changed.
    pub manual: bool,
}

impl<'a> Component<'a> {
    /// Reaches users through its own releases.
    pub const fn standalone() -> Self {
        Self {
            inside: &[],
            manual: false,
        }
    }

    /// Reaches users only inside releases of the components at `inside`.
    pub const fn ships_inside(inside: &'a [usize]) -> Self {
        Self {
            inside,
            manual: false,
        }
    }

    /// Bumped only when named.
    pub const fn manual(self) -> Self {
        Self {
            inside: self.inside,
            manual: true,
        }
    }
}

/// What the caller observed about one component.
#[cfg_attr(verus_only, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Fact {
    /// No release exists.
    Unreleased,
    Released {
        /// The source version compared with the newest released version.
        source: Ordering,
        /// A release made now would differ from the newest one. That includes
        /// a newest release that bundled an older copy of something inside it.
        changed: bool,
    },
}

#[cfg_attr(verus_only, verus_verify, derive(Structural))]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[cfg_attr(kani, derive(kani::Arbitrary))]
pub enum State {
    /// Released as it is.
    UpToDate,
    /// Differs from its newest release under that release's version.
    NeedsBump,
    /// Ahead of its newest release, or never released.
    Ready,
}

#[cfg_attr(verus_only, verus_spec(result =>
    ensures
        result == own_state(fact),
))]
fn own(fact: Fact) -> Option<State> {
    match fact {
        Fact::Unreleased => Some(State::Ready),
        Fact::Released { source, changed } => match source {
            Ordering::Less => None,
            Ordering::Greater => Some(State::Ready),
            Ordering::Equal => Some(if changed {
                State::NeedsBump
            } else {
                State::UpToDate
            }),
        },
    }
}

/// Why a table is not a layout. `component` ships inside `inside`.
#[cfg_attr(verus_only, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Invalid {
    /// `inside` is not a table position.
    Unknown { component: usize, inside: usize },
    /// `inside` is not listed after `component`. Listing every component before
    /// what it ships inside rules out cycles and fixes the publish order.
    OutOfOrder { component: usize, inside: usize },
    /// `inside` is manual, so it could stay behind while `component` goes out.
    ManualOuter { component: usize, inside: usize },
}

/// The source version of `component` is below one already released.
#[cfg_attr(verus_only, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Regressed {
    pub component: usize,
}

/// Why nothing is published.
#[cfg_attr(verus_only, verus_verify)]
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Refusal {
    /// The named component is not ahead of its newest release.
    NotReady { component: usize },
    /// No release of `inside` is on its way, so nobody would receive
    /// `component`.
    Stranded { component: usize, inside: usize },
}

/// A validated table: every component is listed before what it ships inside,
/// and nothing ships inside a manual component.
#[cfg_attr(verus_only, verus_verify)]
#[derive(Clone, Copy, Debug)]
pub struct Layout<'a, const N: usize> {
    components: [Component<'a>; N],
}

/// The state of every component once each release that has to carry another is
/// accounted for.
#[cfg_attr(verus_only, verus_verify)]
#[derive(Clone, Copy, Debug)]
pub struct Plan<'a, const N: usize> {
    components: [Component<'a>; N],
    states: [State; N],
    forced: [Option<usize>; N],
}

/// Table positions in table order.
#[cfg_attr(verus_only, verus_verify)]
#[derive(Clone, Copy, Debug)]
pub struct Order<const N: usize> {
    items: [usize; N],
    len: usize,
}

#[cfg(verus_only)]
verus! {

impl<'a, const N: usize> Layout<'a, N> {
    #[verifier::type_invariant]
    pub closed spec fn well_formed(self) -> bool {
        valid_layout(self.components@)
    }

    /// The table this layout was built from.
    pub closed spec fn view(self) -> Seq<Component<'a>> {
        self.components@
    }
}

impl<'a, const N: usize> Plan<'a, N> {
    #[verifier::type_invariant]
    pub closed spec fn well_formed(self) -> bool {
        valid_layout(self.components@) && settled(self.components@, self.states@)
    }

    pub closed spec fn layout(self) -> Seq<Component<'a>> {
        self.components@
    }

    pub closed spec fn states_view(self) -> Seq<State> {
        self.states@
    }

    pub closed spec fn reasons(self) -> Seq<Option<usize>> {
        self.forced@
    }
}

impl<const N: usize> Order<N> {
    #[verifier::type_invariant]
    pub closed spec fn well_formed(self) -> bool {
        self.len <= N
    }

    pub closed spec fn view(self) -> Seq<usize> {
        self.items@.subrange(0, self.len as int)
    }
}

}

/// `Layout::new`, as a free function: `verus_spec` cannot wrap an associated
/// function that has no receiver.
#[cfg_attr(verus_only, verifier::loop_isolation(false))]
#[cfg_attr(verus_only, verus_spec(result =>
    ensures
        match result {
            Ok(layout) => layout@ == components@ && valid_layout(components@),
            Err(_) => !valid_layout(components@),
        },
))]
#[expect(
    clippy::needless_range_loop,
    reason = "the Verus invariants are stated over the index"
)]
fn layout<'a, const N: usize>(components: [Component<'a>; N]) -> Result<Layout<'a, N>, Invalid> {
    #[cfg_attr(verus_only, verus_spec(
            invariant
                forall|j: int, k: int| 0 <= j < i && 0 <= k < components@[j].inside@.len()
                    ==> #[trigger] edge_ok(components@, j, k),
        ))]
    for i in 0..N {
        let inside = components[i].inside;
        #[cfg_attr(verus_only, verus_spec(
                invariant
                    inside@ == components@[i as int].inside@,
                    forall|j: int, k: int| 0 <= j < i && 0 <= k < components@[j].inside@.len()
                        ==> #[trigger] edge_ok(components@, j, k),
                    forall|done: int| 0 <= done < k ==> #[trigger] edge_ok(components@, i as int, done),
            ))]
        for k in 0..inside.len() {
            let outer = inside[k];
            proof! {
                assert(outer_of(components@, i as int, k as int) == outer);
            }
            if outer >= N {
                proof! {
                    assert(!edge_ok(components@, i as int, k as int));
                }
                return Err(Invalid::Unknown {
                    component: i,
                    inside: outer,
                });
            }
            if outer <= i {
                proof! {
                    assert(!edge_ok(components@, i as int, k as int));
                }
                return Err(Invalid::OutOfOrder {
                    component: i,
                    inside: outer,
                });
            }
            if components[outer].manual {
                proof! {
                    assert(!edge_ok(components@, i as int, k as int));
                }
                return Err(Invalid::ManualOuter {
                    component: i,
                    inside: outer,
                });
            }
        }
    }
    Ok(Layout { components })
}

impl<'a, const N: usize> Layout<'a, N> {
    /// Checks `components` and keeps a copy.
    ///
    /// # Errors
    ///
    /// The first [`Invalid`] entry in table order.
    pub fn new(components: [Component<'a>; N]) -> Result<Self, Invalid> {
        layout(components)
    }

    /// Works out where every component stands. A component that is heading to
    /// users makes everything it ships inside need a release too.
    ///
    /// # Errors
    ///
    /// [`Regressed`] for the first component whose source is below its newest
    /// release.
    #[cfg_attr(verus_only, verifier::loop_isolation(false))]
    #[cfg_attr(verus_only, verus_spec(result =>
        ensures
            match result {
                Ok(plan) => plan.layout() == self@
                    && planned(self@, facts@, plan.states_view(), plan.reasons()),
                Err(regressed) => regressed.component < N
                    && own_state(facts@[regressed.component as int]) is None,
            },
    ))]
    #[expect(
        clippy::needless_range_loop,
        reason = "the Verus invariants are stated over the index"
    )]
    pub fn plan(&self, facts: &[Fact; N]) -> Result<Plan<'a, N>, Regressed> {
        proof! {
            use_type_invariant(self);
        }
        let mut states = [State::UpToDate; N];
        #[cfg_attr(verus_only, verus_spec(
            invariant
                forall|j: int| 0 <= j < i ==> own_state(facts@[j]) == Some(#[trigger] states@[j]),
        ))]
        for i in 0..N {
            match own(facts[i]) {
                Some(state) => states[i] = state,
                None => return Err(Regressed { component: i }),
            }
        }
        proof_decl! {
            let ghost layout = self.components@;
            let ghost own = states@;
        }
        let mut forced: [Option<usize>; N] = [None; N];
        #[cfg_attr(verus_only, verus_spec(
            invariant
                valid_layout(layout),
                forall|j: int| 0 <= j < N ==> (#[trigger] states@[j] == own[j]
                    || (own[j] is UpToDate && states@[j] is NeedsBump)),
                forall|j: int| 0 <= j < N ==> (#[trigger] forced@[j] is Some <==> states@[j] != own[j]),
                forall|j: int| 0 <= j < N ==> (#[trigger] forced@[j] matches Some(inner)
                    ==> inner < i && ships_inside(layout, inner as int, j)
                        && outgoing(layout, states@, inner as int)),
                forall|p: int, k: int| 0 <= p < i && 0 <= k < layout[p].inside@.len()
                    && outgoing(layout, states@, p)
                    ==> !(states@[#[trigger] outer_of(layout, p, k)] is UpToDate),
        ))]
        for i in 0..N {
            let component = self.components[i];
            let heading_out = match states[i] {
                State::Ready => true,
                State::NeedsBump => !component.manual,
                State::UpToDate => false,
            };
            if heading_out {
                let inside = component.inside;
                proof_decl! {
                    let ghost entry = states@;
                }
                #[cfg_attr(verus_only, verus_spec(
                    invariant
                        inside@ == layout[i as int].inside@,
                        valid_layout(layout),
                        outgoing(layout, states@, i as int),
                        forall|j: int| 0 <= j <= i ==> #[trigger] states@[j] == entry[j],
                        forall|j: int| 0 <= j < N ==> (#[trigger] states@[j] == own[j]
                            || (own[j] is UpToDate && states@[j] is NeedsBump)),
                        forall|j: int| 0 <= j < N ==> (#[trigger] forced@[j] is Some <==> states@[j] != own[j]),
                        forall|j: int| 0 <= j < N ==> (#[trigger] forced@[j] matches Some(inner)
                            ==> inner <= i && ships_inside(layout, inner as int, j)
                                && outgoing(layout, states@, inner as int)),
                        forall|p: int, k: int| 0 <= p < i && 0 <= k < layout[p].inside@.len()
                            && outgoing(layout, states@, p)
                            ==> !(states@[#[trigger] outer_of(layout, p, k)] is UpToDate),
                        forall|done: int| 0 <= done < k
                            ==> !(states@[#[trigger] outer_of(layout, i as int, done)] is UpToDate),
                ))]
                for k in 0..inside.len() {
                    let outer = inside[k];
                    proof! {
                        assert(edge_ok(layout, i as int, k as int));
                        assert(outer_of(layout, i as int, k as int) == outer);
                        assert forall|p: int, at: int| 0 <= p <= i && 0 <= at < layout[p].inside@.len()
                            implies p < #[trigger] outer_of(layout, p, at) by {
                            assert(edge_ok(layout, p, at));
                        }
                    }
                    if states[outer] == State::UpToDate {
                        states[outer] = State::NeedsBump;
                        forced[outer] = Some(i);
                        proof! {
                            assert(listed_below(layout, i as int, outer as int, layout[i as int].inside@.len() as int));
                        }
                    }
                }
            }
        }
        Ok(Plan {
            components: self.components,
            states,
            forced,
        })
    }
}

impl<'a, const N: usize> Plan<'a, N> {
    /// Where each component stands.
    #[cfg_attr(verus_only, verus_spec(result =>
        ensures
            result@ == self.states_view(),
    ))]
    pub fn states(&self) -> &[State; N] {
        &self.states
    }

    /// For each component that needs a bump only because something inside it
    /// is heading to users: the first such component.
    #[cfg_attr(verus_only, verus_spec(result =>
        ensures
            result@ == self.reasons(),
    ))]
    pub fn forced_by(&self) -> &[Option<usize>; N] {
        &self.forced
    }

    /// The components to bump: every changed one that is not manual.
    #[cfg_attr(verus_only, verus_spec(result =>
        ensures
            lists(result@, bump_mask(self.layout(), self.states_view(), None)),
    ))]
    pub fn bump(&self) -> Order<N> {
        proof! {
            use_type_invariant(self);
        }
        collect(&bumps(&self.components, &self.states, None))
    }

    /// The components to bump when the caller names them: those at `names`,
    /// then whatever each of them ships inside, and so on outwards. A
    /// component already ahead of its newest release is not raised again.
    ///
    /// # Panics
    ///
    /// When a name is not a table position.
    #[cfg_attr(verus_only, verus_spec(result =>
        requires
            forall|k: int| 0 <= k < names@.len() ==> #[trigger] names@[k] < N,
        ensures
            lists(result@, bump_mask(self.layout(), self.states_view(), Some(names_mask(names@, N as int)))),
    ))]
    pub fn bump_only(&self, names: &[usize]) -> Order<N> {
        proof! {
            use_type_invariant(self);
        }
        let named = mask(names);
        collect(&bumps(&self.components, &self.states, Some(&named)))
    }

    /// Every component ahead of its newest release, in the order to publish
    /// them: each one before what it ships inside.
    ///
    /// # Errors
    ///
    /// [`Refusal::Stranded`] when one of them ships inside a component that
    /// still needs a bump.
    #[cfg_attr(verus_only, verus_spec(result =>
        ensures
            publishes(self.layout(), self.states_view(), None, result),
    ))]
    pub fn publish(&self) -> Result<Order<N>, Refusal> {
        proof! {
            use_type_invariant(self);
        }
        match choose(&self.components, &self.states, None) {
            Ok(chosen) => Ok(collect(&chosen)),
            Err(refusal) => Err(refusal),
        }
    }

    /// The components at `names`, in the order to publish them.
    ///
    /// # Errors
    ///
    /// [`Refusal::NotReady`] when a named component is not ahead of its newest
    /// release, and [`Refusal::Stranded`] when one ships inside a component
    /// that is not ahead of its own.
    ///
    /// # Panics
    ///
    /// When a name is not a table position.
    #[cfg_attr(verus_only, verus_spec(result =>
        requires
            forall|k: int| 0 <= k < names@.len() ==> #[trigger] names@[k] < N,
        ensures
            publishes(self.layout(), self.states_view(), Some(names_mask(names@, N as int)), result),
    ))]
    pub fn publish_only(&self, names: &[usize]) -> Result<Order<N>, Refusal> {
        proof! {
            use_type_invariant(self);
        }
        let named = mask(names);
        match choose(&self.components, &self.states, Some(&named)) {
            Ok(chosen) => Ok(collect(&chosen)),
            Err(refusal) => Err(refusal),
        }
    }
}

impl<const N: usize> Order<N> {
    #[cfg_attr(verus_only, verus_spec(result =>
        ensures
            result@ == self@,
    ))]
    pub fn as_slice(&self) -> &[usize] {
        proof! {
            use_type_invariant(self);
        }
        &self.items[..self.len]
    }
}

#[cfg(verus_only)]
verus! {

/// What `publish` and `publish_only` promise about their result.
pub open spec fn publishes<const N: usize>(
    layout: Seq<Component>,
    states: Seq<State>,
    named: Option<Seq<bool>>,
    result: Result<Order<N>, Refusal>,
) -> bool {
    match result {
        Ok(order) => {
            &&& forall|i: int| 0 <= i < N ==> !not_ready(states, named, i)
            &&& forall|i: int, k: int| 0 <= i < N && 0 <= k < layout[i].inside@.len()
                ==> !#[trigger] stranded(layout, states, named, i, k)
            &&& lists(order@, chosen_mask(states, named))
        },
        Err(Refusal::NotReady { component }) => component < N && not_ready(states, named, component as int),
        Err(Refusal::Stranded { component, inside }) => {
            &&& component < N
            &&& inside < N
            &&& ships_inside(layout, component as int, inside as int)
            &&& chosen(states, named, component as int)
            &&& !(states[inside as int] is Ready)
        },
    }
}

}

/// Marks the table positions at `names`.
#[cfg_attr(verus_only, verifier::loop_isolation(false))]
#[cfg_attr(verus_only, verus_spec(result =>
    requires
        forall|k: int| 0 <= k < names@.len() ==> #[trigger] names@[k] < N,
    ensures
        result@ == names_mask(names@, N as int),
))]
fn mask<const N: usize>(names: &[usize]) -> [bool; N] {
    let mut mask = [false; N];
    #[cfg_attr(verus_only, verus_spec(
        invariant
            forall|j: int| 0 <= j < N ==> #[trigger] mask@[j] == named_below(names@, j, k as int),
    ))]
    for k in 0..names.len() {
        proof! {
            assert forall|j: int| 0 <= j < N implies
                #[trigger] named_below(names@, j, k + 1)
                    == (named_below(names@, j, k as int) || names@[k as int] == j) by {
                lemma_named_step(names@, j, k as int);
            }
        }
        mask[names[k]] = true;
    }
    proof! {
        assert(mask@ =~= names_mask(names@, N as int));
    }
    mask
}

/// The positions `mask` marks, lowest first.
#[cfg_attr(verus_only, verifier::loop_isolation(false))]
#[cfg_attr(verus_only, verus_spec(result =>
    ensures
        lists(result@, mask@),
))]
#[expect(
    clippy::needless_range_loop,
    reason = "the Verus invariants are stated over the index"
)]
fn collect<const N: usize>(mask: &[bool; N]) -> Order<N> {
    let mut items = [0usize; N];
    let mut len = 0usize;
    #[cfg_attr(verus_only, verus_spec(
        invariant
            len <= i,
            forall|p: int| 0 <= p < len ==> #[trigger] items@[p] < i,
            forall|p: int, q: int| 0 <= p < q < len ==> #[trigger] items@[p] < #[trigger] items@[q],
            forall|j: int| 0 <= j < i ==> (items@.subrange(0, len as int).contains(j as usize) <==> #[trigger] mask@[j]),
    ))]
    for i in 0..N {
        proof! {
            let listed = items@.subrange(0, len as int);
            if listed.contains(i) {
                let at = choose|at: int| 0 <= at < listed.len() && listed[at] == i;
                assert(items@[at] < i);
            }
        }
        if mask[i] {
            proof_decl! {
                let ghost listed = items@.subrange(0, len as int);
            }
            items[len] = i;
            len += 1;
            proof! {
                assert(items@.subrange(0, len as int) =~= listed.push(i));
                assert forall|j: int| 0 <= j <= i implies
                    (listed.push(i).contains(j as usize) <==> #[trigger] mask@[j]) by {
                    if j == i {
                        assert(listed.push(i)[listed.len() as int] == i);
                    } else if listed.contains(j as usize) {
                        let at = choose|at: int| 0 <= at < listed.len() && listed[at] == j as usize;
                        assert(listed.push(i)[at] == j as usize);
                    } else if listed.push(i).contains(j as usize) {
                        let at = choose|at: int| 0 <= at < listed.push(i).len() && listed.push(i)[at] == j as usize;
                        assert(listed[at] == j as usize);
                    }
                }
            }
        }
    }
    Order { items, len }
}

/// The components a bump raises. `named` marks the ones the caller asked for.
#[cfg_attr(verus_only, verifier::loop_isolation(false))]
#[cfg_attr(verus_only, verus_spec(result =>
    requires
        valid_layout(layout@),
    ensures
        result@ == bump_mask(layout@, states@, named_view(named)),
))]
#[expect(
    clippy::needless_range_loop,
    reason = "the Verus invariants are stated over the index"
)]
fn bumps<const N: usize>(
    layout: &[Component<'_>; N],
    states: &[State; N],
    named: Option<&[bool; N]>,
) -> [bool; N] {
    let mut raise = [false; N];
    #[cfg_attr(verus_only, verus_spec(
        invariant
            forall|j: int| 0 <= j < i ==> #[trigger] raise@[j] == asked(layout@, states@, named_view(named), j),
    ))]
    for i in 0..N {
        raise[i] = match named {
            Some(named) => named[i],
            None => states[i] == State::NeedsBump && !layout[i].manual,
        };
    }
    #[cfg_attr(verus_only, verus_spec(
        invariant
            valid_layout(layout@),
            forall|j: int| 0 <= j < N ==> #[trigger] raise@[j] == (
                asked(layout@, states@, named_view(named), j)
                || pulled_below(layout@, states@, named_view(named), j, i as int)),
    ))]
    for i in 0..N {
        proof! {
            lemma_wanted_unfolds(layout@, states@, named_view(named), i as int);
            assert forall|j: int| 0 <= j < N implies
                #[trigger] pulled_below(layout@, states@, named_view(named), j, i + 1)
                    == (pulled_below(layout@, states@, named_view(named), j, i as int)
                        || (ships_inside(layout@, i as int, j)
                            && wanted(layout@, states@, named_view(named), i as int))) by {
                lemma_pulled_step(layout@, states@, named_view(named), j, i as int);
            }
        }
        if raise[i] {
            let inside = layout[i].inside;
            #[cfg_attr(verus_only, verus_spec(
                invariant
                    inside@ == layout@[i as int].inside@,
                    valid_layout(layout@),
                    wanted(layout@, states@, named_view(named), i as int),
                    forall|j: int| 0 <= j < N ==> #[trigger] raise@[j] == (
                        asked(layout@, states@, named_view(named), j)
                        || pulled_below(layout@, states@, named_view(named), j, i as int)
                        || listed_below(layout@, i as int, j, k as int)),
            ))]
            for k in 0..inside.len() {
                let outer = inside[k];
                proof! {
                    assert(edge_ok(layout@, i as int, k as int));
                    assert(outer_of(layout@, i as int, k as int) == outer);
                    assert forall|j: int| 0 <= j < N implies
                        #[trigger] listed_below(layout@, i as int, j, k + 1)
                            == (listed_below(layout@, i as int, j, k as int) || outer == j) by {
                        lemma_listed_step(layout@, i as int, j, k as int);
                    }
                }
                raise[outer] = true;
            }
        }
    }
    proof! {
        assert forall|j: int| 0 <= j < N implies
            #[trigger] raise@[j] == wanted(layout@, states@, named_view(named), j) by {
            lemma_wanted_unfolds(layout@, states@, named_view(named), j);
            lemma_pulled_saturates(layout@, states@, named_view(named), j, N as int);
        }
    }
    #[cfg_attr(verus_only, verus_spec(
        invariant
            valid_layout(layout@),
            forall|j: int| 0 <= j < i ==> #[trigger] raise@[j] == bump_mask(layout@, states@, named_view(named))[j],
            forall|j: int| i <= j < N ==> #[trigger] raise@[j] == wanted(layout@, states@, named_view(named), j),
    ))]
    for i in 0..N {
        if states[i] == State::Ready {
            raise[i] = false;
        }
    }
    proof! {
        assert(raise@ =~= bump_mask(layout@, states@, named_view(named)));
    }
    raise
}

/// The components a publish releases, or why it releases none.
#[cfg_attr(verus_only, verifier::loop_isolation(false))]
#[cfg_attr(verus_only, verus_spec(result =>
    requires
        valid_layout(layout@),
    ensures
        match result {
            Ok(picked) => {
                &&& picked@ == chosen_mask(states@, named_view(named))
                &&& forall|i: int| 0 <= i < N ==> !not_ready(states@, named_view(named), i)
                &&& forall|i: int, k: int| 0 <= i < N && 0 <= k < layout@[i].inside@.len()
                    ==> !#[trigger] stranded(layout@, states@, named_view(named), i, k)
            },
            Err(Refusal::NotReady { component }) => component < N
                && not_ready(states@, named_view(named), component as int),
            Err(Refusal::Stranded { component, inside }) => {
                &&& component < N
                &&& inside < N
                &&& ships_inside(layout@, component as int, inside as int)
                &&& chosen(states@, named_view(named), component as int)
                &&& !(states@[inside as int] is Ready)
            },
        },
))]
#[expect(
    clippy::needless_range_loop,
    reason = "the Verus invariants are stated over the index"
)]
fn choose<const N: usize>(
    layout: &[Component<'_>; N],
    states: &[State; N],
    named: Option<&[bool; N]>,
) -> Result<[bool; N], Refusal> {
    let mut picked = [false; N];
    #[cfg_attr(verus_only, verus_spec(
        invariant
            forall|j: int| 0 <= j < i ==> #[trigger] picked@[j] == chosen(states@, named_view(named), j),
            forall|j: int| 0 <= j < i ==> !not_ready(states@, named_view(named), j),
    ))]
    for i in 0..N {
        picked[i] = match named {
            Some(named) => named[i],
            None => states[i] == State::Ready,
        };
        if picked[i] && states[i] != State::Ready {
            return Err(Refusal::NotReady { component: i });
        }
    }
    #[cfg_attr(verus_only, verus_spec(
        invariant
            valid_layout(layout@),
            forall|j: int, k: int| 0 <= j < i && 0 <= k < layout@[j].inside@.len()
                ==> !#[trigger] stranded(layout@, states@, named_view(named), j, k),
    ))]
    for i in 0..N {
        if picked[i] {
            let inside = layout[i].inside;
            #[cfg_attr(verus_only, verus_spec(
                invariant
                    inside@ == layout@[i as int].inside@,
                    valid_layout(layout@),
                    forall|done: int| 0 <= done < k
                        ==> !#[trigger] stranded(layout@, states@, named_view(named), i as int, done),
            ))]
            for k in 0..inside.len() {
                let outer = inside[k];
                proof! {
                    assert(edge_ok(layout@, i as int, k as int));
                    assert(outer_of(layout@, i as int, k as int) == outer);
                }
                if states[outer] != State::Ready {
                    proof! {
                        assert(listed_below(layout@, i as int, outer as int, layout@[i as int].inside@.len() as int));
                    }
                    return Err(Refusal::Stranded {
                        component: i,
                        inside: outer,
                    });
                }
            }
        }
    }
    proof! {
        assert(picked@ =~= chosen_mask(states@, named_view(named)));
    }
    Ok(picked)
}

#[cfg(verus_only)]
verus! {

pub open spec fn named_view<const N: usize>(named: Option<&[bool; N]>) -> Option<Seq<bool>> {
    match named {
        Some(named) => Some(named@),
        None => None,
    }
}

}

#[cfg_attr(verus_only, verifier::external)]
impl fmt::Display for Invalid {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::Unknown { component, inside } => write!(
                f,
                "component {component} ships inside {inside}, which is not in the table"
            ),
            Self::OutOfOrder { component, inside } => write!(
                f,
                "component {component} ships inside {inside}, which has to be listed after it"
            ),
            Self::ManualOuter { component, inside } => write!(
                f,
                "component {component} ships inside {inside}, which is manual and could stay behind"
            ),
        }
    }
}

#[cfg_attr(verus_only, verifier::external)]
impl fmt::Display for Regressed {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "the source of component {} is below its newest release",
            self.component
        )
    }
}

#[cfg_attr(verus_only, verifier::external)]
impl fmt::Display for Refusal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match *self {
            Self::NotReady { component } => {
                write!(
                    f,
                    "component {component} is not ahead of its newest release"
                )
            }
            Self::Stranded { component, inside } => write!(
                f,
                "component {component} would reach nobody: no release of {inside} is on its way"
            ),
        }
    }
}

#[cfg_attr(verus_only, verifier::external)]
impl core::error::Error for Invalid {}
#[cfg_attr(verus_only, verifier::external)]
impl core::error::Error for Regressed {}
#[cfg_attr(verus_only, verifier::external)]
impl core::error::Error for Refusal {}
