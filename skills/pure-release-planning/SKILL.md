---
name: pure-release-planning
description: Plan version bumps and publish order with the pure-release crate. Use when calling or changing code that uses pure_release (Layout, Component, Fact, Plan, bump, publish), or when adding a component to a release table.
---

`pure-release` decides what to bump and in which order to publish when components ship inside one another. It is `no_std`, has no dependencies, and does no I/O: the caller reads tags, versions and diffs, and passes the facts in. `README.md` is the user guide.

# The table

One `Component` per thing released; the array position is its identity in every argument and result.

- `Component::standalone()`: released on its own.
- `Component::ships_inside(&[..])`: reaches users only through the components at those positions (a bootloader inside firmware, a tool inside an installer). Several outer components and several layers are fine.
- `.manual()`: bumped only when named.

List a component before everything it ships inside. `Layout::new` returns `Invalid::Unknown`, `OutOfOrder` or `ManualOuter` otherwise; treat that as a bug in the table, and cover the real table with a test that calls `Layout::new`.

# Call order

1. `Layout::new(components)?`, once.
2. `layout.plan(&facts)?` with one `Fact` per component. `Fact::Released { source, changed }` takes `source = source_version.cmp(&newest_release)`; `changed` is true when a release made now would differ from the newest one, including a newest release that bundled an older copy of something inside it. `Err(Regressed { component })` means the source is below a released version: stop, do not coerce it.
3. `plan.states()` and `plan.forced_by()` for reporting.
4. `plan.bump()` or `plan.bump_only(&names)` gives the positions to raise. Raise the versions, then plan again from fresh facts.
5. `plan.publish()` or `plan.publish_only(&names)` gives `Order::as_slice()`: positions in publish order, inner first. Handle `Refusal::NotReady { component }` and `Refusal::Stranded { component, inside }`.

`names` are table positions; one outside the table panics.

# What the proofs cover

Verus verifies the five release properties in `src/rules/theorems.rs` for tables of any size and shape. Run `tools/verify-verus.sh` with the pinned verifier on `PATH`; its strict flags reject unproved assumptions and skipped executable bodies. `src/rules/spec.rs` is the trusted part; keep helper facts in `src/rules/lemmas.rs` and reuse `vstd` for general ones.

Kani checks the same properties through the public API in `src/rules/bounded.rs`, for every table of five components with up to two outer components each. Run `cargo kani --lib --output-format terse` with Kani 0.68.0.

`verus_spec` cannot wrap an associated function without a receiver, so `Layout::new` delegates to the free function `layout`.

The proofs say nothing about whether the facts are right, about how changes and dependencies are discovered, or about whether a change needs a major version bump.
