# pure-release

Say you fix a bug in a bootloader. You tag it, publish it, and move on. Nobody
gets the fix, because the bootloader only ever reaches a device inside a
firmware image and you never released the firmware again.

`pure-release` is a small Rust library that catches that. You tell it which of
your components ship inside which others, and what has changed since the last
release. It answers with the versions to bump, a publish order, and anything
you should hold back.

The same slip comes in a few shapes. The outer component never gets bumped, so
the fix sits on a shelf. Sometimes the inner one goes out while nothing is on
its way to carry it. And if the outer one is built first, it quietly bundles
the old copy. One rule covers all of them: a component that ships inside
another is only released once the outer one goes out again.

The library only decides. It never touches git, runs a build or uploads a
file, so you call it from whatever release script, `xtask` or CI job you
already have. It's `no_std`, pulls in no dependencies and doesn't allocate.
The decisions are [machine-checked](#what-is-proved) for layouts of any size.

## Is this for you?

It's for projects that release bundles. Firmware with a bootloader or radio
core baked in. An installer carrying four binaries. Apps that ship a plugin,
or a container image wrapped around one executable. The more layers you have,
and the more places one component ends up, the more it saves you.

If your components reach users separately and only depend on each other, the
way crates in a Cargo workspace do, reach for `cargo-release` or
`release-plz`. Those tools also pick version numbers and publish for you.
`pure-release` leaves both jobs to your script.

Got two components? Write an `if`. This crate starts paying for itself around
the time you add a third layer, or a part that ships in two places, because
the rules stay the same and stay proved however the table grows.

## Example

One bootloader goes into two firmware images. A command-line tool ships by
itself.

```rust
use core::cmp::Ordering;

use pure_release::{Component, Fact, Layout, State};

const BOOTLOADER: usize = 0;
const FIRMWARE_A: usize = 1;
const FIRMWARE_B: usize = 2;
const CLI: usize = 3;

# fn main() -> Result<(), Box<dyn std::error::Error>> {
let layout = Layout::new([
    Component::ships_inside(&[FIRMWARE_A, FIRMWARE_B]),
    Component::standalone(),
    Component::standalone(),
    Component::standalone(),
])?;

// Someone fixed the bootloader and has not touched its version yet.
let unchanged = Fact::Released { source: Ordering::Equal, changed: false };
let fixed = Fact::Released { source: Ordering::Equal, changed: true };
let plan = layout.plan(&[fixed, unchanged, unchanged, unchanged])?;

// Both images have to be released again, or the fix reaches nobody.
assert_eq!(plan.bump().as_slice(), [BOOTLOADER, FIRMWARE_A, FIRMWARE_B]);
assert_eq!(plan.forced_by()[FIRMWARE_A], Some(BOOTLOADER));
assert_eq!(plan.states()[CLI], State::UpToDate);

// After you raise those three versions, plan again.
let ahead = Fact::Released { source: Ordering::Greater, changed: true };
let plan = layout.plan(&[ahead, ahead, ahead, unchanged])?;
assert!(plan.bump().as_slice().is_empty());
assert_eq!(plan.publish()?.as_slice(), [BOOTLOADER, FIRMWARE_A, FIRMWARE_B]);
# Ok(())
# }
```

For a runnable walkthrough, try `cargo run --example installer`.
It follows an engine change through an app into its installer, prints which
versions need a bump and why, then shows the build and publish order after
those bumps. Its facts are written out in
[`examples/installer.rs`](examples/installer.rs), so you can try different
release states without touching tags or uploading anything.

## Describing your project

Put your components in an array. Each one's position in that array is its name
from then on, in the facts you pass in and in every answer that comes back.
Constants like the ones above keep that readable, and so does an enum cast
with `as usize`.

A component is one of two things. `Component::standalone()` reaches users
through its own releases. `Component::ships_inside(&[A, B])` only reaches them
inside releases of `A` and `B`, and you can name as many outer components as
you need. Those can ship inside others in turn.

Add `.manual()` to a component you version by hand. It then gets bumped only
when you name it.

The table has a single ordering rule. **List a component before everything it
ships inside.** That ordering is what rules out cycles, and it has a nice side
effect, which is that the publish order is the order you wrote. Break the rule
and `Layout::new` names the entry at fault. It also refuses anything that
ships inside a manual component, since the manual one could stay behind.

## Telling it what happened

`Layout::plan` wants one `Fact` per component. Use `Fact::Unreleased` for
something that has never gone out. For everything else use
`Fact::Released { source, changed }`, where `source` is your source version
compared with the newest released one (`source.cmp(&released)`) and `changed`
says whether a release cut today would differ from that newest one.

Where those facts come from is your call. Tags, a registry, a manifest, a
diff. One case is easy to miss: if the newest release of an outer component
bundled an old copy of something inside it, that counts as `changed`.

A source version below the newest release is a mistake. `plan` returns
`Regressed` and names the component.

## Reading the plan

`plan.states()` gives you one `State` per component.

| State | Meaning | What to do |
| --- | --- | --- |
| `UpToDate` | Released as it is. | Nothing. |
| `NeedsBump` | Differs from its newest release, or must carry something that is going out. | Raise its version. |
| `Ready` | Ahead of its newest release, or never released. | Publish it. |

`plan.bump()` lists what to bump. If you'd rather pick, `plan.bump_only(&[..])`
bumps the components you name plus whatever they ship inside. Publishing works
the same way: `plan.publish()` returns everything that's ready, in order, and
`plan.publish_only(&[..])` sticks to the ones you name. When a component needs
a bump only because it has to carry another, `plan.forced_by()` tells you
which one.

Publishing can refuse. `Refusal::NotReady` means you named a component that
isn't ahead of its release. `Refusal::Stranded` means a component would go out
while something it ships inside stays put. Both name the components involved.

## What is proved

[Verus](https://github.com/verus-lang/verus) checks five properties for tables
of any size, with any pattern of components shipping inside others.

1. A changed component is never reported up to date, and a source below its
   release is refused.
2. After planning, nothing heading to users ships inside a component that stays
   as released. A component is only made to need a bump when something inside
   it is heading out.
3. One bump is enough. Plan again afterwards and nothing is left to bump, and
   publishing then accepts everything that is ready.
4. A named bump brings everything the named components ship inside, however
   many layers out.
5. Publishing releases only components that are ready, always the inner one
   first, and never one whose outer component is staying behind.

[Kani](https://github.com/model-checking/kani) checks the same five a second
way. Its harnesses go through the public API and ignore the Verus
specifications, and they cover every table of five components where each ships
inside at most two others.

The proofs stop at the decisions. Feed it wrong facts and you get a
confidently wrong plan, and nothing here knows what your build and upload
steps do or whether a change deserves a major version.

Run them with the pinned tools.

```sh
tools/verify-verus.sh                        # Verus 0.2026.11.02.8bf68ee on PATH
cargo kani --lib --output-format terse       # Kani 0.68.0
```

The Verus script fails on any unproved assumption or skipped function body.

## Origin

The rules started life as the release planner in
[Odyssey](https://github.com/odysseyarm/odyssey/blob/bfb7e416c55b73ddab9a01d31cf4c08e04247943/crates/xtask/src/release_rules.rs),
which ships net cores and bootloaders inside application firmware.
