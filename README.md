# pure-release

Some things you release never reach users on their own. A bootloader is built
into a firmware image; a helper binary sits inside an installer. Fix the inner
one, forget to release the outer one again, and nobody receives the fix.

`pure-release` keeps track of that for you. You describe which components ship
inside which, tell it what changed, and it answers three questions:

- **What needs a version bump?** Everything that changed, and everything that
  has to be released again to carry it.
- **What can be published, and in what order?** Inner components first.
- **What must not be published yet?** Anything that would go out with nothing
  on its way to carry it.

It decides and nothing else: no git, no builds, no uploads, no network. It is
`no_std`, has no dependencies and does not allocate, so it drops into a
release script, an `xtask` or a CI job. The decisions are machine-checked; see
[what is proved](#what-is-proved).

## Example

One bootloader is built into two firmware images, and a command-line tool
ships on its own.

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

## Describing your project

List your components in an array. A component's position in that array is its
name everywhere else: in the facts you pass in and in every answer you get
back. An enum cast with `as usize`, or constants as above, keeps that readable.

- `Component::standalone()` reaches users through its own releases.
- `Component::ships_inside(&[A, B])` reaches users only inside releases of `A`
  and `B`. It can ship inside as many components as you like, and those can
  ship inside others in turn.
- `.manual()` marks a component that is bumped only when you name it, such as
  one you version by hand.

There is one rule: **list a component before everything it ships inside.**
That is what makes a cycle impossible, and it means the publish order is simply
the order you wrote. `Layout::new` tells you which entry breaks the rule.
Nothing can ship inside a manual component, because the manual one could then
stay behind.

## Telling it what happened

Give `Layout::plan` one `Fact` per component:

- `Fact::Unreleased` if it has never been released.
- `Fact::Released { source, changed }` otherwise. `source` is the source
  version compared with the newest released one (`source.cmp(&released)`).
  `changed` says whether a release made now would differ from that newest one.

How you learn those is up to you: tags, a registry, a manifest, a diff. If the
newest release of an outer component bundled an old copy of something inside
it, count that as `changed`.

A source version *below* the newest release is a mistake, and `plan` returns
`Regressed` instead of guessing.

## Reading the plan

`plan.states()` holds one `State` per component:

| State | Meaning | What to do |
| --- | --- | --- |
| `UpToDate` | Released as it is. | Nothing. |
| `NeedsBump` | Differs from its newest release, or must carry something that is going out. | Raise its version. |
| `Ready` | Ahead of its newest release, or never released. | Publish it. |

- `plan.bump()` lists what to bump. `plan.bump_only(&[..])` bumps the
  components you name and whatever they ship inside.
- `plan.publish()` lists what to publish, in order. `plan.publish_only(&[..])`
  publishes the ones you name.
- `plan.forced_by()` says, for a component that needs a bump only to carry
  another, which one.

Publishing is refused, with the components involved, when a named component is
not ahead of its release (`Refusal::NotReady`) or when a component would go out
while something it ships inside is not being released (`Refusal::Stranded`).

## What is proved

[Verus](https://github.com/verus-lang/verus) checks these for tables of any
size, with any pattern of components shipping inside others:

1. A changed component is never reported up to date, and a source below its
   release is refused.
2. After planning, nothing heading to users ships inside a component that stays
   as released, and a component is only made to need a bump when something
   inside it is heading out.
3. One bump is enough: plan again afterwards and nothing is left to bump, and
   publishing then accepts everything that is ready.
4. A named bump brings everything the named components ship inside, however
   many layers out.
5. Publishing releases only components that are ready, never one whose outer
   component is not being released, and always the inner one first.

[Kani](https://github.com/model-checking/kani) checks the same properties a
second way, through the public API and without the Verus specifications, for
every table of five components that each ship inside at most two others.

The proofs cover the decisions only. They do not know whether your facts are
right, whether a change deserves a major version, or what your build and
upload steps do.

Run them with the pinned tools:

```sh
tools/verify-verus.sh                        # Verus 0.2026.11.02.8bf68ee on PATH
cargo kani --lib --output-format terse       # Kani 0.68.0
```

`tools/verify-verus.sh` rejects unproved assumptions and skipped function
bodies.

## Origin

The rules began as the release planner of
[Odyssey](https://github.com/odysseyarm/odyssey/blob/bfb7e416c55b73ddab9a01d31cf4c08e04247943/crates/xtask/src/release_rules.rs),
which ships net cores and bootloaders inside application firmware.
