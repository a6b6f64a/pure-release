use core::cmp::Ordering;

use super::{Component, Fact, Invalid, Layout, Refusal, Regressed, State};

const UNCHANGED: Fact = Fact::Released {
    source: Ordering::Equal,
    changed: false,
};
const CHANGED: Fact = Fact::Released {
    source: Ordering::Equal,
    changed: true,
};
const AHEAD: Fact = Fact::Released {
    source: Ordering::Greater,
    changed: true,
};

// A command-line tool and a daemon, both bundled by an installer.
const CLI: usize = 0;
const DAEMON: usize = 1;
const INSTALLER: usize = 2;

fn installer() -> Layout<'static, 3> {
    Layout::new([
        Component::ships_inside(&[INSTALLER]),
        Component::ships_inside(&[INSTALLER]),
        Component::standalone(),
    ])
    .expect("each tool is listed before the installer")
}

#[test]
fn a_changed_tool_takes_its_installer_along() {
    let plan = installer()
        .plan(&[CHANGED, UNCHANGED, UNCHANGED])
        .expect("nothing regressed");
    assert_eq!(
        plan.states(),
        &[State::NeedsBump, State::UpToDate, State::NeedsBump]
    );
    assert_eq!(plan.forced_by(), &[None, None, Some(CLI)]);
    assert_eq!(plan.bump().as_slice(), [CLI, INSTALLER]);
    assert_eq!(
        plan.publish().expect("nothing is ahead yet").as_slice(),
        [0usize; 0]
    );

    let bumped = installer()
        .plan(&[AHEAD, UNCHANGED, AHEAD])
        .expect("nothing regressed");
    assert_eq!(bumped.bump().as_slice(), [0usize; 0]);
    assert_eq!(
        bumped
            .publish()
            .expect("the installer carries the tool")
            .as_slice(),
        [CLI, INSTALLER]
    );
}

#[test]
fn nothing_changed_means_nothing_to_do() {
    let plan = installer()
        .plan(&[UNCHANGED; 3])
        .expect("nothing regressed");
    assert_eq!(plan.states(), &[State::UpToDate; 3]);
    assert_eq!(plan.bump().as_slice(), [0usize; 0]);
    assert_eq!(
        plan.publish().expect("nothing to refuse").as_slice(),
        [0usize; 0]
    );
}

#[test]
fn a_tool_ahead_of_its_release_is_stranded_until_the_installer_is_bumped() {
    let plan = installer()
        .plan(&[AHEAD, UNCHANGED, UNCHANGED])
        .expect("nothing regressed");
    assert_eq!(
        plan.publish().map(|order| order.as_slice().len()),
        Err(Refusal::Stranded {
            component: CLI,
            inside: INSTALLER
        })
    );
    assert_eq!(plan.bump().as_slice(), [INSTALLER]);
}

#[test]
fn a_source_below_its_release_is_refused() {
    let regressed = Fact::Released {
        source: Ordering::Less,
        changed: true,
    };
    assert_eq!(
        installer()
            .plan(&[UNCHANGED, regressed, UNCHANGED])
            .map(|_| ()),
        Err(Regressed { component: DAEMON })
    );
}

// One bootloader built into two firmware images.
const BOOTLOADER: usize = 0;
const FIRMWARE_A: usize = 1;
const FIRMWARE_B: usize = 2;

fn firmware(bootloader: Component<'static>) -> Layout<'static, 3> {
    Layout::new([bootloader, Component::standalone(), Component::standalone()])
        .expect("the bootloader is listed before both images")
}

#[test]
fn a_shared_component_takes_everything_it_ships_inside() {
    let layout = firmware(Component::ships_inside(&[FIRMWARE_A, FIRMWARE_B]));
    let plan = layout
        .plan(&[CHANGED, UNCHANGED, AHEAD])
        .expect("nothing regressed");
    assert_eq!(
        plan.states(),
        &[State::NeedsBump, State::NeedsBump, State::Ready]
    );
    assert_eq!(plan.forced_by(), &[None, Some(BOOTLOADER), None]);
    assert_eq!(plan.bump().as_slice(), [BOOTLOADER, FIRMWARE_A]);
}

#[test]
fn a_manual_component_waits_to_be_named_and_then_brings_what_ships_it() {
    let layout = firmware(Component::ships_inside(&[FIRMWARE_A, FIRMWARE_B]).manual());
    let plan = layout
        .plan(&[CHANGED, UNCHANGED, UNCHANGED])
        .expect("nothing regressed");
    assert_eq!(
        plan.states(),
        &[State::NeedsBump, State::UpToDate, State::UpToDate]
    );
    assert_eq!(plan.bump().as_slice(), [0usize; 0]);
    assert_eq!(
        plan.bump_only(&[BOOTLOADER]).as_slice(),
        [BOOTLOADER, FIRMWARE_A, FIRMWARE_B]
    );
}

#[test]
fn naming_a_component_already_ahead_raises_only_what_ships_it() {
    let layout = firmware(Component::ships_inside(&[FIRMWARE_A, FIRMWARE_B]));
    let plan = layout
        .plan(&[AHEAD, UNCHANGED, AHEAD])
        .expect("nothing regressed");
    assert_eq!(plan.bump_only(&[BOOTLOADER]).as_slice(), [FIRMWARE_A]);
}

#[test]
fn a_named_publish_needs_every_name_ready_and_carried() {
    let layout = firmware(Component::ships_inside(&[FIRMWARE_A, FIRMWARE_B]));
    let plan = layout
        .plan(&[AHEAD, AHEAD, AHEAD])
        .expect("nothing regressed");
    assert_eq!(
        plan.publish_only(&[BOOTLOADER])
            .expect("both images are on their way")
            .as_slice(),
        [BOOTLOADER]
    );
    assert_eq!(
        plan.publish_only(&[FIRMWARE_B, BOOTLOADER])
            .expect("names need no order")
            .as_slice(),
        [BOOTLOADER, FIRMWARE_B]
    );

    let waiting = layout
        .plan(&[AHEAD, AHEAD, UNCHANGED])
        .expect("nothing regressed");
    assert_eq!(
        waiting
            .publish_only(&[FIRMWARE_B])
            .map(|order| order.as_slice().len()),
        Err(Refusal::NotReady {
            component: FIRMWARE_B
        })
    );
    assert_eq!(
        waiting
            .publish_only(&[BOOTLOADER])
            .map(|order| order.as_slice().len()),
        Err(Refusal::Stranded {
            component: BOOTLOADER,
            inside: FIRMWARE_B
        })
    );
}

// An asset pack inside an application inside an installer.
#[test]
fn a_change_travels_through_every_layer() {
    let layout = Layout::new([
        Component::ships_inside(&[1]),
        Component::ships_inside(&[2]),
        Component::standalone(),
        Component::standalone(),
    ])
    .expect("each layer is listed before the next");
    let plan = layout
        .plan(&[CHANGED, UNCHANGED, UNCHANGED, UNCHANGED])
        .expect("nothing regressed");
    assert_eq!(
        plan.states(),
        &[
            State::NeedsBump,
            State::NeedsBump,
            State::NeedsBump,
            State::UpToDate
        ]
    );
    assert_eq!(plan.forced_by(), &[None, Some(0), Some(1), None]);
    assert_eq!(plan.bump().as_slice(), [0, 1, 2]);
}

#[test]
fn a_never_released_component_is_ready() {
    let layout = Layout::new([Component::standalone()]).expect("one component needs no order");
    let plan = layout.plan(&[Fact::Unreleased]).expect("nothing regressed");
    assert_eq!(plan.states(), &[State::Ready]);
    assert_eq!(plan.publish().expect("it ships on its own").as_slice(), [0]);
}

#[test]
fn a_table_is_refused_for_each_way_it_can_be_wrong() {
    let cases: [([Component<'static>; 2], Invalid); 4] = [
        (
            [Component::ships_inside(&[2]), Component::standalone()],
            Invalid::Unknown {
                component: 0,
                inside: 2,
            },
        ),
        (
            [Component::standalone(), Component::ships_inside(&[0])],
            Invalid::OutOfOrder {
                component: 1,
                inside: 0,
            },
        ),
        (
            [Component::ships_inside(&[0]), Component::standalone()],
            Invalid::OutOfOrder {
                component: 0,
                inside: 0,
            },
        ),
        (
            [
                Component::ships_inside(&[1]),
                Component::standalone().manual(),
            ],
            Invalid::ManualOuter {
                component: 0,
                inside: 1,
            },
        ),
    ];
    for (table, why) in cases {
        assert_eq!(Layout::new(table).map(|_| ()), Err(why), "{table:?}");
    }
}

#[test]
#[should_panic]
fn a_name_outside_the_table_panics() {
    let plan = installer()
        .plan(&[UNCHANGED; 3])
        .expect("nothing regressed");
    let _ = plan.bump_only(&[3]);
}
