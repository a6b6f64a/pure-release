use core::cmp::Ordering;

use pure_release::{Component, Fact, Layout};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    const ENGINE: usize = 0;
    const APP: usize = 1;
    const INSTALLER: usize = 2;
    const NAMES: [&str; 3] = ["engine", "app", "installer"];

    let layout = Layout::new([
        Component::ships_inside(&[APP]),
        Component::ships_inside(&[INSTALLER]),
        Component::standalone(),
    ])?;

    // Facts come from your release tooling. Only engine code changed here.
    let unchanged = Fact::Released {
        source: Ordering::Equal,
        changed: false,
    };
    let changed = Fact::Released {
        source: Ordering::Equal,
        changed: true,
    };
    let plan = layout.plan(&[changed, unchanged, unchanged])?;
    assert_eq!(plan.bump().as_slice(), [ENGINE, APP, INSTALLER]);

    println!("Engine changed. Versions to bump:");
    for &component in plan.bump().as_slice() {
        match plan.forced_by()[component] {
            Some(inner) => println!("  {} (carries {})", NAMES[component], NAMES[inner]),
            None => println!("  {}", NAMES[component]),
        }
    }

    // Your tooling raises versions, then reads fresh facts before publishing.
    let ahead = Fact::Released {
        source: Ordering::Greater,
        changed: true,
    };
    let plan = layout.plan(&[ahead, ahead, ahead])?;
    let publish = plan.publish()?;
    assert!(plan.bump().as_slice().is_empty());
    assert_eq!(publish.as_slice(), [ENGINE, APP, INSTALLER]);

    println!("\nAfter those version bumps, build and publish in this order:");
    for &component in publish.as_slice() {
        println!("  {}", NAMES[component]);
    }
    Ok(())
}
