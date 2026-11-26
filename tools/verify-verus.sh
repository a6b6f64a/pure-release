#!/bin/sh
set -eu

command -v verus >/dev/null 2>&1 || {
    printf '%s\n' 'error: verus not found on PATH' >&2
    exit 127
}

theorems=src/rules/theorems.rs
[ -f "$theorems" ] || {
    printf '%s\n' "error: missing $theorems" >&2
    exit 1
}
grep -Eq '^[[:space:]]*verus![[:space:]]*\{' "$theorems" || {
    printf '%s\n' "error: $theorems has no Verus module" >&2
    exit 1
}

for theorem in \
    a_changed_component_is_never_up_to_date_and_a_regression_is_refused \
    planning_strands_nothing_and_forces_only_what_carries_something_outgoing \
    one_bump_leaves_nothing_to_bump_and_publish_then_accepts_everything_ready \
    a_named_bump_brings_everything_its_components_ship_inside \
    publish_releases_only_what_is_ready_with_what_carries_it_and_inner_first
do
    if ! grep -Eq "^[[:space:]]*(pub[[:space:]]+)?(proof[[:space:]]+)?fn[[:space:]]+$theorem([<(]|[[:space:]])" "$theorems"; then
        printf '%s\n' "error: missing executable theorem function: $theorem" >&2
        exit 1
    fi
done

exec verus --crate-type=lib src/lib.rs --no-external-by-default --no-cheating --triggers-mode silent
