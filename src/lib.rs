#![doc = include_str!("../README.md")]
#![no_std]
#![cfg_attr(verus_only, feature(proc_macro_hygiene))]

mod rules;

pub use rules::{Component, Fact, Invalid, Layout, Order, Plan, Refusal, Regressed, State};
