#[cfg(verus_keep_ghost)]
pub mod rational;
#[cfg(verus_keep_ghost)]
pub use rational::{Rational, RationalModel};

pub mod runtime_rational;
pub use runtime_rational::RuntimeRational;
