///  RuntimeRational implements the runtime trait hierarchy from verus-algebra.
use crate::RuntimeRational;

#[cfg(verus_keep_ghost)]
use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
use crate::rational::Rational;
#[cfg(verus_keep_ghost)]
use verus_algebra::traits::runtime::*;

#[cfg(verus_keep_ghost)]
verus! {

impl RuntimeRingOps<Rational> for RuntimeRational {
    #[verifier::inline]
    open spec fn rf_view(&self) -> Rational { self@ }

    #[verifier::inline]
    open spec fn wf_spec(&self) -> bool { self.wf_spec() }

    fn rf_add(&self, rhs: &Self) -> (out: Self) { self.add(rhs) }
    fn rf_sub(&self, rhs: &Self) -> (out: Self) { self.sub(rhs) }
    fn rf_neg(&self) -> (out: Self) { self.neg() }
    fn rf_mul(&self, rhs: &Self) -> (out: Self) { self.mul(rhs) }
    fn rf_eq(&self, rhs: &Self) -> (out: bool) { self.eq(rhs) }
    fn rf_copy(&self) -> (out: Self) { crate::runtime_rational::copy_rational(self) }

    fn rf_zero_like(&self) -> (out: Self) { RuntimeRational::from_int(0) }
    fn rf_one_like(&self) -> (out: Self) { RuntimeRational::from_int(1) }
}

impl RuntimeFieldOps<Rational> for RuntimeRational {
    fn rf_recip(&self) -> (out: Self) { self.recip().unwrap() }
    fn rf_div(&self, rhs: &Self) -> (out: Self) { self.div(rhs) }
}

impl RuntimeOrderedFieldOps<Rational> for RuntimeRational {
    fn rf_le(&self, rhs: &Self) -> (out: bool) { self.le(rhs) }
    fn rf_lt(&self, rhs: &Self) -> (out: bool) { self.lt(rhs) }
}

} //  verus!
