///  RuntimeRational implements the runtime trait hierarchy from verus-algebra.
///  Each arithmetic operation normalizes its result so that out@ == raw@.canonical(),
///  matching the Ring trait's canonical() wrapper on spec operations.
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
    open spec fn wf_spec(&self) -> bool { RuntimeRational::wf_spec(self) }

    fn add(&self, rhs: &Self) -> (out: Self) {
        let raw = RuntimeRational::add(self, rhs);
        let out = raw.normalize();
        proof { Rational::lemma_canonical_unique(self@.add_spec(rhs@), out@); }
        out
    }
    fn sub(&self, rhs: &Self) -> (out: Self) {
        let raw = RuntimeRational::sub(self, rhs);
        let out = raw.normalize();
        proof { Rational::lemma_canonical_unique(self@.sub_spec(rhs@), out@); }
        out
    }
    fn neg(&self) -> (out: Self) {
        let raw = RuntimeRational::neg(self);
        let out = raw.normalize();
        proof { Rational::lemma_canonical_unique(self@.neg_spec(), out@); }
        out
    }
    fn mul(&self, rhs: &Self) -> (out: Self) {
        let raw = RuntimeRational::mul(self, rhs);
        let out = raw.normalize();
        proof { Rational::lemma_canonical_unique(self@.mul_spec(rhs@), out@); }
        out
    }
    fn eq(&self, rhs: &Self) -> (out: bool) { RuntimeRational::eq(self, rhs) }
    fn copy(&self) -> (out: Self) { crate::runtime_rational::copy_rational(self) }
    fn zero_like(&self) -> (out: Self) { RuntimeRational::from_int(0) }
    fn one_like(&self) -> (out: Self) { RuntimeRational::from_int(1) }
}

impl RuntimeFieldOps<Rational> for RuntimeRational {
    fn recip(&self) -> (out: Self) {
        let raw = RuntimeRational::recip(self).unwrap();
        let out = raw.normalize();
        proof { Rational::lemma_canonical_unique(self@.reciprocal_spec(), out@); }
        out
    }
    fn div(&self, rhs: &Self) -> (out: Self) {
        let raw = RuntimeRational::div(self, rhs);
        let out = raw.normalize();
        proof { Rational::lemma_canonical_unique(self@.div_spec(rhs@), out@); }
        out
    }
}

impl RuntimeOrderedFieldOps<Rational> for RuntimeRational {
    fn le(&self, rhs: &Self) -> (out: bool) { RuntimeRational::le(self, rhs) }
    fn lt(&self, rhs: &Self) -> (out: bool) { RuntimeRational::lt(self, rhs) }
}

} //  verus!
