///  RuntimeRational implements the runtime trait hierarchy from verus-algebra.
///  Uses fully-qualified syntax (RuntimeRational::method) to delegate to inherent methods,
///  avoiding recursion since trait methods share the same names.
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
    open spec fn model(&self) -> Rational { self@ }

    #[verifier::inline]
    open spec fn wf_spec(&self) -> bool { RuntimeRational::wf_spec(self) }

    fn add(&self, rhs: &Self) -> (out: Self) { RuntimeRational::add(self, rhs) }
    fn sub(&self, rhs: &Self) -> (out: Self) { RuntimeRational::sub(self, rhs) }
    fn neg(&self) -> (out: Self) { RuntimeRational::neg(self) }
    fn mul(&self, rhs: &Self) -> (out: Self) { RuntimeRational::mul(self, rhs) }
    fn eq(&self, rhs: &Self) -> (out: bool) { RuntimeRational::eq(self, rhs) }
    fn copy(&self) -> (out: Self) { crate::runtime_rational::copy_rational(self) }
    fn zero_like(&self) -> (out: Self) { RuntimeRational::from_int(0) }
    fn one_like(&self) -> (out: Self) { RuntimeRational::from_int(1) }
}

impl RuntimeFieldOps<Rational> for RuntimeRational {
    fn recip(&self) -> (out: Self) { RuntimeRational::recip(self).unwrap() }
    fn div(&self, rhs: &Self) -> (out: Self) { RuntimeRational::div(self, rhs) }
}

impl RuntimeOrderedFieldOps<Rational> for RuntimeRational {
    fn le(&self, rhs: &Self) -> (out: bool) { RuntimeRational::le(self, rhs) }
    fn lt(&self, rhs: &Self) -> (out: bool) { RuntimeRational::lt(self, rhs) }
}

} //  verus!
