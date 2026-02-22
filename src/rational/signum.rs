use super::Rational;
use vstd::prelude::*;
use vstd::calc;
use vstd::arithmetic::mul::{
    lemma_mul_basics,
    lemma_mul_by_zero_is_zero,
    lemma_mul_is_commutative,
    lemma_mul_strict_inequality,
};

verus! {

impl Rational {
    pub proof fn lemma_eqv_signum(a: Self, b: Self)
        requires
            a.eqv_spec(b),
        ensures
            a.signum() == b.signum(),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(a.num * b.denom() == b.num * a.denom());

        if a.num == 0 {
            assert(b.num * a.denom() == 0);
            assert((a.denom() != 0 && b.num * a.denom() == 0) ==> (b.num == 0)) by (nonlinear_arith);
            assert(a.denom() != 0);
            assert(b.num == 0);
            Self::lemma_signum_zero_iff(a);
            Self::lemma_signum_zero_iff(b);
            assert((a.signum() == 0) == (a.num == 0));
            assert((b.signum() == 0) == (b.num == 0));
            assert(a.signum() == 0);
            assert(b.signum() == 0);
        } else if a.num > 0 {
            assert((a.num > 0 && b.denom() > 0) ==> a.num * b.denom() > 0) by (nonlinear_arith);
            assert(a.num * b.denom() > 0);
            assert(b.num * a.denom() > 0);
            assert((a.denom() > 0 && b.num * a.denom() > 0) ==> b.num > 0) by (nonlinear_arith);
            assert(b.num > 0);
            Self::lemma_signum_positive_iff(a);
            Self::lemma_signum_positive_iff(b);
            assert((a.signum() == 1) == (a.num > 0));
            assert((b.signum() == 1) == (b.num > 0));
            assert(a.signum() == 1);
            assert(b.signum() == 1);
        } else {
            assert(a.num < 0);
            assert((a.num < 0 && b.denom() > 0) ==> a.num * b.denom() < 0) by (nonlinear_arith);
            assert(a.num * b.denom() < 0);
            assert(b.num * a.denom() < 0);
            assert((a.denom() > 0 && b.num * a.denom() < 0) ==> b.num < 0) by (nonlinear_arith);
            assert(b.num < 0);
            Self::lemma_signum_negative_iff(a);
            Self::lemma_signum_negative_iff(b);
            assert((a.signum() == -1) == (a.num < 0));
            assert((b.signum() == -1) == (b.num < 0));
            assert(a.signum() == -1);
            assert(b.signum() == -1);
        }
        assert(a.signum() == b.signum());
    }

    pub proof fn lemma_signum_positive_iff(a: Self)
        ensures
            (a.signum() == 1) == (a.num > 0),
    {
        if a.num > 0 {
            assert(a.signum() == 1);
        } else {
            assert(a.signum() != 1);
        }
    }

    pub proof fn lemma_signum_neg(a: Self)
        ensures
            a.neg_spec().num == -a.num,
    {
        let n = a.neg_spec();
        assert(n.num == -a.num);
    }

    pub proof fn lemma_signum_negate(a: Self)
        ensures
            a.neg_spec().signum() == -a.signum(),
    {
        let n = a.neg_spec();
        Self::lemma_signum_neg(a);
        if a.num > 0 {
            assert(a.signum() == 1);
            assert(n.num == -a.num);
            assert((a.num > 0) ==> (0 - a.num < 0)) by (nonlinear_arith);
            assert(0 - a.num < 0);
            assert(-a.num == 0 - a.num);
            assert(-a.num < 0);
            assert(n.num < 0);
            assert(n.signum() == -1);
            assert(-a.signum() == -(1));
            assert(-(1) == -1);
        } else if a.num < 0 {
            assert(a.signum() == -1);
            assert(n.num == -a.num);
            assert((a.num < 0) ==> (0 - a.num > 0)) by (nonlinear_arith);
            assert(0 - a.num > 0);
            assert(-a.num == 0 - a.num);
            assert(-a.num > 0);
            assert(n.num > 0);
            assert(n.signum() == 1);
            assert(-a.signum() == -(-1));
            assert(-(-1) == 1);
        } else {
            assert(a.num == 0);
            assert(a.signum() == 0);
            assert(n.num == -a.num);
            assert(n.num == 0);
            assert(n.signum() == 0);
            assert(-a.signum() == -(0));
            assert(-(0) == 0);
        }
        assert(n.signum() == -a.signum());
    }

    pub proof fn lemma_signum_negative_iff(a: Self)
        ensures
            (a.signum() == -1) == (a.num < 0),
    {
        if a.num < 0 {
            assert(a.signum() == -1);
        } else {
            assert(a.signum() != -1);
        }
    }

    pub proof fn lemma_signum_zero_iff(a: Self)
        ensures
            (a.signum() == 0) == (a.num == 0),
    {
        if a.num == 0 {
            assert(a.signum() == 0);
        } else {
            assert(a.signum() != 0);
        }
    }

    pub proof fn lemma_signum_cases(a: Self)
        ensures
            a.signum() == 1 || a.signum() == -1 || a.signum() == 0,
    {
        if a.num > 0 {
            assert(a.signum() == 1);
        } else if a.num < 0 {
            assert(a.signum() == -1);
        } else {
            assert(a.signum() == 0);
        }
    }

    pub proof fn lemma_signum_mul(a: Self, b: Self)
        ensures
            a.mul_spec(b).signum() == a.signum() * b.signum(),
    {
        let p = a.mul_spec(b);
        assert(p.num == a.num * b.num);

        if a.num == 0 {
            assert(a.signum() == 0);
            calc! {
                (==)
                p.num;
                { assert(p.num == a.num * b.num); assert(a.num == 0); }
                0 * b.num;
                {
                    lemma_mul_by_zero_is_zero(b.num);
                    assert(0 * b.num == 0);
                }
                0;
            }
            assert(p.signum() == 0);
            assert(a.signum() * b.signum() == 0);
        } else if a.num > 0 {
            assert(a.signum() == 1);
            if b.num == 0 {
                assert(b.signum() == 0);
                calc! {
                    (==)
                    p.num;
                    { assert(p.num == a.num * b.num); assert(b.num == 0); }
                    a.num * 0;
                    {
                        lemma_mul_by_zero_is_zero(a.num);
                        assert(a.num * 0 == 0);
                    }
                    0;
                }
                assert(p.signum() == 0);
                assert(a.signum() * b.signum() == 0);
            } else if b.num > 0 {
                assert(b.signum() == 1);
                lemma_mul_strict_inequality(0, a.num, b.num);
                lemma_mul_basics(b.num);
                assert(0 * b.num == 0);
                assert(0 < a.num * b.num);
                assert(p.num > 0);
                assert(p.signum() == 1);
                assert(a.signum() * b.signum() == 1);
            } else {
                assert(b.num < 0);
                assert(b.signum() == -1);
                lemma_mul_strict_inequality(b.num, 0, a.num);
                lemma_mul_is_commutative(a.num, b.num);
                lemma_mul_basics(a.num);
                assert(b.num * a.num < 0 * a.num);
                assert(0 * a.num == 0);
                assert(a.num * b.num == b.num * a.num);
                assert(p.num < 0);
                assert(p.signum() == -1);
                assert(a.signum() * b.signum() == -1);
            }
        } else {
            assert(a.num < 0);
            assert(a.signum() == -1);
            if b.num == 0 {
                assert(b.signum() == 0);
                calc! {
                    (==)
                    p.num;
                    { assert(p.num == a.num * b.num); assert(b.num == 0); }
                    a.num * 0;
                    {
                        lemma_mul_by_zero_is_zero(a.num);
                        assert(a.num * 0 == 0);
                    }
                    0;
                }
                assert(p.signum() == 0);
                assert(a.signum() * b.signum() == 0);
            } else if b.num > 0 {
                assert(b.signum() == 1);
                lemma_mul_strict_inequality(a.num, 0, b.num);
                lemma_mul_basics(b.num);
                assert(a.num * b.num < 0 * b.num);
                assert(0 * b.num == 0);
                assert(p.num < 0);
                assert(p.signum() == -1);
                assert(a.signum() * b.signum() == -1);
            } else {
                assert(b.num < 0);
                assert(b.signum() == -1);
                assert((a.num < 0) ==> (0 - a.num > 0)) by (nonlinear_arith);
                assert(0 - a.num > 0);
                assert(-a.num == 0 - a.num);
                assert(-a.num > 0);
                assert((b.num < 0) ==> (0 - b.num > 0)) by (nonlinear_arith);
                assert(0 - b.num > 0);
                assert(-b.num == 0 - b.num);
                assert(-b.num > 0);
                lemma_mul_strict_inequality(0, -a.num, -b.num);
                lemma_mul_basics(-b.num);
                assert(0 * (-b.num) == 0);
                assert(0 < (-a.num) * (-b.num));
                assert((-a.num) * (-b.num) == a.num * b.num) by (nonlinear_arith);
                assert(p.num > 0);
                assert(p.signum() == 1);
                assert(a.signum() * b.signum() == 1);
            }
        }
        assert(p.signum() == a.signum() * b.signum());
    }

}

} // verus!
