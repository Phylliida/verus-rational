use super::Rational;
use vstd::prelude::*;
use vstd::arithmetic::mul::lemma_mul_by_zero_is_zero;

verus! {

impl Rational {
    /// (a * b) as int == (a as int) * (b as int) for nats.
    pub proof fn lemma_nat_mul_cast(a: nat, b: nat)
        ensures
            (a * b) as int == (a as int) * (b as int),
    {
        assert((a * b) as int == (a as int) * (b as int)) by (nonlinear_arith);
    }

    /// The denominator is always positive.
    pub proof fn lemma_denom_positive(a: Self)
        ensures
            a.denom_nat() > 0,
            a.denom() > 0,
    {
        assert(a.denom_nat() > 0);
        assert(a.denom() == a.denom_nat() as int);
        assert(a.denom() > 0);
    }

    /// a ≡ 0 ↔ a.num == 0.
    pub proof fn lemma_eqv_zero_iff_num_zero(a: Self)
        ensures
            a.eqv_spec(Self::from_int_spec(0)) == (a.num == 0),
    {
        let z = Self::from_int_spec(0);
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(a.eqv_spec(z) == (a.num * z.denom() == z.num * a.denom()));
        assert(a.eqv_spec(z) == (a.num * 1 == 0 * a.denom()));
        lemma_mul_by_zero_is_zero(a.denom());
        assert(0 * a.denom() == 0);
        assert(a.eqv_spec(z) == (a.num * 1 == 0));
        assert((a.num * 1 == 0) == (a.num == 0)) by (nonlinear_arith);
    }

    /// denom(a + b) == denom(a) * denom(b) (nat version).
    pub proof fn lemma_add_denom_product(a: Self, b: Self)
        ensures
            a.add_spec(b).denom_nat() == a.denom_nat() * b.denom_nat(),
    {
        let out = a.add_spec(b);
        let lhs = out.denom_nat();
        let rhs = a.denom_nat() * b.denom_nat();

        assert(lhs == (a.den * b.den + a.den + b.den) + 1);
        assert(rhs == (a.den + 1) * (b.den + 1));
        assert((a.den * b.den + a.den + b.den) + 1 == (a.den + 1) * (b.den + 1))
            by (nonlinear_arith);
    }

    /// denom(a + b) == denom(a) * denom(b) (int version).
    pub proof fn lemma_add_denom_product_int(a: Self, b: Self)
        ensures
            a.add_spec(b).denom() == a.denom() * b.denom(),
    {
        let out = a.add_spec(b);
        let da = a.denom_nat();
        let db = b.denom_nat();
        Self::lemma_add_denom_product(a, b);
        Self::lemma_nat_mul_cast(da, db);
        assert(out.denom_nat() == da * db);
        assert(out.denom() == out.denom_nat() as int);
        assert(a.denom() == da as int);
        assert(b.denom() == db as int);
        assert(out.denom() == (da * db) as int);
        assert((da * db) as int == (da as int) * (db as int));
        assert(out.denom() == a.denom() * b.denom());
    }

    /// denom(a * b) == denom(a) * denom(b) (nat version).
    pub proof fn lemma_mul_denom_product(a: Self, b: Self)
        ensures
            a.mul_spec(b).denom_nat() == a.denom_nat() * b.denom_nat(),
    {
        let out = a.mul_spec(b);
        let lhs = out.denom_nat();
        let rhs = a.denom_nat() * b.denom_nat();

        assert(lhs == (a.den * b.den + a.den + b.den) + 1);
        assert(rhs == (a.den + 1) * (b.den + 1));
        assert((a.den * b.den + a.den + b.den) + 1 == (a.den + 1) * (b.den + 1))
            by (nonlinear_arith);
    }

    /// denom(a * b) == denom(a) * denom(b) (int version).
    pub proof fn lemma_mul_denom_product_int(a: Self, b: Self)
        ensures
            a.mul_spec(b).denom() == a.denom() * b.denom(),
    {
        let out = a.mul_spec(b);
        let da = a.denom_nat();
        let db = b.denom_nat();
        Self::lemma_mul_denom_product(a, b);
        Self::lemma_nat_mul_cast(da, db);
        assert(out.denom_nat() == da * db);
        assert(out.denom() == out.denom_nat() as int);
        assert(a.denom() == da as int);
        assert(b.denom() == db as int);
        assert(out.denom() == (da * db) as int);
        assert((da * db) as int == (da as int) * (db as int));
        assert(out.denom() == a.denom() * b.denom());
    }

    /// denom(a - b) == denom(a) * denom(b) (nat version).
    pub proof fn lemma_sub_denom_product(a: Self, b: Self)
        ensures
            a.sub_spec(b).denom_nat() == a.denom_nat() * b.denom_nat(),
    {
        let s = a.sub_spec(b);
        assert(s == a.add_spec(b.neg_spec()));
        Self::lemma_add_denom_product(a, b.neg_spec());
        assert(a.add_spec(b.neg_spec()).denom_nat() == a.denom_nat() * b.neg_spec().denom_nat());
        assert(b.neg_spec().denom_nat() == b.denom_nat());
        assert(s.denom_nat() == a.denom_nat() * b.denom_nat());
    }

    /// denom(a - b) == denom(a) * denom(b) (int version).
    pub proof fn lemma_sub_denom_product_int(a: Self, b: Self)
        ensures
            a.sub_spec(b).denom() == a.denom() * b.denom(),
    {
        let out = a.sub_spec(b);
        let da = a.denom_nat();
        let db = b.denom_nat();
        Self::lemma_sub_denom_product(a, b);
        Self::lemma_nat_mul_cast(da, db);
        assert(out.denom_nat() == da * db);
        assert(out.denom() == out.denom_nat() as int);
        assert(a.denom() == da as int);
        assert(b.denom() == db as int);
        assert(out.denom() == (da * db) as int);
        assert((da * db) as int == (da as int) * (db as int));
        assert(out.denom() == a.denom() * b.denom());
    }

}

} // verus!
