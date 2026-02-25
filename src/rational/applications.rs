use super::Rational;
use vstd::prelude::*;
use vstd::calc;
use vstd::arithmetic::mul::{
    lemma_mul_basics,
    lemma_mul_by_zero_is_zero,
    lemma_mul_is_associative,
    lemma_mul_is_commutative,
    lemma_mul_strict_inequality,
};

verus! {

impl Rational {
    // ── Absolute value ──────────────────────────────────────────────

    /// abs(a) is non-negative.
    pub proof fn lemma_abs_nonneg(a: Self)
        ensures
            a.abs_spec().signum() >= 0,
    {
        if a.num >= 0 {
            assert(a.abs_spec() == a);
            if a.num > 0 {
                assert(a.signum() == 1);
            } else {
                assert(a.signum() == 0);
            }
        } else {
            assert(a.abs_spec() == a.neg_spec());
            assert(a.neg_spec().num == -a.num);
            assert(a.num < 0);
            assert((-a.num) > 0) by (nonlinear_arith)
                requires a.num < 0;
            assert(a.neg_spec().signum() == 1);
        }
    }

    /// abs(a) ≡ 0 if and only if a ≡ 0.
    pub proof fn lemma_abs_zero_iff(a: Self)
        ensures
            a.abs_spec().eqv_spec(Self::from_int_spec(0)) == a.eqv_spec(Self::from_int_spec(0)),
    {
        let z = Self::from_int_spec(0);
        Self::lemma_eqv_zero_iff_num_zero(a);
        if a.num >= 0 {
            assert(a.abs_spec() == a);
        } else {
            assert(a.abs_spec() == a.neg_spec());
            assert(a.neg_spec().num == -a.num);
            Self::lemma_eqv_zero_iff_num_zero(a.neg_spec());
            // -a.num == 0 ↔ a.num == 0; but a.num < 0, so neither is 0
            assert(a.num < 0);
            assert(a.num != 0);
            assert(-a.num != 0);
        }
    }

    /// abs(-a) ≡ abs(a).
    pub proof fn lemma_abs_neg(a: Self)
        ensures
            a.neg_spec().abs_spec().eqv_spec(a.abs_spec()),
    {
        let na = a.neg_spec();
        assert(na.num == -a.num);
        assert(na.den == a.den);
        Self::lemma_denom_positive(a);
        if a.num > 0 {
            // a.abs = a (num >= 0)
            // na.num = -a.num < 0, so na.abs = na.neg = a
            assert(a.abs_spec() == a);
            assert(na.num < 0);
            assert(na.abs_spec() == na.neg_spec());
            Self::lemma_neg_involution(a);
            assert(na.neg_spec() == a);
            Self::lemma_eqv_reflexive(a);
        } else if a.num < 0 {
            // a.abs = a.neg (num < 0)
            // na.num = -a.num > 0, so na.abs = na
            assert(a.abs_spec() == a.neg_spec());
            assert((-a.num) > 0) by (nonlinear_arith)
                requires a.num < 0;
            assert(na.num > 0);
            assert(na.abs_spec() == na);
            // na == a.neg_spec(), so na.abs == na == a.neg == a.abs
            Self::lemma_eqv_reflexive(a.neg_spec());
        } else {
            // a.num == 0
            assert(a.abs_spec() == a);
            assert(na.num == 0);
            assert(na.abs_spec() == na);
            // a and na are both zero-numerator with same den
            assert(na.num == a.num);
            Self::lemma_eqv_reflexive(a);
            assert(na == a);
        }
    }

    /// abs(a * b) ≡ abs(a) * abs(b).
    pub proof fn lemma_abs_mul(a: Self, b: Self)
        ensures
            a.mul_spec(b).abs_spec().eqv_spec(
                a.abs_spec().mul_spec(b.abs_spec())),
    {
        let ab = a.mul_spec(b);
        let aa = a.abs_spec();
        let ba = b.abs_spec();
        let prod_abs = aa.mul_spec(ba);

        assert(ab.num == a.num * b.num);
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);

        // Denominators match: aa.den == a.den, ba.den == b.den
        assert(aa.den == a.den);
        assert(ba.den == b.den);
        assert(ab.den == a.den * b.den + a.den + b.den);
        assert(prod_abs.den == aa.den * ba.den + aa.den + ba.den);
        assert(prod_abs.den == ab.den);

        // Four-way case split on signs
        if a.num >= 0 && b.num >= 0 {
            assert(aa.num == a.num);
            assert(ba.num == b.num);
            assert(prod_abs.num == a.num * b.num);
            assert(a.num * b.num >= 0) by (nonlinear_arith)
                requires a.num >= 0, b.num >= 0;
            assert(ab.abs_spec() == ab);
            assert(ab.abs_spec() == prod_abs);
            Self::lemma_eqv_reflexive(prod_abs);
        } else if a.num >= 0 && b.num < 0 {
            assert(aa.num == a.num);
            assert(ba.num == -b.num);
            assert(prod_abs.num == a.num * (-b.num));
            if a.num == 0 {
                assert(a.num * b.num == 0) by (nonlinear_arith)
                    requires a.num == 0;
                assert(ab.abs_spec() == ab);
                assert(a.num * (-b.num) == 0) by (nonlinear_arith)
                    requires a.num == 0;
                assert(prod_abs.num == 0);
                assert(ab.abs_spec() == prod_abs);
                Self::lemma_eqv_reflexive(prod_abs);
            } else {
                assert(a.num > 0);
                assert(a.num * b.num < 0) by (nonlinear_arith)
                    requires a.num > 0, b.num < 0;
                assert(ab.abs_spec() == ab.neg_spec());
                assert(ab.neg_spec().num == -(a.num * b.num));
                assert(ab.neg_spec().den == ab.den);
                assert(a.num * (-b.num) == -(a.num * b.num)) by (nonlinear_arith)
                    requires a.num > 0, b.num < 0;
                assert(ab.abs_spec() == prod_abs);
                Self::lemma_eqv_reflexive(prod_abs);
            }
        } else if a.num < 0 && b.num >= 0 {
            assert(aa.num == -a.num);
            assert(ba.num == b.num);
            assert(prod_abs.num == (-a.num) * b.num);
            if b.num == 0 {
                assert(a.num * b.num == 0) by (nonlinear_arith)
                    requires b.num == 0;
                assert(ab.abs_spec() == ab);
                assert((-a.num) * b.num == 0) by (nonlinear_arith)
                    requires b.num == 0;
                assert(prod_abs.num == 0);
                assert(ab.num == 0);
                assert(ab.abs_spec() == prod_abs);
                Self::lemma_eqv_reflexive(prod_abs);
            } else {
                assert(b.num > 0);
                assert(a.num * b.num < 0) by (nonlinear_arith)
                    requires a.num < 0, b.num > 0;
                assert(ab.abs_spec() == ab.neg_spec());
                assert(ab.neg_spec().num == -(a.num * b.num));
                assert(ab.neg_spec().den == ab.den);
                assert((-a.num) * b.num == -(a.num * b.num)) by (nonlinear_arith)
                    requires a.num < 0, b.num > 0;
                assert(ab.abs_spec() == prod_abs);
                Self::lemma_eqv_reflexive(prod_abs);
            }
        } else {
            // a.num < 0 && b.num < 0
            assert(a.num < 0);
            assert(b.num < 0);
            assert(aa.num == -a.num);
            assert(ba.num == -b.num);
            assert(prod_abs.num == (-a.num) * (-b.num));
            assert(a.num * b.num > 0) by (nonlinear_arith)
                requires a.num < 0, b.num < 0;
            assert(ab.abs_spec() == ab);
            assert((-a.num) * (-b.num) == a.num * b.num) by (nonlinear_arith)
                requires a.num < 0, b.num < 0;
            assert(prod_abs.num == a.num * b.num);
            assert(ab.abs_spec() == prod_abs);
            Self::lemma_eqv_reflexive(prod_abs);
        }
    }

    /// Triangle inequality: abs(a + b) ≤ abs(a) + abs(b).
    ///
    /// Expressed as: abs(a+b) is le_spec to abs(a).add_spec(abs(b)).
    pub proof fn lemma_triangle_inequality(a: Self, b: Self)
        ensures
            a.add_spec(b).abs_spec().le_spec(
                a.abs_spec().add_spec(b.abs_spec())),
    {
        let s = a.add_spec(b);
        let lhs = s.abs_spec();  // |a + b|
        let rhs = a.abs_spec().add_spec(b.abs_spec());  // |a| + |b|

        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_add_denom_product_int(a, b);
        let da = a.denom();
        let db = b.denom();

        // s.num = a.num * db + b.num * da
        // s.denom() = da * db
        assert(s.num == a.num * db + b.num * da);
        assert(s.denom() == da * db);

        // abs(a): num is a.num or -a.num, den is a.den
        // abs(b): num is b.num or -b.num, den is b.den
        // rhs.num = abs(a).num * db + abs(b).num * da

        // We need: |a.num * db + b.num * da| * rhs.denom() <= rhs.num * lhs.denom()
        // Since lhs.denom() == rhs.denom() (both have denom_nat = da*db products),
        // it suffices to show |a.num * db + b.num * da| <= |a.num| * db + |b.num| * da
        // which is the standard integer triangle inequality (da, db > 0).

        // lhs and rhs have the same denominator structure
        assert(a.abs_spec().den == a.den);
        assert(b.abs_spec().den == b.den);
        Self::lemma_add_denom_product_int(a.abs_spec(), b.abs_spec());
        assert(rhs.denom() == a.abs_spec().denom() * b.abs_spec().denom());
        assert(a.abs_spec().denom() == da);
        assert(b.abs_spec().denom() == db);
        assert(rhs.denom() == da * db);

        // lhs.denom() == s.denom() or s.neg().denom()
        // In either case, denom is preserved through abs
        if s.num >= 0 {
            assert(lhs == s);
        } else {
            assert(lhs == s.neg_spec());
            assert(lhs.den == s.den);
        }
        assert(lhs.denom() == s.denom());
        assert(lhs.denom() == da * db);
        assert(lhs.denom() == rhs.denom());

        // Now reduce to integer inequality
        // lhs.le_spec(rhs) == (lhs.num * rhs.denom() <= rhs.num * lhs.denom())
        // Since lhs.denom() == rhs.denom(), this is lhs.num * D <= rhs.num * D where D > 0
        // i.e. lhs.num <= rhs.num

        let ghost lhs_num = lhs.num;
        let ghost rhs_num = rhs.num;
        let ghost D = lhs.denom();
        assert(D == da * db);
        assert(D > 0);

        // lhs.num = |a.num * db + b.num * da|
        let ghost sn = a.num * db + b.num * da;
        if s.num >= 0 {
            assert(lhs_num == sn);
        } else {
            assert(lhs_num == -sn);
        }

        // rhs.num = |a.num| * db + |b.num| * da  (since da, db > 0 as ints)
        let ghost an = if a.num >= 0 { a.num } else { -a.num };
        let ghost bn = if b.num >= 0 { b.num } else { -b.num };
        assert(a.abs_spec().num == an);
        assert(b.abs_spec().num == bn);
        assert(rhs_num == an * db + bn * da);

        // Integer triangle inequality: |x + y| <= |x| + |y|
        // where x = a.num * db, y = b.num * da
        // |x| = |a.num| * db = an * db  (db > 0)
        // |y| = |b.num| * da = bn * da  (da > 0)
        assert(
            (da > 0 && db > 0)
            ==> (
                (sn >= 0 ==> sn <= an * db + bn * da)
                && (sn < 0 ==> -sn <= an * db + bn * da)
            )
        ) by (nonlinear_arith)
            requires
                an == (if a.num >= 0 { a.num } else { -a.num }),
                bn == (if b.num >= 0 { b.num } else { -b.num }),
                sn == a.num * db + b.num * da,
        ;

        assert(lhs_num <= rhs_num);

        // lhs.num <= rhs.num and D > 0, so lhs.num * D <= rhs.num * D
        assert((lhs_num <= rhs_num && D > 0) ==> lhs_num * D <= rhs_num * D)
            by (nonlinear_arith);
        assert(lhs.le_spec(rhs) == (lhs_num * D <= rhs_num * D));
    }

    // ── Min / max ───────────────────────────────────────────────────

    /// min(a, b) ≤ a.
    pub proof fn lemma_min_le_left(a: Self, b: Self)
        ensures
            a.min_spec(b).le_spec(a),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        if a.le_spec(b) {
            assert(a.min_spec(b) == a);
            // a ≤ a is trivial
        } else {
            assert(a.min_spec(b) == b);
            // ¬(a ≤ b) means b < a, so b ≤ a
            Self::lemma_trichotomy(a, b);
            Self::lemma_lt_implies_le(b, a);
        }
    }

    /// min(a, b) ≤ b.
    pub proof fn lemma_min_le_right(a: Self, b: Self)
        ensures
            a.min_spec(b).le_spec(b),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        if a.le_spec(b) {
            assert(a.min_spec(b) == a);
            // a ≤ b given
        } else {
            assert(a.min_spec(b) == b);
            // b ≤ b trivial
        }
    }

    /// a ≤ max(a, b).
    pub proof fn lemma_max_ge_left(a: Self, b: Self)
        ensures
            a.le_spec(a.max_spec(b)),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        if a.le_spec(b) {
            assert(a.max_spec(b) == b);
            // a ≤ b given
        } else {
            assert(a.max_spec(b) == a);
            // a ≤ a trivial
        }
    }

    /// b ≤ max(a, b).
    pub proof fn lemma_max_ge_right(a: Self, b: Self)
        ensures
            b.le_spec(a.max_spec(b)),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        if a.le_spec(b) {
            assert(a.max_spec(b) == b);
            // b ≤ b trivial
        } else {
            assert(a.max_spec(b) == a);
            // ¬(a ≤ b) means b < a, so b ≤ a
            Self::lemma_trichotomy(a, b);
            Self::lemma_lt_implies_le(b, a);
        }
    }

    /// min(a, b) + max(a, b) ≡ a + b.
    pub proof fn lemma_min_max_sum(a: Self, b: Self)
        ensures
            a.min_spec(b).add_spec(a.max_spec(b)).eqv_spec(a.add_spec(b)),
    {
        if a.le_spec(b) {
            assert(a.min_spec(b) == a);
            assert(a.max_spec(b) == b);
            Self::lemma_eqv_reflexive(a.add_spec(b));
        } else {
            assert(a.min_spec(b) == b);
            assert(a.max_spec(b) == a);
            // b + a ≡ a + b
            Self::lemma_add_commutative(b, a);
            assert(b.add_spec(a) == a.add_spec(b));
            Self::lemma_eqv_reflexive(a.add_spec(b));
        }
    }

    /// min is commutative (up to equivalence).
    pub proof fn lemma_min_commutative(a: Self, b: Self)
        ensures
            a.min_spec(b).eqv_spec(b.min_spec(a)),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_trichotomy(a, b);
        if a.le_spec(b) && b.le_spec(a) {
            Self::lemma_le_antisymmetric(a, b);
            assert(a.min_spec(b) == a);
            assert(b.min_spec(a) == b);
            Self::lemma_eqv_symmetric(a, b);
        } else if a.le_spec(b) {
            assert(a.min_spec(b) == a);
            assert(!b.le_spec(a));
            assert(b.min_spec(a) == a);
            Self::lemma_eqv_reflexive(a);
        } else {
            assert(a.min_spec(b) == b);
            Self::lemma_lt_implies_le(b, a);
            assert(b.le_spec(a));
            assert(b.min_spec(a) == b);
            Self::lemma_eqv_reflexive(b);
        }
    }

    /// max is commutative (up to equivalence).
    pub proof fn lemma_max_commutative(a: Self, b: Self)
        ensures
            a.max_spec(b).eqv_spec(b.max_spec(a)),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_trichotomy(a, b);
        if a.le_spec(b) && b.le_spec(a) {
            Self::lemma_le_antisymmetric(a, b);
            assert(a.max_spec(b) == b);
            assert(b.max_spec(a) == a);
        } else if a.le_spec(b) {
            assert(a.max_spec(b) == b);
            assert(!b.le_spec(a));
            assert(b.max_spec(a) == b);
            Self::lemma_eqv_reflexive(b);
        } else {
            assert(a.max_spec(b) == a);
            Self::lemma_lt_implies_le(b, a);
            assert(b.le_spec(a));
            assert(b.max_spec(a) == a);
            Self::lemma_eqv_reflexive(a);
        }
    }

    // ── Sum of squares ───────────────────────────────────────────────

    /// a*a + b*b ≥ 0 (as le_spec from zero).
    pub proof fn lemma_sum_of_squares_nonneg(a: Self, b: Self)
        ensures
            Self::from_int_spec(0).le_spec(
                a.mul_spec(a).add_spec(b.mul_spec(b))),
    {
        Self::lemma_square_le_nonneg(a);
        Self::lemma_square_le_nonneg(b);
        let z = Self::from_int_spec(0);
        let aa = a.mul_spec(a);
        let bb = b.mul_spec(b);
        let sum = aa.add_spec(bb);
        // z ≤ aa, z ≤ bb
        // z + z ≡ z, and z ≤ aa implies z + z ≤ aa + bb
        // Actually, simpler: just use add monotonicity
        // z ≤ aa and z ≤ bb, so z + z ≤ aa + bb
        Self::lemma_le_add_monotone(z, aa, bb);
        // z + bb ≤ aa + bb
        Self::lemma_le_add_monotone(z, bb, aa);
        // z + aa ≤ bb + aa = aa + bb
        Self::lemma_add_commutative(z, bb);
        Self::lemma_add_commutative(z, aa);
        // z + z ≤ z + aa ≤ aa + bb (but we need z ≤ sum directly)
        // Simpler approach: unfold le_spec directly
        Self::lemma_denom_positive(aa);
        Self::lemma_denom_positive(bb);
        Self::lemma_add_denom_product_int(aa, bb);
        assert(sum.num == aa.num * bb.denom() + bb.num * aa.denom());
        assert(sum.denom() == aa.denom() * bb.denom());
        assert(z.num == 0);
        assert(z.denom() == 1);
        // aa.num = a.num * a.num >= 0
        Self::lemma_mul_denom_product_int(a, a);
        Self::lemma_mul_denom_product_int(b, b);
        assert(aa.num == a.num * a.num);
        assert(bb.num == b.num * b.num);
        assert(a.num * a.num >= 0) by (nonlinear_arith);
        assert(b.num * b.num >= 0) by (nonlinear_arith);
        assert(aa.denom() > 0);
        assert(bb.denom() > 0);
        assert((aa.num >= 0 && bb.denom() > 0) ==> aa.num * bb.denom() >= 0)
            by (nonlinear_arith);
        assert((bb.num >= 0 && aa.denom() > 0) ==> bb.num * aa.denom() >= 0)
            by (nonlinear_arith);
        assert(sum.num >= 0);
        lemma_mul_by_zero_is_zero(sum.denom());
        assert(z.num * sum.denom() == 0);
        assert((z.denom() == 1) ==> sum.num * z.denom() == sum.num)
            by (nonlinear_arith);
    }

    /// a*a + b*b ≡ 0 if and only if a ≡ 0 and b ≡ 0.
    pub proof fn lemma_sum_of_squares_zero_iff(a: Self, b: Self)
        ensures
            a.mul_spec(a).add_spec(b.mul_spec(b)).eqv_spec(Self::from_int_spec(0))
            == (a.eqv_spec(Self::from_int_spec(0)) && b.eqv_spec(Self::from_int_spec(0))),
    {
        let z = Self::from_int_spec(0);
        let aa = a.mul_spec(a);
        let bb = b.mul_spec(b);
        let sum = aa.add_spec(bb);

        Self::lemma_mul_denom_product_int(a, a);
        Self::lemma_mul_denom_product_int(b, b);
        Self::lemma_add_denom_product_int(aa, bb);
        Self::lemma_denom_positive(aa);
        Self::lemma_denom_positive(bb);

        assert(aa.num == a.num * a.num);
        assert(bb.num == b.num * b.num);
        assert(sum.num == aa.num * bb.denom() + bb.num * aa.denom());
        assert(sum.denom() == aa.denom() * bb.denom());

        Self::lemma_eqv_zero_iff_num_zero(sum);
        Self::lemma_eqv_zero_iff_num_zero(a);
        Self::lemma_eqv_zero_iff_num_zero(b);

        // Forward: sum ≡ 0 → a ≡ 0 ∧ b ≡ 0
        // sum.num == 0 means aa.num * bb.denom() + bb.num * aa.denom() == 0
        // Both terms are non-negative, so both must be 0.
        if sum.num == 0 {
            assert(aa.denom() > 0);
            assert(bb.denom() > 0);
            assert(a.num * a.num >= 0) by (nonlinear_arith);
            assert(b.num * b.num >= 0) by (nonlinear_arith);
            assert((aa.num >= 0 && bb.denom() > 0) ==> aa.num * bb.denom() >= 0)
                by (nonlinear_arith);
            assert((bb.num >= 0 && aa.denom() > 0) ==> bb.num * aa.denom() >= 0)
                by (nonlinear_arith);
            // Two non-negative ints summing to 0 → both 0
            assert(aa.num * bb.denom() == 0);
            assert(bb.num * aa.denom() == 0);
            // aa.num * bb.denom() == 0 with bb.denom() > 0 → aa.num == 0
            assert((aa.num * bb.denom() == 0 && bb.denom() > 0) ==> aa.num == 0)
                by (nonlinear_arith);
            assert((bb.num * aa.denom() == 0 && aa.denom() > 0) ==> bb.num == 0)
                by (nonlinear_arith);
            assert(a.num * a.num == 0);
            assert(b.num * b.num == 0);
            assert((a.num * a.num == 0) ==> a.num == 0) by (nonlinear_arith);
            assert((b.num * b.num == 0) ==> b.num == 0) by (nonlinear_arith);
        }

        // Backward: a ≡ 0 ∧ b ≡ 0 → sum ≡ 0
        if a.num == 0 && b.num == 0 {
            assert(a.num * a.num == 0) by (nonlinear_arith)
                requires a.num == 0;
            assert(aa.num == 0);
            assert(b.num * b.num == 0) by (nonlinear_arith)
                requires b.num == 0;
            assert(bb.num == 0);
            lemma_mul_by_zero_is_zero(bb.denom());
            lemma_mul_by_zero_is_zero(aa.denom());
            assert(sum.num == 0);
        }
    }

    /// 3D variant: a*a + b*b + c*c ≥ 0.
    pub proof fn lemma_sum_of_three_squares_nonneg(a: Self, b: Self, c: Self)
        ensures
            Self::from_int_spec(0).le_spec(
                a.mul_spec(a).add_spec(b.mul_spec(b)).add_spec(c.mul_spec(c))),
    {
        Self::lemma_sum_of_squares_nonneg(a, b);
        Self::lemma_square_le_nonneg(c);
        let z = Self::from_int_spec(0);
        let ab = a.mul_spec(a).add_spec(b.mul_spec(b));
        let cc = c.mul_spec(c);
        // z ≤ ab and z ≤ cc, so z ≤ ab + cc by add monotonicity
        Self::lemma_le_add_monotone(z, ab, cc);
        // z + cc ≤ ab + cc
        // We also know z ≤ cc, so z ≤ z + cc ≤ ab + cc
        // Actually, lemma_le_add_monotone gives: z ≤ ab ==> z + cc ≤ ab + cc
        // We need z ≤ z + cc first, then transitivity
        Self::lemma_add_zero_identity(z);
        // z + z ≡ z, and z ≤ cc, so z + z ≤ z + cc, hence z ≤ z + cc (via eqv)
        // Simpler: directly compute z.add_spec(cc) and show z ≤ it
        Self::lemma_denom_positive(cc);
        let zcc = z.add_spec(cc);
        Self::lemma_add_denom_product_int(z, cc);
        assert(zcc.num == z.num * cc.denom() + cc.num * z.denom());
        lemma_mul_by_zero_is_zero(cc.denom());
        assert(z.num * cc.denom() == 0);
        assert(z.denom() == 1);
        Self::lemma_mul_denom_product_int(c, c);
        assert(cc.num == c.num * c.num);
        assert(c.num * c.num >= 0) by (nonlinear_arith);
        assert((cc.num >= 0) ==> cc.num * 1 >= 0) by (nonlinear_arith);
        assert(zcc.num >= 0);
        // z ≤ zcc
        assert(zcc.denom() == z.denom() * cc.denom());
        assert(zcc.denom() == cc.denom());
        lemma_mul_by_zero_is_zero(zcc.denom());
        assert(z.num * zcc.denom() == 0);
        assert((z.denom() == 1) ==> zcc.num * z.denom() == zcc.num) by (nonlinear_arith);
        assert(z.le_spec(zcc));
        // z ≤ z + cc ≤ ab + cc
        Self::lemma_le_transitive(z, zcc, ab.add_spec(cc));
    }

    /// 3D variant: a*a + b*b + c*c ≡ 0 iff a ≡ 0 ∧ b ≡ 0 ∧ c ≡ 0.
    pub proof fn lemma_sum_of_three_squares_zero_iff(a: Self, b: Self, c: Self)
        ensures
            a.mul_spec(a).add_spec(b.mul_spec(b)).add_spec(c.mul_spec(c))
                .eqv_spec(Self::from_int_spec(0))
            == (a.eqv_spec(Self::from_int_spec(0))
                && b.eqv_spec(Self::from_int_spec(0))
                && c.eqv_spec(Self::from_int_spec(0))),
    {
        let z = Self::from_int_spec(0);
        let aa = a.mul_spec(a);
        let bb = b.mul_spec(b);
        let cc = c.mul_spec(c);
        let ab = aa.add_spec(bb);
        let sum = ab.add_spec(cc);

        Self::lemma_eqv_zero_iff_num_zero(a);
        Self::lemma_eqv_zero_iff_num_zero(b);
        Self::lemma_eqv_zero_iff_num_zero(c);
        Self::lemma_eqv_zero_iff_num_zero(sum);

        Self::lemma_mul_denom_product_int(a, a);
        Self::lemma_mul_denom_product_int(b, b);
        Self::lemma_mul_denom_product_int(c, c);
        Self::lemma_add_denom_product_int(aa, bb);
        Self::lemma_add_denom_product_int(ab, cc);
        Self::lemma_denom_positive(aa);
        Self::lemma_denom_positive(bb);
        Self::lemma_denom_positive(cc);
        Self::lemma_denom_positive(ab);

        assert(aa.num == a.num * a.num);
        assert(bb.num == b.num * b.num);
        assert(cc.num == c.num * c.num);
        assert(ab.num == aa.num * bb.denom() + bb.num * aa.denom());
        assert(sum.num == ab.num * cc.denom() + cc.num * ab.denom());

        // Forward: sum.num == 0 → a,b,c all 0
        if sum.num == 0 {
            // All terms non-negative
            assert(a.num * a.num >= 0) by (nonlinear_arith);
            assert(b.num * b.num >= 0) by (nonlinear_arith);
            assert(c.num * c.num >= 0) by (nonlinear_arith);
            assert((aa.num >= 0 && bb.denom() > 0) ==> aa.num * bb.denom() >= 0)
                by (nonlinear_arith);
            assert((bb.num >= 0 && aa.denom() > 0) ==> bb.num * aa.denom() >= 0)
                by (nonlinear_arith);
            assert(ab.num >= 0);
            assert((ab.num >= 0 && cc.denom() > 0) ==> ab.num * cc.denom() >= 0)
                by (nonlinear_arith);
            assert((cc.num >= 0 && ab.denom() > 0) ==> cc.num * ab.denom() >= 0)
                by (nonlinear_arith);
            // Two non-negative summing to 0
            assert(ab.num * cc.denom() == 0);
            assert(cc.num * ab.denom() == 0);
            assert((cc.num * ab.denom() == 0 && ab.denom() > 0) ==> cc.num == 0)
                by (nonlinear_arith);
            assert(c.num * c.num == 0);
            assert((c.num * c.num == 0) ==> c.num == 0) by (nonlinear_arith);
            assert((ab.num * cc.denom() == 0 && cc.denom() > 0) ==> ab.num == 0)
                by (nonlinear_arith);
            // ab.num == 0 → aa and bb both 0 (same argument)
            let ghost x = aa.num * bb.denom();
            let ghost y = bb.num * aa.denom();
            assert(ab.num == x + y);
            assert((x >= 0 && y >= 0 && x + y == 0) ==> (x == 0 && y == 0))
                by (nonlinear_arith);
            assert(aa.num * bb.denom() == 0);
            assert(bb.num * aa.denom() == 0);
            assert((aa.num * bb.denom() == 0 && bb.denom() > 0) ==> aa.num == 0)
                by (nonlinear_arith);
            assert((bb.num * aa.denom() == 0 && aa.denom() > 0) ==> bb.num == 0)
                by (nonlinear_arith);
            assert(a.num * a.num == 0);
            assert(b.num * b.num == 0);
            assert((a.num * a.num == 0) ==> a.num == 0) by (nonlinear_arith);
            assert((b.num * b.num == 0) ==> b.num == 0) by (nonlinear_arith);
        }

        // Backward: a,b,c all 0 → sum.num == 0
        if a.num == 0 && b.num == 0 && c.num == 0 {
            assert(a.num * a.num == 0) by (nonlinear_arith)
                requires a.num == 0;
            assert(aa.num == 0);
            assert(b.num * b.num == 0) by (nonlinear_arith)
                requires b.num == 0;
            assert(bb.num == 0);
            assert(c.num * c.num == 0) by (nonlinear_arith)
                requires c.num == 0;
            assert(cc.num == 0);
            lemma_mul_by_zero_is_zero(bb.denom());
            lemma_mul_by_zero_is_zero(aa.denom());
            assert(ab.num == 0);
            lemma_mul_by_zero_is_zero(cc.denom());
            lemma_mul_by_zero_is_zero(ab.denom());
            assert(sum.num == 0);
        }
    }

    // ── Four-component sum of squares (quaternion norm) ──────────────

    /// a² + b² + c² + d² ≥ 0.
    pub proof fn lemma_sum_of_four_squares_nonneg(a: Self, b: Self, c: Self, d: Self)
        ensures
            Self::from_int_spec(0).le_spec(
                a.mul_spec(a).add_spec(b.mul_spec(b))
                    .add_spec(c.mul_spec(c)).add_spec(d.mul_spec(d))),
    {
        let z = Self::from_int_spec(0);
        let aa = a.mul_spec(a);
        let bb = b.mul_spec(b);
        let cc = c.mul_spec(c);
        let dd = d.mul_spec(d);
        // Build left-associatively to match ensures: ((aa+bb)+cc)+dd
        let ab = aa.add_spec(bb);
        let abc = ab.add_spec(cc);
        // Step 1: 0 ≤ a²+b²
        Self::lemma_sum_of_squares_nonneg(a, b);
        // Step 2: 0 ≤ c²
        Self::lemma_square_le_nonneg(c);
        // Step 3: 0+0 ≤ (a²+b²)+c²
        Self::lemma_le_add_both(z, ab, z, cc);
        Self::lemma_add_zero_identity(z);
        Self::lemma_eqv_symmetric(z.add_spec(z), z);
        Self::lemma_eqv_implies_le(z, z.add_spec(z));
        Self::lemma_le_transitive(z, z.add_spec(z), abc);
        // Step 4: 0 ≤ d²
        Self::lemma_square_le_nonneg(d);
        // Step 5: 0+0 ≤ ((a²+b²)+c²)+d²
        Self::lemma_le_add_both(z, abc, z, dd);
        Self::lemma_le_transitive(z, z.add_spec(z), abc.add_spec(dd));
    }

    /// a² + b² + c² + d² ≡ 0 ↔ a ≡ 0 ∧ b ≡ 0 ∧ c ≡ 0 ∧ d ≡ 0.
    pub proof fn lemma_sum_of_four_squares_zero_iff(
        a: Self, b: Self, c: Self, d: Self,
    )
        ensures
            a.mul_spec(a).add_spec(b.mul_spec(b))
                .add_spec(c.mul_spec(c)).add_spec(d.mul_spec(d))
                .eqv_spec(Self::from_int_spec(0))
            == (a.eqv_spec(Self::from_int_spec(0))
                && b.eqv_spec(Self::from_int_spec(0))
                && c.eqv_spec(Self::from_int_spec(0))
                && d.eqv_spec(Self::from_int_spec(0))),
    {
        let z = Self::from_int_spec(0);
        let aa = a.mul_spec(a);
        let bb = b.mul_spec(b);
        let cc = c.mul_spec(c);
        let dd = d.mul_spec(d);
        // Left-associative to match ensures: ((aa+bb)+cc)+dd
        let s2 = aa.add_spec(bb);
        let s3 = s2.add_spec(cc);
        let sum = s3.add_spec(dd);

        Self::lemma_eqv_zero_iff_num_zero(a);
        Self::lemma_eqv_zero_iff_num_zero(b);
        Self::lemma_eqv_zero_iff_num_zero(c);
        Self::lemma_eqv_zero_iff_num_zero(d);
        Self::lemma_eqv_zero_iff_num_zero(sum);

        Self::lemma_mul_denom_product_int(a, a);
        Self::lemma_mul_denom_product_int(b, b);
        Self::lemma_mul_denom_product_int(c, c);
        Self::lemma_mul_denom_product_int(d, d);
        Self::lemma_add_denom_product_int(aa, bb);
        Self::lemma_add_denom_product_int(s2, cc);
        Self::lemma_add_denom_product_int(s3, dd);
        Self::lemma_denom_positive(aa);
        Self::lemma_denom_positive(bb);
        Self::lemma_denom_positive(cc);
        Self::lemma_denom_positive(dd);
        Self::lemma_denom_positive(s2);
        Self::lemma_denom_positive(s3);

        assert(aa.num == a.num * a.num);
        assert(bb.num == b.num * b.num);
        assert(cc.num == c.num * c.num);
        assert(dd.num == d.num * d.num);
        assert(s2.num == aa.num * bb.denom() + bb.num * aa.denom());
        assert(s3.num == s2.num * cc.denom() + cc.num * s2.denom());
        assert(sum.num == s3.num * dd.denom() + dd.num * s3.denom());

        // Forward: sum.num == 0 → all zero
        if sum.num == 0 {
            // All individual squares are non-negative
            assert(a.num * a.num >= 0) by (nonlinear_arith);
            assert(b.num * b.num >= 0) by (nonlinear_arith);
            assert(c.num * c.num >= 0) by (nonlinear_arith);
            assert(d.num * d.num >= 0) by (nonlinear_arith);
            // s2.num >= 0
            assert(aa.num * bb.denom() >= 0) by (nonlinear_arith)
                requires aa.num >= 0, bb.denom() > 0;
            assert(bb.num * aa.denom() >= 0) by (nonlinear_arith)
                requires bb.num >= 0, aa.denom() > 0;
            assert(s2.num >= 0);
            // s3.num >= 0
            assert(s2.num * cc.denom() >= 0) by (nonlinear_arith)
                requires s2.num >= 0, cc.denom() > 0;
            assert(cc.num * s2.denom() >= 0) by (nonlinear_arith)
                requires cc.num >= 0, s2.denom() > 0;
            assert(s3.num >= 0);
            // sum.num == 0 with s3.num >= 0 and dd.num >= 0
            assert(s3.num * dd.denom() >= 0) by (nonlinear_arith)
                requires s3.num >= 0, dd.denom() > 0;
            assert(dd.num * s3.denom() >= 0) by (nonlinear_arith)
                requires dd.num >= 0, s3.denom() > 0;
            // Two non-negative parts summing to 0
            let ghost p1 = s3.num * dd.denom();
            let ghost q1 = dd.num * s3.denom();
            assert(p1 + q1 == 0);
            assert(p1 == 0 && q1 == 0) by (nonlinear_arith)
                requires p1 >= 0, q1 >= 0, p1 + q1 == 0;
            assert(s3.num == 0) by (nonlinear_arith)
                requires p1 == 0, dd.denom() > 0, p1 == s3.num * dd.denom();
            assert(dd.num == 0) by (nonlinear_arith)
                requires q1 == 0, s3.denom() > 0, q1 == dd.num * s3.denom();
            assert(d.num * d.num == 0);
            assert(d.num == 0) by (nonlinear_arith) requires d.num * d.num == 0;
            // Decompose s3.num == 0 → s2.num == 0 and cc.num == 0
            let ghost p2 = s2.num * cc.denom();
            let ghost q2 = cc.num * s2.denom();
            assert(p2 + q2 == 0);
            assert(p2 == 0 && q2 == 0) by (nonlinear_arith)
                requires p2 >= 0, q2 >= 0, p2 + q2 == 0;
            assert(s2.num == 0) by (nonlinear_arith)
                requires p2 == 0, cc.denom() > 0, p2 == s2.num * cc.denom();
            assert(cc.num == 0) by (nonlinear_arith)
                requires q2 == 0, s2.denom() > 0, q2 == cc.num * s2.denom();
            assert(c.num * c.num == 0);
            assert(c.num == 0) by (nonlinear_arith) requires c.num * c.num == 0;
            // Decompose s2.num == 0 → aa.num == 0 and bb.num == 0
            let ghost p3 = aa.num * bb.denom();
            let ghost q3 = bb.num * aa.denom();
            assert(p3 + q3 == 0);
            assert(p3 == 0 && q3 == 0) by (nonlinear_arith)
                requires p3 >= 0, q3 >= 0, p3 + q3 == 0;
            assert(aa.num == 0) by (nonlinear_arith)
                requires p3 == 0, bb.denom() > 0, p3 == aa.num * bb.denom();
            assert(bb.num == 0) by (nonlinear_arith)
                requires q3 == 0, aa.denom() > 0, q3 == bb.num * aa.denom();
            assert(a.num * a.num == 0);
            assert(a.num == 0) by (nonlinear_arith) requires a.num * a.num == 0;
            assert(b.num * b.num == 0);
            assert(b.num == 0) by (nonlinear_arith) requires b.num * b.num == 0;
        }

        // Backward: all zero → sum.num == 0
        if a.num == 0 && b.num == 0 && c.num == 0 && d.num == 0 {
            assert(a.num * a.num == 0) by (nonlinear_arith) requires a.num == 0;
            assert(b.num * b.num == 0) by (nonlinear_arith) requires b.num == 0;
            assert(c.num * c.num == 0) by (nonlinear_arith) requires c.num == 0;
            assert(d.num * d.num == 0) by (nonlinear_arith) requires d.num == 0;
            lemma_mul_by_zero_is_zero(bb.denom());
            lemma_mul_by_zero_is_zero(aa.denom());
            assert(s2.num == 0);
            lemma_mul_by_zero_is_zero(cc.denom());
            lemma_mul_by_zero_is_zero(s2.denom());
            assert(s3.num == 0);
            lemma_mul_by_zero_is_zero(dd.denom());
            lemma_mul_by_zero_is_zero(s3.denom());
            assert(sum.num == 0);
        }
    }

    // ── Subtraction algebra (item 18) ─────────────────────────────────

    /// a - a ≡ 0.
    pub proof fn lemma_sub_self(a: Self)
        ensures
            a.sub_spec(a).eqv_spec(Self::from_int_spec(0)),
    {
        Self::lemma_sub_eqv_zero_iff_eqv(a, a);
        Self::lemma_eqv_reflexive(a);
    }

    /// a - (-b) == a + b (structural).
    pub proof fn lemma_sub_neg(a: Self, b: Self)
        ensures
            a.sub_spec(b.neg_spec()) == a.add_spec(b),
    {
        // sub_spec(x,y) = x.add_spec(y.neg_spec())
        // so a.sub_spec(b.neg_spec()) = a.add_spec(b.neg_spec().neg_spec())
        // and neg_involution gives b.neg_spec().neg_spec() == b
        Self::lemma_neg_involution(b);
    }

    /// -(a - b) == b - a (structural).
    pub proof fn lemma_neg_sub(a: Self, b: Self)
        ensures
            a.sub_spec(b).neg_spec() == b.sub_spec(a),
    {
        // Already proved as lemma_sub_antisymmetric with reversed direction
        Self::lemma_sub_antisymmetric(b, a);
        // b.sub_spec(a) == a.sub_spec(b).neg_spec() -- that's the wrong direction
        // lemma_sub_antisymmetric(a, b) gives a.sub_spec(b) == b.sub_spec(a).neg_spec()
        // We need: a.sub_spec(b).neg_spec() == b.sub_spec(a)
        // From antisymmetric: a - b == -(b - a), so -(a-b) == --(b-a) == b-a
        Self::lemma_sub_antisymmetric(a, b);
        // a.sub_spec(b) == b.sub_spec(a).neg_spec()
        // so a.sub_spec(b).neg_spec() == b.sub_spec(a).neg_spec().neg_spec()
        Self::lemma_neg_involution(b.sub_spec(a));
        // b.sub_spec(a).neg_spec().neg_spec() == b.sub_spec(a)
    }

    // ── Algebraic identities (item 17) ────────────────────────────────

    /// x + x ≡ 2 * x.
    pub proof fn lemma_double(x: Self)
        ensures
            x.add_spec(x).eqv_spec(Self::from_int_spec(2).mul_spec(x)),
    {
        let xx = x.add_spec(x);
        let two_x = Self::from_int_spec(2).mul_spec(x);
        Self::lemma_denom_positive(x);
        Self::lemma_add_denom_product_int(x, x);
        Self::lemma_mul_denom_product_int(Self::from_int_spec(2), x);
        // xx.num = x.num * x.denom() + x.num * x.denom() = 2 * x.num * x.denom()
        // xx.denom() = x.denom() * x.denom()
        // two_x.num = 2 * x.num, two_x.denom() = 1 * x.denom() = x.denom()
        assert(Self::from_int_spec(2).num == 2);
        assert(Self::from_int_spec(2).denom() == 1);
        assert(two_x.num == 2 * x.num);
        assert(two_x.denom() == x.denom());
        assert(xx.num == x.num * x.denom() + x.num * x.denom());
        assert(xx.denom() == x.denom() * x.denom());
        // eqv: xx.num * two_x.denom() == two_x.num * xx.denom()
        // (2 * x.num * x.denom()) * x.denom() == (2 * x.num) * (x.denom() * x.denom())
        assert(xx.num * two_x.denom() == two_x.num * xx.denom()) by (nonlinear_arith)
            requires
                xx.num == x.num * x.denom() + x.num * x.denom(),
                xx.denom() == x.denom() * x.denom(),
                two_x.num == 2 * x.num,
                two_x.denom() == x.denom();
    }

    /// (a+b)² ≡ a² + 2ab + b².
    pub proof fn lemma_square_of_sum(a: Self, b: Self)
        ensures
            a.add_spec(b).mul_spec(a.add_spec(b)).eqv_spec(
                a.mul_spec(a).add_spec(
                    Self::from_int_spec(2).mul_spec(a.mul_spec(b))
                ).add_spec(b.mul_spec(b))),
    {
        let s = a.add_spec(b);
        let lhs = s.mul_spec(s);
        let aa = a.mul_spec(a);
        let ab = a.mul_spec(b);
        let bb = b.mul_spec(b);
        let two = Self::from_int_spec(2);
        let two_ab = two.mul_spec(ab);

        // (a+b)*(a+b) ≡ (a+b)*a + (a+b)*b
        Self::lemma_eqv_mul_distributive_left(s, a, b);
        // s*a ≡ a*a + b*a
        Self::lemma_eqv_mul_distributive_right(a, b, a);
        // s*b ≡ a*b + b*b
        Self::lemma_eqv_mul_distributive_right(a, b, b);
        // So lhs ≡ (aa + ba) + (ab + bb)
        let ba = b.mul_spec(a);
        Self::lemma_mul_commutative(b, a);
        assert(ba == ab);
        // lhs ≡ (aa + ab) + (ab + bb)
        // Need: (aa + ab) + (ab + bb) ≡ aa + 2ab + bb
        // i.e. (aa + ab) + (ab + bb) ≡ (aa + 2ab) + bb
        // Use associativity: (aa + ab) + (ab + bb) ≡ aa + (ab + (ab + bb))
        Self::lemma_add_associative(aa, ab, ab.add_spec(bb));
        // ab + (ab + bb) ≡ (ab + ab) + bb
        Self::lemma_add_associative(ab, ab, bb);
        Self::lemma_eqv_symmetric(ab.add_spec(ab).add_spec(bb), ab.add_spec(ab.add_spec(bb)));
        // ab + ab ≡ 2*ab
        Self::lemma_double(ab);
        // Chain: (ab + ab) + bb ≡ 2ab + bb
        Self::lemma_eqv_add_congruence_left(ab.add_spec(ab), two_ab, bb);
        // So ab + (ab + bb) ≡ 2ab + bb
        Self::lemma_eqv_transitive(
            ab.add_spec(ab.add_spec(bb)),
            ab.add_spec(ab).add_spec(bb),
            two_ab.add_spec(bb),
        );
        // aa + (ab + (ab + bb)) ≡ aa + (2ab + bb)
        Self::lemma_eqv_add_congruence_right(
            aa,
            ab.add_spec(ab.add_spec(bb)),
            two_ab.add_spec(bb),
        );
        // aa + (2ab + bb) ≡ (aa + 2ab) + bb
        Self::lemma_add_associative(aa, two_ab, bb);
        // Chain: lhs ≡ s*a + s*b ≡ (aa+ab) + (ab+bb)
        Self::lemma_eqv_add_congruence(
            s.mul_spec(a), aa.add_spec(ab),
            s.mul_spec(b), ab.add_spec(bb),
        );
        Self::lemma_eqv_transitive(lhs, s.mul_spec(a).add_spec(s.mul_spec(b)),
            aa.add_spec(ab).add_spec(ab.add_spec(bb)));
        // ≡ aa + (ab + (ab + bb))
        Self::lemma_eqv_transitive(lhs, aa.add_spec(ab).add_spec(ab.add_spec(bb)),
            aa.add_spec(ab.add_spec(ab.add_spec(bb))));
        // ≡ aa + (2ab + bb)
        Self::lemma_eqv_transitive(lhs,
            aa.add_spec(ab.add_spec(ab.add_spec(bb))),
            aa.add_spec(two_ab.add_spec(bb)));
        // ≡ (aa + 2ab) + bb
        Self::lemma_eqv_transitive(lhs,
            aa.add_spec(two_ab.add_spec(bb)),
            aa.add_spec(two_ab).add_spec(bb));
    }

    /// (a-b)² ≡ a² - 2ab + b².
    pub proof fn lemma_square_of_difference(a: Self, b: Self)
        ensures
            a.sub_spec(b).mul_spec(a.sub_spec(b)).eqv_spec(
                a.mul_spec(a).sub_spec(
                    Self::from_int_spec(2).mul_spec(a.mul_spec(b))
                ).add_spec(b.mul_spec(b))),
    {
        // (a - b) = a + (-b), so (a-b)² = (a+(-b))²
        let nb = b.neg_spec();
        // Apply square_of_sum to a, -b:
        // (a+(-b))² ≡ a² + 2*a*(-b) + (-b)²
        Self::lemma_square_of_sum(a, nb);
        // Now relate terms:
        // a*(-b) == -(a*b): num differs by a.num*(-b.num) vs -(a.num*b.num)
        assert(a.num * (-b.num) == -(a.num * b.num)) by (nonlinear_arith);
        assert(a.mul_spec(nb) == a.mul_spec(b).neg_spec());
        // nb*nb == b*b
        assert(nb.mul_spec(nb).num == b.num * b.num) by (nonlinear_arith)
            requires nb.num == -b.num;
        assert(nb.mul_spec(nb).den == b.mul_spec(b).den);
        assert(nb.mul_spec(nb) == b.mul_spec(b));
        // 2*a*(-b) = 2*(-(a*b)) = -(2*(a*b))
        let ab = a.mul_spec(b);
        let nab = ab.neg_spec();
        let two = Self::from_int_spec(2);
        Self::lemma_mul_neg_right(two, ab);
        assert(two.mul_spec(nab) == two.mul_spec(ab).neg_spec());
        // So a² + 2*a*nb + nb² ≡ a² + (-(2ab)) + b²
        //                       ≡ a² - 2ab + b²
        // a² - 2ab = a².add_spec((2ab).neg_spec()) = a².sub_spec(2ab)? No:
        // sub_spec(x,y) = x.add_spec(y.neg_spec())
        // a².sub_spec(2ab) = a².add_spec((2ab).neg_spec()) = a².add_spec(-(2ab))
        let aa = a.mul_spec(a);
        let two_ab = two.mul_spec(ab);
        let two_nab = two.mul_spec(nab);
        // two_nab == two_ab.neg_spec() (shown above)
        // So aa.add_spec(two_nab) == aa.add_spec(two_ab.neg_spec()) == aa.sub_spec(two_ab)
        assert(aa.add_spec(two_nab) == aa.sub_spec(two_ab));
        // The ensures of square_of_sum gives:
        // s.mul_spec(s) ≡ aa.add_spec(two.mul_spec(a.mul_spec(nb))).add_spec(nb.mul_spec(nb))
        // = aa.add_spec(two_nab).add_spec(b.mul_spec(b))
        // = aa.sub_spec(two_ab).add_spec(bb) ✓
    }

    /// a² - b² ≡ (a+b)(a-b).
    pub proof fn lemma_difference_of_squares(a: Self, b: Self)
        ensures
            a.mul_spec(a).sub_spec(b.mul_spec(b)).eqv_spec(
                a.add_spec(b).mul_spec(a.sub_spec(b))),
    {
        // (a+b)(a-b) = (a+b)(a+(-b))
        // Use distributive: (a+b)*(a+(-b)) ≡ (a+b)*a + (a+b)*(-b)
        let s = a.add_spec(b);
        let d = a.sub_spec(b); // = a.add_spec(b.neg_spec())
        let nb = b.neg_spec();
        let rhs = s.mul_spec(d);
        let aa = a.mul_spec(a);
        let bb = b.mul_spec(b);
        let lhs = aa.sub_spec(bb);

        // (a+b)*(a+(-b)) ≡ (a+b)*a + (a+b)*(-b)
        Self::lemma_eqv_mul_distributive_left(s, a, nb);
        // (a+b)*a ≡ a*a + b*a
        Self::lemma_eqv_mul_distributive_right(a, b, a);
        // (a+b)*(-b) ≡ a*(-b) + b*(-b)
        Self::lemma_eqv_mul_distributive_right(a, b, nb);

        let ba = b.mul_spec(a);
        let anb = a.mul_spec(nb);
        let bnb = b.mul_spec(nb);

        Self::lemma_mul_commutative(b, a);
        assert(ba == a.mul_spec(b));
        let ab = a.mul_spec(b);

        // a*(-b) == -(a*b): num a.num*(-b.num) vs -(a.num*b.num)
        assert(a.num * (-b.num) == -(a.num * b.num)) by (nonlinear_arith);
        assert(anb == ab.neg_spec());
        // b*(-b): num = b.num * (-b.num), same den as b*b
        // -(b*b): num = -(b.num * b.num) = b.num * (-b.num) by nonlinear_arith
        assert(b.num * (-b.num) == -(b.num * b.num)) by (nonlinear_arith);
        assert(bnb == bb.neg_spec());

        // So rhs ≡ (aa + ab) + (-(ab) + -(bb))
        //        ≡ (aa + ab) + (-(ab + bb))  by neg_add
        Self::lemma_neg_add(ab, bb);
        assert(ab.neg_spec().add_spec(bb.neg_spec()) == ab.add_spec(bb).neg_spec());
        // (aa + ab) + (-(ab + bb))
        // = (aa + ab).sub_spec(ab + bb)? No, it's add with neg.
        // = (aa + ab).add_spec((ab + bb).neg_spec())
        // = (aa + ab).sub_spec(ab.add_spec(bb))
        // Need to show this ≡ aa - bb.

        // aa + ab - (ab + bb):
        // Use sub_add_distributes or work step by step:
        // (aa + ab) + (-(ab) + -(bb))
        // ≡ aa + (ab + (-(ab) + -(bb)))  by add_assoc
        Self::lemma_add_associative(aa, ab, ab.neg_spec().add_spec(bb.neg_spec()));
        // ab + (-(ab) + -(bb)) ≡ (ab + -(ab)) + -(bb)  by add_assoc
        Self::lemma_add_associative(ab, ab.neg_spec(), bb.neg_spec());
        Self::lemma_eqv_symmetric(
            ab.add_spec(ab.neg_spec()).add_spec(bb.neg_spec()),
            ab.add_spec(ab.neg_spec().add_spec(bb.neg_spec())),
        );
        // ab + -(ab) ≡ 0
        Self::lemma_sub_self(ab);
        // Note: ab.add_spec(ab.neg_spec()) == ab.sub_spec(ab) structurally
        // ab + -(ab) + -(bb) ≡ 0 + -(bb)
        Self::lemma_eqv_add_congruence_left(
            ab.add_spec(ab.neg_spec()),
            Self::from_int_spec(0),
            bb.neg_spec(),
        );
        // 0 + -(bb) == -(bb)  structurally
        Self::lemma_add_zero_identity(bb.neg_spec());
        // So ab + (-(ab) + -(bb)) ≡ -(bb)
        Self::lemma_eqv_transitive(
            ab.add_spec(ab.neg_spec().add_spec(bb.neg_spec())),
            ab.add_spec(ab.neg_spec()).add_spec(bb.neg_spec()),
            Self::from_int_spec(0).add_spec(bb.neg_spec()),
        );
        // aa + (ab + (-(ab) + -(bb))) ≡ aa + -(bb)
        Self::lemma_eqv_add_congruence_right(
            aa,
            ab.add_spec(ab.neg_spec().add_spec(bb.neg_spec())),
            bb.neg_spec(),
        );
        // aa + -(bb) == aa.sub_spec(bb) structurally
        assert(aa.add_spec(bb.neg_spec()) == aa.sub_spec(bb));
        // Chain everything for rhs:
        // rhs ≡ s*a + s*nb
        Self::lemma_eqv_add_congruence(
            s.mul_spec(a), aa.add_spec(ab),
            s.mul_spec(nb), anb.add_spec(bnb),
        );
        // = (aa + ab) + (-(ab) + -(bb))
        // ≡ aa + (ab + (-(ab) + -(bb)))
        Self::lemma_eqv_transitive(
            rhs,
            s.mul_spec(a).add_spec(s.mul_spec(nb)),
            aa.add_spec(ab).add_spec(anb.add_spec(bnb)),
        );
        Self::lemma_eqv_transitive(
            rhs,
            aa.add_spec(ab).add_spec(anb.add_spec(bnb)),
            aa.add_spec(ab.add_spec(anb.add_spec(bnb))),
        );
        Self::lemma_eqv_transitive(
            rhs,
            aa.add_spec(ab.add_spec(anb.add_spec(bnb))),
            aa.add_spec(bb.neg_spec()),
        );
        // rhs ≡ lhs
        Self::lemma_eqv_symmetric(rhs, lhs);
    }

    // ── 2×2 determinant & Cramer's rule (item 20) ────────────────────

    /// det2(a, b, c, d) = a*d - b*c.
    pub open spec fn det2_spec(a: Self, b: Self, c: Self, d: Self) -> Self {
        a.mul_spec(d).sub_spec(b.mul_spec(c))
    }

    /// Swapping rows negates the determinant.
    pub proof fn lemma_det2_antisymmetric(a: Self, b: Self, c: Self, d: Self)
        ensures
            Self::det2_spec(c, d, a, b).eqv_spec(
                Self::det2_spec(a, b, c, d).neg_spec()),
    {
        // det2(c,d,a,b) = c*b - d*a
        // det2(a,b,c,d) = a*d - b*c
        // -(a*d - b*c) = b*c - a*d
        // Need: c*b - d*a ≡ b*c - a*d
        let cb = c.mul_spec(b);
        let da = d.mul_spec(a);
        let ad = a.mul_spec(d);
        let bc = b.mul_spec(c);
        Self::lemma_mul_commutative(c, b);
        assert(cb == bc);
        Self::lemma_mul_commutative(d, a);
        assert(da == ad);
        // det2(c,d,a,b) = cb - da = bc - ad
        // -(det2(a,b,c,d)) = -(ad - bc) = bc - ad  by neg_sub
        Self::lemma_neg_sub(ad, bc);
        // ad.sub_spec(bc).neg_spec() == bc.sub_spec(ad)
        Self::lemma_eqv_reflexive(bc.sub_spec(ad));
    }

    /// det2 ≡ 0 ↔ a*d ≡ b*c (collinearity).
    pub proof fn lemma_det2_zero_iff_proportional(a: Self, b: Self, c: Self, d: Self)
        ensures
            Self::det2_spec(a, b, c, d).eqv_spec(Self::from_int_spec(0))
            == a.mul_spec(d).eqv_spec(b.mul_spec(c)),
    {
        Self::lemma_sub_eqv_zero_iff_eqv(a.mul_spec(d), b.mul_spec(c));
    }

    /// Cramer's rule: when det ≢ 0, the solution
    /// x = (d*e - b*f)/det, y = (a*f - c*e)/det
    /// satisfies a*x + b*y ≡ e and c*x + d*y ≡ f.
    pub proof fn lemma_cramer2_satisfies(
        a: Self, b: Self, c: Self, d: Self, e: Self, f: Self,
    )
        requires
            !Self::det2_spec(a, b, c, d).eqv_spec(Self::from_int_spec(0)),
        ensures ({
            let det = Self::det2_spec(a, b, c, d);
            let x = d.mul_spec(e).sub_spec(b.mul_spec(f)).div_spec(det);
            let y = a.mul_spec(f).sub_spec(c.mul_spec(e)).div_spec(det);
            a.mul_spec(x).add_spec(b.mul_spec(y)).eqv_spec(e)
            && c.mul_spec(x).add_spec(d.mul_spec(y)).eqv_spec(f)
        }),
    {
        let det = Self::det2_spec(a, b, c, d);
        let num_x = d.mul_spec(e).sub_spec(b.mul_spec(f));
        let num_y = a.mul_spec(f).sub_spec(c.mul_spec(e));
        let x = num_x.div_spec(det);
        let y = num_y.div_spec(det);

        Self::lemma_eqv_zero_iff_num_zero(det);

        // x = num_x / det, so det * x ≡ num_x
        Self::lemma_div_cancel(det, num_x);
        // det * x ≡ num_x = d*e - b*f

        // y = num_y / det, so det * y ≡ num_y
        Self::lemma_div_cancel(det, num_y);
        // det * y ≡ num_y = a*f - c*e

        // We need: a*x + b*y ≡ e
        // Multiply both sides by det: det*(a*x + b*y) ≡ det*e
        // det*(a*x + b*y) ≡ det*a*x + det*b*y
        //                  ≡ a*(det*x) + b*(det*y)
        //                  ≡ a*num_x + b*num_y
        //                  = a*(d*e - b*f) + b*(a*f - c*e)
        //                  = a*d*e - a*b*f + a*b*f - b*c*e
        //                  = a*d*e - b*c*e
        //                  = (a*d - b*c)*e
        //                  = det * e
        // So det*(a*x + b*y) ≡ det*e, cancel det to get a*x + b*y ≡ e.

        // a*x: a * (num_x / det) = a * (num_x * inv_det)
        //    ≡ (a * num_x) / det  by div_mul_assoc (reversed)
        Self::lemma_div_mul_assoc(num_x, det, a);
        Self::lemma_mul_commutative(x, a);
        // x * a = a * x structurally... no, x = num_x.div_spec(det) = num_x.mul_spec(inv)
        // a.mul_spec(x) vs num_x.div_spec(det).mul_spec(a)... hmm

        // Let me use a different approach: show det * (a*x + b*y) ≡ det * e
        // then cancel.

        // det * (a*x + b*y) ≡ det*a*x + det*b*y  by distributive
        let ax = a.mul_spec(x);
        let by_ = b.mul_spec(y);
        let sum = ax.add_spec(by_);
        Self::lemma_eqv_mul_distributive_left(det, ax, by_);
        // det*ax ≡ a*(det*x) by commut+assoc
        Self::lemma_mul_commutative(det, ax);
        Self::lemma_mul_commutative(det, a);
        // det*a = a*det structurally. det*ax = ax*det = (a*x)*det
        // (a*x)*det ≡ a*(x*det) by assoc
        Self::lemma_mul_associative(a, x, det);
        Self::lemma_mul_commutative(x, det);
        // x*det == det*x structurally
        // a*(x*det) = a*(det*x) structurally
        // det*x ≡ num_x (from div_cancel: det * (num_x/det) ≡ num_x)
        // So a*(det*x) ≡ a*num_x
        Self::lemma_eqv_mul_congruence_right(
            a, det.mul_spec(x), num_x,
        );
        // Chain: det*ax = ax*det ≡ a*(x*det) = a*(det*x) ≡ a*num_x
        assert(ax.mul_spec(det) == det.mul_spec(ax));
        Self::lemma_eqv_transitive(
            det.mul_spec(ax),
            a.mul_spec(x.mul_spec(det)),
            a.mul_spec(num_x),
        );

        // Similarly for det*by ≡ b*num_y
        Self::lemma_mul_associative(b, y, det);
        Self::lemma_mul_commutative(y, det);
        Self::lemma_eqv_mul_congruence_right(
            b, det.mul_spec(y), num_y,
        );
        assert(by_.mul_spec(det) == det.mul_spec(by_));
        Self::lemma_eqv_transitive(
            det.mul_spec(by_),
            b.mul_spec(y.mul_spec(det)),
            b.mul_spec(num_y),
        );

        // det*(ax+by) ≡ det*ax + det*by ≡ a*num_x + b*num_y
        Self::lemma_eqv_add_congruence(
            det.mul_spec(ax), a.mul_spec(num_x),
            det.mul_spec(by_), b.mul_spec(num_y),
        );
        Self::lemma_eqv_transitive(
            det.mul_spec(sum),
            det.mul_spec(ax).add_spec(det.mul_spec(by_)),
            a.mul_spec(num_x).add_spec(b.mul_spec(num_y)),
        );

        // a*num_x + b*num_y = a*(d*e - b*f) + b*(a*f - c*e)
        // Expand a*(d*e - b*f):
        Self::lemma_sub_mul_right(d.mul_spec(e), b.mul_spec(f), a);
        // = a*d*e - a*b*f  (eqv)
        // Expand b*(a*f - c*e):
        Self::lemma_sub_mul_right(a.mul_spec(f), c.mul_spec(e), b);
        // = b*a*f - b*c*e  (eqv)

        // Strategy: show det*(ax+by) ≡ a*num_x + b*num_y ≡ det*e, then cancel det.
        // a * num_x = num_x * a (by commut)
        Self::lemma_mul_commutative(a, num_x);
        // num_x * a ≡ de*a - bf*a (by sub_mul_right)
        let de = d.mul_spec(e);
        let bf = b.mul_spec(f);
        // sub_mul_right(de, bf, a): (de - bf) * a ≡ de*a - bf*a
        // But we also need: de*a ≡ a*d*e etc. This telescopes into many assoc/commut steps.

        // This proof is getting extremely long. Let me use a much simpler approach:
        // prove it directly at the numerator/denominator cross-multiplication level.
        // This avoids all the algebraic manipulation.

        // SIMPLIFIED APPROACH: prove eqv directly via cross-multiplication.
        // For a*x + b*y ≡ e, we check:
        // (a*x + b*y).num * e.denom() == e.num * (a*x + b*y).denom()
        // This is tedious but mechanical and avoids the algebraic chain.

        // Even simpler: just use the fact that det*(a*x + b*y) ≡ det*e,
        // where det*e = (ad-bc)*e.
        // Since we've shown det*(ax+by) ≡ a*num_x + b*num_y above,
        // we need a*num_x + b*num_y ≡ det*e.
        // This is an algebraic identity that we can verify at the num level.

        // Actually the cleanest: note that a*(de-bf) + b*(af-ce) = ade-abf+baf-bce = ade-bce = (ad-bc)e = det*e.
        // All these are eqv (not ==), so we need the chain.

        // Let me try yet another approach: prove it for the FIRST equation only using a helper,
        // and note the second is symmetric.

        // FINAL APPROACH: Use the identity directly.
        // We want: a*x + b*y ≡ e where x = num_x/det, y = num_y/det.
        // Equivalently: (a*num_x + b*num_y)/det ≡ e.
        // (a*num_x + b*num_y) = a*(de-bf) + b*(af-ce)
        // We'll prove a*(de-bf) + b*(af-ce) ≡ det*e
        // then use div_cancel to conclude (det*e)/det ≡ e.

        // Let me use div_add_numerator: (a*num_x + b*num_y)/det = a*num_x/det + b*num_y/det
        Self::lemma_div_add_numerator(a.mul_spec(num_x), b.mul_spec(num_y), det);
        // a*num_x/det ≡ a*(num_x/det) = a*x  by div_mul_assoc
        Self::lemma_div_mul_assoc(num_x, det, a);
        // (num_x/det)*a ≡ (num_x*a)/det
        Self::lemma_mul_commutative(x, a);
        // a*x = x*a = (num_x*inv)*a, and (num_x/det)*a = x*a structurally
        // Similarly: b*num_y/det ≡ b*y by div_mul_assoc
        Self::lemma_div_mul_assoc(num_y, det, b);
        Self::lemma_mul_commutative(y, b);

        // So (a*num_x + b*num_y)/det ≡ a*x + b*y
        // And if a*num_x + b*num_y ≡ det*e, then (det*e)/det ≡ e by div_mul_cancel
        Self::lemma_div_mul_cancel(e, det);
        // (e*det)/det ≡ e
        Self::lemma_mul_commutative(e, det);
        // e*det = det*e structurally

        // Now prove: a*num_x + b*num_y ≡ det*e
        // a*(de-bf) + b*(af-ce) ≡ (ad-bc)*e
        // Expand using sub_mul_right:
        // (de-bf)*a ≡ de*a - bf*a
        Self::lemma_sub_mul_right(de, bf, a);
        // (af-ce)*b ≡ af*b - ce*b
        let af = a.mul_spec(f);
        let ce = c.mul_spec(e);
        Self::lemma_sub_mul_right(af, ce, b);

        // Now: num_x*a + num_y*b ≡ (de*a - bf*a) + (af*b - ce*b)
        // We need a*num_x + b*num_y, but by commut:
        assert(a.mul_spec(num_x) == num_x.mul_spec(a));
        assert(b.mul_spec(num_y) == num_y.mul_spec(b));
        Self::lemma_eqv_add_congruence(
            num_x.mul_spec(a), de.mul_spec(a).sub_spec(bf.mul_spec(a)),
            num_y.mul_spec(b), af.mul_spec(b).sub_spec(ce.mul_spec(b)),
        );
        // = (de*a - bf*a) + (af*b - ce*b)
        // Use sub_add_distributes: (X-Y) + (Z-W) ≡ (X+Z) - (Y+W)... wait that's not right.
        // Actually sub_add_distributes is: (a+b) - (c+d) ≡ (a-c) + (b-d)
        // We need: (de*a - bf*a) + (af*b - ce*b)
        // ≡ (de*a + af*b) - (bf*a + ce*b)  ... need to prove this

        // This is getting extremely long. Let me take a completely different tack and
        // prove it at the raw numerator level with nonlinear_arith.

        // Actually, for a complex theorem like Cramer's rule, the most reliable approach
        // in Verus is to unfold everything to numerators and use nonlinear_arith.
        // Let me abandon the algebraic approach and do this directly.

        // I'll assert the final result and let the SMT solver handle it with enough hints.
        // The key insight: a*x + b*y ≡ e means
        // (a*x + b*y).num * e.denom() == e.num * (a*x + b*y).denom()

        // But even this would be incredibly complex at the numerator level because of
        // the chain of additions and multiplications.

        // PRAGMATIC APPROACH: Accept that Cramer's rule is too complex for a single proof
        // and instead just prove the identity a*(de-bf) + b*(af-ce) ≡ (ad-bc)*e
        // using the sub_add_distributes + cancellation lemmas we already have.

        // Actually I realize I'm overcomplicating this. Let me use:
        // 1. det * (a*x + b*y) ≡ a*(det*x) + b*(det*y) ≡ a*num_x + b*num_y
        // 2. a*num_x + b*num_y ≡ det*e (algebraic identity)
        // 3. So det*(a*x + b*y) ≡ det*e, cancel det.

        // For step 2, use sub_mul_right and cancellation.
        // I've already started this. Let me continue more carefully.

        // After sub_mul_right:
        // num_x*a ≡ de*a - bf*a
        // num_y*b ≡ af*b - ce*b
        // We need their sum ≡ det*e

        // de*a = d*e*a, bf*a = b*f*a, af*b = a*f*b, ce*b = c*e*b
        // By mul commutative/associative:
        // de*a ≡ a*d*e = (a*d)*e ≡ ad*e  (where ad = a*d = a.mul_spec(d))
        // bf*a ≡ a*b*f   ... hmm not bf*a but b*f then *a

        // I think the cleanest approach for Cramer's is to defer to a numerator-level proof.
        // But that would be enormous. Let me try a simpler ensures instead:
        // just verify it as an opaque identity. Actually no, I want it verified.

        // OK let me commit to the algebraic approach step by step.

        // I proved: det*(ax+by) ≡ a*num_x + b*num_y
        //                        = a*(de-bf) + b*(af-ce)
        // Need: ≡ det*e = (ad-bc)*e

        // a*(de-bf) + b*(af-ce)
        // Expand using sub_mul_right (already called):
        // ≡ (de*a - bf*a) + (af*b - ce*b)

        // Now use commutative to rewrite:
        // de*a: (d*e)*a ≡ d*(e*a) by assoc, e*a = a*e by commut, so d*(a*e) ≡ (d*a)*e by assoc back
        //       d*a = a*d by commut. So de*a ≡ ad*e.
        // bf*a: (b*f)*a ≡ b*(f*a) by assoc, f*a = a*f by commut, so b*(a*f) ≡ (b*a)*f = (a*b)*f by commut
        //       So bf*a ≡ ab*f = a*b*f. Hmm we need bf*a ≡ af*b? Let me check:
        //       bf*a = b*f*a, af*b = a*f*b. By commut: b*f*a = a*b*f (via commut+assoc), a*f*b = a*b*f similarly.
        //       So bf*a ≡ af*b.
        // af*b: same
        // ce*b: (c*e)*b ≡ c*(e*b) = c*(b*e) ≡ (c*b)*e = (b*c)*e by commut

        // So: (ad*e - af*b) + (af*b - bc*e)
        //   = ad*e - af*b + af*b - bc*e
        //   ≡ ad*e - bc*e  (after af*b cancels)
        //   ≡ (ad - bc)*e  by sub_mul_right backward
        //   = det*e  ✓

        // This requires showing bf*a ≡ af*b and the cancellation.
        // Since this is extremely involved, let me break it down:

        // Step A: de*a ≡ ad*e
        let ad = a.mul_spec(d);
        let bc_ = b.mul_spec(c);
        Self::lemma_mul_associative(d, e, a);
        // de*a ≡ d*(e*a)
        Self::lemma_mul_commutative(e, a);
        // e*a == a*e structurally
        // d*(a*e) ≡ (d*a)*e by assoc backward
        Self::lemma_mul_associative(d, a, e);
        Self::lemma_eqv_symmetric(d.mul_spec(a).mul_spec(e), d.mul_spec(a.mul_spec(e)));
        Self::lemma_mul_commutative(d, a);
        assert(d.mul_spec(a) == ad);
        // de*a ≡ d*(e*a) = d*(a*e) ≡ (d*a)*e = ad*e
        Self::lemma_eqv_transitive(
            de.mul_spec(a), d.mul_spec(e.mul_spec(a)), d.mul_spec(a.mul_spec(e)),
        );
        Self::lemma_eqv_transitive(
            de.mul_spec(a), d.mul_spec(a.mul_spec(e)), ad.mul_spec(e),
        );

        // Step B: bf*a ≡ af*b (these cancel)
        // bf*a = (b*f)*a ≡ b*(f*a) by assoc
        Self::lemma_mul_associative(b, f, a);
        // f*a == a*f structurally by commut
        Self::lemma_mul_commutative(f, a);
        // So b*(f*a) == b*(a*f) structurally, i.e. bf*a ≡ b*(a*f)
        // b*(a*f) ≡ (b*a)*f by assoc (backward)
        Self::lemma_mul_associative(b, a, f);
        Self::lemma_eqv_symmetric(b.mul_spec(a).mul_spec(f), b.mul_spec(a.mul_spec(f)));
        // Chain: bf*a ≡ b*(a*f) ≡ (b*a)*f
        Self::lemma_eqv_transitive(
            bf.mul_spec(a), b.mul_spec(a.mul_spec(f)), b.mul_spec(a).mul_spec(f),
        );
        // af*b = (a*f)*b ≡ a*(f*b) by assoc
        Self::lemma_mul_associative(a, f, b);
        // f*b == b*f structurally by commut
        Self::lemma_mul_commutative(f, b);
        // a*(f*b) == a*(b*f) structurally
        // a*(b*f) ≡ (a*b)*f by assoc (backward)
        Self::lemma_mul_associative(a, b, f);
        Self::lemma_eqv_symmetric(a.mul_spec(b).mul_spec(f), a.mul_spec(b.mul_spec(f)));
        // Chain: af*b ≡ a*(b*f) ≡ (a*b)*f
        Self::lemma_eqv_transitive(
            af.mul_spec(b), a.mul_spec(b.mul_spec(f)), a.mul_spec(b).mul_spec(f),
        );
        // (b*a)*f == (a*b)*f since b*a == a*b structurally
        Self::lemma_mul_commutative(b, a);
        assert(b.mul_spec(a) == a.mul_spec(b));
        // bf*a ≡ (a*b)*f and af*b ≡ (a*b)*f, so bf*a ≡ af*b
        Self::lemma_eqv_symmetric(af.mul_spec(b), a.mul_spec(b).mul_spec(f));
        Self::lemma_eqv_transitive(bf.mul_spec(a), a.mul_spec(b).mul_spec(f), af.mul_spec(b));

        // Step C: ce*b ≡ bc*e
        Self::lemma_mul_associative(c, e, b);
        Self::lemma_mul_commutative(e, b);
        Self::lemma_mul_associative(c, b, e);
        Self::lemma_eqv_symmetric(c.mul_spec(b).mul_spec(e), c.mul_spec(b.mul_spec(e)));
        Self::lemma_mul_commutative(c, b);
        assert(c.mul_spec(b) == bc_);
        Self::lemma_eqv_transitive(
            ce.mul_spec(b), c.mul_spec(e.mul_spec(b)), c.mul_spec(b.mul_spec(e)),
        );
        Self::lemma_eqv_transitive(
            ce.mul_spec(b), c.mul_spec(b.mul_spec(e)), bc_.mul_spec(e),
        );

        // Step D: (de*a - bf*a) + (af*b - ce*b) ≡ (ad*e - af*b) + (af*b - bc*e)
        // de*a ≡ ad*e, bf*a ≡ af*b → de*a - bf*a ≡ ad*e - af*b
        Self::lemma_eqv_sub_congruence(de.mul_spec(a), ad.mul_spec(e), bf.mul_spec(a), af.mul_spec(b));
        // af*b ≡ af*b (refl), ce*b ≡ bc*e → af*b - ce*b ≡ af*b - bc*e
        Self::lemma_eqv_reflexive(af.mul_spec(b));
        Self::lemma_eqv_sub_congruence(af.mul_spec(b), af.mul_spec(b), ce.mul_spec(b), bc_.mul_spec(e));
        // Sum: ≡ (ad*e - af*b) + (af*b - bc*e)
        Self::lemma_eqv_add_congruence(
            de.mul_spec(a).sub_spec(bf.mul_spec(a)),
            ad.mul_spec(e).sub_spec(af.mul_spec(b)),
            af.mul_spec(b).sub_spec(ce.mul_spec(b)),
            af.mul_spec(b).sub_spec(bc_.mul_spec(e)),
        );

        // Step E: (ad*e - af*b) + (af*b - bc*e) ≡ ad*e - bc*e
        // This is X - Y + Y - Z ≡ X - Z
        // Use: (X-Y)+(Y-Z) ≡ X-Z by eqv_sub_chain
        Self::lemma_eqv_sub_chain(ad.mul_spec(e), af.mul_spec(b), bc_.mul_spec(e));

        // Step F: ad*e - bc*e ≡ (ad - bc)*e = det*e
        // (ad - bc)*e ≡ ad*e - bc*e  by sub_mul_right
        Self::lemma_sub_mul_right(ad, bc_, e);
        Self::lemma_eqv_symmetric(ad.mul_spec(e).sub_spec(bc_.mul_spec(e)), det.mul_spec(e));

        // Combine D+E+F: (de*a - bf*a) + (af*b - ce*b) ≡ det*e
        Self::lemma_eqv_transitive(
            de.mul_spec(a).sub_spec(bf.mul_spec(a)).add_spec(
                af.mul_spec(b).sub_spec(ce.mul_spec(b))),
            ad.mul_spec(e).sub_spec(af.mul_spec(b)).add_spec(
                af.mul_spec(b).sub_spec(bc_.mul_spec(e))),
            ad.mul_spec(e).sub_spec(bc_.mul_spec(e)),
        );
        Self::lemma_eqv_transitive(
            de.mul_spec(a).sub_spec(bf.mul_spec(a)).add_spec(
                af.mul_spec(b).sub_spec(ce.mul_spec(b))),
            ad.mul_spec(e).sub_spec(bc_.mul_spec(e)),
            det.mul_spec(e),
        );

        // From sub_mul_right earlier:
        // num_x*a ≡ de*a - bf*a
        // num_y*b ≡ af*b - ce*b
        // So a*num_x + b*num_y ≡ de*a - bf*a + af*b - ce*b ≡ det*e
        Self::lemma_eqv_transitive(
            num_x.mul_spec(a).add_spec(num_y.mul_spec(b)),
            de.mul_spec(a).sub_spec(bf.mul_spec(a)).add_spec(
                af.mul_spec(b).sub_spec(ce.mul_spec(b))),
            det.mul_spec(e),
        );

        // We had: det*(ax+by) ≡ a*num_x + b*num_y = num_x*a + num_y*b
        Self::lemma_eqv_transitive(
            det.mul_spec(sum),
            num_x.mul_spec(a).add_spec(num_y.mul_spec(b)),
            det.mul_spec(e),
        );
        // Cancel det: ax + by ≡ e
        Self::lemma_mul_cancel_left(sum, e, det);

        // === Second equation: c*x + d*y ≡ f ===
        // By exact same argument with c,d,f instead of a,b,e.
        // c*num_x + d*num_y = c*(de-bf) + d*(af-ce)
        //   = cde - cbf + daf - dce
        //   = daf - cbf + cde - dce  ... rearranging
        //   = f*(da - cb) + e*(cd - dc)
        //   Hmm, that doesn't simplify nicely.
        // Actually: c*(de-bf) + d*(af-ce)
        //   = cde - cbf + daf - dce
        //   = daf - cbf + cde - dce  ... no
        // Let me redo: = c*d*e - c*b*f + d*a*f - d*c*e
        //              = (c*d*e - d*c*e) + (d*a*f - c*b*f)
        //              = 0 + (da - cb)*f
        //              = (ad - bc)*f  (since da=ad, cb=bc by commut)
        //              = det * f

        // So same structure. Let me do it.
        let cx = c.mul_spec(x);
        let dy = d.mul_spec(y);
        let sum2 = cx.add_spec(dy);
        Self::lemma_eqv_mul_distributive_left(det, cx, dy);

        Self::lemma_mul_associative(c, x, det);
        Self::lemma_eqv_mul_congruence_right(c, det.mul_spec(x), num_x);
        assert(cx.mul_spec(det) == det.mul_spec(cx));
        Self::lemma_eqv_transitive(
            det.mul_spec(cx), c.mul_spec(x.mul_spec(det)), c.mul_spec(num_x),
        );

        Self::lemma_mul_associative(d, y, det);
        Self::lemma_eqv_mul_congruence_right(d, det.mul_spec(y), num_y);
        assert(dy.mul_spec(det) == det.mul_spec(dy));
        Self::lemma_eqv_transitive(
            det.mul_spec(dy), d.mul_spec(y.mul_spec(det)), d.mul_spec(num_y),
        );

        Self::lemma_eqv_add_congruence(
            det.mul_spec(cx), c.mul_spec(num_x),
            det.mul_spec(dy), d.mul_spec(num_y),
        );
        Self::lemma_eqv_transitive(
            det.mul_spec(sum2),
            det.mul_spec(cx).add_spec(det.mul_spec(dy)),
            c.mul_spec(num_x).add_spec(d.mul_spec(num_y)),
        );

        // c*num_x + d*num_y ≡ det*f (same algebraic identity)
        assert(c.mul_spec(num_x) == num_x.mul_spec(c));
        assert(d.mul_spec(num_y) == num_y.mul_spec(d));
        Self::lemma_sub_mul_right(de, bf, c);
        Self::lemma_sub_mul_right(af, ce, d);
        Self::lemma_eqv_add_congruence(
            num_x.mul_spec(c), de.mul_spec(c).sub_spec(bf.mul_spec(c)),
            num_y.mul_spec(d), af.mul_spec(d).sub_spec(ce.mul_spec(d)),
        );

        // de*c ≡ cd*e, bf*c ≡ bc*f... wait let me redo for second eq.
        // de*c: (d*e)*c ≡ d*(e*c) = d*(c*e) ≡ (d*c)*e = (c*d)*e
        Self::lemma_mul_associative(d, e, c);
        Self::lemma_mul_commutative(e, c);
        Self::lemma_mul_associative(d, c, e);
        Self::lemma_eqv_symmetric(d.mul_spec(c).mul_spec(e), d.mul_spec(c.mul_spec(e)));
        Self::lemma_mul_commutative(d, c);
        let cd = c.mul_spec(d);
        let dc = d.mul_spec(c);
        assert(dc == cd);
        Self::lemma_eqv_transitive(
            de.mul_spec(c), d.mul_spec(e.mul_spec(c)), d.mul_spec(c.mul_spec(e)),
        );
        Self::lemma_eqv_transitive(de.mul_spec(c), d.mul_spec(c.mul_spec(e)), cd.mul_spec(e));
        // cd*e ≡ dc*e = de*c is what we showed. So de*c ≡ cd*e.

        // ce*d: (c*e)*d ≡ c*(e*d) = c*(d*e) ≡ (c*d)*e = cd*e
        Self::lemma_mul_associative(c, e, d);
        Self::lemma_mul_commutative(e, d);
        Self::lemma_mul_associative(c, d, e);
        Self::lemma_eqv_symmetric(cd.mul_spec(e), c.mul_spec(d.mul_spec(e)));
        Self::lemma_eqv_transitive(
            ce.mul_spec(d), c.mul_spec(e.mul_spec(d)), c.mul_spec(d.mul_spec(e)),
        );
        Self::lemma_eqv_transitive(ce.mul_spec(d), c.mul_spec(d.mul_spec(e)), cd.mul_spec(e));
        // So de*c ≡ cd*e and ce*d ≡ cd*e, hence de*c ≡ ce*d
        Self::lemma_eqv_symmetric(ce.mul_spec(d), cd.mul_spec(e));
        Self::lemma_eqv_transitive(de.mul_spec(c), cd.mul_spec(e), ce.mul_spec(d));

        // bf*c ≡ af*d: both ≡ ?
        // Actually we need: bf*c ≡ ? and af*d ≡ ?
        // Let me check what we need:
        // (de*c - bf*c) + (af*d - ce*d) ≡ det*f = (ad-bc)*f
        // de*c ≡ ce*d (shown above), so these cancel:
        // ≡ af*d - bf*c
        // af*d: (a*f)*d ≡ a*(f*d) = a*(d*f) ≡ (a*d)*f = ad*f
        Self::lemma_mul_associative(a, f, d);
        Self::lemma_mul_commutative(f, d);
        Self::lemma_mul_associative(a, d, f);
        Self::lemma_eqv_symmetric(ad.mul_spec(f), a.mul_spec(d.mul_spec(f)));
        Self::lemma_eqv_transitive(
            af.mul_spec(d), a.mul_spec(f.mul_spec(d)), a.mul_spec(d.mul_spec(f)),
        );
        Self::lemma_eqv_transitive(af.mul_spec(d), a.mul_spec(d.mul_spec(f)), ad.mul_spec(f));

        // bf*c: (b*f)*c ≡ b*(f*c) = b*(c*f) ≡ (b*c)*f = bc*f
        Self::lemma_mul_associative(b, f, c);
        Self::lemma_mul_commutative(f, c);
        Self::lemma_mul_associative(b, c, f);
        Self::lemma_eqv_symmetric(bc_.mul_spec(f), b.mul_spec(c.mul_spec(f)));
        Self::lemma_eqv_transitive(
            bf.mul_spec(c), b.mul_spec(f.mul_spec(c)), b.mul_spec(c.mul_spec(f)),
        );
        Self::lemma_eqv_transitive(bf.mul_spec(c), b.mul_spec(c.mul_spec(f)), bc_.mul_spec(f));

        // (de*c - bf*c) ≡ (ce*d - bc*f)... wait, de*c ≡ ce*d
        Self::lemma_eqv_sub_congruence(de.mul_spec(c), ce.mul_spec(d), bf.mul_spec(c), bf.mul_spec(c));
        Self::lemma_eqv_reflexive(bf.mul_spec(c));
        // (af*d - ce*d) ≡ (ad*f - ce*d)... wait
        Self::lemma_eqv_reflexive(ce.mul_spec(d));
        Self::lemma_eqv_sub_congruence(af.mul_spec(d), ad.mul_spec(f), ce.mul_spec(d), ce.mul_spec(d));

        // (de*c - bf*c) + (af*d - ce*d) ≡ (ce*d - bf*c) + (ad*f - ce*d)
        Self::lemma_eqv_add_congruence(
            de.mul_spec(c).sub_spec(bf.mul_spec(c)),
            ce.mul_spec(d).sub_spec(bf.mul_spec(c)),
            af.mul_spec(d).sub_spec(ce.mul_spec(d)),
            ad.mul_spec(f).sub_spec(ce.mul_spec(d)),
        );

        // (ce*d - bf*c) + (ad*f - ce*d) ≡ ad*f - bf*c  by eqv_sub_chain
        Self::lemma_eqv_sub_chain(ad.mul_spec(f), ce.mul_spec(d), bf.mul_spec(c));
        // Wait, sub_chain(X, Y, Z) gives (X-Y) + (Y-Z) ≡ X-Z
        // I need (ce*d - bf*c) + (ad*f - ce*d):
        // With X=ce*d, Y=bf*c... no that gives (ce*d - bf*c) + (bf*c - ?)
        // I need X=ad*f, Y=ce*d, Z=bf*c:
        // (ad*f - ce*d) + (ce*d - bf*c) ≡ ad*f - bf*c
        // But the order is (ce*d - bf*c) + (ad*f - ce*d), which is reversed.
        // Use add_commutative:
        Self::lemma_add_commutative(
            ce.mul_spec(d).sub_spec(bf.mul_spec(c)),
            ad.mul_spec(f).sub_spec(ce.mul_spec(d)),
        );
        Self::lemma_eqv_sub_chain(ad.mul_spec(f), ce.mul_spec(d), bf.mul_spec(c));
        Self::lemma_eqv_transitive(
            ce.mul_spec(d).sub_spec(bf.mul_spec(c)).add_spec(
                ad.mul_spec(f).sub_spec(ce.mul_spec(d))),
            ad.mul_spec(f).sub_spec(ce.mul_spec(d)).add_spec(
                ce.mul_spec(d).sub_spec(bf.mul_spec(c))),
            ad.mul_spec(f).sub_spec(bf.mul_spec(c)),
        );

        // ad*f - bf*c ≡ ad*f - bc*f (since bf*c ≡ bc*f)
        Self::lemma_eqv_reflexive(ad.mul_spec(f));
        Self::lemma_eqv_sub_congruence(
            ad.mul_spec(f), ad.mul_spec(f),
            bf.mul_spec(c), bc_.mul_spec(f),
        );
        // ad*f - bc*f ≡ (ad - bc)*f = det*f
        Self::lemma_sub_mul_right(ad, bc_, f);
        Self::lemma_eqv_symmetric(ad.mul_spec(f).sub_spec(bc_.mul_spec(f)), det.mul_spec(f));

        // Full chain for second eq:
        Self::lemma_eqv_transitive(
            num_x.mul_spec(c).add_spec(num_y.mul_spec(d)),
            de.mul_spec(c).sub_spec(bf.mul_spec(c)).add_spec(
                af.mul_spec(d).sub_spec(ce.mul_spec(d))),
            ce.mul_spec(d).sub_spec(bf.mul_spec(c)).add_spec(
                ad.mul_spec(f).sub_spec(ce.mul_spec(d))),
        );
        Self::lemma_eqv_transitive(
            num_x.mul_spec(c).add_spec(num_y.mul_spec(d)),
            ce.mul_spec(d).sub_spec(bf.mul_spec(c)).add_spec(
                ad.mul_spec(f).sub_spec(ce.mul_spec(d))),
            ad.mul_spec(f).sub_spec(bf.mul_spec(c)),
        );
        Self::lemma_eqv_transitive(
            num_x.mul_spec(c).add_spec(num_y.mul_spec(d)),
            ad.mul_spec(f).sub_spec(bf.mul_spec(c)),
            ad.mul_spec(f).sub_spec(bc_.mul_spec(f)),
        );
        Self::lemma_eqv_transitive(
            num_x.mul_spec(c).add_spec(num_y.mul_spec(d)),
            ad.mul_spec(f).sub_spec(bc_.mul_spec(f)),
            det.mul_spec(f),
        );

        // det*(cx+dy) ≡ c*num_x + d*num_y ≡ det*f
        Self::lemma_eqv_transitive(
            det.mul_spec(sum2),
            num_x.mul_spec(c).add_spec(num_y.mul_spec(d)),
            det.mul_spec(f),
        );
        // Cancel det
        Self::lemma_mul_cancel_left(sum2, f, det);

        // Second eq: c*x + d*y ≡ f
        // (We showed det*(cx+dy) ≡ det*f, cancelled to cx+dy ≡ f)
        Self::lemma_mul_commutative(e, det);
        Self::lemma_div_mul_cancel(e, det);
        Self::lemma_mul_commutative(f, det);
        Self::lemma_div_mul_cancel(f, det);
    }

    // ── Integer power (item 22) ───────────────────────────────────────

    /// a^n by repeated multiplication.
    pub open spec fn pow_spec(self, n: nat) -> Self
        decreases n,
    {
        if n == 0 {
            Self::from_int_spec(1)
        } else {
            self.mul_spec(self.pow_spec((n - 1) as nat))
        }
    }

    /// a^0 == 1 (structural).
    pub proof fn lemma_pow_zero(a: Self)
        ensures
            a.pow_spec(0) == Self::from_int_spec(1),
    {}

    /// a^1 ≡ a.
    pub proof fn lemma_pow_one(a: Self)
        ensures
            a.pow_spec(1).eqv_spec(a),
    {
        // a^1 = a * a^0 = a * from_int(1)
        // Unfold: pow_spec(1) with n=1 > 0, so a.mul_spec(a.pow_spec(0))
        // pow_spec(0) = from_int_spec(1)
        assert(a.pow_spec(0nat) == Self::from_int_spec(1));
        assert(a.pow_spec(1nat) == a.mul_spec(a.pow_spec(0nat)));
        Self::lemma_mul_one_identity(a);
    }

    /// a^2 ≡ a*a.
    pub proof fn lemma_pow_two(a: Self)
        ensures
            a.pow_spec(2).eqv_spec(a.mul_spec(a)),
    {
        // a^2 = a * a^1
        assert(a.pow_spec(2) == a.mul_spec(a.pow_spec(1)));
        // a^1 ≡ a
        Self::lemma_pow_one(a);
        Self::lemma_eqv_mul_congruence_right(a, a.pow_spec(1), a);
    }

    /// a^(n+1) == a * a^n (structural, from definition).
    pub proof fn lemma_pow_succ(a: Self, n: nat)
        ensures
            a.pow_spec(n + 1) == a.mul_spec(a.pow_spec(n)),
    {}

    /// (a*b)^n ≡ a^n * b^n.
    pub proof fn lemma_pow_mul(a: Self, b: Self, n: nat)
        ensures
            a.mul_spec(b).pow_spec(n).eqv_spec(
                a.pow_spec(n).mul_spec(b.pow_spec(n))),
        decreases n,
    {
        if n == 0 {
            // (a*b)^0 = 1, a^0 * b^0 = 1 * 1
            Self::lemma_from_int_mul(1, 1);
            // from_int(1) * from_int(1) ≡ from_int(1*1) = from_int(1)
            Self::lemma_eqv_symmetric(
                Self::from_int_spec(1).mul_spec(Self::from_int_spec(1)),
                Self::from_int_spec(1),
            );
        } else {
            let ab = a.mul_spec(b);
            // (ab)^n = ab * (ab)^(n-1)
            // By IH: (ab)^(n-1) ≡ a^(n-1) * b^(n-1)
            Self::lemma_pow_mul(a, b, (n - 1) as nat);
            // ab * (ab)^(n-1) ≡ ab * (a^(n-1) * b^(n-1))
            Self::lemma_eqv_mul_congruence_right(
                ab, ab.pow_spec((n - 1) as nat),
                a.pow_spec((n - 1) as nat).mul_spec(b.pow_spec((n - 1) as nat)),
            );
            // ab * (a^(n-1) * b^(n-1)) ≡ (a * a^(n-1)) * (b * b^(n-1))
            // = a^n * b^n
            // This requires rearranging: a*b * (a'*b') = (a*a') * (b*b')
            // by assoc and commut.
            let an1 = a.pow_spec((n - 1) as nat);
            let bn1 = b.pow_spec((n - 1) as nat);
            // ab * (an1 * bn1) ≡ a * (b * (an1 * bn1)) by assoc
            Self::lemma_mul_associative(a, b, an1.mul_spec(bn1));
            // b * (an1 * bn1) ≡ (b * an1) * bn1 by assoc (backward)
            Self::lemma_mul_associative(b, an1, bn1);
            Self::lemma_eqv_symmetric(b.mul_spec(an1).mul_spec(bn1), b.mul_spec(an1.mul_spec(bn1)));
            // b * an1 == an1 * b by commut
            Self::lemma_mul_commutative(b, an1);
            assert(b.mul_spec(an1) == an1.mul_spec(b));
            // (an1 * b) * bn1 ≡ an1 * (b * bn1) by assoc
            Self::lemma_mul_associative(an1, b, bn1);
            // So b * (an1 * bn1) ≡ (b*an1)*bn1 = (an1*b)*bn1 ≡ an1*(b*bn1)
            Self::lemma_eqv_transitive(
                b.mul_spec(an1.mul_spec(bn1)),
                b.mul_spec(an1).mul_spec(bn1),
                an1.mul_spec(b.mul_spec(bn1)),
            );
            // a * (b * (an1 * bn1)) ≡ a * (an1 * (b * bn1))
            Self::lemma_eqv_mul_congruence_right(
                a, b.mul_spec(an1.mul_spec(bn1)), an1.mul_spec(b.mul_spec(bn1)),
            );
            // a * (an1 * (b*bn1)) ≡ (a*an1) * (b*bn1) by assoc (backward)
            Self::lemma_mul_associative(a, an1, b.mul_spec(bn1));
            Self::lemma_eqv_symmetric(
                a.mul_spec(an1).mul_spec(b.mul_spec(bn1)),
                a.mul_spec(an1.mul_spec(b.mul_spec(bn1))),
            );
            // Chain: ab*(an1*bn1) ≡ a*(b*(an1*bn1)) ≡ a*(an1*(b*bn1)) ≡ (a*an1)*(b*bn1)
            Self::lemma_eqv_transitive(
                ab.mul_spec(an1.mul_spec(bn1)),
                a.mul_spec(b.mul_spec(an1.mul_spec(bn1))),
                a.mul_spec(an1.mul_spec(b.mul_spec(bn1))),
            );
            Self::lemma_eqv_transitive(
                ab.mul_spec(an1.mul_spec(bn1)),
                a.mul_spec(an1.mul_spec(b.mul_spec(bn1))),
                a.mul_spec(an1).mul_spec(b.mul_spec(bn1)),
            );
            // Full chain: (ab)^n ≡ ab * (an1*bn1) ≡ (a*an1)*(b*bn1) = a^n * b^n
            Self::lemma_eqv_transitive(
                ab.pow_spec(n),
                ab.mul_spec(a.pow_spec((n - 1) as nat).mul_spec(b.pow_spec((n - 1) as nat))),
                a.mul_spec(an1).mul_spec(b.mul_spec(bn1)),
            );
        }
    }

    /// a^(m+n) ≡ a^m * a^n.
    pub proof fn lemma_pow_add(a: Self, m: nat, n: nat)
        ensures
            a.pow_spec(m + n).eqv_spec(
                a.pow_spec(m).mul_spec(a.pow_spec(n))),
        decreases m,
    {
        if m == 0 {
            // a^(0+n) = a^n, a^0 * a^n = 1 * a^n = a^n
            Self::lemma_mul_one_identity(a.pow_spec(n));
            Self::lemma_eqv_symmetric(
                Self::from_int_spec(1).mul_spec(a.pow_spec(n)),
                a.pow_spec(n),
            );
        } else {
            // a^(m+n) = a * a^(m-1+n)
            // By IH: a^(m-1+n) ≡ a^(m-1) * a^n
            Self::lemma_pow_add(a, (m - 1) as nat, n);
            // a * a^(m-1+n) ≡ a * (a^(m-1) * a^n)
            Self::lemma_eqv_mul_congruence_right(
                a, a.pow_spec(((m - 1) as nat) + n),
                a.pow_spec((m - 1) as nat).mul_spec(a.pow_spec(n)),
            );
            // a * (a^(m-1) * a^n) ≡ (a * a^(m-1)) * a^n by assoc (backward)
            Self::lemma_mul_associative(a, a.pow_spec((m - 1) as nat), a.pow_spec(n));
            Self::lemma_eqv_symmetric(
                a.mul_spec(a.pow_spec((m - 1) as nat)).mul_spec(a.pow_spec(n)),
                a.mul_spec(a.pow_spec((m - 1) as nat).mul_spec(a.pow_spec(n))),
            );
            // Chain
            Self::lemma_eqv_transitive(
                a.pow_spec(m + n),
                a.mul_spec(a.pow_spec((m - 1) as nat).mul_spec(a.pow_spec(n))),
                a.mul_spec(a.pow_spec((m - 1) as nat)).mul_spec(a.pow_spec(n)),
            );
            // a * a^(m-1) = a^m by definition
        }
    }

    /// 0 ≤ a^(2n).
    pub proof fn lemma_pow_even_nonneg(a: Self, n: nat)
        ensures
            Self::from_int_spec(0).le_spec(a.pow_spec(2 * n)),
        decreases n,
    {
        if n == 0 {
            // a^0 = 1, 0 ≤ 1
            Self::lemma_from_int_preserves_le(0, 1);
        } else {
            // a^(2n) = a^(2(n-1) + 2) = a^(2(n-1)) * a^2
            Self::lemma_pow_add(a, 2 * ((n - 1) as nat), 2);
            let prev = a.pow_spec(2 * ((n - 1) as nat));
            let sq = a.pow_spec(2);
            // 0 ≤ prev by IH
            Self::lemma_pow_even_nonneg(a, (n - 1) as nat);
            // 0 ≤ sq (a^2 ≡ a*a ≥ 0)
            Self::lemma_pow_two(a);
            Self::lemma_square_le_nonneg(a);
            let z = Self::from_int_spec(0);
            // 0 ≤ a*a and sq ≡ a*a, so 0 ≤ sq
            Self::lemma_eqv_symmetric(sq, a.mul_spec(a));
            Self::lemma_eqv_implies_le(a.mul_spec(a), sq);
            Self::lemma_le_transitive(z, a.mul_spec(a), sq);
            // 0 ≤ prev and 0 ≤ sq → 0 ≤ prev*sq
            Self::lemma_le_mul_nonneg_both(z, prev, z, sq);
            // prev*sq ≡ a^(2n)
            Self::lemma_eqv_symmetric(a.pow_spec(2 * n), prev.mul_spec(sq));
            Self::lemma_eqv_implies_le(prev.mul_spec(sq), a.pow_spec(2 * n));
            // 0*0 ≡ 0
            Self::lemma_mul_zero(z);
            Self::lemma_eqv_implies_le(z, z.mul_spec(z));
            Self::lemma_le_transitive(z, z.mul_spec(z), prev.mul_spec(sq));
            Self::lemma_le_transitive(z, prev.mul_spec(sq), a.pow_spec(2 * n));
        }
    }

    /// a > 0 → a^n > 0.
    pub proof fn lemma_pow_positive(a: Self, n: nat)
        requires
            Self::from_int_spec(0).lt_spec(a),
        ensures
            Self::from_int_spec(0).lt_spec(a.pow_spec(n)),
        decreases n,
    {
        let z = Self::from_int_spec(0);
        if n == 0 {
            // a^0 = from_int(1), and 0 < 1
            Self::lemma_from_int_preserves_lt(0, 1);
        } else {
            // a^n = a * a^(n-1)
            // By IH: 0 < a^(n-1)
            Self::lemma_pow_positive(a, (n - 1) as nat);
            // 0 < a and 0 < a^(n-1) → 0*a^(n-1) < a*a^(n-1)
            Self::lemma_lt_mul_positive(z, a, a.pow_spec((n - 1) as nat));
            // 0 ≡ 0*a^(n-1) → 0 ≤ 0*a^(n-1)
            Self::lemma_mul_zero(a.pow_spec((n - 1) as nat));
            Self::lemma_eqv_implies_le(z, z.mul_spec(a.pow_spec((n - 1) as nat)));
            // Chain: 0 ≤ 0*a^(n-1) < a*a^(n-1) = a^n
            Self::lemma_le_lt_transitive(z, z.mul_spec(a.pow_spec((n - 1) as nat)),
                a.pow_spec(n));
        }
    }

    /// a ≥ 0 → a^n ≥ 0.
    pub proof fn lemma_pow_nonneg(a: Self, n: nat)
        requires
            Self::from_int_spec(0).le_spec(a),
        ensures
            Self::from_int_spec(0).le_spec(a.pow_spec(n)),
        decreases n,
    {
        let z = Self::from_int_spec(0);
        if n == 0 {
            Self::lemma_from_int_preserves_le(0, 1);
        } else {
            // a^n = a * a^(n-1)
            Self::lemma_pow_nonneg(a, (n - 1) as nat);
            // 0 ≤ a and 0 ≤ a^(n-1) → 0*0 ≤ a * a^(n-1)
            Self::lemma_le_mul_nonneg_both(z, a, z, a.pow_spec((n - 1) as nat));
            // 0*0 ≡ 0
            Self::lemma_mul_zero(z);
            Self::lemma_eqv_implies_le(z, z.mul_spec(z));
            Self::lemma_le_transitive(z, z.mul_spec(z), a.pow_spec(n));
        }
    }

    /// a ≢ 0 → (a⁻¹)^n ≡ (a^n)⁻¹.
    pub proof fn lemma_pow_reciprocal(a: Self, n: nat)
        requires
            !a.eqv_spec(Self::from_int_spec(0)),
        ensures
            a.reciprocal_spec().pow_spec(n).eqv_spec(
                a.pow_spec(n).reciprocal_spec()),
        decreases n,
    {
        Self::lemma_eqv_zero_iff_num_zero(a);
        let inv = a.reciprocal_spec();
        let one = Self::from_int_spec(1);
        if n == 0 {
            // (a⁻¹)^0 = 1 and (a^0)⁻¹ = 1⁻¹
            // 1⁻¹ ≡ 1 (since 1 * 1 = 1)
            assert(one.num == 1);
            assert(one.denom() == 1);
            assert(one.reciprocal_spec().num == 1);
            assert(one.reciprocal_spec().denom() == 1);
            Self::lemma_eqv_reflexive(one);
        } else {
            // (a⁻¹)^n = a⁻¹ * (a⁻¹)^(n-1)
            // By IH: (a⁻¹)^(n-1) ≡ (a^(n-1))⁻¹
            Self::lemma_pow_reciprocal(a, (n - 1) as nat);
            let prev_pow = a.pow_spec((n - 1) as nat);
            // prev_pow.num != 0 is NOT guaranteed (a^(n-1) could be 0 if
            // a ≡ 0, but we have a ≢ 0, so a.num != 0, hence a^(n-1).num != 0).
            // Actually, a.num != 0, so a^(n-1) has num = a.num^(n-1) which ≠ 0.
            // We need: a^(n-1) ≢ 0
            // From a^(n-1) = a * a^(n-2) * ... all having nonzero num:
            // The numerator of a^k is a.num^k (by mul_spec definition), which is nonzero.
            Self::lemma_pow_num_nonzero(a, (n - 1) as nat);

            // a⁻¹ * (a⁻¹)^(n-1) ≡ a⁻¹ * (a^(n-1))⁻¹  by congruence + IH
            Self::lemma_eqv_mul_congruence_right(
                inv,
                inv.pow_spec((n - 1) as nat),
                prev_pow.reciprocal_spec(),
            );
            // a⁻¹ * (a^(n-1))⁻¹ ≡ (a * a^(n-1))⁻¹   by reciprocal_of_product (backward)
            Self::lemma_reciprocal_of_product(a, prev_pow);
            Self::lemma_eqv_symmetric(
                a.mul_spec(prev_pow).reciprocal_spec(),
                inv.mul_spec(prev_pow.reciprocal_spec()),
            );
            // Chain
            Self::lemma_eqv_transitive(
                inv.pow_spec(n),
                inv.mul_spec(prev_pow.reciprocal_spec()),
                a.mul_spec(prev_pow).reciprocal_spec(),
            );
            // a * a^(n-1) = a^n  structurally
        }
    }

    /// Helper: if a.num ≠ 0 then a^n has nonzero numerator.
    proof fn lemma_pow_num_nonzero(a: Self, n: nat)
        requires
            a.num != 0,
        ensures
            a.pow_spec(n).num != 0,
        decreases n,
    {
        if n == 0 {
            assert(a.pow_spec(0).num == 1);
        } else {
            Self::lemma_pow_num_nonzero(a, (n - 1) as nat);
            let prev = a.pow_spec((n - 1) as nat);
            assert(a.pow_spec(n).num == a.num * prev.num);
            assert(a.num != 0 && prev.num != 0 ==> a.num * prev.num != 0)
                by (nonlinear_arith);
        }
    }

    /// 0 ≤ a ≤ b → a^n ≤ b^n.
    pub proof fn lemma_pow_monotone(a: Self, b: Self, n: nat)
        requires
            Self::from_int_spec(0).le_spec(a),
            a.le_spec(b),
        ensures
            a.pow_spec(n).le_spec(b.pow_spec(n)),
        decreases n,
    {
        let z = Self::from_int_spec(0);
        if n == 0 {
            // a^0 = b^0 = 1, so 1 ≤ 1 by reflexivity
            Self::lemma_eqv_reflexive(Self::from_int_spec(1));
            Self::lemma_eqv_implies_le(Self::from_int_spec(1), Self::from_int_spec(1));
        } else {
            // a^n = a * a^(n-1), b^n = b * b^(n-1)
            // By IH: a^(n-1) ≤ b^(n-1)
            Self::lemma_pow_monotone(a, b, (n - 1) as nat);
            // 0 ≤ a^(n-1) by pow_nonneg
            Self::lemma_pow_nonneg(a, (n - 1) as nat);
            // 0 ≤ a ≤ b and 0 ≤ a^(n-1) ≤ b^(n-1) → a*a^(n-1) ≤ b*b^(n-1)
            Self::lemma_le_mul_nonneg_both(
                a, b,
                a.pow_spec((n - 1) as nat), b.pow_spec((n - 1) as nat),
            );
        }
    }

    /// 0 ≤ a < b ∧ n > 0 → a^n < b^n.
    pub proof fn lemma_pow_strict_monotone(a: Self, b: Self, n: nat)
        requires
            Self::from_int_spec(0).le_spec(a),
            a.lt_spec(b),
            n > 0,
        ensures
            a.pow_spec(n).lt_spec(b.pow_spec(n)),
        decreases n,
    {
        let z = Self::from_int_spec(0);
        if n == 1 {
            // a^1 ≡ a and b^1 ≡ b, and a < b, so a^1 < b^1.
            Self::lemma_pow_one(a);
            Self::lemma_pow_one(b);
            // a^1 ≡ a → a^1 ≤ a
            Self::lemma_eqv_symmetric(a.pow_spec(1), a);
            Self::lemma_eqv_implies_le(a, a.pow_spec(1));
            // b ≡ b^1 → b ≤ b^1
            Self::lemma_eqv_implies_le(b.pow_spec(1), b);
            // a^1 ≤ a < b → a^1 < b
            Self::lemma_le_lt_transitive(a.pow_spec(1), a, b);
            // a^1 < b ≤ b^1 → a^1 < b^1
            Self::lemma_lt_le_transitive(a.pow_spec(1), b, b.pow_spec(1));
        } else {
            // a^n = a * a^(n-1), b^n = b * b^(n-1)
            // By IH: a^(n-1) < b^(n-1) (since n-1 > 0)
            Self::lemma_pow_strict_monotone(a, b, (n - 1) as nat);
            // 0 ≤ a < b → 0 < b
            Self::lemma_le_lt_transitive(z, a, b);
            // 0 < b and a^(n-1) < b^(n-1) → a^(n-1)*b < b^(n-1)*b
            Self::lemma_lt_mul_positive(
                a.pow_spec((n - 1) as nat), b.pow_spec((n - 1) as nat), b,
            );
            // By commutativity: x*b == b*x structurally
            Self::lemma_mul_commutative(b, a.pow_spec((n - 1) as nat));
            Self::lemma_mul_commutative(b, b.pow_spec((n - 1) as nat));
            // So: b*a^(n-1) < b*b^(n-1)

            // a ≤ b and 0 ≤ a^(n-1) → a*a^(n-1) ≤ b*a^(n-1)
            Self::lemma_pow_nonneg(a, (n - 1) as nat);
            Self::lemma_lt_implies_le(a, b);
            Self::lemma_le_mul_nonneg(a, b, a.pow_spec((n - 1) as nat));

            // Chain: a^n = a*a^(n-1) ≤ b*a^(n-1) < b*b^(n-1) = b^n
            Self::lemma_le_lt_transitive(
                a.pow_spec(n),
                b.mul_spec(a.pow_spec((n - 1) as nat)),
                b.mul_spec(b.pow_spec((n - 1) as nat)),
            );
        }
    }

    // ── Quadratic discriminant (item 21) ────────────────────────────

    /// discriminant(a, b, c) = b² - 4ac.
    pub open spec fn discriminant_spec(a: Self, b: Self, c: Self) -> Self {
        b.mul_spec(b).sub_spec(
            Self::from_int_spec(4).mul_spec(a.mul_spec(c)))
    }

    /// If t is a rational root of ax²+bx+c, verify it satisfies the equation.
    pub proof fn lemma_quadratic_at_rational_root(a: Self, b: Self, c: Self, t: Self)
        requires
            a.mul_spec(t.mul_spec(t)).add_spec(b.mul_spec(t)).add_spec(c)
                .eqv_spec(Self::from_int_spec(0)),
        ensures
            a.mul_spec(t).mul_spec(t).add_spec(b.mul_spec(t)).add_spec(c)
                .eqv_spec(Self::from_int_spec(0)),
    {
        // a*(t*t) ≡ (a*t)*t by associativity (backward)
        Self::lemma_mul_associative(a, t, t);
        Self::lemma_eqv_symmetric(
            a.mul_spec(t).mul_spec(t),
            a.mul_spec(t.mul_spec(t)),
        );
        // Replace a*(t*t) with (a*t)*t in the sum
        Self::lemma_eqv_add_congruence_left(
            a.mul_spec(t.mul_spec(t)),
            a.mul_spec(t).mul_spec(t),
            b.mul_spec(t),
        );
        Self::lemma_eqv_add_congruence_left(
            a.mul_spec(t.mul_spec(t)).add_spec(b.mul_spec(t)),
            a.mul_spec(t).mul_spec(t).add_spec(b.mul_spec(t)),
            c,
        );
        Self::lemma_eqv_transitive(
            a.mul_spec(t).mul_spec(t).add_spec(b.mul_spec(t)).add_spec(c),
            a.mul_spec(t.mul_spec(t)).add_spec(b.mul_spec(t)).add_spec(c),
            Self::from_int_spec(0),
        );
    }

    /// When disc = 0 and a ≢ 0, the double root -b/(2a) satisfies ax²+bx+c = 0.
    pub proof fn lemma_quadratic_double_root(a: Self, b: Self, c: Self)
        requires
            !a.eqv_spec(Self::from_int_spec(0)),
            Self::discriminant_spec(a, b, c).eqv_spec(Self::from_int_spec(0)),
        ensures ({
            let two_a = Self::from_int_spec(2).mul_spec(a);
            let t = b.neg_spec().div_spec(two_a);
            a.mul_spec(t.mul_spec(t)).add_spec(b.mul_spec(t)).add_spec(c)
                .eqv_spec(Self::from_int_spec(0))
        }),
    {
        let z = Self::from_int_spec(0);
        let two = Self::from_int_spec(2);
        let four = Self::from_int_spec(4);
        let two_a = two.mul_spec(a);
        let nb = b.neg_spec();
        let t = nb.div_spec(two_a);

        Self::lemma_eqv_zero_iff_num_zero(a);
        // 2a ≢ 0 since a ≢ 0
        Self::lemma_eqv_zero_iff_num_zero(two_a);
        Self::lemma_mul_denom_product_int(two, a);
        assert(two.num == 2);
        assert(two.denom() == 1);
        assert(two_a.num == 2 * a.num);
        assert(two_a.num != 0) by (nonlinear_arith)
            requires a.num != 0, two_a.num == 2 * a.num;

        // Algebraic approach: factor a*t²+b*t = t*(a*t+b), show a*t+b ≡ b/2,
        // then show (b/2)*t + c ≡ 0 using disc=0.

        // Step 1: 2a*t ≡ -b (from div_cancel)
        Self::lemma_div_cancel(two_a, nb);
        // two_a * t ≡ nb

        // Step 2: Derive 2*(a*t) ≡ -b using associativity
        let at_ = a.mul_spec(t);
        Self::lemma_mul_associative(two, a, t);
        // (two*a)*t ≡ two*(a*t), i.e., two_a*t ≡ two*at_
        Self::lemma_eqv_symmetric(two.mul_spec(a).mul_spec(t), two.mul_spec(a.mul_spec(t)));
        // two*at_ ≡ two_a*t
        Self::lemma_eqv_transitive(two.mul_spec(at_), two_a.mul_spec(t), nb);
        // two*at_ ≡ nb

        // Step 3: a*t ≡ -b/2 by cancellation
        let recip_two = two.reciprocal_spec();
        let half_nb = nb.div_spec(two);   // = nb * recip(2) = -b/2
        let half_b = b.div_spec(two);     // = b * recip(2) = b/2

        Self::lemma_eqv_zero_iff_num_zero(two);
        Self::lemma_div_cancel(two, nb);
        // two * half_nb ≡ nb
        Self::lemma_eqv_symmetric(two.mul_spec(half_nb), nb);
        // nb ≡ two * half_nb
        Self::lemma_eqv_transitive(two.mul_spec(at_), nb, two.mul_spec(half_nb));
        // two*at_ ≡ two*half_nb
        Self::lemma_mul_cancel_left(at_, half_nb, two);
        // at_ ≡ half_nb, i.e., a*t ≡ -b/2

        // Step 4: Show half_nb == half_b.neg_spec() (structural)
        Self::lemma_mul_commutative(nb, recip_two);
        Self::lemma_mul_neg_right(recip_two, b);
        Self::lemma_mul_commutative(recip_two, b);
        // half_nb = nb * recip_two == recip_two * nb == recip_two * b.neg_spec()
        //         == (recip_two * b).neg_spec() == (b * recip_two).neg_spec()
        //         == half_b.neg_spec()
        assert(half_nb == half_b.neg_spec());

        // Step 5: a*t + b ≡ half_b
        // First show b ≡ half_b + half_b:
        Self::lemma_div_cancel(two, b);
        // two * half_b ≡ b
        Self::lemma_double(half_b);
        // half_b + half_b ≡ two * half_b
        Self::lemma_eqv_transitive(
            half_b.add_spec(half_b), two.mul_spec(half_b), b);
        // half_b + half_b ≡ b
        Self::lemma_eqv_symmetric(half_b.add_spec(half_b), b);
        // b ≡ half_b + half_b

        // at_ + b ≡ half_nb + b (by congruence with at_ ≡ half_nb)
        Self::lemma_eqv_add_congruence_left(at_, half_nb, b);
        // at_ + b ≡ half_nb + b

        // half_nb + b ≡ half_nb + (half_b + half_b) (by congruence)
        Self::lemma_eqv_add_congruence_right(half_nb, b, half_b.add_spec(half_b));
        // half_nb + b ≡ half_nb + (half_b + half_b)

        // (half_nb + half_b) + half_b ≡ half_nb + (half_b + half_b) (associativity)
        Self::lemma_add_associative(half_nb, half_b, half_b);
        Self::lemma_eqv_symmetric(
            half_nb.add_spec(half_b).add_spec(half_b),
            half_nb.add_spec(half_b.add_spec(half_b)));
        // half_nb + (half_b + half_b) ≡ (half_nb + half_b) + half_b

        // half_nb + half_b ≡ 0 (since half_nb == -half_b)
        Self::lemma_add_commutative(half_nb, half_b);
        // half_nb + half_b ≡ half_b + half_nb
        // half_nb == half_b.neg_spec(), so half_b + half_nb == half_b + half_b.neg_spec()
        //                              == half_b.sub_spec(half_b)
        Self::lemma_sub_self(half_b);
        // half_b.sub_spec(half_b) ≡ 0
        // half_b + half_b.neg_spec() == half_b.sub_spec(half_b) [structural from sub_spec def]
        Self::lemma_eqv_transitive(
            half_nb.add_spec(half_b),
            half_b.add_spec(half_nb),
            Self::from_int_spec(0));
        // half_nb + half_b ≡ 0

        // (half_nb + half_b) + half_b ≡ 0 + half_b (congruence)
        Self::lemma_eqv_add_congruence_left(
            half_nb.add_spec(half_b),
            Self::from_int_spec(0),
            half_b);
        // 0 + half_b == half_b (structural from add_zero_identity)
        Self::lemma_add_zero_identity(half_b);

        // Chain: at_ + b ≡ half_nb + b ≡ half_nb + (half_b + half_b)
        //        ≡ (half_nb + half_b) + half_b ≡ 0 + half_b == half_b
        Self::lemma_eqv_transitive(
            at_.add_spec(b), half_nb.add_spec(b),
            half_nb.add_spec(half_b.add_spec(half_b)));
        Self::lemma_eqv_transitive(
            at_.add_spec(b),
            half_nb.add_spec(half_b.add_spec(half_b)),
            half_nb.add_spec(half_b).add_spec(half_b));
        Self::lemma_eqv_transitive(
            at_.add_spec(b),
            half_nb.add_spec(half_b).add_spec(half_b),
            Self::from_int_spec(0).add_spec(half_b));
        // at_ + b ≡ 0 + half_b == half_b
        // So at_ + b ≡ half_b (via eqv with the structural == step)
        Self::lemma_eqv_reflexive(half_b);

        // Step 6: Factor: a*(t*t) + b*t ≡ (a*t + b) * t
        let tt = t.mul_spec(t);
        let att = a.mul_spec(tt);
        let bt = b.mul_spec(t);
        let att_bt = att.add_spec(bt);
        let at_b = at_.add_spec(b);
        let at_b_t = at_b.mul_spec(t);

        // (a*t + b)*t ≡ (a*t)*t + b*t  [distributive]
        Self::lemma_eqv_mul_distributive_right(at_, b, t);
        // at_b * t ≡ at_*t + b*t

        // (a*t)*t ≡ a*(t*t)  [associativity]
        Self::lemma_mul_associative(a, t, t);
        Self::lemma_eqv_add_congruence_left(
            a.mul_spec(t).mul_spec(t), a.mul_spec(t.mul_spec(t)), bt);
        // (a*t)*t + bt ≡ a*(t*t) + bt = att + bt = att_bt

        // at_b_t ≡ at_*t + bt ≡ att_bt
        Self::lemma_eqv_transitive(at_b_t, at_.mul_spec(t).add_spec(bt), att_bt);
        // att_bt ≡ at_b_t [symmetric]
        Self::lemma_eqv_symmetric(at_b_t, att_bt);

        // Step 7: att_bt ≡ half_b * t (via congruence)
        let half_b_t = half_b.mul_spec(t);
        // at_b ≡ half_b (from step 5, eqv chain above)
        // We need to establish at_b ≡ half_b properly for mul_congruence
        // at_ + b ≡ z + half_b, and z + half_b == half_b structurally
        // So at_b.eqv_spec(half_b)
        Self::lemma_eqv_mul_congruence_left(at_b, half_b, t);
        // at_b_t ≡ half_b_t

        // att_bt ≡ at_b_t ≡ half_b_t
        Self::lemma_eqv_transitive(att_bt, at_b_t, half_b_t);
        // att_bt ≡ half_b_t

        // Step 8: expr = att_bt + c ≡ half_b_t + c
        let expr = att_bt.add_spec(c);
        let result = half_b_t.add_spec(c);
        Self::lemma_eqv_add_congruence_left(att_bt, half_b_t, c);
        // expr ≡ result

        // Step 9: Show result ≡ 0 at the numerator level.
        // half_b.num = b.num, half_b.denom() = 2 * b.denom()
        // (since from_int(2).reciprocal_spec() = Rational{num:1, den:1},
        //  so half_b = b * Rational{num:1, den:1}, half_b.num = b.num*1,
        //  half_b.denom() = b.denom() * 2)
        Self::lemma_mul_denom_product_int(b, recip_two);
        assert(recip_two.num == 1);
        assert(recip_two.denom() == 2);
        assert(half_b.num == b.num);
        assert(half_b.denom() == b.denom() * 2);

        Self::lemma_mul_denom_product_int(half_b, t);
        Self::lemma_add_denom_product_int(half_b_t, c);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        Self::lemma_denom_positive(t);

        let ghost bn = b.num;
        let ghost bd = b.denom();
        let ghost cn = c.num;
        let ghost cd = c.denom();
        let ghost tn = t.num;
        let ghost td = t.denom();
        let ghost an = a.num;
        let ghost ad = a.denom();

        // half_b_t.num = half_b.num * t.num = bn * tn
        // half_b_t.denom() = half_b.denom() * t.denom() = 2*bd * td
        // result.num = half_b_t.num * c.denom() + c.num * half_b_t.denom()
        //            = bn*tn*cd + cn*2*bd*td
        assert(result.num == bn * tn * cd + cn * (2 * bd) * td) by (nonlinear_arith)
            requires
                result.num == half_b_t.num * cd + cn * half_b_t.denom(),
                half_b_t.num == bn * tn,
                half_b_t.denom() == (bd * 2) * td;

        // From 2a*t ≡ -b, extract cross-multiplication:
        Self::lemma_mul_denom_product_int(two_a, t);
        assert(2 * an * tn * bd == -(bn * ad * td)) by (nonlinear_arith)
            requires
                two_a.mul_spec(t).num * nb.denom() == nb.num * two_a.mul_spec(t).denom(),
                two_a.mul_spec(t).num == two_a.num * tn,
                two_a.num == 2 * an,
                two_a.mul_spec(t).denom() == two_a.denom() * td,
                two_a.denom() == ad,
                nb.num == -bn,
                nb.denom() == bd;

        // From disc ≡ 0: b² ≡ 4ac (cross-multiplication)
        let bb = b.mul_spec(b);
        let ac_ = a.mul_spec(c);
        let four_ac = four.mul_spec(ac_);
        Self::lemma_sub_eqv_zero_iff_eqv(bb, four_ac);
        Self::lemma_mul_denom_product_int(b, b);
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_mul_denom_product_int(four, ac_);
        assert(bn * bn * (ad * cd) == 4 * an * cn * (bd * bd)) by (nonlinear_arith)
            requires
                bb.num * four_ac.denom() == four_ac.num * bb.denom(),
                bb.num == bn * bn,
                bb.denom() == bd * bd,
                four_ac.num == four.num * ac_.num,
                four.num == 4,
                ac_.num == an * cn,
                four_ac.denom() == four.denom() * ac_.denom(),
                four.denom() == 1,
                ac_.denom() == ad * cd;

        // Show result.num == 0 by case split on bn
        // (bn*tn*cd + 2*cn*bd*td) * (bn*ad) = 0, using both constraints
        if bn == 0 {
            // From disc: 0 = 4*an*cn*bd², so cn = 0
            assert(cn == 0) by (nonlinear_arith)
                requires bn * bn * (ad * cd) == 4 * an * cn * (bd * bd),
                    bn == 0, an != 0, bd > 0;
            assert(result.num == 0) by (nonlinear_arith)
                requires result.num == bn * tn * cd + cn * (2 * bd) * td,
                    bn == 0, cn == 0;
        } else {
            // Multiply (bn*tn*cd) by (bn*ad), use (**):
            // bn*ad*(bn*tn*cd) = bn²*ad*cd*tn
            // From (*): bn²*ad*cd = 4*an*cn*bd²
            // So = 4*an*cn*bd²*tn

            // Multiply (2*cn*bd*td) by (bn*ad), use (**):
            // bn*ad*(2*cn*bd*td) = 2*cn*bd*(bn*ad*td) = 2*cn*bd*(-2*an*tn*bd)
            // = -4*an*cn*bd²*tn

            // Sum = 4*an*cn*bd²*tn - 4*an*cn*bd²*tn = 0
            let ghost P = bn * tn * cd;
            let ghost Q = 2 * cn * bd * td;
            let ghost ba = bn * ad;

            // P*ba = bn²*ad*tn*cd = (bn²*ad*cd)*tn = 4*an*cn*bd²*tn
            let ghost P_ba = P * ba;
            let ghost disc_factor = bn * bn * ad * cd;
            assert(disc_factor == 4 * an * cn * bd * bd) by (nonlinear_arith)
                requires bn * bn * (ad * cd) == 4 * an * cn * (bd * bd),
                    disc_factor == bn * bn * ad * cd;
            assert(P_ba == disc_factor * tn) by (nonlinear_arith)
                requires P == bn * tn * cd, ba == bn * ad, P_ba == P * ba,
                    disc_factor == bn * bn * ad * cd;
            assert(P_ba == 4 * an * cn * bd * bd * tn) by (nonlinear_arith)
                requires P_ba == disc_factor * tn,
                    disc_factor == 4 * an * cn * bd * bd;

            // Q*ba = 2*cn*bd*td*bn*ad = 2*cn*bd*(bn*ad*td)
            let ghost Q_ba = Q * ba;
            let ghost bat = bn * ad * td;
            assert(bat == -(2 * an * tn * bd)) by (nonlinear_arith)
                requires 2 * an * tn * bd == -(bn * ad * td), bat == bn * ad * td;
            assert(Q_ba == 2 * cn * bd * bat) by (nonlinear_arith)
                requires Q == 2 * cn * bd * td, ba == bn * ad,
                    Q_ba == Q * ba, bat == bn * ad * td;
            assert(Q_ba == -(4 * an * cn * bd * bd * tn)) by (nonlinear_arith)
                requires Q_ba == 2 * cn * bd * bat,
                    bat == -(2 * an * tn * bd);

            // (P + Q) * ba = P_ba + Q_ba = 0
            assert(P_ba + Q_ba == 0) by (nonlinear_arith)
                requires P_ba == 4 * an * cn * bd * bd * tn,
                    Q_ba == -(4 * an * cn * bd * bd * tn);
            assert((P + Q) * ba == 0) by (nonlinear_arith)
                requires P_ba + Q_ba == 0, P_ba == P * ba, Q_ba == Q * ba;
            assert(P + Q == 0) by (nonlinear_arith)
                requires (P + Q) * ba == 0, ba == bn * ad, bn != 0, ad > 0;
            // Bridge: cn*(2*bd)*td == 2*cn*bd*td
            assert(result.num == P + Q) by (nonlinear_arith)
                requires result.num == bn * tn * cd + cn * (2 * bd) * td,
                    P == bn * tn * cd, Q == 2 * cn * bd * td;
            assert(result.num == 0) by (nonlinear_arith)
                requires result.num == P + Q, P + Q == 0;
        }

        Self::lemma_eqv_zero_iff_num_zero(result);
        // result ≡ 0, and expr ≡ result
        Self::lemma_eqv_transitive(expr, result, Self::from_int_spec(0));
    }

    /// If a*t²+b*t+c ≡ 0 and a ≢ 0, then discriminant b²-4ac ≥ 0.
    pub proof fn lemma_discriminant_nonneg_square(a: Self, b: Self, c: Self, t: Self)
        requires
            a.mul_spec(t.mul_spec(t)).add_spec(b.mul_spec(t)).add_spec(c)
                .eqv_spec(Self::from_int_spec(0)),
            !a.eqv_spec(Self::from_int_spec(0)),
        ensures
            Self::from_int_spec(0).le_spec(Self::discriminant_spec(a, b, c)),
    {
        let tt = t.mul_spec(t);
        let att = a.mul_spec(tt);
        let bt = b.mul_spec(t);
        let att_bt = att.add_spec(bt);
        let expr = att_bt.add_spec(c);

        // expr ≡ 0 ↔ expr.num == 0
        Self::lemma_eqv_zero_iff_num_zero(expr);
        // a ≢ 0 ↔ a.num != 0
        Self::lemma_eqv_zero_iff_num_zero(a);

        // Structural facts
        Self::lemma_mul_denom_product_int(t, t);
        Self::lemma_mul_denom_product_int(a, tt);
        Self::lemma_mul_denom_product_int(b, t);
        Self::lemma_add_denom_product_int(att, bt);
        Self::lemma_add_denom_product_int(att_bt, c);
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        Self::lemma_denom_positive(t);

        // Discriminant structural facts
        let bb = b.mul_spec(b);
        let ac_ = a.mul_spec(c);
        let four = Self::from_int_spec(4);
        let four_ac = four.mul_spec(ac_);
        let disc = Self::discriminant_spec(a, b, c);
        Self::lemma_mul_denom_product_int(b, b);
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_mul_denom_product_int(four, ac_);
        Self::lemma_add_denom_product_int(bb, four_ac.neg_spec());
        Self::lemma_denom_positive(bb);
        Self::lemma_denom_positive(four_ac);

        let ghost an = a.num;
        let ghost ad_ = a.denom();
        let ghost bn = b.num;
        let ghost bd_ = b.denom();
        let ghost cn = c.num;
        let ghost cd_ = c.denom();
        let ghost tn = t.num;
        let ghost td_ = t.denom();

        // disc.num = bn²*ad*cd - 4*an*cn*bd²
        assert(four.num == 4);
        assert(four.denom() == 1);
        assert(disc.num == bn * bn * (ad_ * cd_) + (-(4 * (an * cn))) * (bd_ * bd_));

        let ghost disc_num = bn * bn * (ad_ * cd_) + (-(4 * (an * cn))) * (bd_ * bd_);

        // Ghost variables for completing the square
        let ghost alpha = an * bd_ * cd_;
        let ghost beta = bn * ad_ * cd_;
        let ghost gamma = cn * ad_ * bd_;

        // Step 1: Factor expr.num as td * (alpha*tn² + beta*tn*td + gamma*td²)
        // Break into three terms
        let ghost t1 = ((an * (tn * tn)) * (bd_ * td_)) * cd_;
        assert(t1 == alpha * tn * tn * td_) by (nonlinear_arith)
            requires t1 == ((an * (tn * tn)) * (bd_ * td_)) * cd_,
                alpha == an * bd_ * cd_;

        let ghost t2 = ((bn * tn) * (ad_ * (td_ * td_))) * cd_;
        assert(t2 == beta * tn * td_ * td_) by (nonlinear_arith)
            requires t2 == ((bn * tn) * (ad_ * (td_ * td_))) * cd_,
                beta == bn * ad_ * cd_;

        let ghost t3 = cn * ((ad_ * (td_ * td_)) * (bd_ * td_));
        assert(t3 == gamma * td_ * td_ * td_) by (nonlinear_arith)
            requires t3 == cn * ((ad_ * (td_ * td_)) * (bd_ * td_)),
                gamma == cn * ad_ * bd_;

        // expr.num = t1 + t2 + t3
        assert(expr.num == t1 + t2 + t3) by (nonlinear_arith)
            requires
                expr.num == (att_bt.num) * cd_ + cn * att_bt.denom(),
                att_bt.num == (an * (tn * tn)) * (bd_ * td_) + (bn * tn) * (ad_ * (td_ * td_)),
                att_bt.denom() == (ad_ * (td_ * td_)) * (bd_ * td_),
                t1 == ((an * (tn * tn)) * (bd_ * td_)) * cd_,
                t2 == ((bn * tn) * (ad_ * (td_ * td_))) * cd_,
                t3 == cn * ((ad_ * (td_ * td_)) * (bd_ * td_));

        // Factor td_: expr.num = td_ * (alpha*tn² + beta*tn*td_ + gamma*td_²)
        let ghost inner = alpha * tn * tn + beta * tn * td_ + gamma * td_ * td_;
        assert(t1 + t2 + t3 == td_ * inner) by (nonlinear_arith)
            requires
                t1 == alpha * tn * tn * td_,
                t2 == beta * tn * td_ * td_,
                t3 == gamma * td_ * td_ * td_,
                inner == alpha * tn * tn + beta * tn * td_ + gamma * td_ * td_;

        // Since expr.num == 0 and td_ > 0: inner == 0
        assert(inner == 0) by (nonlinear_arith)
            requires expr.num == 0,
                expr.num == t1 + t2 + t3,
                t1 + t2 + t3 == td_ * inner,
                td_ > 0;

        // Step 2: Completing the square
        let ghost w = 2 * alpha * tn + beta * td_;

        // w² via FOIL: w = p + q where p = 2αtn, q = βtd
        let ghost w_sq = w * w;
        let ghost p = 2 * alpha * tn;
        let ghost q = beta * td_;
        let ghost pp = p * p;
        let ghost pq = p * q;
        let ghost qq = q * q;
        assert(w_sq == pp + 2 * pq + qq) by (nonlinear_arith)
            requires w == p + q, w_sq == w * w,
                pp == p * p, pq == p * q, qq == q * q;
        let ghost expand1 = 4 * alpha * alpha * tn * tn;
        let ghost expand2 = 4 * alpha * beta * tn * td_;
        let ghost expand3 = beta * beta * td_ * td_;
        assert(pp == expand1) by (nonlinear_arith)
            requires pp == p * p, p == 2 * alpha * tn,
                expand1 == 4 * alpha * alpha * tn * tn;
        assert(2 * pq == expand2) by (nonlinear_arith)
            requires pq == p * q, p == 2 * alpha * tn, q == beta * td_,
                expand2 == 4 * alpha * beta * tn * td_;
        assert(qq == expand3) by (nonlinear_arith)
            requires qq == q * q, q == beta * td_,
                expand3 == beta * beta * td_ * td_;
        assert(w_sq == expand1 + expand2 + expand3) by (nonlinear_arith)
            requires w_sq == pp + 2 * pq + qq,
                pp == expand1, 2 * pq == expand2, qq == expand3;

        // From inner == 0: 4*alpha*(alpha*tn² + beta*tn*td) = -4*alpha*gamma*td²
        let ghost four_alpha_inner_part = 4 * alpha * (alpha * tn * tn + beta * tn * td_);
        assert(four_alpha_inner_part == -(4 * alpha * gamma * td_ * td_))
            by (nonlinear_arith)
            requires
                inner == 0,
                inner == alpha * tn * tn + beta * tn * td_ + gamma * td_ * td_,
                four_alpha_inner_part == 4 * alpha * (alpha * tn * tn + beta * tn * td_);

        assert(expand1 + expand2 == four_alpha_inner_part) by (nonlinear_arith)
            requires
                expand1 == 4 * alpha * alpha * tn * tn,
                expand2 == 4 * alpha * beta * tn * td_,
                four_alpha_inner_part == 4 * alpha * (alpha * tn * tn + beta * tn * td_);

        assert(w_sq == expand3 - 4 * alpha * gamma * td_ * td_) by (nonlinear_arith)
            requires
                w_sq == expand1 + expand2 + expand3,
                expand1 + expand2 == four_alpha_inner_part,
                four_alpha_inner_part == -(4 * alpha * gamma * td_ * td_);

        assert(w_sq == (beta * beta - 4 * alpha * gamma) * td_ * td_)
            by (nonlinear_arith)
            requires
                w_sq == expand3 - 4 * alpha * gamma * td_ * td_,
                expand3 == beta * beta * td_ * td_;

        // Step 3: Show disc_num * ad_ * cd_ == beta² - 4*alpha*gamma
        // beta² = bn²*ad²*cd²
        let ghost beta_sq = beta * beta;
        assert(beta_sq == bn * bn * ad_ * ad_ * cd_ * cd_) by (nonlinear_arith)
            requires beta == bn * ad_ * cd_, beta_sq == beta * beta;

        // 4*alpha*gamma = 4*an*cn*ad*bd²*cd
        let ghost four_ag = 4 * alpha * gamma;
        assert(four_ag == 4 * an * cn * ad_ * bd_ * bd_ * cd_) by (nonlinear_arith)
            requires alpha == an * bd_ * cd_, gamma == cn * ad_ * bd_,
                four_ag == 4 * alpha * gamma;

        // First simplify disc_num to a flat form
        let ghost dn_flat = bn * bn * ad_ * cd_ - 4 * an * cn * bd_ * bd_;
        assert(disc_num == dn_flat) by (nonlinear_arith)
            requires
                disc_num == bn * bn * (ad_ * cd_) + (-(4 * (an * cn))) * (bd_ * bd_),
                dn_flat == bn * bn * ad_ * cd_ - 4 * an * cn * bd_ * bd_;

        // Now show dn_flat * ad_ * cd_ == beta_sq - four_ag
        // Split: dn_flat * ad_ * cd_ = bn²*ad_*cd_*ad_*cd_ - 4*an*cn*bd²*ad_*cd_
        let ghost part1 = bn * bn * ad_ * cd_ * ad_ * cd_;
        let ghost part2 = 4 * an * cn * bd_ * bd_ * ad_ * cd_;
        assert(dn_flat * ad_ * cd_ == part1 - part2) by (nonlinear_arith)
            requires dn_flat == bn * bn * ad_ * cd_ - 4 * an * cn * bd_ * bd_,
                part1 == bn * bn * ad_ * cd_ * ad_ * cd_,
                part2 == 4 * an * cn * bd_ * bd_ * ad_ * cd_;
        assert(part1 == beta_sq) by (nonlinear_arith)
            requires
                part1 == bn * bn * ad_ * cd_ * ad_ * cd_,
                beta_sq == bn * bn * ad_ * ad_ * cd_ * cd_;
        assert(part2 == four_ag) by (nonlinear_arith)
            requires
                part2 == 4 * an * cn * bd_ * bd_ * ad_ * cd_,
                four_ag == 4 * an * cn * ad_ * bd_ * bd_ * cd_;
        assert(disc_num * ad_ * cd_ == beta_sq - four_ag) by (nonlinear_arith)
            requires
                disc_num == dn_flat,
                dn_flat * ad_ * cd_ == part1 - part2,
                part1 == beta_sq, part2 == four_ag;

        // Step 4: Conclude disc_num ≥ 0
        assert(w_sq >= 0int) by (nonlinear_arith)
            requires w_sq == w * w;
        assert(disc_num * (ad_ * cd_ * td_ * td_) >= 0) by (nonlinear_arith)
            requires
                w_sq == (beta * beta - 4 * alpha * gamma) * td_ * td_,
                disc_num * ad_ * cd_ == beta_sq - four_ag,
                beta_sq == beta * beta,
                four_ag == 4 * alpha * gamma,
                w_sq >= 0int;
        assert(disc_num >= 0) by (nonlinear_arith)
            requires
                disc_num * (ad_ * cd_ * td_ * td_) >= 0,
                ad_ > 0, cd_ > 0, td_ > 0;

        // le_spec: from_int(0).le_spec(disc) ↔ 0 * disc.denom() <= disc.num * 1
        //        ↔ disc.num >= 0
        assert(disc.num == disc_num);
    }

    // ── Interval containment (item 23) ───────────────────────────────

    /// a ∈ [lo_a, hi_a] ∧ b ∈ [lo_b, hi_b] → a+b ∈ [lo_a+lo_b, hi_a+hi_b].
    pub proof fn lemma_add_interval(
        a: Self, lo_a: Self, hi_a: Self,
        b: Self, lo_b: Self, hi_b: Self,
    )
        requires
            lo_a.le_spec(a), a.le_spec(hi_a),
            lo_b.le_spec(b), b.le_spec(hi_b),
        ensures
            lo_a.add_spec(lo_b).le_spec(a.add_spec(b)),
            a.add_spec(b).le_spec(hi_a.add_spec(hi_b)),
    {
        Self::lemma_le_add_both(lo_a, a, lo_b, b);
        Self::lemma_le_add_both(a, hi_a, b, hi_b);
    }

    /// Both non-negative: a*b ∈ [lo_a*lo_b, hi_a*hi_b].
    pub proof fn lemma_mul_interval_nonneg(
        a: Self, lo_a: Self, hi_a: Self,
        b: Self, lo_b: Self, hi_b: Self,
    )
        requires
            Self::from_int_spec(0).le_spec(lo_a),
            lo_a.le_spec(a), a.le_spec(hi_a),
            Self::from_int_spec(0).le_spec(lo_b),
            lo_b.le_spec(b), b.le_spec(hi_b),
        ensures
            lo_a.mul_spec(lo_b).le_spec(a.mul_spec(b)),
            a.mul_spec(b).le_spec(hi_a.mul_spec(hi_b)),
    {
        let z = Self::from_int_spec(0);
        Self::lemma_le_transitive(z, lo_a, a);
        Self::lemma_le_transitive(z, lo_b, b);
        Self::lemma_le_mul_nonneg_both(lo_a, a, lo_b, b);
        Self::lemma_le_mul_nonneg_both(a, hi_a, b, hi_b);
    }

    /// lo ≤ hi → lo ≤ midpoint(lo, hi) ≤ hi.
    pub proof fn lemma_interval_contains_midpoint(lo: Self, hi: Self)
        requires
            lo.le_spec(hi),
        ensures
            lo.le_spec(Self::midpoint_spec(lo, hi)),
            Self::midpoint_spec(lo, hi).le_spec(hi),
    {
        Self::lemma_le_iff_lt_or_eqv(lo, hi);
        if lo.eqv_spec(hi) {
            Self::lemma_midpoint_eqv_self(lo);
            Self::lemma_eqv_symmetric(Self::midpoint_spec(lo, lo), lo);
            // midpoint(lo, hi) ≡ midpoint(lo, lo) ≡ lo
            // Need midpoint(lo, hi) when hi ≡ lo
            // midpoint_spec(lo, hi) = (lo + hi) * (1/2)
            // If lo ≡ hi, then lo + hi ≡ lo + lo, so midpoint(lo, hi) ≡ midpoint(lo, lo) ≡ lo
            Self::lemma_eqv_add_congruence_right(lo, hi, lo);
            let half = Rational { num: 1, den: 1 };
            Self::lemma_eqv_mul_congruence_left(lo.add_spec(hi), lo.add_spec(lo), half);
            // midpoint(lo,hi) ≡ midpoint(lo,lo) ≡ lo ≡ hi
            Self::lemma_eqv_transitive(
                Self::midpoint_spec(lo, hi),
                Self::midpoint_spec(lo, lo),
                lo,
            );
            Self::lemma_eqv_implies_le(lo, Self::midpoint_spec(lo, hi));
            Self::lemma_eqv_symmetric(Self::midpoint_spec(lo, hi), lo);
            Self::lemma_eqv_transitive(Self::midpoint_spec(lo, hi), lo, hi);
            Self::lemma_eqv_implies_le(Self::midpoint_spec(lo, hi), hi);
        } else {
            // lo < hi case
            Self::lemma_midpoint_between_left(lo, hi);
            Self::lemma_midpoint_between_right(lo, hi);
            Self::lemma_lt_implies_le(lo, Self::midpoint_spec(lo, hi));
            Self::lemma_lt_implies_le(Self::midpoint_spec(lo, hi), hi);
        }
    }

    // ── Cauchy-Schwarz squared form (item 24) ─────────────────────────

    /// (ac + bd)² ≤ (a² + b²)(c² + d²).
    pub proof fn lemma_cauchy_schwarz_2d(a: Self, b: Self, c: Self, d: Self)
        ensures
            a.mul_spec(c).add_spec(b.mul_spec(d))
                .mul_spec(a.mul_spec(c).add_spec(b.mul_spec(d)))
                .le_spec(
                    a.mul_spec(a).add_spec(b.mul_spec(b)).mul_spec(
                        c.mul_spec(c).add_spec(d.mul_spec(d)))),
    {
        // Cauchy-Schwarz: (ac+bd)² ≤ (a²+b²)(c²+d²)
        // Equivalently: (a²+b²)(c²+d²) - (ac+bd)² ≥ 0
        // Expansion: a²c² + a²d² + b²c² + b²d² - a²c² - 2abcd - b²d² = a²d² - 2abcd + b²c²
        // = (ad - bc)² ≥ 0
        // So this reduces to proving (ad - bc)² ≥ 0, which is lemma_square_le_nonneg.

        let ac = a.mul_spec(c);
        let bd = b.mul_spec(d);
        let dot = ac.add_spec(bd);
        let dot_sq = dot.mul_spec(dot);
        let aa = a.mul_spec(a);
        let bb = b.mul_spec(b);
        let cc = c.mul_spec(c);
        let dd = d.mul_spec(d);
        let norm_a = aa.add_spec(bb);
        let norm_c = cc.add_spec(dd);
        let prod = norm_a.mul_spec(norm_c);

        // (ad - bc)² ≥ 0
        let ad_ = a.mul_spec(d);
        let bc__ = b.mul_spec(c);
        let cross = ad_.sub_spec(bc__);
        Self::lemma_square_le_nonneg(cross);
        // cross² ≡ (ad)² - 2(ad)(bc) + (bc)²  by square_of_difference
        Self::lemma_square_of_difference(ad_, bc__);

        // prod - dot² ≡ cross² ≥ 0
        // This means prod ≥ dot².
        // The full algebraic proof that prod - dot² ≡ cross² is very involved.
        // It requires expanding both sides and showing they match.
        // For now, let me prove this at the numerator cross-multiplication level.

        // Actually, the cleanest proof: show prod ≡ dot² + cross²
        // Then since cross² ≥ 0, prod ≥ dot².

        // prod = (a²+b²)(c²+d²) = a²c² + a²d² + b²c² + b²d²
        // dot² = (ac+bd)² = a²c² + 2abcd + b²d²
        // cross² = (ad-bc)² = a²d² - 2abcd + b²c²
        // dot² + cross² = a²c² + 2abcd + b²d² + a²d² - 2abcd + b²c²
        //               = a²c² + a²d² + b²c² + b²d² = prod  ✓

        // Strategy: reduce to standard Cauchy-Schwarz in 4 ghost variables.
        // Key observation: dot_sq.denom() == prod.denom() (both = ad²bd²cd²dd²),
        // so le_spec reduces to dot.num² ≤ norm_a.num * norm_c.num.

        // Establish denom products
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_mul_denom_product_int(b, d);
        Self::lemma_mul_denom_product_int(a, a);
        Self::lemma_mul_denom_product_int(b, b);
        Self::lemma_mul_denom_product_int(c, c);
        Self::lemma_mul_denom_product_int(d, d);
        Self::lemma_add_denom_product_int(ac, bd);
        Self::lemma_add_denom_product_int(aa, bb);
        Self::lemma_add_denom_product_int(cc, dd);
        Self::lemma_mul_denom_product_int(dot, dot);
        Self::lemma_mul_denom_product_int(norm_a, norm_c);
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        Self::lemma_denom_positive(d);

        let ghost an = a.num;
        let ghost bn = b.num;
        let ghost cn = c.num;
        let ghost dn = d.num;
        let ghost ad_ = a.denom();
        let ghost bd_ = b.denom();
        let ghost cd_ = c.denom();
        let ghost dd_ = d.denom();

        // Ghost variables for the Cauchy-Schwarz reduction
        let ghost x1 = an * bd_;
        let ghost x2 = bn * ad_;
        let ghost y1 = cn * dd_;
        let ghost y2 = dn * cd_;

        // dot.num = x1*y1 + x2*y2 (break into two product identities)
        let ghost p1 = (an * cn) * (bd_ * dd_);
        let ghost p2 = (bn * dn) * (ad_ * cd_);
        assert(p1 == x1 * y1) by (nonlinear_arith)
            requires p1 == (an * cn) * (bd_ * dd_),
                x1 == an * bd_, y1 == cn * dd_;
        assert(p2 == x2 * y2) by (nonlinear_arith)
            requires p2 == (bn * dn) * (ad_ * cd_),
                x2 == bn * ad_, y2 == dn * cd_;
        assert(dot.num == x1 * y1 + x2 * y2) by (nonlinear_arith)
            requires
                dot.num == p1 + p2,
                p1 == x1 * y1, p2 == x2 * y2;

        // norm_a.num = x1² + x2²
        assert(norm_a.num == x1 * x1 + x2 * x2) by (nonlinear_arith)
            requires
                norm_a.num == (an * an) * (bd_ * bd_) + (bn * bn) * (ad_ * ad_),
                x1 == an * bd_, x2 == bn * ad_;

        // norm_c.num = y1² + y2²
        assert(norm_c.num == y1 * y1 + y2 * y2) by (nonlinear_arith)
            requires
                norm_c.num == (cn * cn) * (dd_ * dd_) + (dn * dn) * (cd_ * cd_),
                y1 == cn * dd_, y2 == dn * cd_;

        // Cauchy-Schwarz: (x1y1+x2y2)² ≤ (x1²+x2²)(y1²+y2²)
        // Proof: RHS - LHS = (x1y2 - x2y1)² ≥ 0
        let ghost z = x1 * y2 - x2 * y1;
        assert(z * z >= 0int) by (nonlinear_arith)
            requires z == x1 * y2 - x2 * y1;
        // Lagrange identity via aij = xi*yj decomposition
        let ghost a11 = x1 * y1;
        let ghost a12 = x1 * y2;
        let ghost a21 = x2 * y1;
        let ghost a22 = x2 * y2;
        // (x1²+x2²)(y1²+y2²) = a11²+a12²+a21²+a22² via distribution
        let ghost x1sq = x1 * x1;
        let ghost x2sq = x2 * x2;
        // x1² * nc = a11² + a12²
        assert(x1sq * norm_c.num == a11 * a11 + a12 * a12) by (nonlinear_arith)
            requires
                norm_c.num == y1 * y1 + y2 * y2,
                x1sq == x1 * x1,
                a11 == x1 * y1, a12 == x1 * y2;
        // x2² * nc = a21² + a22²
        assert(x2sq * norm_c.num == a21 * a21 + a22 * a22) by (nonlinear_arith)
            requires
                norm_c.num == y1 * y1 + y2 * y2,
                x2sq == x2 * x2,
                a21 == x2 * y1, a22 == x2 * y2;
        // na * nc = (x1²+x2²)*nc = x1²*nc + x2²*nc
        assert(norm_a.num * norm_c.num == a11 * a11 + a12 * a12 + a21 * a21 + a22 * a22)
            by (nonlinear_arith)
            requires
                norm_a.num == x1sq + x2sq,
                x1sq * norm_c.num == a11 * a11 + a12 * a12,
                x2sq * norm_c.num == a21 * a21 + a22 * a22,
                x1sq == x1 * x1, x2sq == x2 * x2;
        // a11*a22 == a12*a21 (both = x1*x2*y1*y2)
        assert(a11 * a22 == a12 * a21) by (nonlinear_arith)
            requires
                a11 == x1 * y1, a12 == x1 * y2,
                a21 == x2 * y1, a22 == x2 * y2;
        // dot² + z² = (a11+a22)² + (a12-a21)² = a11²+a12²+a21²+a22² + 2(a11*a22-a12*a21)
        let ghost dot_sq_val = dot.num * dot.num;
        let ghost sum_sq = a11 * a11 + a12 * a12 + a21 * a21 + a22 * a22;
        assert(dot_sq_val + z * z == sum_sq) by (nonlinear_arith)
            requires
                dot.num == a11 + a22,
                z == a12 - a21,
                dot_sq_val == dot.num * dot.num,
                sum_sq == a11 * a11 + a12 * a12 + a21 * a21 + a22 * a22,
                a11 * a22 == a12 * a21;
        assert(dot.num * dot.num <= norm_a.num * norm_c.num) by (nonlinear_arith)
            requires
                dot_sq_val == dot.num * dot.num,
                dot_sq_val + z * z == sum_sq,
                norm_a.num * norm_c.num == sum_sq,
                z * z >= 0int;

        // Show dot_sq.denom() == prod.denom()
        // Both equal ad²bd²cd²dd² (just different parenthesization)
        let ghost D1 = ad_ * cd_;
        let ghost D2 = bd_ * dd_;
        let ghost D1sq = D1 * D1;
        let ghost D2sq = D2 * D2;
        assert((D1 * D2) * (D1 * D2) == D1sq * D2sq) by (nonlinear_arith)
            requires D1sq == D1 * D1, D2sq == D2 * D2;
        assert(dot_sq.denom() == D1sq * D2sq) by (nonlinear_arith)
            requires
                dot_sq.denom() == dot.denom() * dot.denom(),
                dot.denom() == D1 * D2,
                D1sq == D1 * D1, D2sq == D2 * D2;

        let ghost na_d = ad_ * ad_ * (bd_ * bd_);
        let ghost nc_d = cd_ * cd_ * (dd_ * dd_);
        assert(prod.denom() == na_d * nc_d) by (nonlinear_arith)
            requires
                prod.denom() == norm_a.denom() * norm_c.denom(),
                norm_a.denom() == (ad_ * ad_) * (bd_ * bd_),
                norm_c.denom() == (cd_ * cd_) * (dd_ * dd_),
                na_d == ad_ * ad_ * (bd_ * bd_),
                nc_d == cd_ * cd_ * (dd_ * dd_);

        assert(D1sq * D2sq == na_d * nc_d) by (nonlinear_arith)
            requires
                D1sq == (ad_ * cd_) * (ad_ * cd_),
                D2sq == (bd_ * dd_) * (bd_ * dd_),
                na_d == ad_ * ad_ * (bd_ * bd_),
                nc_d == cd_ * cd_ * (dd_ * dd_),
                D1 == ad_ * cd_, D2 == bd_ * dd_;

        assert(dot_sq.denom() == prod.denom()) by (nonlinear_arith)
            requires
                dot_sq.denom() == D1sq * D2sq,
                prod.denom() == na_d * nc_d,
                D1sq * D2sq == na_d * nc_d;

        // prod.denom() > 0
        assert(prod.denom() > 0) by (nonlinear_arith)
            requires
                prod.denom() == na_d * nc_d,
                na_d == ad_ * ad_ * (bd_ * bd_),
                nc_d == cd_ * cd_ * (dd_ * dd_),
                ad_ > 0, bd_ > 0, cd_ > 0, dd_ > 0;

        // Final: since dot_sq.denom() == prod.denom() and
        // dot.num² ≤ norm_a.num * norm_c.num,
        // we get dot_sq.num * prod.denom() ≤ prod.num * dot_sq.denom()
        assert(dot_sq.num * prod.denom() <= prod.num * dot_sq.denom())
            by (nonlinear_arith)
            requires
                dot_sq.num == dot.num * dot.num,
                prod.num == norm_a.num * norm_c.num,
                dot_sq.denom() == prod.denom(),
                dot.num * dot.num <= norm_a.num * norm_c.num,
                prod.denom() > 0;
    }

    /// Helper: norm.num == v1² + v2² + v3² given rational add/mul structure.
    proof fn lemma_norm_num_sum_squares_3d(
        norm_num: int, ab_num: int, ab_D: int,
        xn: int, yn: int, zn: int,
        dx: int, dy: int, dz: int,
    )
        requires
            norm_num == ab_num * (dz * dz) + (zn * zn) * ab_D,
            ab_num == (xn * xn) * (dy * dy) + (yn * yn) * (dx * dx),
            ab_D == (dx * dx) * (dy * dy),
        ensures
            norm_num == (xn * dy * dz) * (xn * dy * dz)
                + (yn * dx * dz) * (yn * dx * dz)
                + (zn * dx * dy) * (zn * dx * dy),
    {
        let ghost v1 = xn * dy * dz;
        let ghost v2 = yn * dx * dz;
        let ghost v3 = zn * dx * dy;

        let ghost t1 = ((xn * xn) * (dy * dy)) * (dz * dz);
        let ghost t2 = ((yn * yn) * (dx * dx)) * (dz * dz);
        let ghost t3 = (zn * zn) * ((dx * dx) * (dy * dy));
        assert(t1 == v1 * v1) by (nonlinear_arith)
            requires t1 == ((xn * xn) * (dy * dy)) * (dz * dz),
                v1 == xn * dy * dz;
        assert(t2 == v2 * v2) by (nonlinear_arith)
            requires t2 == ((yn * yn) * (dx * dx)) * (dz * dz),
                v2 == yn * dx * dz;
        assert(t3 == v3 * v3) by (nonlinear_arith)
            requires t3 == (zn * zn) * ((dx * dx) * (dy * dy)),
                v3 == zn * dx * dy;

        assert(norm_num == t1 + t2 + t3) by (nonlinear_arith)
            requires
                norm_num == ab_num * (dz * dz) + (zn * zn) * ab_D,
                ab_num == (xn * xn) * (dy * dy) + (yn * yn) * (dx * dx),
                ab_D == (dx * dx) * (dy * dy),
                t1 == ((xn * xn) * (dy * dy)) * (dz * dz),
                t2 == ((yn * yn) * (dx * dx)) * (dz * dz),
                t3 == (zn * zn) * ((dx * dx) * (dy * dy));

        assert(norm_num == v1 * v1 + v2 * v2 + v3 * v3) by (nonlinear_arith)
            requires norm_num == t1 + t2 + t3,
                t1 == v1 * v1, t2 == v2 * v2, t3 == v3 * v3;
    }

    /// Helper: Lagrange identity — dot² + z1² + z2² + z3² = sum of all aij².
    proof fn lemma_lagrange_identity_3d(
        a11: int, a12: int, a13: int,
        a21: int, a22: int, a23: int,
        a31: int, a32: int, a33: int,
        dot_num: int,
    )
        requires
            dot_num == a11 + a22 + a33,
            a11 * a22 == a12 * a21,
            a11 * a33 == a13 * a31,
            a22 * a33 == a23 * a32,
        ensures
            dot_num * dot_num + (a12 - a21)*(a12 - a21)
                + (a13 - a31)*(a13 - a31) + (a23 - a32)*(a23 - a32)
                == a11*a11 + a12*a12 + a13*a13
                    + a21*a21 + a22*a22 + a23*a23
                    + a31*a31 + a32*a32 + a33*a33,
            (a12 - a21)*(a12 - a21) >= 0int,
            (a13 - a31)*(a13 - a31) >= 0int,
            (a23 - a32)*(a23 - a32) >= 0int,
    {
        let ghost z1 = a12 - a21;
        let ghost z2 = a13 - a31;
        let ghost z3 = a23 - a32;
        let ghost dot_sq_val = dot_num * dot_num;

        let ghost diag_sq = a11*a11 + a22*a22 + a33*a33;
        let ghost cross_diag = 2 * (a11*a22 + a11*a33 + a22*a33);
        assert(dot_sq_val == diag_sq + cross_diag) by (nonlinear_arith)
            requires
                dot_num == a11 + a22 + a33,
                dot_sq_val == dot_num * dot_num,
                diag_sq == a11*a11 + a22*a22 + a33*a33,
                cross_diag == 2 * (a11*a22 + a11*a33 + a22*a33);

        let ghost off_diag_sq = a12*a12 + a21*a21 + a13*a13 + a31*a31 + a23*a23 + a32*a32;
        let ghost cross_off = 2 * (a12*a21 + a13*a31 + a23*a32);
        assert(z1*z1 + z2*z2 + z3*z3 == off_diag_sq - cross_off) by (nonlinear_arith)
            requires
                z1 == a12 - a21, z2 == a13 - a31, z3 == a23 - a32,
                off_diag_sq == a12*a12 + a21*a21 + a13*a13 + a31*a31 + a23*a23 + a32*a32,
                cross_off == 2 * (a12*a21 + a13*a31 + a23*a32);

        assert(cross_diag == cross_off) by (nonlinear_arith)
            requires
                cross_diag == 2 * (a11*a22 + a11*a33 + a22*a33),
                cross_off == 2 * (a12*a21 + a13*a31 + a23*a32),
                a11 * a22 == a12 * a21,
                a11 * a33 == a13 * a31,
                a22 * a33 == a23 * a32;

        let ghost sum_sq = a11*a11 + a12*a12 + a13*a13
            + a21*a21 + a22*a22 + a23*a23
            + a31*a31 + a32*a32 + a33*a33;

        assert(dot_sq_val + z1*z1 + z2*z2 + z3*z3 == sum_sq) by (nonlinear_arith)
            requires
                dot_sq_val == diag_sq + cross_diag,
                z1*z1 + z2*z2 + z3*z3 == off_diag_sq - cross_off,
                cross_diag == cross_off,
                sum_sq == a11*a11 + a12*a12 + a13*a13
                    + a21*a21 + a22*a22 + a23*a23
                    + a31*a31 + a32*a32 + a33*a33,
                diag_sq == a11*a11 + a22*a22 + a33*a33,
                off_diag_sq == a12*a12 + a21*a21 + a13*a13 + a31*a31 + a23*a23 + a32*a32;

        assert(z1*z1 >= 0int) by (nonlinear_arith);
        assert(z2*z2 >= 0int) by (nonlinear_arith);
        assert(z3*z3 >= 0int) by (nonlinear_arith);
    }

    /// Integer Cauchy-Schwarz: (x1y1+x2y2+x3y3)² ≤ (x1²+x2²+x3²)(y1²+y2²+y3²).
    proof fn lemma_cauchy_schwarz_int_3d(
        norm_l_num: int, norm_r_num: int, dot_num: int,
        x1: int, x2: int, x3: int,
        y1: int, y2: int, y3: int,
    )
        requires
            norm_l_num == x1*x1 + x2*x2 + x3*x3,
            norm_r_num == y1*y1 + y2*y2 + y3*y3,
            dot_num == x1*y1 + x2*y2 + x3*y3,
        ensures
            dot_num * dot_num <= norm_l_num * norm_r_num,
    {
        let ghost a11 = x1 * y1;
        let ghost a12 = x1 * y2;
        let ghost a13 = x1 * y3;
        let ghost a21 = x2 * y1;
        let ghost a22 = x2 * y2;
        let ghost a23 = x2 * y3;
        let ghost a31 = x3 * y1;
        let ghost a32 = x3 * y2;
        let ghost a33 = x3 * y3;

        let ghost x1sq = x1 * x1;
        let ghost x2sq = x2 * x2;
        let ghost x3sq = x3 * x3;
        let ghost y1sq = y1 * y1;
        let ghost y2sq = y2 * y2;
        let ghost y3sq = y3 * y3;

        // Distribution: decompose xi² * yj² = aij² first, then combine
        assert(x1sq * y1sq == a11*a11) by (nonlinear_arith)
            requires x1sq == x1*x1, y1sq == y1*y1, a11 == x1*y1;
        assert(x1sq * y2sq == a12*a12) by (nonlinear_arith)
            requires x1sq == x1*x1, y2sq == y2*y2, a12 == x1*y2;
        assert(x1sq * y3sq == a13*a13) by (nonlinear_arith)
            requires x1sq == x1*x1, y3sq == y3*y3, a13 == x1*y3;
        assert(x1sq * norm_r_num == a11*a11 + a12*a12 + a13*a13)
            by (nonlinear_arith)
            requires norm_r_num == y1sq + y2sq + y3sq,
                x1sq * y1sq == a11*a11, x1sq * y2sq == a12*a12,
                x1sq * y3sq == a13*a13;

        assert(x2sq * y1sq == a21*a21) by (nonlinear_arith)
            requires x2sq == x2*x2, y1sq == y1*y1, a21 == x2*y1;
        assert(x2sq * y2sq == a22*a22) by (nonlinear_arith)
            requires x2sq == x2*x2, y2sq == y2*y2, a22 == x2*y2;
        assert(x2sq * y3sq == a23*a23) by (nonlinear_arith)
            requires x2sq == x2*x2, y3sq == y3*y3, a23 == x2*y3;
        assert(x2sq * norm_r_num == a21*a21 + a22*a22 + a23*a23)
            by (nonlinear_arith)
            requires norm_r_num == y1sq + y2sq + y3sq,
                x2sq * y1sq == a21*a21, x2sq * y2sq == a22*a22,
                x2sq * y3sq == a23*a23;

        assert(x3sq * y1sq == a31*a31) by (nonlinear_arith)
            requires x3sq == x3*x3, y1sq == y1*y1, a31 == x3*y1;
        assert(x3sq * y2sq == a32*a32) by (nonlinear_arith)
            requires x3sq == x3*x3, y2sq == y2*y2, a32 == x3*y2;
        assert(x3sq * y3sq == a33*a33) by (nonlinear_arith)
            requires x3sq == x3*x3, y3sq == y3*y3, a33 == x3*y3;
        assert(x3sq * norm_r_num == a31*a31 + a32*a32 + a33*a33)
            by (nonlinear_arith)
            requires norm_r_num == y1sq + y2sq + y3sq,
                x3sq * y1sq == a31*a31, x3sq * y2sq == a32*a32,
                x3sq * y3sq == a33*a33;

        let ghost sum_sq = a11*a11 + a12*a12 + a13*a13
            + a21*a21 + a22*a22 + a23*a23
            + a31*a31 + a32*a32 + a33*a33;
        assert(norm_l_num * norm_r_num == sum_sq) by (nonlinear_arith)
            requires
                norm_l_num == x1sq + x2sq + x3sq,
                x1sq * norm_r_num == a11*a11 + a12*a12 + a13*a13,
                x2sq * norm_r_num == a21*a21 + a22*a22 + a23*a23,
                x3sq * norm_r_num == a31*a31 + a32*a32 + a33*a33,
                sum_sq == a11*a11 + a12*a12 + a13*a13
                    + a21*a21 + a22*a22 + a23*a23
                    + a31*a31 + a32*a32 + a33*a33;

        // Cross equalities
        assert(a11 * a22 == a12 * a21) by (nonlinear_arith)
            requires a11==x1*y1, a22==x2*y2, a12==x1*y2, a21==x2*y1;
        assert(a11 * a33 == a13 * a31) by (nonlinear_arith)
            requires a11==x1*y1, a33==x3*y3, a13==x1*y3, a31==x3*y1;
        assert(a22 * a33 == a23 * a32) by (nonlinear_arith)
            requires a22==x2*y2, a33==x3*y3, a23==x2*y3, a32==x3*y2;

        // Lagrange identity
        Self::lemma_lagrange_identity_3d(
            a11, a12, a13, a21, a22, a23, a31, a32, a33, dot_num,
        );

        // Final: dot² ≤ norm_l * norm_r
        assert(dot_num * dot_num <= norm_l_num * norm_r_num) by (nonlinear_arith)
            requires
                dot_num * dot_num + (a12 - a21)*(a12 - a21)
                    + (a13 - a31)*(a13 - a31) + (a23 - a32)*(a23 - a32)
                    == a11*a11 + a12*a12 + a13*a13
                        + a21*a21 + a22*a22 + a23*a23
                        + a31*a31 + a32*a32 + a33*a33,
                norm_l_num * norm_r_num == sum_sq,
                sum_sq == a11*a11 + a12*a12 + a13*a13
                    + a21*a21 + a22*a22 + a23*a23
                    + a31*a31 + a32*a32 + a33*a33,
                (a12 - a21)*(a12 - a21) >= 0int,
                (a13 - a31)*(a13 - a31) >= 0int,
                (a23 - a32)*(a23 - a32) >= 0int;
    }

    /// Helper: ((da*dd_)*(db*de)*(dc*df))² == (da²*db²*dc²)*(dd_²*de²*df²).
    proof fn lemma_denom_sq_three_factors(
        da: int, db: int, dc: int, dd_: int, de: int, df: int,
    )
        ensures
            ((da * dd_) * (db * de) * (dc * df))
                * ((da * dd_) * (db * de) * (dc * df))
                == ((da * da) * (db * db) * (dc * dc))
                    * ((dd_ * dd_) * (de * de) * (df * df)),
    {
        let ghost g1 = da * dd_;
        let ghost g2 = db * de;
        let ghost g3 = dc * df;
        let ghost D_dot = (da * dd_) * (db * de) * (dc * df);
        let ghost Dsq = D_dot * D_dot;
        let ghost nl_d = (da * da) * (db * db) * (dc * dc);
        let ghost nr_d = (dd_ * dd_) * (de * de) * (df * df);

        assert(D_dot == g1 * g2 * g3) by (nonlinear_arith)
            requires D_dot == (da * dd_) * (db * de) * (dc * df),
                g1 == da * dd_, g2 == db * de, g3 == dc * df;
        let ghost g1s = g1 * g1;
        let ghost g2s = g2 * g2;
        let ghost g3s = g3 * g3;
        let ghost g12 = g1 * g2;
        assert(D_dot == g12 * g3) by (nonlinear_arith)
            requires D_dot == g1 * g2 * g3, g12 == g1 * g2;
        let ghost g12s = g12 * g12;
        assert(Dsq == g12s * g3s) by (nonlinear_arith)
            requires Dsq == D_dot * D_dot, D_dot == g12 * g3,
                g12s == g12 * g12, g3s == g3 * g3;
        assert(g12s == g1s * g2s) by (nonlinear_arith)
            requires g12s == g12 * g12, g12 == g1 * g2,
                g1s == g1 * g1, g2s == g2 * g2;
        assert(Dsq == g1s * g2s * g3s) by (nonlinear_arith)
            requires Dsq == g12s * g3s, g12s == g1s * g2s;

        assert(g1s == da * da * (dd_ * dd_)) by (nonlinear_arith)
            requires g1s == g1 * g1, g1 == da * dd_;
        assert(g2s == db * db * (de * de)) by (nonlinear_arith)
            requires g2s == g2 * g2, g2 == db * de;
        assert(g3s == dc * dc * (df * df)) by (nonlinear_arith)
            requires g3s == g3 * g3, g3 == dc * df;

        let ghost da2 = da * da;
        let ghost db2 = db * db;
        let ghost dc2 = dc * dc;
        let ghost dd2 = dd_ * dd_;
        let ghost de2 = de * de;
        let ghost df2 = df * df;
        let ghost nl_nr = nl_d * nr_d;
        assert(nl_d == da2 * db2 * dc2) by (nonlinear_arith)
            requires nl_d == (da * da) * (db * db) * (dc * dc),
                da2 == da * da, db2 == db * db, dc2 == dc * dc;
        assert(nr_d == dd2 * de2 * df2) by (nonlinear_arith)
            requires nr_d == (dd_ * dd_) * (de * de) * (df * df),
                dd2 == dd_ * dd_, de2 == de * de, df2 == df * df;
        let ghost h12 = g1s * g2s;
        assert(h12 == da2 * dd2 * db2 * de2) by (nonlinear_arith)
            requires h12 == g1s * g2s,
                g1s == da2 * dd2, g2s == db2 * de2;
        let ghost h123 = h12 * g3s;
        assert(h123 == da2 * dd2 * db2 * de2 * dc2 * df2) by (nonlinear_arith)
            requires h123 == h12 * g3s,
                h12 == da2 * dd2 * db2 * de2,
                g3s == dc2 * df2;
        let ghost nl_nr_flat = da2 * db2 * dc2 * dd2 * de2 * df2;
        assert(nl_nr == nl_nr_flat) by (nonlinear_arith)
            requires nl_nr == nl_d * nr_d,
                nl_d == da2 * db2 * dc2,
                nr_d == dd2 * de2 * df2,
                nl_nr_flat == da2 * db2 * dc2 * dd2 * de2 * df2;
        assert(h123 == nl_nr_flat) by (nonlinear_arith)
            requires
                h123 == da2 * dd2 * db2 * de2 * dc2 * df2,
                nl_nr_flat == da2 * db2 * dc2 * dd2 * de2 * df2;
        assert(nl_d * nr_d == g1s * g2s * g3s) by (nonlinear_arith)
            requires nl_nr == nl_nr_flat, h123 == nl_nr_flat,
                h123 == h12 * g3s, h12 == g1s * g2s, nl_nr == nl_d * nr_d;

        assert(Dsq == nl_d * nr_d) by (nonlinear_arith)
            requires Dsq == g1s * g2s * g3s,
                nl_d * nr_d == g1s * g2s * g3s;
    }

    /// (a*d + b*e + c*f)² ≤ (a² + b² + c²)(d² + e² + f²).
    pub proof fn lemma_cauchy_schwarz_3d(
        a: Self, b: Self, c: Self, d: Self, e: Self, f: Self,
    )
        ensures
            a.mul_spec(d).add_spec(b.mul_spec(e)).add_spec(c.mul_spec(f))
                .mul_spec(
                    a.mul_spec(d).add_spec(b.mul_spec(e)).add_spec(c.mul_spec(f)))
                .le_spec(
                    a.mul_spec(a).add_spec(b.mul_spec(b)).add_spec(c.mul_spec(c))
                        .mul_spec(
                            d.mul_spec(d).add_spec(e.mul_spec(e)).add_spec(f.mul_spec(f)))),
    {
        // Build the dot product: dot = a*d + b*e + c*f
        let ad_ = a.mul_spec(d);
        let be = b.mul_spec(e);
        let cf = c.mul_spec(f);
        let ad_be = ad_.add_spec(be);
        let dot = ad_be.add_spec(cf);
        let dot_sq = dot.mul_spec(dot);

        // Build the norms
        let aa = a.mul_spec(a);
        let bb = b.mul_spec(b);
        let cc = c.mul_spec(c);
        let dd = d.mul_spec(d);
        let ee = e.mul_spec(e);
        let ff = f.mul_spec(f);
        let aa_bb = aa.add_spec(bb);
        let norm_l = aa_bb.add_spec(cc);
        let dd_ee = dd.add_spec(ee);
        let norm_r = dd_ee.add_spec(ff);
        let prod = norm_l.mul_spec(norm_r);

        // Establish denom products
        Self::lemma_mul_denom_product_int(a, d);
        Self::lemma_mul_denom_product_int(b, e);
        Self::lemma_mul_denom_product_int(c, f);
        Self::lemma_add_denom_product_int(ad_, be);
        Self::lemma_add_denom_product_int(ad_be, cf);
        Self::lemma_mul_denom_product_int(a, a);
        Self::lemma_mul_denom_product_int(b, b);
        Self::lemma_mul_denom_product_int(c, c);
        Self::lemma_mul_denom_product_int(d, d);
        Self::lemma_mul_denom_product_int(e, e);
        Self::lemma_mul_denom_product_int(f, f);
        Self::lemma_add_denom_product_int(aa, bb);
        Self::lemma_add_denom_product_int(aa_bb, cc);
        Self::lemma_add_denom_product_int(dd, ee);
        Self::lemma_add_denom_product_int(dd_ee, ff);
        Self::lemma_mul_denom_product_int(dot, dot);
        Self::lemma_mul_denom_product_int(norm_l, norm_r);
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        Self::lemma_denom_positive(d);
        Self::lemma_denom_positive(e);
        Self::lemma_denom_positive(f);

        let ghost an = a.num;
        let ghost bn = b.num;
        let ghost cn = c.num;
        let ghost dn = d.num;
        let ghost en_ = e.num;
        let ghost fn_ = f.num;
        let ghost da = a.denom();
        let ghost db = b.denom();
        let ghost dc = c.denom();
        let ghost dd_ = d.denom();
        let ghost de = e.denom();
        let ghost df = f.denom();

        // Ghost variables for the 3D Cauchy-Schwarz reduction
        let ghost x1 = an * db * dc;
        let ghost x2 = bn * da * dc;
        let ghost x3 = cn * da * db;
        let ghost y1 = dn * de * df;
        let ghost y2 = en_ * dd_ * df;
        let ghost y3 = fn_ * dd_ * de;

        // ── Show dot.num = x1*y1 + x2*y2 + x3*y3 ──
        let ghost p1 = ((an * dn) * (db * de)) * (dc * df);
        assert(p1 == x1 * y1) by (nonlinear_arith)
            requires p1 == ((an * dn) * (db * de)) * (dc * df),
                x1 == an * db * dc, y1 == dn * de * df;

        let ghost p2 = ((bn * en_) * (da * dd_)) * (dc * df);
        assert(p2 == x2 * y2) by (nonlinear_arith)
            requires p2 == ((bn * en_) * (da * dd_)) * (dc * df),
                x2 == bn * da * dc, y2 == en_ * dd_ * df;

        let ghost p3 = (cn * fn_) * ((da * dd_) * (db * de));
        assert(p3 == x3 * y3) by (nonlinear_arith)
            requires p3 == (cn * fn_) * ((da * dd_) * (db * de)),
                x3 == cn * da * db, y3 == fn_ * dd_ * de;

        assert(dot.num == p1 + p2 + p3) by (nonlinear_arith)
            requires
                dot.num == ad_be.num * (dc * df) + (cn * fn_) * ad_be.denom(),
                ad_be.num == (an * dn) * (db * de) + (bn * en_) * (da * dd_),
                ad_be.denom() == (da * dd_) * (db * de),
                p1 == ((an * dn) * (db * de)) * (dc * df),
                p2 == ((bn * en_) * (da * dd_)) * (dc * df),
                p3 == (cn * fn_) * ((da * dd_) * (db * de));

        assert(dot.num == x1 * y1 + x2 * y2 + x3 * y3) by (nonlinear_arith)
            requires dot.num == p1 + p2 + p3,
                p1 == x1 * y1, p2 == x2 * y2, p3 == x3 * y3;

        // ── norm_l.num = x1² + x2² + x3² ──
        Self::lemma_norm_num_sum_squares_3d(
            norm_l.num, aa_bb.num, aa_bb.denom(),
            an, bn, cn, da, db, dc,
        );

        // ── norm_r.num = y1² + y2² + y3² ──
        Self::lemma_norm_num_sum_squares_3d(
            norm_r.num, dd_ee.num, dd_ee.denom(),
            dn, en_, fn_, dd_, de, df,
        );

        // ── Integer Cauchy-Schwarz: dot² ≤ norm_l * norm_r ──
        Self::lemma_cauchy_schwarz_int_3d(
            norm_l.num, norm_r.num, dot.num,
            x1, x2, x3, y1, y2, y3,
        );

        // ── Show dot_sq.denom() == prod.denom() ──
        // dot.denom() = (da*dd_)*(db*de)*(dc*df)
        // dot_sq.denom() = dot.denom()²
        // prod.denom() = norm_l.denom() * norm_r.denom()
        //              = (da²*db²*dc²) * (dd_²*de²*df²)
        let ghost D_dot = (da * dd_) * (db * de) * (dc * df);
        assert(dot.denom() == D_dot) by (nonlinear_arith)
            requires
                dot.denom() == ad_be.denom() * (dc * df),
                ad_be.denom() == (da * dd_) * (db * de),
                D_dot == (da * dd_) * (db * de) * (dc * df);

        let ghost Dsq = D_dot * D_dot;
        assert(dot_sq.denom() == Dsq) by (nonlinear_arith)
            requires
                dot_sq.denom() == dot.denom() * dot.denom(),
                dot.denom() == D_dot,
                Dsq == D_dot * D_dot;

        let ghost nl_d = (da * da) * (db * db) * (dc * dc);
        assert(norm_l.denom() == nl_d) by (nonlinear_arith)
            requires
                norm_l.denom() == aa_bb.denom() * (dc * dc),
                aa_bb.denom() == (da * da) * (db * db),
                nl_d == (da * da) * (db * db) * (dc * dc);

        let ghost nr_d = (dd_ * dd_) * (de * de) * (df * df);
        assert(norm_r.denom() == nr_d) by (nonlinear_arith)
            requires
                norm_r.denom() == dd_ee.denom() * (df * df),
                dd_ee.denom() == (dd_ * dd_) * (de * de),
                nr_d == (dd_ * dd_) * (de * de) * (df * df);

        assert(prod.denom() == nl_d * nr_d) by (nonlinear_arith)
            requires
                prod.denom() == norm_l.denom() * norm_r.denom(),
                norm_l.denom() == nl_d, norm_r.denom() == nr_d;

        // Dsq == nl_d * nr_d via helper
        Self::lemma_denom_sq_three_factors(da, db, dc, dd_, de, df);

        assert(dot_sq.denom() == prod.denom()) by (nonlinear_arith)
            requires
                dot_sq.denom() == Dsq,
                prod.denom() == nl_d * nr_d,
                Dsq == D_dot * D_dot,
                D_dot == (da * dd_) * (db * de) * (dc * df),
                ((da * dd_) * (db * de) * (dc * df))
                    * ((da * dd_) * (db * de) * (dc * df))
                    == nl_d * nr_d;

        // prod.denom() > 0
        assert(prod.denom() > 0) by (nonlinear_arith)
            requires
                prod.denom() == nl_d * nr_d,
                nl_d == (da * da) * (db * db) * (dc * dc),
                nr_d == (dd_ * dd_) * (de * de) * (df * df),
                da > 0, db > 0, dc > 0, dd_ > 0, de > 0, df > 0;

        // Final: dot_sq.num * prod.denom() ≤ prod.num * dot_sq.denom()
        assert(dot_sq.num * prod.denom() <= prod.num * dot_sq.denom())
            by (nonlinear_arith)
            requires
                dot_sq.num == dot.num * dot.num,
                prod.num == norm_l.num * norm_r.num,
                dot_sq.denom() == prod.denom(),
                dot.num * dot.num <= norm_l.num * norm_r.num,
                prod.denom() > 0;
    }

}

} // verus!
