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

}

} // verus!
