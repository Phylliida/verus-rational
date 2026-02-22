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
    // ── Trichotomy and ordering ───────────────────────────────────────

    /// No rational is strictly less than itself.
    pub proof fn lemma_lt_irreflexive(a: Self)
        ensures
            !a.lt_spec(a),
    {
        Self::lemma_denom_positive(a);
        // a.lt_spec(a) == (a.num * a.denom() < a.num * a.denom()), trivially false
    }

    /// Strict less-than is asymmetric.
    pub proof fn lemma_lt_asymmetric(a: Self, b: Self)
        requires
            a.lt_spec(b),
        ensures
            !b.lt_spec(a),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        // a.num * b.denom() < b.num * a.denom()
        // so !(b.num * a.denom() < a.num * b.denom())
    }

    /// Strict less-than is transitive.
    pub proof fn lemma_lt_transitive(a: Self, b: Self, c: Self)
        requires
            a.lt_spec(b),
            b.lt_spec(c),
        ensures
            a.lt_spec(c),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        let da = a.denom();
        let db = b.denom();
        let dc = c.denom();
        // a.num * db < b.num * da
        // b.num * dc < c.num * db
        // Multiply first by dc (> 0): a.num * db * dc < b.num * da * dc
        // Multiply second by da (> 0): b.num * dc * da < c.num * db * da
        // b.num * da * dc == b.num * dc * da, so by int transitivity:
        //   a.num * db * dc < c.num * db * da
        // db > 0, so divide: a.num * dc < c.num * da
        assert(
            (a.num * db < b.num * da && b.num * dc < c.num * db
                && da > 0 && db > 0 && dc > 0)
            ==> a.num * dc < c.num * da
        ) by (nonlinear_arith);
    }

    /// Exactly one of `a < b`, `a ≡ b`, `b < a` holds.
    pub proof fn lemma_trichotomy(a: Self, b: Self)
        ensures
            a.lt_spec(b) || a.eqv_spec(b) || b.lt_spec(a),
            !(a.lt_spec(b) && a.eqv_spec(b)),
            !(a.lt_spec(b) && b.lt_spec(a)),
            !(a.eqv_spec(b) && b.lt_spec(a)),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        // All three predicates compare a.num * b.denom() vs b.num * a.denom(),
        // which are plain integers — trichotomy is immediate.
    }

    /// le is equivalent to lt-or-eqv.
    pub proof fn lemma_le_iff_lt_or_eqv(a: Self, b: Self)
        ensures
            a.le_spec(b) == (a.lt_spec(b) || a.eqv_spec(b)),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
    }

    /// Strict less-than implies le.
    pub proof fn lemma_lt_implies_le(a: Self, b: Self)
        requires
            a.lt_spec(b),
        ensures
            a.le_spec(b),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
    }

    /// Equivalence implies le (in both directions).
    pub proof fn lemma_eqv_implies_le(a: Self, b: Self)
        requires
            a.eqv_spec(b),
        ensures
            a.le_spec(b),
            b.le_spec(a),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
    }

    /// Antisymmetry: le in both directions implies equivalence.
    pub proof fn lemma_le_antisymmetric(a: Self, b: Self)
        requires
            a.le_spec(b),
            b.le_spec(a),
        ensures
            a.eqv_spec(b),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
    }

    /// le is transitive.
    pub proof fn lemma_le_transitive(a: Self, b: Self, c: Self)
        requires
            a.le_spec(b),
            b.le_spec(c),
        ensures
            a.le_spec(c),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        let da = a.denom();
        let db = b.denom();
        let dc = c.denom();
        assert(
            (a.num * db <= b.num * da && b.num * dc <= c.num * db
                && da > 0 && db > 0 && dc > 0)
            ==> a.num * dc <= c.num * da
        ) by (nonlinear_arith);
    }

    /// Mixed transitivity: a ≤ b ∧ b < c → a < c.
    pub proof fn lemma_le_lt_transitive(a: Self, b: Self, c: Self)
        requires
            a.le_spec(b),
            b.lt_spec(c),
        ensures
            a.lt_spec(c),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        assert(
            (a.num * b.denom() <= b.num * a.denom()
                && b.num * c.denom() < c.num * b.denom()
                && a.denom() > 0 && b.denom() > 0 && c.denom() > 0)
            ==> a.num * c.denom() < c.num * a.denom()
        ) by (nonlinear_arith);
    }

    /// Mixed transitivity: a < b ∧ b ≤ c → a < c.
    pub proof fn lemma_lt_le_transitive(a: Self, b: Self, c: Self)
        requires
            a.lt_spec(b),
            b.le_spec(c),
        ensures
            a.lt_spec(c),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        assert(
            (a.num * b.denom() < b.num * a.denom()
                && b.num * c.denom() <= c.num * b.denom()
                && a.denom() > 0 && b.denom() > 0 && c.denom() > 0)
            ==> a.num * c.denom() < c.num * a.denom()
        ) by (nonlinear_arith);
    }

    // ── Square non-negativity ───────────────────────────────────────

    /// The square of any rational is non-negative.
    pub proof fn lemma_square_nonneg(a: Self)
        ensures
            a.mul_spec(a).signum() >= 0,
    {
        let sq = a.mul_spec(a);
        assert(sq.num == a.num * a.num);
        assert(a.num * a.num >= 0) by (nonlinear_arith);
        if a.num == 0 {
            assert(sq.num == 0);
            assert(sq.signum() == 0);
        } else {
            assert((a.num != 0) ==> a.num * a.num > 0) by (nonlinear_arith);
            assert(sq.num > 0);
            assert(sq.signum() == 1);
        }
    }

    /// The square of any rational is le-nonneg: from_int(0) ≤ a*a.
    pub proof fn lemma_square_le_nonneg(a: Self)
        ensures
            Self::from_int_spec(0).le_spec(a.mul_spec(a)),
    {
        let z = Self::from_int_spec(0);
        let sq = a.mul_spec(a);
        Self::lemma_denom_positive(sq);
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(sq.num == a.num * a.num);
        assert(a.num * a.num >= 0) by (nonlinear_arith);
        assert(z.le_spec(sq) == (z.num * sq.denom() <= sq.num * z.denom()));
        assert((z.num == 0) ==> z.num * sq.denom() == 0) by (nonlinear_arith);
        assert(z.num * sq.denom() == 0);
        assert((z.denom() == 1) ==> sq.num * z.denom() == sq.num) by (nonlinear_arith);
        assert(sq.num * z.denom() == sq.num);
        assert(0 <= sq.num);
    }

    // ── Integer embedding ───────────────────────────────────────────

    /// Helper: from_int produces denom() == 1.
    pub proof fn lemma_from_int_denom(m: int)
        ensures
            Self::from_int_spec(m).denom() == 1,
            Self::from_int_spec(m).num == m,
    {
    }

    /// Integer embedding preserves strict ordering.
    pub proof fn lemma_from_int_preserves_lt(m: int, n: int)
        requires
            m < n,
        ensures
            Self::from_int_spec(m).lt_spec(Self::from_int_spec(n)),
    {
        let a = Self::from_int_spec(m);
        let b = Self::from_int_spec(n);
        // a.num * b.denom() < b.num * a.denom()
        // m * 1 < n * 1
        Self::lemma_from_int_denom(m);
        Self::lemma_from_int_denom(n);
    }

    /// Integer embedding preserves non-strict ordering.
    pub proof fn lemma_from_int_preserves_le(m: int, n: int)
        requires
            m <= n,
        ensures
            Self::from_int_spec(m).le_spec(Self::from_int_spec(n)),
    {
        Self::lemma_from_int_denom(m);
        Self::lemma_from_int_denom(n);
    }

    /// Integer embedding is injective (equivalent images implies equal inputs).
    pub proof fn lemma_from_int_injective(m: int, n: int)
        requires
            Self::from_int_spec(m).eqv_spec(Self::from_int_spec(n)),
        ensures
            m == n,
    {
        Self::lemma_from_int_denom(m);
        Self::lemma_from_int_denom(n);
        // eqv: m * 1 == n * 1, so m == n
    }

    /// Integer embedding distributes over addition.
    pub proof fn lemma_from_int_add(m: int, n: int)
        ensures
            Self::from_int_spec(m).add_spec(Self::from_int_spec(n)).eqv_spec(
                Self::from_int_spec(m + n)),
    {
        let a = Self::from_int_spec(m);
        let b = Self::from_int_spec(n);
        let sum = a.add_spec(b);
        let target = Self::from_int_spec(m + n);
        Self::lemma_from_int_denom(m);
        Self::lemma_from_int_denom(n);
        Self::lemma_from_int_denom(m + n);
        // sum.num = m * 1 + n * 1 = m + n
        // sum.denom_nat() = 0*0 + 0 + 0 + 1 = 1, so sum.denom() = 1
        // target.num = m + n, target.denom() = 1
        // eqv: (m+n) * 1 == (m+n) * 1
        Self::lemma_add_denom_product_int(a, b);
        assert(sum.denom() == a.denom() * b.denom());
        assert(sum.denom() == 1);
        assert(sum.num == m * 1 + n * 1);
        assert(m * 1 + n * 1 == m + n) by (nonlinear_arith);
        assert(sum.eqv_spec(target) == (sum.num * target.denom() == target.num * sum.denom()));
    }

    /// Integer embedding distributes over multiplication.
    pub proof fn lemma_from_int_mul(m: int, n: int)
        ensures
            Self::from_int_spec(m).mul_spec(Self::from_int_spec(n)).eqv_spec(
                Self::from_int_spec(m * n)),
    {
        let a = Self::from_int_spec(m);
        let b = Self::from_int_spec(n);
        let prod = a.mul_spec(b);
        let target = Self::from_int_spec(m * n);
        Self::lemma_from_int_denom(m);
        Self::lemma_from_int_denom(n);
        Self::lemma_from_int_denom(m * n);
        Self::lemma_mul_denom_product_int(a, b);
        assert(prod.denom() == a.denom() * b.denom());
        assert(prod.denom() == 1);
        assert(prod.num == m * n);
        assert(prod.eqv_spec(target) == (prod.num * target.denom() == target.num * prod.denom()));
    }

    /// Integer embedding distributes over negation.
    pub proof fn lemma_from_int_neg(m: int)
        ensures
            Self::from_int_spec(m).neg_spec() == Self::from_int_spec(-m),
    {
        // neg_spec just negates num, den stays 0
    }

    /// Integer embedding distributes over subtraction.
    pub proof fn lemma_from_int_sub(m: int, n: int)
        ensures
            Self::from_int_spec(m).sub_spec(Self::from_int_spec(n)).eqv_spec(
                Self::from_int_spec(m - n)),
    {
        // sub = add(neg)
        Self::lemma_from_int_neg(n);
        // from_int(n).neg_spec() == from_int(-n)
        // so sub == from_int(m).add(from_int(-n))
        Self::lemma_from_int_add(m, -n);
        // from_int(m).add(from_int(-n)) ≡ from_int(m + (-n)) = from_int(m - n)
        let a = Self::from_int_spec(m);
        let b = Self::from_int_spec(n);
        assert(a.sub_spec(b) == a.add_spec(b.neg_spec()));
        assert(b.neg_spec() == Self::from_int_spec(-n));
        assert(a.add_spec(Self::from_int_spec(-n)).eqv_spec(Self::from_int_spec(m + (-n))));
        assert(m + (-n) == m - n);
        assert(a.sub_spec(b) == a.add_spec(Self::from_int_spec(-n)));
    }

    // ── Sign-preserving multiplication monotonicity ──────────────────

    /// If a ≤ b and 0 ≤ c, then a*c ≤ b*c.
    pub proof fn lemma_le_mul_nonneg(a: Self, b: Self, c: Self)
        requires
            a.le_spec(b),
            Self::from_int_spec(0).le_spec(c),
        ensures
            a.mul_spec(c).le_spec(b.mul_spec(c)),
    {
        let z = Self::from_int_spec(0);
        let ac = a.mul_spec(c);
        let bc = b.mul_spec(c);
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_mul_denom_product_int(b, c);
        assert(ac.num == a.num * c.num);
        assert(bc.num == b.num * c.num);
        assert(ac.denom() == a.denom() * c.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(ac.le_spec(bc) == (ac.num * bc.denom() <= bc.num * ac.denom()));
        assert(a.le_spec(b) == (a.num * b.denom() <= b.num * a.denom()));
        assert(a.num * b.denom() <= b.num * a.denom());
        assert(z.num == 0);
        assert(z.denom() == 1);
        lemma_mul_by_zero_is_zero(c.denom());
        assert(0 <= c.num * 1) by (nonlinear_arith)
            requires z.le_spec(c), z.num == 0, z.denom() == 1;
        assert(c.num >= 0) by (nonlinear_arith)
            requires 0 <= c.num * 1;
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        assert((a.num * b.denom() <= b.num * a.denom() && c.num >= 0 && c.denom() > 0)
            ==> ((a.num * c.num) * (b.denom() * c.denom())
                <= (b.num * c.num) * (a.denom() * c.denom())))
            by (nonlinear_arith);
        assert(ac.num * bc.denom() == (a.num * c.num) * (b.denom() * c.denom()));
        assert(bc.num * ac.denom() == (b.num * c.num) * (a.denom() * c.denom()));
        assert(ac.num * bc.denom() <= bc.num * ac.denom());
    }

    /// If 0 ≤ a ≤ b and 0 ≤ c ≤ d, then a*c ≤ b*d.
    pub proof fn lemma_le_mul_nonneg_both(a: Self, b: Self, c: Self, d: Self)
        requires
            Self::from_int_spec(0).le_spec(a),
            a.le_spec(b),
            Self::from_int_spec(0).le_spec(c),
            c.le_spec(d),
        ensures
            a.mul_spec(c).le_spec(b.mul_spec(d)),
    {
        // a*c ≤ b*c (monotone in first arg with c ≥ 0)
        Self::lemma_le_mul_nonneg(a, b, c);
        // b*c ≤ b*d (monotone in second arg with b ≥ 0)
        // Use commutativity: b*c = c*b, b*d = d*b
        Self::lemma_mul_commutative(b, c);
        Self::lemma_mul_commutative(b, d);
        Self::lemma_le_transitive(Self::from_int_spec(0), a, b);
        Self::lemma_le_mul_nonneg(c, d, b);
        // c*b ≤ d*b, which structurally == b*c ≤ b*d
        // since mul_commutative gives ==
        // Now transitivity: a*c ≤ b*c ≤ b*d
        Self::lemma_le_transitive(a.mul_spec(c), b.mul_spec(c), b.mul_spec(d));
    }

    // ── Cross-multiplication ordering ────────────────────────────────

    /// For rationals, a ≤ b ↔ a.num * b.denom() ≤ b.num * a.denom().
    /// (This is definitional, but exposing it as a lemma is convenient.)
    pub proof fn lemma_cross_mul_le(a: Self, b: Self)
        ensures
            a.le_spec(b) == (a.num * b.denom() <= b.num * a.denom()),
    {
        // le_spec is defined exactly this way, so nothing to prove.
    }

    /// a < b ↔ a.num * b.denom() < b.num * a.denom().
    pub proof fn lemma_cross_mul_lt(a: Self, b: Self)
        ensures
            a.lt_spec(b) == (a.num * b.denom() < b.num * a.denom()),
    {
        // lt_spec is defined exactly this way, so nothing to prove.
    }

    // ── Density / midpoint ───────────────────────────────────────────

    /// The midpoint of two rationals: (a + b) / 2.
    pub open spec fn midpoint_spec(a: Self, b: Self) -> Self {
        a.add_spec(b).mul_spec(Self { num: 1, den: 1 })
        // den=1 means denom()=2, so this is (a+b) * (1/2)
    }

    /// midpoint(a, a) ≡ a.
    pub proof fn lemma_midpoint_eqv_self(a: Self)
        ensures
            Self::midpoint_spec(a, a).eqv_spec(a),
    {
        let aa = a.add_spec(a);
        let half = Rational { num: 1, den: 1 };
        let mid = aa.mul_spec(half);

        Self::lemma_denom_positive(a);
        Self::lemma_add_denom_product_int(a, a);
        // aa.num = a.num * a.denom() + a.num * a.denom() = 2 * a.num * a.denom()
        assert(aa.num == a.num * a.denom() + a.num * a.denom());
        assert(aa.denom() == a.denom() * a.denom());

        Self::lemma_mul_denom_product_int(aa, half);
        assert(half.denom() == 2);
        assert(mid.num == aa.num * half.num);
        assert(mid.denom() == aa.denom() * half.denom());
        assert(half.num == 1);
        assert(mid.num == aa.num * 1);
        assert(mid.num == aa.num) by (nonlinear_arith)
            requires mid.num == aa.num * 1;
        assert(mid.denom() == aa.denom() * 2);

        // mid ≡ a means mid.num * a.denom() == a.num * mid.denom()
        // mid.num = 2 * a.num * a.denom()
        // mid.denom() = a.denom()^2 * 2
        // mid.num * a.denom() = 2 * a.num * a.denom() * a.denom()
        // a.num * mid.denom() = a.num * a.denom()^2 * 2
        // These are equal.
        assert(aa.num == 2 * a.num * a.denom()) by (nonlinear_arith)
            requires aa.num == a.num * a.denom() + a.num * a.denom();
        assert(mid.num == 2 * a.num * a.denom());
        assert(mid.denom() == a.denom() * a.denom() * 2);
        assert(mid.num * a.denom() == 2 * a.num * a.denom() * a.denom()) by (nonlinear_arith)
            requires mid.num == 2 * a.num * a.denom();
        assert(a.num * mid.denom() == a.num * (a.denom() * a.denom() * 2))
            by (nonlinear_arith)
            requires mid.denom() == a.denom() * a.denom() * 2;
        assert(a.num * (a.denom() * a.denom() * 2) == 2 * a.num * a.denom() * a.denom())
            by (nonlinear_arith);
        assert(mid.num * a.denom() == a.num * mid.denom());
    }

    /// If a < b, then a < midpoint(a, b) (midpoint is strictly between).
    pub proof fn lemma_midpoint_between_left(a: Self, b: Self)
        requires
            a.lt_spec(b),
        ensures
            a.lt_spec(Self::midpoint_spec(a, b)),
    {
        let s = a.add_spec(b);
        let half = Rational { num: 1, den: 1 };
        let mid = s.mul_spec(half);

        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_add_denom_product_int(a, b);
        Self::lemma_mul_denom_product_int(s, half);

        assert(half.num == 1);
        assert(half.denom() == 2);
        assert(s.num == a.num * b.denom() + b.num * a.denom());
        assert(s.denom() == a.denom() * b.denom());
        assert(mid.num == s.num * 1);
        assert(mid.num == s.num) by (nonlinear_arith)
            requires mid.num == s.num * 1;
        assert(mid.denom() == s.denom() * 2);

        // a < b means a.num * b.denom() < b.num * a.denom()
        assert(a.num * b.denom() < b.num * a.denom());
        let ghost an_bd = a.num * b.denom();
        let ghost bn_ad = b.num * a.denom();

        // a < mid means a.num * mid.denom() < mid.num * a.denom()
        // a.num * mid.denom() = a.num * s.denom() * 2
        //                     = a.num * a.denom() * b.denom() * 2
        // mid.num * a.denom() = s.num * a.denom()
        //                     = (a.num * b.denom() + b.num * a.denom()) * a.denom()
        //                     = a.num * b.denom() * a.denom() + b.num * a.denom() * a.denom()
        // Need: a.num * a.denom() * b.denom() * 2
        //     < a.num * b.denom() * a.denom() + b.num * a.denom() * a.denom()
        // i.e. 2 * a.num * a.denom() * b.denom()
        //    < (a.num * b.denom() + b.num * a.denom()) * a.denom()
        // i.e. 2 * an_bd * a.denom() < (an_bd + bn_ad) * a.denom()
        // Since a.denom() > 0, dividing: 2 * an_bd < an_bd + bn_ad
        // i.e. an_bd < bn_ad, which is exactly a < b. ✓

        assert(a.num * mid.denom() == a.num * (s.denom() * 2));
        assert(mid.num * a.denom() == s.num * a.denom());
        assert(s.num == an_bd + bn_ad);

        assert((an_bd < bn_ad && a.denom() > 0)
            ==> a.num * (s.denom() * 2) < s.num * a.denom())
            by (nonlinear_arith)
            requires
                s.denom() == a.denom() * b.denom(),
                s.num == an_bd + bn_ad,
                an_bd == a.num * b.denom(),
                bn_ad == b.num * a.denom(),
        ;
    }

    /// If a < b, then midpoint(a, b) < b.
    pub proof fn lemma_midpoint_between_right(a: Self, b: Self)
        requires
            a.lt_spec(b),
        ensures
            Self::midpoint_spec(a, b).lt_spec(b),
    {
        let s = a.add_spec(b);
        let half = Rational { num: 1, den: 1 };
        let mid = s.mul_spec(half);

        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_add_denom_product_int(a, b);
        Self::lemma_mul_denom_product_int(s, half);

        assert(half.num == 1);
        assert(half.denom() == 2);
        assert(s.num == a.num * b.denom() + b.num * a.denom());
        assert(s.denom() == a.denom() * b.denom());
        assert(mid.num == s.num * 1);
        assert(mid.num == s.num) by (nonlinear_arith)
            requires mid.num == s.num * 1;
        assert(mid.denom() == s.denom() * 2);

        assert(a.num * b.denom() < b.num * a.denom());
        let ghost an_bd = a.num * b.denom();
        let ghost bn_ad = b.num * a.denom();

        // mid < b means mid.num * b.denom() < b.num * mid.denom()
        // mid.num * b.denom() = s.num * b.denom()
        //                     = (an_bd + bn_ad) * b.denom()
        // b.num * mid.denom() = b.num * s.denom() * 2
        //                     = b.num * a.denom() * b.denom() * 2
        //                     = 2 * bn_ad * b.denom()
        // Need: (an_bd + bn_ad) * b.denom() < 2 * bn_ad * b.denom()
        // Since b.denom() > 0: an_bd + bn_ad < 2 * bn_ad
        // i.e. an_bd < bn_ad ✓

        assert(mid.num * b.denom() == s.num * b.denom());
        assert(b.num * mid.denom() == b.num * (s.denom() * 2));

        assert((an_bd < bn_ad && b.denom() > 0)
            ==> s.num * b.denom() < b.num * (s.denom() * 2))
            by (nonlinear_arith)
            requires
                s.denom() == a.denom() * b.denom(),
                s.num == an_bd + bn_ad,
                an_bd == a.num * b.denom(),
                bn_ad == b.num * a.denom(),
        ;
    }

    // ── Sign of products ─────────────────────────────────────────────

    /// Positive times positive is positive.
    pub proof fn lemma_pos_mul_pos(a: Self, b: Self)
        requires
            Self::from_int_spec(0).lt_spec(a),
            Self::from_int_spec(0).lt_spec(b),
        ensures
            Self::from_int_spec(0).lt_spec(a.mul_spec(b)),
    {
        let z = Self::from_int_spec(0);
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        assert(z.num == 0);
        assert(z.denom() == 1);
        // 0 < a means 0 * a.denom() < a.num * 1, i.e. 0 < a.num
        assert(a.num > 0) by (nonlinear_arith)
            requires z.lt_spec(a), z.num == 0, z.denom() == 1;
        assert(b.num > 0) by (nonlinear_arith)
            requires z.lt_spec(b), z.num == 0, z.denom() == 1;
        Self::lemma_mul_denom_product_int(a, b);
        let ab = a.mul_spec(b);
        assert(ab.num == a.num * b.num);
        assert(ab.denom() == a.denom() * b.denom());
        assert(a.num * b.num > 0) by (nonlinear_arith)
            requires a.num > 0, b.num > 0;
        lemma_mul_by_zero_is_zero(ab.denom());
        assert(z.num * ab.denom() == 0);
        assert((z.denom() == 1) ==> ab.num * z.denom() == ab.num) by (nonlinear_arith);
    }

    /// Negative times negative is positive.
    pub proof fn lemma_neg_mul_neg(a: Self, b: Self)
        requires
            a.lt_spec(Self::from_int_spec(0)),
            b.lt_spec(Self::from_int_spec(0)),
        ensures
            Self::from_int_spec(0).lt_spec(a.mul_spec(b)),
    {
        let z = Self::from_int_spec(0);
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(a.num < 0) by (nonlinear_arith)
            requires a.lt_spec(z), z.num == 0, z.denom() == 1, a.denom() > 0;
        assert(b.num < 0) by (nonlinear_arith)
            requires b.lt_spec(z), z.num == 0, z.denom() == 1, b.denom() > 0;
        Self::lemma_mul_denom_product_int(a, b);
        let ab = a.mul_spec(b);
        assert(ab.num == a.num * b.num);
        assert(a.num * b.num > 0) by (nonlinear_arith)
            requires a.num < 0, b.num < 0;
        lemma_mul_by_zero_is_zero(ab.denom());
        assert((z.denom() == 1) ==> ab.num * z.denom() == ab.num) by (nonlinear_arith);
    }

    /// Positive times negative is negative.
    pub proof fn lemma_pos_mul_neg(a: Self, b: Self)
        requires
            Self::from_int_spec(0).lt_spec(a),
            b.lt_spec(Self::from_int_spec(0)),
        ensures
            a.mul_spec(b).lt_spec(Self::from_int_spec(0)),
    {
        let z = Self::from_int_spec(0);
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(a.num > 0) by (nonlinear_arith)
            requires z.lt_spec(a), z.num == 0, z.denom() == 1;
        assert(b.num < 0) by (nonlinear_arith)
            requires b.lt_spec(z), z.num == 0, z.denom() == 1, b.denom() > 0;
        Self::lemma_mul_denom_product_int(a, b);
        let ab = a.mul_spec(b);
        assert(ab.num == a.num * b.num);
        assert(ab.denom() == a.denom() * b.denom());
        assert(a.num * b.num < 0) by (nonlinear_arith)
            requires a.num > 0, b.num < 0;
        lemma_mul_by_zero_is_zero(ab.denom());
        assert((z.denom() == 1) ==> ab.num * z.denom() == ab.num) by (nonlinear_arith);
    }

    /// Negative times positive is negative.
    pub proof fn lemma_neg_mul_pos(a: Self, b: Self)
        requires
            a.lt_spec(Self::from_int_spec(0)),
            Self::from_int_spec(0).lt_spec(b),
        ensures
            a.mul_spec(b).lt_spec(Self::from_int_spec(0)),
    {
        Self::lemma_mul_commutative(a, b);
        Self::lemma_pos_mul_neg(b, a);
    }

    /// If either factor is zero, the product is zero.
    pub proof fn lemma_zero_mul_sign(a: Self, b: Self)
        requires
            a.eqv_spec(Self::from_int_spec(0))
            || b.eqv_spec(Self::from_int_spec(0)),
        ensures
            a.mul_spec(b).eqv_spec(Self::from_int_spec(0)),
    {
        let z = Self::from_int_spec(0);
        Self::lemma_eqv_zero_iff_num_zero(a);
        Self::lemma_eqv_zero_iff_num_zero(b);
        if a.eqv_spec(z) {
            assert(a.num == 0);
            Self::lemma_mul_left_zero_num(a, b);
            assert(a.mul_spec(b).num == 0);
            Self::lemma_eqv_zero_iff_num_zero(a.mul_spec(b));
        } else {
            assert(b.num == 0);
            Self::lemma_mul_right_zero_num(a, b);
            assert(a.mul_spec(b).num == 0);
            Self::lemma_eqv_zero_iff_num_zero(a.mul_spec(b));
        }
    }

    // ── Strict ordering + arithmetic ─────────────────────────────────

    /// Strict addition monotonicity: a < b → a + c < b + c.
    pub proof fn lemma_lt_add_monotone(a: Self, b: Self, c: Self)
        requires
            a.lt_spec(b),
        ensures
            a.add_spec(c).lt_spec(b.add_spec(c)),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        Self::lemma_add_denom_product_int(a, c);
        Self::lemma_add_denom_product_int(b, c);
        let ac = a.add_spec(c);
        let bc = b.add_spec(c);
        assert(ac.num == a.num * c.denom() + c.num * a.denom());
        assert(bc.num == b.num * c.denom() + c.num * b.denom());
        assert(ac.denom() == a.denom() * c.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(a.num * b.denom() < b.num * a.denom());
        // ac < bc means ac.num * bc.denom() < bc.num * ac.denom()
        assert((a.num * b.denom() < b.num * a.denom()
            && c.denom() > 0 && a.denom() > 0 && b.denom() > 0)
            ==> (a.num * c.denom() + c.num * a.denom()) * (b.denom() * c.denom())
                < (b.num * c.denom() + c.num * b.denom()) * (a.denom() * c.denom()))
            by (nonlinear_arith);
    }

    /// Strict multiplication monotonicity with positive factor.
    pub proof fn lemma_lt_mul_positive(a: Self, b: Self, c: Self)
        requires
            a.lt_spec(b),
            Self::from_int_spec(0).lt_spec(c),
        ensures
            a.mul_spec(c).lt_spec(b.mul_spec(c)),
    {
        let z = Self::from_int_spec(0);
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(c.num > 0) by (nonlinear_arith)
            requires z.lt_spec(c), z.num == 0, z.denom() == 1;
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_mul_denom_product_int(b, c);
        let ac = a.mul_spec(c);
        let bc = b.mul_spec(c);
        assert(ac.num == a.num * c.num);
        assert(bc.num == b.num * c.num);
        assert(ac.denom() == a.denom() * c.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(a.num * b.denom() < b.num * a.denom());
        assert((a.num * b.denom() < b.num * a.denom() && c.num > 0 && c.denom() > 0)
            ==> (a.num * c.num) * (b.denom() * c.denom())
                < (b.num * c.num) * (a.denom() * c.denom()))
            by (nonlinear_arith);
    }

    /// Strict multiplication with negative factor reverses order.
    pub proof fn lemma_lt_mul_negative(a: Self, b: Self, c: Self)
        requires
            a.lt_spec(b),
            c.lt_spec(Self::from_int_spec(0)),
        ensures
            b.mul_spec(c).lt_spec(a.mul_spec(c)),
    {
        let z = Self::from_int_spec(0);
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(c.num < 0) by (nonlinear_arith)
            requires c.lt_spec(z), z.num == 0, z.denom() == 1, c.denom() > 0;
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_mul_denom_product_int(b, c);
        let ac = a.mul_spec(c);
        let bc = b.mul_spec(c);
        assert(ac.num == a.num * c.num);
        assert(bc.num == b.num * c.num);
        assert(ac.denom() == a.denom() * c.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(a.num * b.denom() < b.num * a.denom());
        // With c.num < 0, inequality reverses
        assert((a.num * b.denom() < b.num * a.denom() && c.num < 0 && c.denom() > 0)
            ==> (b.num * c.num) * (a.denom() * c.denom())
                < (a.num * c.num) * (b.denom() * c.denom()))
            by (nonlinear_arith);
    }

    /// a < b ↔ 0 < b - a.
    pub proof fn lemma_lt_sub_equiv(a: Self, b: Self)
        ensures
            a.lt_spec(b) == Self::from_int_spec(0).lt_spec(b.sub_spec(a)),
    {
        let z = Self::from_int_spec(0);
        let neg_a = a.neg_spec();
        let diff = b.add_spec(neg_a); // == b.sub_spec(a)
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        assert(z.num == 0);
        assert(z.denom() == 1);
        // neg_a has same den as a, so same denom_nat/denom
        assert(neg_a.den == a.den);
        assert(neg_a.denom_nat() == a.denom_nat());
        assert(neg_a.num == -a.num);
        // Unfold add_spec: diff.num = b.num * (neg_a.denom_nat() as int) + neg_a.num * (b.denom_nat() as int)
        //                           = b.num * a.denom() + (-a.num) * b.denom()
        let da = a.denom();
        let db = b.denom();
        assert(diff.num == b.num * (neg_a.denom_nat() as int) + neg_a.num * (b.denom_nat() as int));
        assert(neg_a.denom_nat() as int == da);
        assert(b.denom_nat() as int == db);
        assert(diff.num == b.num * da + (-a.num) * db);
        // (-a.num) * db == -(a.num * db)
        assert((-a.num) * db == -(a.num * db)) by (nonlinear_arith);
        assert(diff.num == b.num * da - a.num * db);
        // a < b means a.num * b.denom() < b.num * a.denom()
        // 0 < diff means 0 * diff.denom() < diff.num * z.denom()
        //   i.e. 0 < diff.num (since z.denom() == 1)
        //   i.e. b.num * da - a.num * db > 0
        //   i.e. a.num * db < b.num * da
        lemma_mul_by_zero_is_zero(diff.denom());
        assert((z.denom() == 1) ==> diff.num * z.denom() == diff.num) by (nonlinear_arith);
    }

    // ── Negation reverses ordering ───────────────────────────────────

    /// a ≤ b → -b ≤ -a.
    pub proof fn lemma_neg_reverses_le(a: Self, b: Self)
        requires
            a.le_spec(b),
        ensures
            b.neg_spec().le_spec(a.neg_spec()),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        let na = a.neg_spec();
        let nb = b.neg_spec();
        assert(na.num == -a.num);
        assert(nb.num == -b.num);
        assert(na.denom() == a.denom());
        assert(nb.denom() == b.denom());
        assert(a.num * b.denom() <= b.num * a.denom());
        // Need: nb.num * na.denom() <= na.num * nb.denom()
        // i.e. (-b.num) * a.denom() <= (-a.num) * b.denom()
        assert((-b.num) * a.denom() <= (-a.num) * b.denom()
            <==> a.num * b.denom() <= b.num * a.denom())
            by (nonlinear_arith);
    }

    /// a < b → -b < -a.
    pub proof fn lemma_neg_reverses_lt(a: Self, b: Self)
        requires
            a.lt_spec(b),
        ensures
            b.neg_spec().lt_spec(a.neg_spec()),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        let na = a.neg_spec();
        let nb = b.neg_spec();
        assert(na.num == -a.num);
        assert(nb.num == -b.num);
        assert(na.denom() == a.denom());
        assert(nb.denom() == b.denom());
        assert(a.num * b.denom() < b.num * a.denom());
        assert((-b.num) * a.denom() < (-a.num) * b.denom()
            <==> a.num * b.denom() < b.num * a.denom())
            by (nonlinear_arith);
    }

    /// a ≤ b → a - c ≤ b - c.
    pub proof fn lemma_sub_le_monotone_left(a: Self, b: Self, c: Self)
        requires
            a.le_spec(b),
        ensures
            a.sub_spec(c).le_spec(b.sub_spec(c)),
    {
        // a - c = a + (-c), b - c = b + (-c)
        Self::lemma_le_add_monotone(a, b, c.neg_spec());
    }

    /// a ≤ b → c - b ≤ c - a (reversal in second arg).
    pub proof fn lemma_sub_le_monotone_right(a: Self, b: Self, c: Self)
        requires
            a.le_spec(b),
        ensures
            c.sub_spec(b).le_spec(c.sub_spec(a)),
    {
        Self::lemma_neg_reverses_le(a, b);
        // -b ≤ -a
        Self::lemma_le_add_monotone(b.neg_spec(), a.neg_spec(), c);
        // c + (-b) ≤ c + (-a)
        // which is c - b ≤ c - a
    }

    // ── Bilateral addition monotonicity ──────────────────────────────

    /// a ≤ b ∧ c ≤ d → a + c ≤ b + d.
    pub proof fn lemma_le_add_both(a: Self, b: Self, c: Self, d: Self)
        requires
            a.le_spec(b),
            c.le_spec(d),
        ensures
            a.add_spec(c).le_spec(b.add_spec(d)),
    {
        Self::lemma_le_add_monotone(a, b, c);
        // a + c ≤ b + c
        Self::lemma_add_commutative(b, c);
        Self::lemma_add_commutative(b, d);
        Self::lemma_le_add_monotone(c, d, b);
        // c + b ≤ d + b, i.e. b + c ≤ b + d
        Self::lemma_le_transitive(a.add_spec(c), b.add_spec(c), b.add_spec(d));
    }

    /// a < b ∧ c < d → a + c < b + d.
    pub proof fn lemma_lt_add_both(a: Self, b: Self, c: Self, d: Self)
        requires
            a.lt_spec(b),
            c.lt_spec(d),
        ensures
            a.add_spec(c).lt_spec(b.add_spec(d)),
    {
        Self::lemma_lt_add_monotone(a, b, c);
        Self::lemma_add_commutative(b, c);
        Self::lemma_add_commutative(b, d);
        Self::lemma_lt_add_monotone(c, d, b);
        Self::lemma_lt_transitive(a.add_spec(c), b.add_spec(c), b.add_spec(d));
    }

    /// a ≤ b ∧ c < d → a + c < b + d.
    pub proof fn lemma_le_lt_add(a: Self, b: Self, c: Self, d: Self)
        requires
            a.le_spec(b),
            c.lt_spec(d),
        ensures
            a.add_spec(c).lt_spec(b.add_spec(d)),
    {
        Self::lemma_le_add_monotone(a, b, c);
        // a + c ≤ b + c
        Self::lemma_add_commutative(b, c);
        Self::lemma_add_commutative(b, d);
        Self::lemma_lt_add_monotone(c, d, b);
        // b + c < b + d
        Self::lemma_le_iff_lt_or_eqv(a.add_spec(c), b.add_spec(c));
        if a.add_spec(c).lt_spec(b.add_spec(c)) {
            Self::lemma_lt_transitive(a.add_spec(c), b.add_spec(c), b.add_spec(d));
        } else {
            // a+c ≡ b+c, and b+c < b+d
            // So a+c < b+d via eqv + lt
            assert(a.add_spec(c).eqv_spec(b.add_spec(c)));
            // eqv means same cross-product
            let ac = a.add_spec(c);
            let bc = b.add_spec(c);
            let bd = b.add_spec(d);
            assert(ac.num * bc.denom() == bc.num * ac.denom());
            assert(bc.num * bd.denom() < bd.num * bc.denom());
            Self::lemma_denom_positive(ac);
            Self::lemma_denom_positive(bc);
            Self::lemma_denom_positive(bd);
            // ac.num * bd.denom() = (ac.num * bc.denom()) * bd.denom() / bc.denom()
            // but we can do: ac.num * bd.denom() < bd.num * ac.denom()
            assert((ac.num * bc.denom() == bc.num * ac.denom()
                && bc.num * bd.denom() < bd.num * bc.denom()
                && bc.denom() > 0 && ac.denom() > 0)
                ==> ac.num * bd.denom() < bd.num * ac.denom())
                by (nonlinear_arith);
        }
    }

}

} // verus!
