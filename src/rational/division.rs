use super::Rational;
use vstd::prelude::*;
use vstd::calc;
use vstd::arithmetic::mul::{
    lemma_mul_by_zero_is_zero,
    lemma_mul_is_associative,
    lemma_mul_is_commutative,
};

verus! {

impl Rational {
    // ── Multiplicative cancellation ──────────────────────────────────

    /// a*c ≡ b*c ∧ c ≢ 0 → a ≡ b.
    pub proof fn lemma_mul_cancel_right(a: Self, b: Self, c: Self)
        requires
            a.mul_spec(c).eqv_spec(b.mul_spec(c)),
            !c.eqv_spec(Self::from_int_spec(0)),
        ensures
            a.eqv_spec(b),
    {
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        Self::lemma_eqv_zero_iff_num_zero(c);
        assert(c.num != 0);
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_mul_denom_product_int(b, c);
        let ac = a.mul_spec(c);
        let bc = b.mul_spec(c);
        assert(ac.num == a.num * c.num);
        assert(bc.num == b.num * c.num);
        assert(ac.denom() == a.denom() * c.denom());
        assert(bc.denom() == b.denom() * c.denom());
        // ac ≡ bc means ac.num * bc.denom() == bc.num * ac.denom()
        assert(ac.num * bc.denom() == bc.num * ac.denom());
        // (a.num * c.num) * (b.denom() * c.denom()) == (b.num * c.num) * (a.denom() * c.denom())
        // Factor out c.num * c.denom():
        // a.num * b.denom() * (c.num * c.denom()) == b.num * a.denom() * (c.num * c.denom())
        // Since c.num != 0 and c.denom() > 0, c.num * c.denom() != 0
        assert((c.num != 0 && c.denom() > 0) ==> c.num * c.denom() != 0)
            by (nonlinear_arith);
        assert(((a.num * c.num) * (b.denom() * c.denom())
            == (b.num * c.num) * (a.denom() * c.denom())
            && c.num * c.denom() != 0)
            ==> a.num * b.denom() == b.num * a.denom())
            by (nonlinear_arith);
    }

    /// c*a ≡ c*b ∧ c ≢ 0 → a ≡ b.
    pub proof fn lemma_mul_cancel_left(a: Self, b: Self, c: Self)
        requires
            c.mul_spec(a).eqv_spec(c.mul_spec(b)),
            !c.eqv_spec(Self::from_int_spec(0)),
        ensures
            a.eqv_spec(b),
    {
        Self::lemma_mul_commutative(c, a);
        Self::lemma_mul_commutative(c, b);
        // c*a == a*c and c*b == b*c structurally
        Self::lemma_mul_cancel_right(a, b, c);
    }

    // ── Division properties ──────────────────────────────────────────

    /// Linking lemma: reciprocal_spec(a) is the multiplicative inverse of a.
    /// Returns inv == a.reciprocal_spec() with a.mul_spec(inv) ≡ 1.
    pub proof fn lemma_reciprocal_spec_inverse(a: Self) -> (inv: Self)
        requires
            a.num != 0,
        ensures
            inv == a.reciprocal_spec(),
            a.mul_spec(inv).eqv_spec(Self::from_int_spec(1)),
            inv.mul_spec(a).eqv_spec(Self::from_int_spec(1)),
    {
        Self::reciprocal_constructive(a)
    }

    /// (a + b) / c ≡ a/c + b/c when c ≢ 0.
    pub proof fn lemma_div_add_numerator(a: Self, b: Self, c: Self)
        requires
            !c.eqv_spec(Self::from_int_spec(0)),
        ensures
            a.add_spec(b).div_spec(c).eqv_spec(
                a.div_spec(c).add_spec(b.div_spec(c))),
    {
        Self::lemma_eqv_zero_iff_num_zero(c);
        let inv = Self::lemma_reciprocal_spec_inverse(c);
        Self::lemma_eqv_mul_distributive_right(a, b, inv);
    }

    /// a ≢ 0 → a / a ≡ 1.
    pub proof fn lemma_div_self(a: Self)
        requires
            !a.eqv_spec(Self::from_int_spec(0)),
        ensures
            a.div_spec(a).eqv_spec(Self::from_int_spec(1)),
    {
        Self::lemma_eqv_zero_iff_num_zero(a);
        let inv = Self::lemma_reciprocal_spec_inverse(a);
    }

    /// a ≢ 0 → a * (b / a) ≡ b.
    pub proof fn lemma_div_cancel(a: Self, b: Self)
        requires
            !a.eqv_spec(Self::from_int_spec(0)),
        ensures
            a.mul_spec(b.div_spec(a)).eqv_spec(b),
    {
        Self::lemma_eqv_zero_iff_num_zero(a);
        let inv = Self::lemma_reciprocal_spec_inverse(a);
        let ba = b.mul_spec(inv);
        Self::lemma_mul_commutative(b, inv);
        Self::lemma_mul_associative(a, inv, b);
        Self::lemma_eqv_symmetric(
            a.mul_spec(inv).mul_spec(b),
            a.mul_spec(inv.mul_spec(b)),
        );
        assert(a.mul_spec(ba) == a.mul_spec(inv.mul_spec(b)));
        let one = Self::from_int_spec(1);
        assert(a.mul_spec(inv).eqv_spec(one));
        Self::lemma_eqv_mul_congruence_left(a.mul_spec(inv), one, b);
        Self::lemma_mul_commutative(one, b);
        Self::lemma_mul_one_identity(b);
        assert(one.mul_spec(b) == b.mul_spec(one));
        assert(b.mul_spec(one).eqv_spec(b));
        Self::lemma_eqv_transitive(
            a.mul_spec(ba),
            a.mul_spec(inv).mul_spec(b),
            one.mul_spec(b),
        );
        Self::lemma_eqv_transitive(a.mul_spec(ba), one.mul_spec(b), b);
    }

    /// b ≢ 0 → (a * b) / b ≡ a.
    pub proof fn lemma_div_mul_cancel(a: Self, b: Self)
        requires
            !b.eqv_spec(Self::from_int_spec(0)),
        ensures
            a.mul_spec(b).div_spec(b).eqv_spec(a),
    {
        Self::lemma_eqv_zero_iff_num_zero(b);
        let inv = Self::lemma_reciprocal_spec_inverse(b);
        let result = a.mul_spec(b).mul_spec(inv);
        Self::lemma_mul_associative(a, b, inv);
        Self::lemma_eqv_symmetric(
            a.mul_spec(b).mul_spec(inv),
            a.mul_spec(b.mul_spec(inv)),
        );
        let one = Self::from_int_spec(1);
        assert(b.mul_spec(inv).eqv_spec(one));
        Self::lemma_eqv_mul_congruence_right(a, b.mul_spec(inv), one);
        Self::lemma_mul_one_identity(a);
        Self::lemma_eqv_transitive(result, a.mul_spec(b.mul_spec(inv)), a.mul_spec(one));
        Self::lemma_eqv_transitive(result, a.mul_spec(one), a);
    }

    /// a ≤ b ∧ c > 0 → a/c ≤ b/c.
    pub proof fn lemma_div_le_monotone(a: Self, b: Self, c: Self)
        requires
            a.le_spec(b),
            Self::from_int_spec(0).lt_spec(c),
        ensures
            a.div_spec(c).le_spec(b.div_spec(c)),
    {
        let z = Self::from_int_spec(0);
        Self::lemma_denom_positive(c);
        Self::lemma_eqv_zero_iff_num_zero(c);
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(c.num > 0) by (nonlinear_arith)
            requires z.lt_spec(c), z.num == 0, z.denom() == 1;
        let inv = Self::lemma_reciprocal_spec_inverse(c);
        Self::lemma_signum_mul(c, inv);
        let one = Self::from_int_spec(1);
        assert(c.mul_spec(inv).eqv_spec(one));
        Self::lemma_eqv_signum(c.mul_spec(inv), one);
        assert(one.signum() == 1);
        assert(c.mul_spec(inv).signum() == 1);
        assert(c.signum() * inv.signum() == 1);
        Self::lemma_signum_positive_iff(c);
        assert(c.signum() == 1);
        assert(inv.signum() == 1);
        Self::lemma_signum_positive_iff(inv);
        assert(inv.num > 0);
        Self::lemma_denom_positive(inv);
        lemma_mul_by_zero_is_zero(inv.denom());
        assert((z.denom() == 1) ==> inv.num * z.denom() == inv.num)
            by (nonlinear_arith);
        assert(z.le_spec(inv));
        Self::lemma_le_mul_nonneg(a, b, inv);
    }

    // ── Convex combination / interpolation ───────────────────────────

    /// If a ≤ b and 0 ≤ t ≤ 1, then a ≤ a*(1-t) + b*t ≤ b.
    pub proof fn lemma_convex_between(a: Self, b: Self, t: Self)
        requires
            a.le_spec(b),
            Self::from_int_spec(0).le_spec(t),
            t.le_spec(Self::from_int_spec(1)),
        ensures
            a.le_spec(
                a.mul_spec(Self::from_int_spec(1).sub_spec(t)).add_spec(b.mul_spec(t))),
            a.mul_spec(Self::from_int_spec(1).sub_spec(t)).add_spec(b.mul_spec(t))
                .le_spec(b),
    {
        let z = Self::from_int_spec(0);
        let one = Self::from_int_spec(1);
        let s = one.sub_spec(t);  // 1 - t
        // 0 ≤ t ≤ 1 → 0 ≤ 1-t ≤ 1
        // 1 - t ≥ 0:
        Self::lemma_sub_le_monotone_left(t, one, t);
        // t - t ≤ 1 - t
        Self::lemma_sub_then_add_cancel(z, t);
        // z = z - t + t... actually let's do it differently
        // We know t ≤ 1, so 0 ≤ 1 - t
        Self::lemma_le_add_monotone(t, one, t.neg_spec());
        // t + (-t) ≤ 1 + (-t), i.e. t - t ≤ 1 - t
        Self::lemma_sub_self_zero_signum(t);
        // t - t has signum 0, so t - t ≡ 0
        assert(t.sub_spec(t).num == 0);
        Self::lemma_eqv_zero_iff_num_zero(t.sub_spec(t));
        Self::lemma_denom_positive(t.sub_spec(t));
        Self::lemma_denom_positive(s);
        // We need to show z ≤ s
        // t.sub_spec(t).le_spec(s) means (t-t).num * s.denom() ≤ s.num * (t-t).denom()
        // 0 * s.denom() ≤ s.num * (t-t).denom()
        // So s.num * (t-t).denom() ≥ 0
        // From t + (-t) ≤ 1 + (-t) we get: t.add_spec(t.neg_spec()).le_spec(one.add_spec(t.neg_spec()))
        // which is t.sub_spec(t).le_spec(one.sub_spec(t)) = t.sub_spec(t).le_spec(s)
        // So z ≤ t-t ≤ s → z ≤ s (but z ≤ t-t needs separate proof)
        // Actually, t-t has num == 0, so for z ≤ t-t:
        lemma_mul_by_zero_is_zero(t.sub_spec(t).denom());
        assert(z.num * t.sub_spec(t).denom() == 0);
        assert(t.sub_spec(t).num == 0);
        lemma_mul_by_zero_is_zero(z.denom());
        // z.le_spec(t-t) = (0 ≤ 0) = true
        assert(z.le_spec(t.sub_spec(t)));
        // t-t ≤ s
        assert(t.sub_spec(t).le_spec(s));
        Self::lemma_le_transitive(z, t.sub_spec(t), s);

        // Also: s ≤ 1
        // 1 - t ≤ 1 iff 0 ≤ t, which is given
        Self::lemma_le_add_monotone(z, t, one.sub_spec(t));
        // z + (1-t) ≤ t + (1-t)
        Self::lemma_add_commutative(z, s);
        assert(z.add_spec(s) == s.add_spec(z));
        Self::lemma_add_zero_identity(s);
        // s + z ≡ s, and z + s ≤ t + s
        // t + (1-t) = t + 1 - t ≡ 1
        // This is getting complex. Let me just use the direct approach.

        // Direct approach for a ≤ a*s + b*t:
        // a = a * 1 = a * (s + t) (since s + t = (1-t) + t = 1)
        //   = a*s + a*t (by distributivity)
        // a*s + a*t ≤ a*s + b*t (since a ≤ b and t ≥ 0 → a*t ≤ b*t)
        // So: a ≡ a*s + a*t ≤ a*s + b*t

        // First: a ≡ a * 1
        Self::lemma_mul_one_identity(a);
        // a * 1 ≡ a, so a ≡ a*1

        // s + t ≡ 1: (1-t) + t = 1
        Self::lemma_sub_then_add_cancel(one, t);
        // sub_then_add_cancel(one, t): t.add_spec(s) ≡ one
        // We need s.add_spec(t) ≡ one, so apply commutativity + transitivity:
        Self::lemma_add_commutative(s, t);
        // s.add_spec(t) ≡ t.add_spec(s)
        Self::lemma_eqv_transitive(s.add_spec(t), t.add_spec(s), one);

        // a * (s + t) ≡ a * 1 ≡ a by congruence
        Self::lemma_eqv_mul_congruence_right(a, s.add_spec(t), one);
        // a * (s+t) ≡ a * 1
        // a * (s+t) ≡ a*s + a*t by distributivity
        Self::lemma_eqv_mul_distributive_left(a, s, t);
        // a * (s+t) ≡ a*s + a*t

        // Now a*t ≤ b*t (since a ≤ b and t ≥ 0)
        Self::lemma_le_mul_nonneg(a, b, t);

        // a*s + a*t ≤ a*s + b*t by add monotonicity on second component
        let ghost at_as = a.mul_spec(t).add_spec(a.mul_spec(s));
        let ghost bt_as = b.mul_spec(t).add_spec(a.mul_spec(s));
        Self::lemma_add_commutative(a.mul_spec(s), a.mul_spec(t));
        Self::lemma_add_commutative(a.mul_spec(s), b.mul_spec(t));
        Self::lemma_le_add_monotone(a.mul_spec(t), b.mul_spec(t), a.mul_spec(s));
        // at_as ≤ bt_as

        // Chain: a ≡ a*1 ≡ a*(s+t) ≡ a*s + a*t ≤ a*s + b*t
        let ghost v1 = a.mul_spec(one);
        let ghost v2 = a.mul_spec(s.add_spec(t));
        let ghost v3 = a.mul_spec(s).add_spec(a.mul_spec(t));
        let ghost v4 = a.mul_spec(s).add_spec(b.mul_spec(t));

        // a ≡ v1
        Self::lemma_eqv_symmetric(v1, a);
        // v1 ≡ v2 (congruence, since s+t ≡ one → a*(s+t) ≡ a*one)
        Self::lemma_eqv_symmetric(a.mul_spec(s.add_spec(t)), a.mul_spec(one));
        // v2 ≡ v3 (distributivity)

        // a ≡ v1 ≡ v2 ≡ v3, so a ≡ v3
        Self::lemma_eqv_transitive(a, v1, v2);
        Self::lemma_eqv_transitive(a, v2, v3);
        // a ≡ v3 → a ≤ v3
        Self::lemma_eqv_implies_le(a, v3);

        // v3 ≤ v4: bridge through at_as and bt_as
        // v3 ≡ at_as → v3 ≤ at_as
        Self::lemma_eqv_implies_le(v3, at_as);
        // at_as ≤ bt_as (from le_add_monotone)
        Self::lemma_le_transitive(v3, at_as, bt_as);
        // bt_as ≡ v4 → bt_as ≤ v4
        Self::lemma_eqv_implies_le(bt_as, v4);
        Self::lemma_le_transitive(v3, bt_as, v4);
        // now v3 ≤ v4
        Self::lemma_le_transitive(a, v3, v4);

        // Now b ≥ a*s + b*t:
        // b = b * 1 = b * (s + t) = b*s + b*t
        // a*s + b*t ≤ b*s + b*t (since a ≤ b and s ≥ 0 → a*s ≤ b*s)
        Self::lemma_mul_one_identity(b);
        Self::lemma_eqv_mul_congruence_right(b, s.add_spec(t), one);
        Self::lemma_eqv_mul_distributive_left(b, s, t);

        Self::lemma_le_mul_nonneg(a, b, s);
        // a*s ≤ b*s
        Self::lemma_le_add_monotone(a.mul_spec(s), b.mul_spec(s), b.mul_spec(t));
        // a*s + b*t ≤ b*s + b*t

        let ghost w3 = b.mul_spec(s).add_spec(b.mul_spec(t));
        let ghost w2 = b.mul_spec(s.add_spec(t));
        let ghost w1 = b.mul_spec(one);

        // w3 ≡ w2 ≡ w1 ≡ b
        Self::lemma_eqv_symmetric(w3, w2);
        Self::lemma_eqv_transitive(w3, w2, w1);
        Self::lemma_eqv_symmetric(w1, b);
        Self::lemma_eqv_transitive(w3, w1, b);
        // v4 ≤ w3 ≡ b, so v4 ≤ b
        Self::lemma_eqv_implies_le(w3, b);
        Self::lemma_le_transitive(v4, w3, b);
    }

    // ── Extended division / reciprocal (item 19) ──────────────────────

    /// (a*b)⁻¹ ≡ a⁻¹ * b⁻¹ when a ≢ 0 and b ≢ 0.
    pub proof fn lemma_reciprocal_of_product(a: Self, b: Self)
        requires
            !a.eqv_spec(Self::from_int_spec(0)),
            !b.eqv_spec(Self::from_int_spec(0)),
        ensures
            a.mul_spec(b).reciprocal_spec().eqv_spec(
                a.reciprocal_spec().mul_spec(b.reciprocal_spec())),
    {
        Self::lemma_eqv_zero_iff_num_zero(a);
        Self::lemma_eqv_zero_iff_num_zero(b);
        let ab = a.mul_spec(b);
        assert(ab.num == a.num * b.num);
        assert(ab.num != 0) by (nonlinear_arith)
            requires a.num != 0, b.num != 0, ab.num == a.num * b.num;
        // Get inverses
        let inv_a = Self::lemma_reciprocal_spec_inverse(a);
        let inv_b = Self::lemma_reciprocal_spec_inverse(b);
        let inv_ab = Self::lemma_reciprocal_spec_inverse(ab);
        // inv_ab is the unique inverse of ab (up to eqv)
        // inv_a * inv_b is also an inverse of ab:
        // ab * (inv_a * inv_b) = a * b * inv_a * inv_b
        //                      = (a * inv_a) * (b * inv_b)  by assoc+commut
        //                      ≡ 1 * 1 = 1
        let prod = inv_a.mul_spec(inv_b);
        let one = Self::from_int_spec(1);
        // a * (b * (inv_a * inv_b)):
        // = a * ((b * inv_a) * inv_b) -- but we want a*inv_a first
        // Rearrange: ab * prod = (a * b) * (inv_a * inv_b)
        //   ≡ a * (b * (inv_a * inv_b))  by assoc
        Self::lemma_mul_associative(a, b, prod);
        //   b * (inv_a * inv_b) ≡ (b * inv_a) * inv_b by assoc
        //   but b*inv_a = inv_a*b by commut
        //   inv_a * b * inv_b ≡ inv_a * (b * inv_b) by assoc
        Self::lemma_mul_commutative(b, inv_a);
        Self::lemma_mul_commutative(b, prod);
        // b * prod = b * (inv_a * inv_b)
        // inv_a * b = b * inv_a structurally (by lemma_mul_commutative)
        // Actually let me use a cleaner approach:
        // (a*b) * (inv_a * inv_b)
        // ≡ a * (b * (inv_a * inv_b))     by assoc
        // ≡ a * (b * inv_a * inv_b)        by assoc on inner (backward)
        // But I need: a * ((inv_a) * (b * inv_b))
        // via commutativity and associativity
        // Let's do: b * (inv_a * inv_b) ≡ inv_a * (b * inv_b)
        Self::lemma_mul_associative(inv_a, b, inv_b);
        // inv_a * b * inv_b ≡ inv_a * (b * inv_b)
        Self::lemma_mul_commutative(inv_a, b);
        // inv_a * b == b * inv_a structurally
        // so b * inv_a * inv_b ≡ inv_a * (b * inv_b)
        // but we need b * (inv_a * inv_b) first
        Self::lemma_mul_associative(b, inv_a, inv_b);
        // b * inv_a * inv_b ≡ b * (inv_a * inv_b)
        Self::lemma_eqv_symmetric(b.mul_spec(inv_a).mul_spec(inv_b), b.mul_spec(inv_a.mul_spec(inv_b)));
        // So b * (inv_a * inv_b) ≡ b * inv_a * inv_b
        //                        = (inv_a * b) * inv_b  structurally (commut)
        //                        ≡ inv_a * (b * inv_b)  by assoc
        assert(b.mul_spec(inv_a) == inv_a.mul_spec(b));
        Self::lemma_eqv_transitive(
            b.mul_spec(inv_a.mul_spec(inv_b)),
            b.mul_spec(inv_a).mul_spec(inv_b),
            inv_a.mul_spec(b.mul_spec(inv_b)),
        );
        // b * inv_b ≡ 1
        // so inv_a * (b * inv_b) ≡ inv_a * 1
        Self::lemma_eqv_mul_congruence_right(inv_a, b.mul_spec(inv_b), one);
        Self::lemma_mul_one_identity(inv_a);
        // inv_a * 1 == inv_a structurally
        Self::lemma_eqv_transitive(
            b.mul_spec(inv_a.mul_spec(inv_b)),
            inv_a.mul_spec(b.mul_spec(inv_b)),
            inv_a.mul_spec(one),
        );
        // inv_a 1 == inv_a
        Self::lemma_eqv_transitive(
            b.mul_spec(inv_a.mul_spec(inv_b)),
            inv_a.mul_spec(one),
            inv_a,
        );
        // So b * prod ≡ inv_a
        // a * (b * prod) ≡ a * inv_a ≡ 1
        Self::lemma_eqv_mul_congruence_right(a, b.mul_spec(prod), inv_a);
        Self::lemma_eqv_transitive(
            a.mul_spec(b.mul_spec(prod)),
            a.mul_spec(inv_a),
            one,
        );
        // a * (b * prod) ≡ 1
        // And (a*b) * prod ≡ a * (b * prod) by assoc
        Self::lemma_eqv_transitive(
            ab.mul_spec(prod),
            a.mul_spec(b.mul_spec(prod)),
            one,
        );
        // So ab * prod ≡ 1 and ab * inv_ab ≡ 1
        // Therefore prod ≡ inv_ab by cancellation
        Self::lemma_mul_cancel_left(prod, inv_ab, ab);
        Self::lemma_eqv_symmetric(prod, inv_ab);
    }

    /// b ≢ 0 → (a/b) * c ≡ (a*c) / b.
    pub proof fn lemma_div_mul_assoc(a: Self, b: Self, c: Self)
        requires
            !b.eqv_spec(Self::from_int_spec(0)),
        ensures
            a.div_spec(b).mul_spec(c).eqv_spec(
                a.mul_spec(c).div_spec(b)),
    {
        Self::lemma_eqv_zero_iff_num_zero(b);
        let inv = Self::lemma_reciprocal_spec_inverse(b);
        // a/b = a * inv, so (a/b)*c = (a*inv)*c
        // (a*c)/b = (a*c)*inv
        // Need: (a*inv)*c ≡ (a*c)*inv
        // By associativity: (a*inv)*c ≡ a*(inv*c)
        Self::lemma_mul_associative(a, inv, c);
        // inv*c == c*inv structurally
        Self::lemma_mul_commutative(inv, c);
        // a*(inv*c) == a*(c*inv) structurally
        // a*(c*inv) ≡ (a*c)*inv by associativity (backward)
        Self::lemma_mul_associative(a, c, inv);
        Self::lemma_eqv_symmetric(a.mul_spec(c).mul_spec(inv), a.mul_spec(c.mul_spec(inv)));
        // Chain: (a*inv)*c ≡ a*(inv*c) = a*(c*inv) ≡ (a*c)*inv
        assert(a.mul_spec(inv.mul_spec(c)) == a.mul_spec(c.mul_spec(inv)));
        Self::lemma_eqv_transitive(
            a.mul_spec(inv).mul_spec(c),
            a.mul_spec(inv.mul_spec(c)),
            a.mul_spec(c).mul_spec(inv),
        );
    }

    /// a ≤ b ∧ c < 0 → b/c ≤ a/c (order reversal).
    pub proof fn lemma_div_neg_denominator(a: Self, b: Self, c: Self)
        requires
            a.le_spec(b),
            c.lt_spec(Self::from_int_spec(0)),
        ensures
            b.div_spec(c).le_spec(a.div_spec(c)),
    {
        let z = Self::from_int_spec(0);
        Self::lemma_denom_positive(c);
        Self::lemma_eqv_zero_iff_num_zero(c);
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(c.num < 0) by (nonlinear_arith)
            requires c.lt_spec(z), z.num == 0, z.denom() == 1;
        let inv = Self::lemma_reciprocal_spec_inverse(c);
        // c < 0 means inv < 0 (since c * inv ≡ 1 > 0, and c < 0, inv must be < 0)
        // Prove inv.num < 0 from the reciprocal_spec definition
        // c.num < 0, so reciprocal_spec goes to the else-if branch:
        // inv = Rational { num: -c.denom(), den: ((-c.num) as nat - 1) as nat }
        // c.denom() > 0 so -c.denom() < 0, so inv.num < 0
        assert(inv.num == -c.denom());
        assert(inv.num < 0) by (nonlinear_arith)
            requires c.denom() > 0, inv.num == -c.denom();
        Self::lemma_denom_positive(inv);
        // Now: a ≤ b and inv < 0 (inv.num < 0, inv.denom() > 0)
        // We want: b*inv ≤ a*inv (multiplication by negative reverses order)
        // a ≤ b means a.num * b.denom() ≤ b.num * a.denom()
        // Need: (b*inv).num * (a*inv).denom() ≤ (a*inv).num * (b*inv).denom()
        // = (b.num * inv.num) * (a.denom() * inv.denom())
        //   ≤ (a.num * inv.num) * (b.denom() * inv.denom())
        Self::lemma_mul_denom_product_int(a, inv);
        Self::lemma_mul_denom_product_int(b, inv);
        assert(a.mul_spec(inv).num == a.num * inv.num);
        assert(b.mul_spec(inv).num == b.num * inv.num);
        assert(a.mul_spec(inv).denom() == a.denom() * inv.denom());
        assert(b.mul_spec(inv).denom() == b.denom() * inv.denom());
        // Use ghost vars so nonlinear_arith can reason with simple names
        let ghost an = a.num;
        let ghost bn = b.num;
        let ghost ad = a.denom();
        let ghost bd = b.denom();
        let ghost in_ = inv.num;
        let ghost id = inv.denom();
        // a ≤ b: an * bd ≤ bn * ad
        assert(an * bd <= bn * ad);
        // Multiply both sides by in_ * id (negative * positive = negative),
        // inequality reverses:
        // (bn * in_) * (ad * id) ≤ (an * in_) * (bd * id)
        assert((an * bd <= bn * ad && in_ < 0 && id > 0) ==>
            (bn * in_) * (ad * id) <= (an * in_) * (bd * id))
            by (nonlinear_arith);
    }

}

} // verus!
