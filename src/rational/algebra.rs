use super::Rational;
use verus_algebra::traits::*;
use vstd::prelude::*;

verus! {

// ── Equivalence ─────────────────────────────────────────────────────

impl Equivalence for Rational {
    open spec fn eqv(self, other: Self) -> bool {
        self.eqv_spec(other)
    }

    proof fn axiom_eqv_reflexive(a: Self) {
        Self::lemma_eqv_reflexive(a);
    }

    proof fn axiom_eqv_symmetric(a: Self, b: Self) {
        Self::lemma_eqv_symmetric(a, b);
    }

    proof fn axiom_eqv_transitive(a: Self, b: Self, c: Self) {
        Self::lemma_eqv_transitive(a, b, c);
    }
}

// ── AdditiveGroup ───────────────────────────────────────────────────

impl AdditiveGroup for Rational {
    open spec fn zero() -> Self {
        Self::from_int_spec(0)
    }

    open spec fn add(self, other: Self) -> Self {
        self.add_spec(other)
    }

    open spec fn neg(self) -> Self {
        self.neg_spec()
    }

    open spec fn sub(self, other: Self) -> Self {
        self.sub_spec(other)
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {
        Self::lemma_add_commutative(a, b);
    }

    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
        Self::lemma_add_associative(a, b, c);
    }

    proof fn axiom_add_zero_right(a: Self) {
        Self::lemma_add_zero_identity(a);
        Self::lemma_eqv_reflexive(a);
    }

    proof fn axiom_add_inverse_right(a: Self) {
        Self::lemma_add_inverse(a);
    }

    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {
        // sub_spec(a, b) == add_spec(a, neg_spec(b)) by definition
        Self::lemma_eqv_reflexive(a.sub_spec(b));
    }

    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {
        Self::lemma_eqv_add_congruence_left(a, b, c);
    }

    proof fn axiom_neg_congruence(a: Self, b: Self) {
        Self::lemma_eqv_neg_congruence(a, b);
    }
}

// ── Ring ─────────────────────────────────────────────────────────────

impl Ring for Rational {
    open spec fn one() -> Self {
        Self::from_int_spec(1)
    }

    open spec fn mul(self, other: Self) -> Self {
        self.mul_spec(other)
    }

    proof fn axiom_mul_commutative(a: Self, b: Self) {
        Self::lemma_mul_commutative(a, b);
        Self::lemma_eqv_reflexive(a.mul_spec(b));
    }

    proof fn axiom_mul_associative(a: Self, b: Self, c: Self) {
        Self::lemma_mul_associative(a, b, c);
    }

    proof fn axiom_mul_one_right(a: Self) {
        Self::lemma_mul_one_identity(a);
        Self::lemma_eqv_reflexive(a);
    }

    proof fn axiom_mul_zero_right(a: Self) {
        Self::lemma_mul_zero(a);
    }

    proof fn axiom_mul_distributes_left(a: Self, b: Self, c: Self) {
        Self::lemma_mul_distributes_over_add(a, b, c);
    }

    proof fn axiom_one_ne_zero() {
        Self::lemma_eqv_zero_iff_num_zero(Self::from_int_spec(1));
    }

    proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self) {
        Self::lemma_eqv_mul_congruence_left(a, b, c);
    }
}

// ── OrderedRing ──────────────────────────────────────────────────────

impl OrderedRing for Rational {
    open spec fn le(self, other: Self) -> bool {
        self.le_spec(other)
    }

    open spec fn lt(self, other: Self) -> bool {
        self.lt_spec(other)
    }

    proof fn axiom_le_reflexive(a: Self) {
        // a.le_spec(a) == (a.num * a.denom() <= a.num * a.denom()), trivially true
    }

    proof fn axiom_le_antisymmetric(a: Self, b: Self) {
        Self::lemma_le_antisymmetric(a, b);
    }

    proof fn axiom_le_transitive(a: Self, b: Self, c: Self) {
        Self::lemma_le_transitive(a, b, c);
    }

    proof fn axiom_le_total(a: Self, b: Self) {
        Self::lemma_trichotomy(a, b);
        Self::lemma_le_iff_lt_or_eqv(a, b);
        Self::lemma_le_iff_lt_or_eqv(b, a);
    }

    proof fn axiom_lt_iff_le_and_not_eqv(a: Self, b: Self) {
        Self::lemma_le_iff_lt_or_eqv(a, b);
        Self::lemma_trichotomy(a, b);
    }

    proof fn axiom_le_add_monotone(a: Self, b: Self, c: Self) {
        Self::lemma_le_add_monotone(a, b, c);
    }

    proof fn axiom_le_mul_nonneg_monotone(a: Self, b: Self, c: Self) {
        Self::lemma_le_mul_nonneg(a, b, c);
    }

    proof fn axiom_le_congruence(a1: Self, a2: Self, b1: Self, b2: Self) {
        Self::lemma_eqv_symmetric(a1, a2);     // a2 ≡ a1
        Self::lemma_eqv_implies_le(a2, a1);    // a2 ≤ a1
        Self::lemma_le_transitive(a2, a1, b1); // a2 ≤ b1
        Self::lemma_eqv_implies_le(b1, b2);    // b1 ≤ b2
        Self::lemma_le_transitive(a2, b1, b2); // a2 ≤ b2
    }
}

// ── Field ────────────────────────────────────────────────────────────

impl Field for Rational {
    open spec fn recip(self) -> Self {
        self.reciprocal_spec()
    }

    open spec fn div(self, other: Self) -> Self {
        self.div_spec(other)
    }

    proof fn axiom_mul_recip_right(a: Self) {
        // requires: !a.eqv(Self::zero()), i.e. !a.eqv_spec(from_int_spec(0))
        // Bridge: eqv_spec(0) ↔ num == 0
        Self::lemma_eqv_zero_iff_num_zero(a);
        Self::lemma_reciprocal_spec_inverse(a);
    }

    proof fn axiom_div_is_mul_recip(a: Self, b: Self) {
        // div_spec(a, b) == mul_spec(a, reciprocal_spec(b)) by definition
        Self::lemma_eqv_reflexive(a.div_spec(b));
    }

    proof fn axiom_recip_congruence(a: Self, b: Self) {
        // Given: a ≡ b, !a.eqv(0). Show: recip(a) ≡ recip(b).
        Self::lemma_eqv_zero_iff_num_zero(a);
        Self::lemma_eqv_zero_iff_num_zero(b);
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        // a ≡ b means a.num * b.denom() == b.num * a.denom()
        // !a.eqv(0) means a.num != 0
        // a.num != 0 and a.num * b.denom() == b.num * a.denom() with denoms > 0
        // implies b.num != 0
        assert(a.num != 0);
        assert(a.num * b.denom() == b.num * a.denom());
        assert((a.num * b.denom() == b.num * a.denom() && a.num != 0 && a.denom() > 0)
            ==> b.num != 0) by (nonlinear_arith);

        // Get inverses
        let inv_a = Self::lemma_reciprocal_spec_inverse(a);
        let inv_b = Self::lemma_reciprocal_spec_inverse(b);

        // a * inv_a ≡ 1 and b * inv_b ≡ 1
        let one = Self::from_int_spec(1);

        // a ≡ b, so a*inv_a ≡ b*inv_a (left congruence)
        Self::lemma_eqv_mul_congruence_left(a, b, inv_a);
        // a*inv_a ≡ 1, so b*inv_a ≡ 1 (by symmetry + transitivity)
        Self::lemma_eqv_symmetric(a.mul_spec(inv_a), b.mul_spec(inv_a));
        Self::lemma_eqv_transitive(b.mul_spec(inv_a), a.mul_spec(inv_a), one);
        // b*inv_a ≡ 1 and b*inv_b ≡ 1
        // So b*inv_a ≡ b*inv_b
        Self::lemma_eqv_symmetric(b.mul_spec(inv_b), one);
        Self::lemma_eqv_transitive(b.mul_spec(inv_a), one, b.mul_spec(inv_b));

        // Cancel b: inv_a ≡ inv_b
        // b ≢ 0 since b.num != 0
        Self::lemma_mul_cancel_left(inv_a, inv_b, b);
    }
}

// ── OrderedField ─────────────────────────────────────────────────────

impl OrderedField for Rational {}

} // verus!
