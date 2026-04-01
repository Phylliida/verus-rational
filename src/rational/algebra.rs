use super::Rational;
use verus_algebra::traits::*;
use vstd::prelude::*;

verus! {

//  ── Equivalence ─────────────────────────────────────────────────────

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

    proof fn axiom_eq_implies_eqv(a: Self, b: Self) {
    }
}

//  ── Helper: bridge through canonical ─────────────────────────────────
//
//  Pattern: existing lemma proves `raw.eqv(expected)`.
//  We need `raw.canonical().eqv(expected)`.
//  Chain: canonical(raw).eqv(raw).eqv(expected) by transitivity.

proof fn canonical_eqv_bridge(raw: Rational, expected: Rational)
    requires raw.eqv_spec(expected),
    ensures raw.canonical().eqv_spec(expected),
{
    Rational::lemma_canonical_exists(raw);
    Rational::lemma_eqv_transitive(raw.canonical(), raw, expected);
}

proof fn canonical_eqv_both(a: Rational, b: Rational)
    requires a.eqv_spec(b),
    ensures a.canonical().eqv_spec(b.canonical()),
{
    Rational::lemma_canonical_exists(a);
    Rational::lemma_canonical_exists(b);
    Rational::lemma_eqv_transitive(a.canonical(), a, b);
    Rational::lemma_eqv_transitive(a.canonical(), b, b.canonical());
}

//  ── AdditiveCommutativeMonoid ───────────────────────────────────────

impl AdditiveCommutativeMonoid for Rational {
    open spec fn zero() -> Self {
        Self::from_int_spec(0)
    }

    open spec fn add(self, other: Self) -> Self {
        self.add_spec(other).canonical()
    }

    proof fn axiom_add_commutative(a: Self, b: Self) {
        Self::lemma_add_commutative(a, b);
        canonical_eqv_both(a.add_spec(b), b.add_spec(a));
    }

    proof fn axiom_add_associative(a: Self, b: Self, c: Self) {
        //  LHS: add(add(a,b),c) = add_spec(add_spec(a,b).canonical(), c).canonical()
        //  RHS: add(a, add(b,c)) = add_spec(a, add_spec(b,c).canonical()).canonical()
        //  Bridge inner canonicals through add congruence, then use raw associativity.
        Rational::lemma_canonical_exists(a.add_spec(b));
        Self::lemma_eqv_add_congruence_left(a.add_spec(b).canonical(), a.add_spec(b), c);
        Rational::lemma_canonical_exists(b.add_spec(c));
        Self::lemma_eqv_add_congruence_right(a, b.add_spec(c).canonical(), b.add_spec(c));
        Self::lemma_add_associative(a, b, c);
        //  Chain: LHS raw eqv raw_assoc eqv RHS raw
        canonical_eqv_both(a.add_spec(b).canonical().add_spec(c), a.add_spec(b).add_spec(c));
        canonical_eqv_both(a.add_spec(b).add_spec(c), a.add_spec(b.add_spec(c)));
        canonical_eqv_both(a.add_spec(b.add_spec(c)), a.add_spec(b.add_spec(c).canonical()));
        //  Transitivity: LHS.canonical eqv middle.canonical eqv RHS.canonical
        Self::lemma_eqv_transitive(
            a.add_spec(b).canonical().add_spec(c).canonical(),
            a.add_spec(b).add_spec(c).canonical(),
            a.add_spec(b.add_spec(c)).canonical());
        Self::lemma_eqv_symmetric(
            a.add_spec(b.add_spec(c).canonical()).canonical(),
            a.add_spec(b.add_spec(c)).canonical());
        Self::lemma_eqv_transitive(
            a.add_spec(b).canonical().add_spec(c).canonical(),
            a.add_spec(b.add_spec(c)).canonical(),
            a.add_spec(b.add_spec(c).canonical()).canonical());
    }

    proof fn axiom_add_zero_right(a: Self) {
        Self::lemma_add_zero_identity(a);
        Self::lemma_eqv_reflexive(a);
        canonical_eqv_bridge(a.add_spec(Self::from_int_spec(0)), a);
    }

    proof fn axiom_add_congruence_left(a: Self, b: Self, c: Self) {
        Self::lemma_eqv_add_congruence_left(a, b, c);
        canonical_eqv_both(a.add_spec(c), b.add_spec(c));
    }
}

//  ── AdditiveGroup ───────────────────────────────────────────────────

impl AdditiveGroup for Rational {
    open spec fn neg(self) -> Self {
        self.neg_spec().canonical()
    }

    open spec fn sub(self, other: Self) -> Self {
        self.sub_spec(other).canonical()
    }

    proof fn axiom_add_inverse_right(a: Self) {
        Self::lemma_add_inverse(a);
        //  add_spec(a, neg_spec(a)).eqv(zero)
        //  Need: add_spec(a, neg_spec(a).canonical()).canonical().eqv(zero)
        Rational::lemma_canonical_exists(a.neg_spec());
        Self::lemma_eqv_add_congruence_right(a, a.neg_spec().canonical(), a.neg_spec());
        Self::lemma_eqv_transitive(
            a.add_spec(a.neg_spec().canonical()),
            a.add_spec(a.neg_spec()),
            Self::from_int_spec(0));
        canonical_eqv_bridge(a.add_spec(a.neg_spec().canonical()), Self::from_int_spec(0));
    }

    proof fn axiom_sub_is_add_neg(a: Self, b: Self) {
        //  sub_spec(a,b) == add_spec(a, neg_spec(b)) by definition
        Self::lemma_eqv_reflexive(a.sub_spec(b));
        Rational::lemma_canonical_exists(b.neg_spec());
        Self::lemma_eqv_symmetric(b.neg_spec().canonical(), b.neg_spec());
        Self::lemma_eqv_add_congruence_right(a, b.neg_spec(), b.neg_spec().canonical());
        Self::lemma_eqv_transitive(
            a.sub_spec(b),
            a.add_spec(b.neg_spec()),
            a.add_spec(b.neg_spec().canonical()));
        canonical_eqv_both(a.sub_spec(b), a.add_spec(b.neg_spec().canonical()));
    }

    proof fn axiom_neg_congruence(a: Self, b: Self) {
        Self::lemma_eqv_neg_congruence(a, b);
        canonical_eqv_both(a.neg_spec(), b.neg_spec());
    }
}

//  ── Ring ─────────────────────────────────────────────────────────────

impl Ring for Rational {
    open spec fn one() -> Self {
        Self::from_int_spec(1)
    }

    open spec fn mul(self, other: Self) -> Self {
        self.mul_spec(other).canonical()
    }

    proof fn axiom_mul_commutative(a: Self, b: Self) {
        Self::lemma_mul_commutative(a, b);
        Self::lemma_eqv_reflexive(a.mul_spec(b));
        canonical_eqv_both(a.mul_spec(b), b.mul_spec(a));
    }

    proof fn axiom_mul_associative(a: Self, b: Self, c: Self) {
        Rational::lemma_canonical_exists(a.mul_spec(b));
        Self::lemma_eqv_mul_congruence_left(a.mul_spec(b).canonical(), a.mul_spec(b), c);
        Rational::lemma_canonical_exists(b.mul_spec(c));
        Self::lemma_eqv_mul_congruence_right(a, b.mul_spec(c).canonical(), b.mul_spec(c));
        Self::lemma_mul_associative(a, b, c);
        canonical_eqv_both(a.mul_spec(b).canonical().mul_spec(c), a.mul_spec(b).mul_spec(c));
        canonical_eqv_both(a.mul_spec(b).mul_spec(c), a.mul_spec(b.mul_spec(c)));
        canonical_eqv_both(a.mul_spec(b.mul_spec(c)), a.mul_spec(b.mul_spec(c).canonical()));
        Self::lemma_eqv_transitive(
            a.mul_spec(b).canonical().mul_spec(c).canonical(),
            a.mul_spec(b).mul_spec(c).canonical(),
            a.mul_spec(b.mul_spec(c)).canonical());
        Self::lemma_eqv_symmetric(
            a.mul_spec(b.mul_spec(c).canonical()).canonical(),
            a.mul_spec(b.mul_spec(c)).canonical());
        Self::lemma_eqv_transitive(
            a.mul_spec(b).canonical().mul_spec(c).canonical(),
            a.mul_spec(b.mul_spec(c)).canonical(),
            a.mul_spec(b.mul_spec(c).canonical()).canonical());
    }

    proof fn axiom_mul_one_right(a: Self) {
        Self::lemma_mul_one_identity(a);
        Self::lemma_eqv_reflexive(a);
        canonical_eqv_bridge(a.mul_spec(Self::from_int_spec(1)), a);
    }

    proof fn axiom_mul_zero_right(a: Self) {
        Self::lemma_mul_zero(a);
        canonical_eqv_bridge(a.mul_spec(Self::from_int_spec(0)), Self::from_int_spec(0));
    }

    proof fn axiom_mul_distributes_left(a: Self, b: Self, c: Self) {
        Self::lemma_mul_distributes_over_add(a, b, c);
        //  raw: mul(a, add_raw(b,c)).eqv(add_raw(mul(a,b), mul(a,c)))
        //  LHS: mul(a, add(b,c)) = mul_spec(a, add_spec(b,c).canonical()).canonical()
        Rational::lemma_canonical_exists(b.add_spec(c));
        Self::lemma_eqv_mul_congruence_right(a, b.add_spec(c).canonical(), b.add_spec(c));
        //  RHS: add(mul(a,b), mul(a,c)) = add_spec(mul_spec(a,b).canonical(), mul_spec(a,c).canonical()).canonical()
        Rational::lemma_canonical_exists(a.mul_spec(b));
        Rational::lemma_canonical_exists(a.mul_spec(c));
        Self::lemma_eqv_add_congruence_left(a.mul_spec(b).canonical(), a.mul_spec(b), a.mul_spec(c));
        Self::lemma_eqv_add_congruence_right(a.mul_spec(b).canonical(), a.mul_spec(c).canonical(), a.mul_spec(c));
        Self::lemma_eqv_transitive(
            a.mul_spec(b).canonical().add_spec(a.mul_spec(c).canonical()),
            a.mul_spec(b).canonical().add_spec(a.mul_spec(c)),
            a.mul_spec(b).add_spec(a.mul_spec(c)));
        //  Chain all through canonical
        canonical_eqv_both(a.mul_spec(b.add_spec(c).canonical()), a.mul_spec(b.add_spec(c)));
        canonical_eqv_both(a.mul_spec(b.add_spec(c)), a.mul_spec(b).add_spec(a.mul_spec(c)));
        canonical_eqv_both(
            a.mul_spec(b).canonical().add_spec(a.mul_spec(c).canonical()),
            a.mul_spec(b).add_spec(a.mul_spec(c)));
        Self::lemma_eqv_transitive(
            a.mul_spec(b.add_spec(c).canonical()).canonical(),
            a.mul_spec(b.add_spec(c)).canonical(),
            a.mul_spec(b).add_spec(a.mul_spec(c)).canonical());
        Self::lemma_eqv_symmetric(
            a.mul_spec(b).canonical().add_spec(a.mul_spec(c).canonical()).canonical(),
            a.mul_spec(b).add_spec(a.mul_spec(c)).canonical());
        Self::lemma_eqv_transitive(
            a.mul_spec(b.add_spec(c).canonical()).canonical(),
            a.mul_spec(b).add_spec(a.mul_spec(c)).canonical(),
            a.mul_spec(b).canonical().add_spec(a.mul_spec(c).canonical()).canonical());
    }

    proof fn axiom_one_ne_zero() {
        Self::lemma_eqv_zero_iff_num_zero(Self::from_int_spec(1));
    }

    proof fn axiom_mul_congruence_left(a: Self, b: Self, c: Self) {
        Self::lemma_eqv_mul_congruence_left(a, b, c);
        canonical_eqv_both(a.mul_spec(c), b.mul_spec(c));
    }
}

//  ── PartialOrder ────────────────────────────────────────────────────

impl PartialOrder for Rational {
    open spec fn le(self, other: Self) -> bool {
        self.le_spec(other)
    }

    proof fn axiom_le_reflexive(a: Self) {}

    proof fn axiom_le_antisymmetric(a: Self, b: Self) {
        Self::lemma_le_antisymmetric(a, b);
    }

    proof fn axiom_le_transitive(a: Self, b: Self, c: Self) {
        Self::lemma_le_transitive(a, b, c);
    }

    proof fn axiom_le_congruence(a1: Self, a2: Self, b1: Self, b2: Self) {
        Self::lemma_eqv_symmetric(a1, a2);
        Self::lemma_eqv_implies_le(a2, a1);
        Self::lemma_le_transitive(a2, a1, b1);
        Self::lemma_eqv_implies_le(b1, b2);
        Self::lemma_le_transitive(a2, b1, b2);
    }
}

//  ── OrderedRing ──────────────────────────────────────────────────────

impl OrderedRing for Rational {
    open spec fn lt(self, other: Self) -> bool {
        self.lt_spec(other)
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
        //  raw: add_spec(a,c).le(add_spec(b,c))
        //  Need: canonical(add_spec(a,c)).le(canonical(add_spec(b,c)))
        Rational::lemma_canonical_exists(a.add_spec(c));
        Rational::lemma_canonical_exists(b.add_spec(c));
        Self::lemma_eqv_implies_le(a.add_spec(c).canonical(), a.add_spec(c));
        Self::lemma_le_transitive(a.add_spec(c).canonical(), a.add_spec(c), b.add_spec(c));
        Self::lemma_eqv_symmetric(b.add_spec(c).canonical(), b.add_spec(c));
        Self::lemma_eqv_implies_le(b.add_spec(c), b.add_spec(c).canonical());
        Self::lemma_le_transitive(a.add_spec(c).canonical(), b.add_spec(c), b.add_spec(c).canonical());
    }

    proof fn axiom_le_mul_nonneg_monotone(a: Self, b: Self, c: Self) {
        Self::lemma_le_mul_nonneg(a, b, c);
        Rational::lemma_canonical_exists(a.mul_spec(c));
        Rational::lemma_canonical_exists(b.mul_spec(c));
        Self::lemma_eqv_implies_le(a.mul_spec(c).canonical(), a.mul_spec(c));
        Self::lemma_le_transitive(a.mul_spec(c).canonical(), a.mul_spec(c), b.mul_spec(c));
        Self::lemma_eqv_symmetric(b.mul_spec(c).canonical(), b.mul_spec(c));
        Self::lemma_eqv_implies_le(b.mul_spec(c), b.mul_spec(c).canonical());
        Self::lemma_le_transitive(a.mul_spec(c).canonical(), b.mul_spec(c), b.mul_spec(c).canonical());
    }
}

//  ── Field ────────────────────────────────────────────────────────────

impl Field for Rational {
    open spec fn recip(self) -> Self {
        self.reciprocal_spec().canonical()
    }

    open spec fn div(self, other: Self) -> Self {
        self.div_spec(other).canonical()
    }

    proof fn axiom_mul_recip_right(a: Self) {
        Self::lemma_eqv_zero_iff_num_zero(a);
        Self::lemma_reciprocal_spec_inverse(a);
        Rational::lemma_canonical_exists(a.reciprocal_spec());
        Self::lemma_eqv_mul_congruence_right(a, a.reciprocal_spec().canonical(), a.reciprocal_spec());
        Self::lemma_eqv_transitive(
            a.mul_spec(a.reciprocal_spec().canonical()),
            a.mul_spec(a.reciprocal_spec()),
            Self::from_int_spec(1));
        canonical_eqv_bridge(a.mul_spec(a.reciprocal_spec().canonical()), Self::from_int_spec(1));
    }

    proof fn axiom_div_is_mul_recip(a: Self, b: Self) {
        Self::lemma_eqv_reflexive(a.div_spec(b));
        Rational::lemma_canonical_exists(b.reciprocal_spec());
        Self::lemma_eqv_symmetric(b.reciprocal_spec().canonical(), b.reciprocal_spec());
        Self::lemma_eqv_mul_congruence_right(a, b.reciprocal_spec(), b.reciprocal_spec().canonical());
        Self::lemma_eqv_transitive(
            a.div_spec(b),
            a.mul_spec(b.reciprocal_spec()),
            a.mul_spec(b.reciprocal_spec().canonical()));
        canonical_eqv_both(a.div_spec(b), a.mul_spec(b.reciprocal_spec().canonical()));
    }

    proof fn axiom_recip_congruence(a: Self, b: Self) {
        Self::lemma_eqv_zero_iff_num_zero(a);
        Self::lemma_denom_positive(b);
        assert(b.num != 0) by (nonlinear_arith)
            requires a.num * b.denom() == b.num * a.denom(), a.num != 0, b.denom() >= 1;
        Self::lemma_eqv_zero_iff_num_zero(b);
        Self::lemma_denom_positive(a);
        let ra = a.reciprocal_spec();
        let rb = b.reciprocal_spec();
        assert(ra.num * rb.denom() == rb.num * ra.denom()) by (nonlinear_arith)
            requires
                a.num * b.denom() == b.num * a.denom(),
                a.num != 0, b.num != 0,
                a.denom() >= 1, b.denom() >= 1,
                a.num > 0 ==> (ra.num == a.denom() && ra.denom() == a.num),
                a.num < 0 ==> (ra.num == -a.denom() && ra.denom() == -a.num),
                b.num > 0 ==> (rb.num == b.denom() && rb.denom() == b.num),
                b.num < 0 ==> (rb.num == -b.denom() && rb.denom() == -b.num);
        canonical_eqv_both(ra, rb);
    }
}

//  ── OrderedField ─────────────────────────────────────────────────────

impl OrderedField for Rational {}

} //  verus!
