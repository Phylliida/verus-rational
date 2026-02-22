use super::Rational;
use vstd::prelude::*;

verus! {

impl Rational {

    // ── Polynomial evaluation / Horner's method ────────────────────

    /// General Horner evaluation: coeffs[0] + x * (coeffs[1] + x * (... + x * coeffs[n]))
    /// Computes c₀ + c₁x + c₂x² + ... + cₙxⁿ efficiently (n muls, n adds).
    pub open spec fn horner_spec(coeffs: Seq<Self>, x: Self) -> Self
        decreases coeffs.len(),
    {
        if coeffs.len() == 0 {
            Self::from_int_spec(0)
        } else {
            coeffs[0].add_spec(
                x.mul_spec(Self::horner_spec(coeffs.subrange(1, coeffs.len() as int), x))
            )
        }
    }

    /// horner([], x) = 0.
    pub proof fn lemma_horner_empty(x: Self)
        ensures
            Self::horner_spec(Seq::empty(), x) == Self::from_int_spec(0),
    {}

    /// horner([c], x) ≡ c.
    pub proof fn lemma_horner_single(c: Self, x: Self)
        ensures
            Self::horner_spec(seq![c], x).eqv_spec(c),
    {
        let s = seq![c];
        let rest = s.subrange(1, s.len() as int);
        assert(rest =~= Seq::<Self>::empty());
        let z = Self::from_int_spec(0);
        // Help Verus unfold the recursion
        assert(rest.len() == 0);
        assert(Self::horner_spec(rest, x) == z);
        assert(s[0] == c);
        // Now: horner(s, x) == c.add_spec(x.mul_spec(z))
        let hval = c.add_spec(x.mul_spec(z));
        assert(Self::horner_spec(s, x) == hval);
        // x * 0 ≡ 0
        Self::lemma_mul_zero(x);
        // c + x*0 ≡ c + 0
        Self::lemma_eqv_add_congruence_right(c, x.mul_spec(z), z);
        // c + 0 == c (structural)
        Self::lemma_add_zero_identity(c);
        // hval ≡ c+0 ≡ c
    }

    /// horner([c₀, c₁], x) ≡ c₀ + c₁ * x.
    pub proof fn lemma_horner_linear(c0: Self, c1: Self, x: Self)
        ensures
            Self::horner_spec(seq![c0, c1], x).eqv_spec(
                c0.add_spec(c1.mul_spec(x))),
    {
        let s = seq![c0, c1];
        assert(s.subrange(1, 2) =~= seq![c1]);
        // horner([c0, c1], x) = c0 + x * horner([c1], x)
        // horner([c1], x) ≡ c1
        Self::lemma_horner_single(c1, x);
        // x * horner([c1], x) ≡ x * c1
        Self::lemma_eqv_mul_congruence_right(
            x, Self::horner_spec(seq![c1], x), c1,
        );
        // c0 + x*horner ≡ c0 + x*c1
        Self::lemma_eqv_add_congruence_right(
            c0,
            x.mul_spec(Self::horner_spec(seq![c1], x)),
            x.mul_spec(c1),
        );
        // x*c1 == c1*x structurally
        Self::lemma_mul_commutative(x, c1);
    }

    /// horner([c₀, c₁, c₂], x) ≡ c₀ + c₁x + c₂x².
    pub proof fn lemma_horner_quadratic(c0: Self, c1: Self, c2: Self, x: Self)
        ensures
            Self::horner_spec(seq![c0, c1, c2], x).eqv_spec(
                c0.add_spec(c1.mul_spec(x).add_spec(c2.mul_spec(x.mul_spec(x))))),
    {
        let s = seq![c0, c1, c2];
        assert(s.subrange(1, 3) =~= seq![c1, c2]);
        // horner([c0,c1,c2], x) = c0 + x * horner([c1,c2], x)
        // horner([c1,c2], x) ≡ c1 + c2*x
        Self::lemma_horner_linear(c1, c2, x);
        // x * horner([c1,c2], x) ≡ x * (c1 + c2*x)
        Self::lemma_eqv_mul_congruence_right(
            x, Self::horner_spec(seq![c1, c2], x), c1.add_spec(c2.mul_spec(x)),
        );
        // x * (c1 + c2*x) ≡ x*c1 + x*(c2*x) by distributivity
        Self::lemma_eqv_mul_distributive_left(x, c1, c2.mul_spec(x));
        // Chain: x*horner ≡ x*(c1+c2*x) ≡ x*c1 + x*(c2*x)
        Self::lemma_eqv_transitive(
            x.mul_spec(Self::horner_spec(seq![c1, c2], x)),
            x.mul_spec(c1.add_spec(c2.mul_spec(x))),
            x.mul_spec(c1).add_spec(x.mul_spec(c2.mul_spec(x))),
        );
        // x*c1 == c1*x structurally
        Self::lemma_mul_commutative(x, c1);
        // x*(c2*x) ≡ c2*(x*x): assoc gives (x*c2)*x ≡ x*(c2*x),
        // commut gives x*c2 == c2*x, then assoc gives c2*(x*x) ≡ (c2*x)*x
        Self::lemma_mul_associative(x, c2, x);
        Self::lemma_eqv_symmetric(
            x.mul_spec(c2).mul_spec(x),
            x.mul_spec(c2.mul_spec(x)),
        );
        Self::lemma_mul_commutative(x, c2);
        // (x*c2)*x == (c2*x)*x
        Self::lemma_mul_associative(c2, x, x);
        Self::lemma_eqv_symmetric(
            c2.mul_spec(x).mul_spec(x),
            c2.mul_spec(x.mul_spec(x)),
        );
        // Chain: x*(c2*x) ≡ (x*c2)*x == (c2*x)*x ≡ c2*(x*x)
        Self::lemma_eqv_transitive(
            x.mul_spec(c2.mul_spec(x)),
            x.mul_spec(c2).mul_spec(x),
            c2.mul_spec(x.mul_spec(x)),
        );
        // Congruence on add: c1*x + x*(c2*x) ≡ c1*x + c2*(x*x)
        Self::lemma_eqv_add_congruence_right(
            c1.mul_spec(x),
            x.mul_spec(c2.mul_spec(x)),
            c2.mul_spec(x.mul_spec(x)),
        );
        // Chain: x*horner ≡ x*c1 + x*(c2*x) == c1*x + x*(c2*x) ≡ c1*x + c2*(x*x)
        Self::lemma_eqv_transitive(
            x.mul_spec(c1).add_spec(x.mul_spec(c2.mul_spec(x))),
            c1.mul_spec(x).add_spec(x.mul_spec(c2.mul_spec(x))),
            c1.mul_spec(x).add_spec(c2.mul_spec(x.mul_spec(x))),
        );
        Self::lemma_eqv_transitive(
            x.mul_spec(Self::horner_spec(seq![c1, c2], x)),
            x.mul_spec(c1).add_spec(x.mul_spec(c2.mul_spec(x))),
            c1.mul_spec(x).add_spec(c2.mul_spec(x.mul_spec(x))),
        );
        // Outer: c0 + x*horner ≡ c0 + (c1*x + c2*x²)
        Self::lemma_eqv_add_congruence_right(
            c0,
            x.mul_spec(Self::horner_spec(seq![c1, c2], x)),
            c1.mul_spec(x).add_spec(c2.mul_spec(x.mul_spec(x))),
        );
    }

    /// Evaluating at zero: horner(coeffs, 0) ≡ coeffs[0] when non-empty.
    pub proof fn lemma_horner_at_zero(coeffs: Seq<Self>)
        requires
            coeffs.len() > 0,
        ensures
            Self::horner_spec(coeffs, Self::from_int_spec(0)).eqv_spec(coeffs[0]),
    {
        let z = Self::from_int_spec(0);
        let rest = coeffs.subrange(1, coeffs.len() as int);
        // horner(coeffs, 0) = coeffs[0] + 0 * horner(rest, 0)
        // 0 * anything ≡ 0
        Self::lemma_mul_zero(Self::horner_spec(rest, z));
        Self::lemma_eqv_symmetric(
            z.mul_spec(Self::horner_spec(rest, z)),
            z,
        );
        // coeffs[0] + 0*horner ≡ coeffs[0] + 0
        Self::lemma_eqv_add_congruence_right(
            coeffs[0],
            z.mul_spec(Self::horner_spec(rest, z)),
            z,
        );
        // coeffs[0] + 0 == coeffs[0] structurally
        Self::lemma_add_zero_identity(coeffs[0]);
    }

}

} // verus!
