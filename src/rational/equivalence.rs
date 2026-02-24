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
    /// a ≡ a.
    pub proof fn lemma_eqv_reflexive(a: Self)
        ensures
            a.eqv_spec(a),
    {
        assert(a.num * a.denom() == a.num * a.denom());
    }

    /// a ≡ b ↔ b ≡ a.
    pub proof fn lemma_eqv_symmetric(a: Self, b: Self)
        ensures
            a.eqv_spec(b) == b.eqv_spec(a),
    {
        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(b.eqv_spec(a) == (b.num * a.denom() == a.num * b.denom()));
    }

    /// a ≡ b ∧ b ≡ c → a ≡ c.
    pub proof fn lemma_eqv_transitive(a: Self, b: Self, c: Self)
        requires
            a.eqv_spec(b),
            b.eqv_spec(c),
        ensures
            a.eqv_spec(c),
    {
        Self::lemma_denom_positive(b);
        assert(b.denom() != 0);

        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(b.eqv_spec(c) == (b.num * c.denom() == c.num * b.denom()));
        assert(a.num * b.denom() == b.num * a.denom());
        assert(b.num * c.denom() == c.num * b.denom());

        calc! {
            (==)
            a.num * b.denom() * c.denom();
            {
                assert(a.num * b.denom() == b.num * a.denom());
            }
            b.num * a.denom() * c.denom();
            {
                assert(b.num * a.denom() * c.denom() == b.num * c.denom() * a.denom()) by (nonlinear_arith);
            }
            b.num * c.denom() * a.denom();
            {
                assert(b.num * c.denom() == c.num * b.denom());
            }
            c.num * b.denom() * a.denom();
        }
        assert((b.denom() != 0 && a.num * b.denom() * c.denom() == c.num * b.denom() * a.denom())
            ==> (a.num * c.denom() == c.num * a.denom())) by (nonlinear_arith);
        assert(a.num * c.denom() == c.num * a.denom());
    }

    /// Canonical normalization predicate for the model:
    /// among semantically-equivalent representations, this value has a
    /// minimal denominator.
    pub open spec fn normalized_spec(self) -> bool {
        forall|other: Self| #[trigger] self.eqv_spec(other) ==> self.denom_nat() <= other.denom_nat()
    }

    /// from_int(v) is normalized (denominator 1 is minimal).
    pub proof fn lemma_from_int_is_normalized(value: int)
        ensures
            Self::from_int_spec(value).normalized_spec(),
    {
        let s = Self::from_int_spec(value);
        assert(s.denom_nat() == 1);
        assert forall|other: Self| #![auto] s.eqv_spec(other) implies s.denom_nat() <= other.denom_nat() by {
            Self::lemma_denom_positive(other);
            assert(other.denom_nat() > 0);
            assert(1 <= other.denom_nat());
        };
    }

    /// Two normalized equivalents have equal denominators.
    pub proof fn lemma_normalized_eqv_implies_equal_denom(a: Self, b: Self)
        requires
            a.normalized_spec(),
            b.normalized_spec(),
            a.eqv_spec(b),
        ensures
            a.denom_nat() == b.denom_nat(),
    {
        Self::lemma_eqv_symmetric(a, b);
        assert(a.eqv_spec(b) == b.eqv_spec(a));
        assert(b.eqv_spec(a));

        assert(a.denom_nat() <= b.denom_nat());
        assert(b.denom_nat() <= a.denom_nat());
        assert((a.denom_nat() <= b.denom_nat() && b.denom_nat() <= a.denom_nat())
            ==> a.denom_nat() == b.denom_nat()) by (nonlinear_arith);
        assert(a.denom_nat() == b.denom_nat());
    }

    /// a ≡ b with equal denominators implies equal numerators.
    pub proof fn lemma_eqv_and_equal_denom_implies_equal_num(a: Self, b: Self)
        requires
            a.eqv_spec(b),
            a.denom_nat() == b.denom_nat(),
        ensures
            a.num == b.num,
    {
        Self::lemma_denom_positive(a);
        assert(a.denom() > 0);
        assert(a.denom() != 0);

        assert(a.denom() == a.denom_nat() as int);
        assert(b.denom() == b.denom_nat() as int);
        assert((a.denom_nat() as int) == (b.denom_nat() as int));
        assert(a.denom() == b.denom());

        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(a.num * b.denom() == b.num * a.denom());
        assert(a.num * a.denom() == b.num * a.denom());
        assert((a.denom() != 0 && a.num * a.denom() == b.num * a.denom()) ==> (a.num == b.num))
            by (nonlinear_arith);
        assert(a.num == b.num);
    }

    /// Strongest normalization bridge currently available:
    /// normalized semantic-equality implies structural equality.
    pub proof fn lemma_normalized_eqv_implies_equal(a: Self, b: Self)
        requires
            a.normalized_spec(),
            b.normalized_spec(),
            a.eqv_spec(b),
        ensures
            a == b,
    {
        Self::lemma_normalized_eqv_implies_equal_denom(a, b);
        Self::lemma_eqv_and_equal_denom_implies_equal_num(a, b);
        assert(a.den + 1 == b.den + 1);
        assert((a.den + 1 == b.den + 1) ==> a.den == b.den) by (nonlinear_arith);
        assert(a.den == b.den);
        assert(a.num == b.num);
        assert(a == b);
    }

    /// Normalized values use canonical zero representation.
    pub proof fn lemma_normalized_zero_has_unit_denom(a: Self)
        requires
            a.normalized_spec(),
            a.num == 0,
        ensures
            a.denom_nat() == 1,
    {
        let z = Self::from_int_spec(0);
        Self::lemma_eqv_zero_iff_num_zero(a);
        assert(a.eqv_spec(z) == (a.num == 0));
        assert(a.eqv_spec(z));
        assert(a.denom_nat() <= z.denom_nat());
        assert(z.denom_nat() == 1);
        Self::lemma_denom_positive(a);
        assert(a.denom_nat() > 0);
        assert((a.denom_nat() > 0 && a.denom_nat() <= 1) ==> a.denom_nat() == 1) by (nonlinear_arith);
        assert(a.denom_nat() == 1);
    }

    /// Canonical sign placement for rationals:
    /// denominator positive, and zero has denominator `1`.
    pub open spec fn canonical_sign_spec(self) -> bool {
        &&& self.denom_nat() > 0
        &&& (self.num == 0 ==> self.denom_nat() == 1)
    }

    pub open spec fn common_divisor_spec(self, d: nat) -> bool {
        &&& d > 0
        &&& exists|kn: int, kd: nat|
            (#[trigger] (d * kd)) == self.denom_nat()
                && (#[trigger] ((d as int) * kn)) == self.num
    }

    pub open spec fn gcd_one_spec(self) -> bool {
        forall|d: nat| #![auto] self.common_divisor_spec(d) ==> d == 1
    }

    pub proof fn lemma_normalized_implies_gcd_one(a: Self)
        requires
            a.normalized_spec(),
        ensures
            a.gcd_one_spec(),
    {
        assert forall|d: nat| #![auto] a.common_divisor_spec(d) implies d == 1 by {
            assert(d > 0);
            let (kn, kd) = choose|kn: int, kd: nat|
                (#[trigger] ((d as int) * kn)) == a.num && (#[trigger] (d * kd)) == a.denom_nat();
            assert((d as int) * kn == a.num);
            assert(d * kd == a.denom_nat());

            if d == 1 {
                assert(d == 1);
            } else {
                assert(d != 1);
                assert((d > 0 && d != 1) ==> 1 < d) by (nonlinear_arith);
                assert(1 < d);
                Self::lemma_denom_positive(a);
                assert(a.denom_nat() > 0);
                assert((d > 0 && d * kd == a.denom_nat() && a.denom_nat() > 0) ==> kd > 0)
                    by (nonlinear_arith);
                assert(kd > 0);

                let b = Rational { num: kn, den: (kd as int - 1) as nat };
                assert(b.denom_nat() == kd);
                assert(b.denom() == b.denom_nat() as int);
                assert(a.denom() == a.denom_nat() as int);
                Self::lemma_nat_mul_cast(d, kd);
                assert((d * kd) as int == (d as int) * (kd as int));
                assert((d as int) * (kd as int) == a.denom());
                assert(b.denom_nat() == kd);
                assert(b.denom() == kd as int);

                assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
                assert(a.num == (d as int) * kn);
                assert(b.num == kn);
                assert(a.num * b.denom() == ((d as int) * kn) * (kd as int));
                assert(b.num * a.denom() == kn * ((d as int) * (kd as int)));
                assert(((d as int) * kn) * (kd as int) == kn * ((d as int) * (kd as int)))
                    by (nonlinear_arith);
                assert(a.eqv_spec(b));

                assert(a.denom_nat() <= b.denom_nat());
                assert(a.denom_nat() == d * kd);
                assert((d > 1 && kd > 0) ==> kd < d * kd) by (nonlinear_arith);
                assert(b.denom_nat() == kd);
                assert(b.denom_nat() < a.denom_nat());
                assert((a.denom_nat() <= b.denom_nat() && b.denom_nat() < a.denom_nat()) ==> false)
                    by (nonlinear_arith);
                assert(false);
            }
        };
    }

    pub proof fn lemma_normalized_implies_canonical_sign(a: Self)
        requires
            a.normalized_spec(),
        ensures
            a.canonical_sign_spec(),
    {
        Self::lemma_denom_positive(a);
        if a.num == 0 {
            Self::lemma_normalized_zero_has_unit_denom(a);
        }
    }

    pub proof fn lemma_nat_not_le_prev_implies_ge_bound(x: nat, bound: nat)
        requires
            bound > 0,
            !(x <= bound - 1),
        ensures
            bound <= x,
    {
        assert((bound > 0 && !(x <= bound - 1)) ==> bound <= x) by (nonlinear_arith);
        assert(bound <= x);
    }

    pub proof fn lemma_nat_le_and_not_le_prev_implies_eq(x: nat, bound: nat)
        requires
            bound > 0,
            x <= bound,
            !(x <= bound - 1),
        ensures
            x == bound,
    {
        Self::lemma_nat_not_le_prev_implies_ge_bound(x, bound);
        assert(bound <= x);
        assert((bound <= x && x <= bound) ==> x == bound) by (nonlinear_arith);
        assert(x == bound);
    }

    /// Constructively picks an equivalent scalar whose denominator is minimal
    /// among all equivalent forms with denominator at most `bound`.
    pub proof fn normalize_bounded(a: Self, bound: nat) -> (m: Self)
        requires
            exists|s: Self| #![auto] s.eqv_spec(a) && s.denom_nat() <= bound,
        ensures
            m.eqv_spec(a),
            m.denom_nat() <= bound,
            forall|t: Self| #![auto]
                t.eqv_spec(a) && t.denom_nat() <= bound ==> m.denom_nat() <= t.denom_nat(),
        decreases bound,
    {
        if bound == 0 {
            let s = choose|s: Self| #![auto] s.eqv_spec(a) && s.denom_nat() <= bound;
            Self::lemma_denom_positive(s);
            assert(s.denom_nat() > 0);
            assert(s.denom_nat() <= 0);
            assert(false);
            s
        } else {
            let prev = (bound as int - 1) as nat;
            if exists|s: Self| #![auto] s.eqv_spec(a) && s.denom_nat() <= prev {
                let mprev = Self::normalize_bounded(a, prev);
                assert(mprev.eqv_spec(a));
                assert(mprev.denom_nat() <= prev);
                assert((mprev.denom_nat() <= prev && prev <= bound) ==> mprev.denom_nat() <= bound)
                    by (nonlinear_arith);
                assert(mprev.denom_nat() <= bound);

                assert forall|t: Self| #![auto]
                    t.eqv_spec(a) && t.denom_nat() <= bound implies mprev.denom_nat() <= t.denom_nat() by {
                    if t.denom_nat() <= prev {
                        assert(t.eqv_spec(a) && t.denom_nat() <= prev);
                        assert(mprev.denom_nat() <= t.denom_nat());
                    } else {
                        Self::lemma_nat_not_le_prev_implies_ge_bound(t.denom_nat(), bound);
                        assert(bound <= t.denom_nat());
                        assert((mprev.denom_nat() <= bound && bound <= t.denom_nat())
                            ==> mprev.denom_nat() <= t.denom_nat()) by (nonlinear_arith);
                        assert(mprev.denom_nat() <= t.denom_nat());
                    }
                };
                mprev
            } else {
                let s0 = choose|s: Self| #![auto] s.eqv_spec(a) && s.denom_nat() <= bound;
                assert(s0.eqv_spec(a));
                assert(s0.denom_nat() <= bound);
                if s0.denom_nat() <= prev {
                    assert(exists|s: Self| #![auto] s.eqv_spec(a) && s.denom_nat() <= prev) by {
                        assert(s0.eqv_spec(a));
                        assert(s0.denom_nat() <= prev);
                    };
                    assert(false);
                }
                Self::lemma_nat_le_and_not_le_prev_implies_eq(s0.denom_nat(), bound);
                assert(s0.denom_nat() == bound);

                assert forall|t: Self| #![auto]
                    t.eqv_spec(a) && t.denom_nat() <= bound implies s0.denom_nat() <= t.denom_nat() by {
                    if t.denom_nat() <= prev {
                        assert(exists|s: Self| #![auto] s.eqv_spec(a) && s.denom_nat() <= prev) by {
                            assert(t.eqv_spec(a));
                            assert(t.denom_nat() <= prev);
                        };
                        assert(false);
                    } else {
                        Self::lemma_nat_not_le_prev_implies_ge_bound(t.denom_nat(), bound);
                        assert(bound <= t.denom_nat());
                        assert(s0.denom_nat() == bound);
                        assert(s0.denom_nat() <= t.denom_nat());
                    }
                };
                s0
            }
        }
    }

    /// Fully verified constructive normalization:
    /// returns an equivalent scalar with globally minimal denominator.
    pub proof fn normalize_constructive(a: Self) -> (m: Self)
        ensures
            m.eqv_spec(a),
            m.normalized_spec(),
            m.canonical_sign_spec(),
    {
        Self::lemma_eqv_reflexive(a);
        assert(exists|s: Self| #![auto] s.eqv_spec(a) && s.denom_nat() <= a.denom_nat()) by {
            assert(a.eqv_spec(a));
            assert(a.denom_nat() <= a.denom_nat());
        };
        let m0 = Self::normalize_bounded(a, a.denom_nat());
        assert(m0.eqv_spec(a));
        assert(m0.denom_nat() <= a.denom_nat());

        assert forall|t: Self| #![auto] m0.eqv_spec(t) implies m0.denom_nat() <= t.denom_nat() by {
            Self::lemma_eqv_symmetric(m0, t);
            assert(m0.eqv_spec(t) == t.eqv_spec(m0));
            assert(t.eqv_spec(m0));
            Self::lemma_eqv_transitive(t, m0, a);
            assert(t.eqv_spec(a));
            if t.denom_nat() <= a.denom_nat() {
                assert(m0.denom_nat() <= t.denom_nat());
            } else {
                assert((!(t.denom_nat() <= a.denom_nat())) ==> a.denom_nat() <= t.denom_nat())
                    by (nonlinear_arith);
                assert(a.denom_nat() <= t.denom_nat());
                assert((m0.denom_nat() <= a.denom_nat() && a.denom_nat() <= t.denom_nat())
                    ==> m0.denom_nat() <= t.denom_nat()) by (nonlinear_arith);
                assert(m0.denom_nat() <= t.denom_nat());
            }
        };
        assert(m0.normalized_spec());
        Self::lemma_normalized_implies_canonical_sign(m0);
        assert(m0.canonical_sign_spec());
        m0
    }

    pub proof fn lemma_eqv_neg_congruence(a: Self, b: Self)
        requires
            a.eqv_spec(b),
        ensures
            a.neg_spec().eqv_spec(b.neg_spec()),
    {
        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(a.neg_spec().eqv_spec(b.neg_spec())
            == (a.neg_spec().num * b.neg_spec().denom() == b.neg_spec().num * a.neg_spec().denom()));
        assert(a.neg_spec().num == -a.num);
        assert(b.neg_spec().num == -b.num);
        assert(a.neg_spec().denom() == a.denom());
        assert(b.neg_spec().denom() == b.denom());
        assert((a.num * b.denom() == b.num * a.denom())
            ==> ((-a.num) * b.denom() == (-b.num) * a.denom())) by (nonlinear_arith);
        assert(a.neg_spec().eqv_spec(b.neg_spec()));
    }

    pub proof fn lemma_eqv_add_congruence_left(a: Self, b: Self, c: Self)
        requires
            a.eqv_spec(b),
        ensures
            a.add_spec(c).eqv_spec(b.add_spec(c)),
    {
        let ac = a.add_spec(c);
        let bc = b.add_spec(c);
        Self::lemma_add_denom_product_int(a, c);
        Self::lemma_add_denom_product_int(b, c);
        assert(ac.num == a.num * c.denom() + c.num * a.denom());
        assert(bc.num == b.num * c.denom() + c.num * b.denom());
        assert(ac.denom() == a.denom() * c.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(a.num * b.denom() == b.num * a.denom());
        assert(ac.eqv_spec(bc) == (ac.num * bc.denom() == bc.num * ac.denom()));
        assert((a.num * b.denom() == b.num * a.denom())
            ==> ((a.num * c.denom() + c.num * a.denom()) * (b.denom() * c.denom())
                == (b.num * c.denom() + c.num * b.denom()) * (a.denom() * c.denom())))
            by (nonlinear_arith);
        assert((a.num * c.denom() + c.num * a.denom()) * (b.denom() * c.denom())
            == (b.num * c.denom() + c.num * b.denom()) * (a.denom() * c.denom()));
        calc! {
            (==)
            ac.num * bc.denom();
            {
                assert(ac.num == a.num * c.denom() + c.num * a.denom());
                assert(bc.denom() == b.denom() * c.denom());
            }
            (a.num * c.denom() + c.num * a.denom()) * (b.denom() * c.denom());
            { }
            (b.num * c.denom() + c.num * b.denom()) * (a.denom() * c.denom());
            {
                assert(bc.num == b.num * c.denom() + c.num * b.denom());
                assert(ac.denom() == a.denom() * c.denom());
            }
            bc.num * ac.denom();
        }
        assert(ac.eqv_spec(bc));
    }

    pub proof fn lemma_eqv_add_congruence_right(a: Self, b: Self, c: Self)
        requires
            b.eqv_spec(c),
        ensures
            a.add_spec(b).eqv_spec(a.add_spec(c)),
    {
        let ab = a.add_spec(b);
        let ac = a.add_spec(c);
        Self::lemma_add_denom_product_int(a, b);
        Self::lemma_add_denom_product_int(a, c);
        assert(ab.num == a.num * b.denom() + b.num * a.denom());
        assert(ac.num == a.num * c.denom() + c.num * a.denom());
        assert(ab.denom() == a.denom() * b.denom());
        assert(ac.denom() == a.denom() * c.denom());
        assert(b.eqv_spec(c) == (b.num * c.denom() == c.num * b.denom()));
        assert(b.num * c.denom() == c.num * b.denom());
        assert(ab.eqv_spec(ac) == (ab.num * ac.denom() == ac.num * ab.denom()));
        assert((b.num * c.denom() == c.num * b.denom())
            ==> ((a.num * b.denom() + b.num * a.denom()) * (a.denom() * c.denom())
                == (a.num * c.denom() + c.num * a.denom()) * (a.denom() * b.denom())))
            by (nonlinear_arith);
        assert((a.num * b.denom() + b.num * a.denom()) * (a.denom() * c.denom())
            == (a.num * c.denom() + c.num * a.denom()) * (a.denom() * b.denom()));
        calc! {
            (==)
            ab.num * ac.denom();
            {
                assert(ab.num == a.num * b.denom() + b.num * a.denom());
                assert(ac.denom() == a.denom() * c.denom());
            }
            (a.num * b.denom() + b.num * a.denom()) * (a.denom() * c.denom());
            { }
            (a.num * c.denom() + c.num * a.denom()) * (a.denom() * b.denom());
            {
                assert(ac.num == a.num * c.denom() + c.num * a.denom());
                assert(ab.denom() == a.denom() * b.denom());
            }
            ac.num * ab.denom();
        }
        assert(ab.eqv_spec(ac));
    }

    pub proof fn lemma_eqv_add_congruence(a1: Self, a2: Self, b1: Self, b2: Self)
        requires
            a1.eqv_spec(a2),
            b1.eqv_spec(b2),
        ensures
            a1.add_spec(b1).eqv_spec(a2.add_spec(b2)),
    {
        Self::lemma_eqv_add_congruence_left(a1, a2, b1);
        Self::lemma_eqv_add_congruence_right(a2, b1, b2);
        Self::lemma_eqv_transitive(a1.add_spec(b1), a2.add_spec(b1), a2.add_spec(b2));
    }

    pub proof fn lemma_eqv_mul_congruence_left(a: Self, b: Self, c: Self)
        requires
            a.eqv_spec(b),
        ensures
            a.mul_spec(c).eqv_spec(b.mul_spec(c)),
    {
        let ac = a.mul_spec(c);
        let bc = b.mul_spec(c);
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_mul_denom_product_int(b, c);
        assert(ac.num == a.num * c.num);
        assert(bc.num == b.num * c.num);
        assert(ac.denom() == a.denom() * c.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(a.num * b.denom() == b.num * a.denom());
        assert(ac.eqv_spec(bc) == (ac.num * bc.denom() == bc.num * ac.denom()));
        assert((a.num * b.denom() == b.num * a.denom())
            ==> ((a.num * c.num) * (b.denom() * c.denom())
                == (b.num * c.num) * (a.denom() * c.denom())))
            by (nonlinear_arith);
        assert((a.num * c.num) * (b.denom() * c.denom())
            == (b.num * c.num) * (a.denom() * c.denom()));
        calc! {
            (==)
            ac.num * bc.denom();
            {
                assert(ac.num == a.num * c.num);
                assert(bc.denom() == b.denom() * c.denom());
            }
            (a.num * c.num) * (b.denom() * c.denom());
            { }
            (b.num * c.num) * (a.denom() * c.denom());
            {
                assert(bc.num == b.num * c.num);
                assert(ac.denom() == a.denom() * c.denom());
            }
            bc.num * ac.denom();
        }
        assert(ac.eqv_spec(bc));
    }

    pub proof fn lemma_eqv_mul_congruence_right(a: Self, b: Self, c: Self)
        requires
            b.eqv_spec(c),
        ensures
            a.mul_spec(b).eqv_spec(a.mul_spec(c)),
    {
        let ab = a.mul_spec(b);
        let ac = a.mul_spec(c);
        Self::lemma_mul_denom_product_int(a, b);
        Self::lemma_mul_denom_product_int(a, c);
        assert(ab.num == a.num * b.num);
        assert(ac.num == a.num * c.num);
        assert(ab.denom() == a.denom() * b.denom());
        assert(ac.denom() == a.denom() * c.denom());
        assert(b.eqv_spec(c) == (b.num * c.denom() == c.num * b.denom()));
        assert(b.num * c.denom() == c.num * b.denom());
        assert(ab.eqv_spec(ac) == (ab.num * ac.denom() == ac.num * ab.denom()));
        assert((b.num * c.denom() == c.num * b.denom())
            ==> ((a.num * b.num) * (a.denom() * c.denom())
                == (a.num * c.num) * (a.denom() * b.denom())))
            by (nonlinear_arith);
        assert((a.num * b.num) * (a.denom() * c.denom())
            == (a.num * c.num) * (a.denom() * b.denom()));
        calc! {
            (==)
            ab.num * ac.denom();
            {
                assert(ab.num == a.num * b.num);
                assert(ac.denom() == a.denom() * c.denom());
            }
            (a.num * b.num) * (a.denom() * c.denom());
            { }
            (a.num * c.num) * (a.denom() * b.denom());
            {
                assert(ac.num == a.num * c.num);
                assert(ab.denom() == a.denom() * b.denom());
            }
            ac.num * ab.denom();
        }
        assert(ab.eqv_spec(ac));
    }

    pub proof fn lemma_eqv_mul_congruence(a1: Self, a2: Self, b1: Self, b2: Self)
        requires
            a1.eqv_spec(a2),
            b1.eqv_spec(b2),
        ensures
            a1.mul_spec(b1).eqv_spec(a2.mul_spec(b2)),
    {
        Self::lemma_eqv_mul_congruence_left(a1, a2, b1);
        Self::lemma_eqv_mul_congruence_right(a2, b1, b2);
        Self::lemma_eqv_transitive(a1.mul_spec(b1), a2.mul_spec(b1), a2.mul_spec(b2));
    }

    pub proof fn lemma_eqv_sub_congruence(a1: Self, a2: Self, b1: Self, b2: Self)
        requires
            a1.eqv_spec(a2),
            b1.eqv_spec(b2),
        ensures
            a1.sub_spec(b1).eqv_spec(a2.sub_spec(b2)),
    {
        Self::lemma_eqv_neg_congruence(b1, b2);
        Self::lemma_eqv_add_congruence(a1, a2, b1.neg_spec(), b2.neg_spec());
        assert(a1.sub_spec(b1) == a1.add_spec(b1.neg_spec()));
        assert(a2.sub_spec(b2) == a2.add_spec(b2.neg_spec()));
        assert(a1.add_spec(b1.neg_spec()).eqv_spec(a2.add_spec(b2.neg_spec())));
        assert(a1.sub_spec(b1).eqv_spec(a2.sub_spec(b2)));
    }

    pub proof fn lemma_eqv_mul_distributive_left(a: Self, b: Self, c: Self)
        ensures
            a.mul_spec(b.add_spec(c)).eqv_spec(a.mul_spec(b).add_spec(a.mul_spec(c))),
    {
        let bc = b.add_spec(c);
        let lhs = a.mul_spec(bc);
        let ab = a.mul_spec(b);
        let ac = a.mul_spec(c);
        let rhs = ab.add_spec(ac);

        Self::lemma_add_denom_product_int(b, c);
        Self::lemma_mul_denom_product_int(a, bc);
        Self::lemma_mul_denom_product_int(a, b);
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_add_denom_product_int(ab, ac);

        assert(bc.num == b.num * c.denom() + c.num * b.denom());
        assert(lhs.num == a.num * bc.num);
        assert(lhs.num == a.num * (b.num * c.denom() + c.num * b.denom()));
        assert(lhs.denom() == a.denom() * bc.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(lhs.denom() == a.denom() * (b.denom() * c.denom()));

        assert(ab.num == a.num * b.num);
        assert(ac.num == a.num * c.num);
        assert(ab.denom() == a.denom() * b.denom());
        assert(ac.denom() == a.denom() * c.denom());
        assert(rhs.num == ab.num * ac.denom() + ac.num * ab.denom());
        calc! {
            (==)
            rhs.num;
            { }
            ab.num * ac.denom() + ac.num * ab.denom();
            {
                assert(ab.num == a.num * b.num);
                assert(ac.num == a.num * c.num);
                assert(ab.denom() == a.denom() * b.denom());
                assert(ac.denom() == a.denom() * c.denom());
            }
            (a.num * b.num) * (a.denom() * c.denom()) + (a.num * c.num) * (a.denom() * b.denom());
            {
                assert((a.num * b.num) * (a.denom() * c.denom())
                    == (a.num * a.denom()) * (b.num * c.denom())) by (nonlinear_arith);
                assert((a.num * c.num) * (a.denom() * b.denom())
                    == (a.num * a.denom()) * (c.num * b.denom())) by (nonlinear_arith);
                assert((a.num * a.denom()) * (b.num * c.denom()) + (a.num * a.denom()) * (c.num * b.denom())
                    == a.num * a.denom() * (b.num * c.denom() + c.num * b.denom())) by (nonlinear_arith);
            }
            a.num * a.denom() * (b.num * c.denom() + c.num * b.denom());
        }
        assert(rhs.denom() == ab.denom() * ac.denom());
        assert(rhs.denom() == (a.denom() * b.denom()) * (a.denom() * c.denom()));

        assert(lhs.eqv_spec(rhs) == (lhs.num * rhs.denom() == rhs.num * lhs.denom()));
        calc! {
            (==)
            lhs.num * rhs.denom();
            {
                assert(lhs.num == a.num * (b.num * c.denom() + c.num * b.denom()));
                assert(rhs.denom() == (a.denom() * b.denom()) * (a.denom() * c.denom()));
            }
            (a.num * (b.num * c.denom() + c.num * b.denom()))
                * ((a.denom() * b.denom()) * (a.denom() * c.denom()));
        }
        calc! {
            (==)
            rhs.num * lhs.denom();
            {
                assert(rhs.num == a.num * a.denom() * (b.num * c.denom() + c.num * b.denom()));
                assert(lhs.denom() == a.denom() * (b.denom() * c.denom()));
            }
            (a.num * a.denom() * (b.num * c.denom() + c.num * b.denom()))
                * (a.denom() * (b.denom() * c.denom()));
        }
        assert(
            (a.num * (b.num * c.denom() + c.num * b.denom()))
                * ((a.denom() * b.denom()) * (a.denom() * c.denom()))
            ==
            (a.num * a.denom() * (b.num * c.denom() + c.num * b.denom()))
                * (a.denom() * (b.denom() * c.denom()))
        ) by (nonlinear_arith);
        assert(lhs.num * rhs.denom() == rhs.num * lhs.denom());
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_eqv_mul_distributive_right(a: Self, b: Self, c: Self)
        ensures
            a.add_spec(b).mul_spec(c).eqv_spec(a.mul_spec(c).add_spec(b.mul_spec(c))),
    {
        let lhs = a.add_spec(b).mul_spec(c);
        let mid = c.mul_spec(a.add_spec(b));
        let mid_rhs = c.mul_spec(a).add_spec(c.mul_spec(b));
        let rhs = a.mul_spec(c).add_spec(b.mul_spec(c));

        Self::lemma_mul_commutative(a.add_spec(b), c);
        assert(lhs == mid);
        Self::lemma_eqv_reflexive(lhs);
        assert(lhs.eqv_spec(mid));

        Self::lemma_eqv_mul_distributive_left(c, a, b);
        assert(mid.eqv_spec(mid_rhs));

        Self::lemma_mul_commutative(c, a);
        Self::lemma_mul_commutative(c, b);
        assert(mid_rhs == rhs);
        Self::lemma_eqv_reflexive(mid_rhs);
        assert(mid_rhs.eqv_spec(rhs));

        Self::lemma_eqv_transitive(lhs, mid, mid_rhs);
        Self::lemma_eqv_transitive(lhs, mid_rhs, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_eqv_sub_cancel_right(a: Self, b: Self, k: Self)
        ensures
            a.add_spec(k).sub_spec(b.add_spec(k)).eqv_spec(a.sub_spec(b)),
    {
        let ak = a.add_spec(k);
        let bk = b.add_spec(k);
        let lhs = ak.sub_spec(bk);
        let rhs = a.sub_spec(b);

        Self::lemma_add_denom_product_int(a, k);
        Self::lemma_add_denom_product_int(b, k);
        Self::lemma_sub_denom_product_int(ak, bk);
        Self::lemma_sub_denom_product_int(a, b);

        assert(ak.num == a.num * k.denom() + k.num * a.denom());
        assert(bk.num == b.num * k.denom() + k.num * b.denom());
        assert(lhs.num == ak.num * bk.denom() + (-bk.num) * ak.denom());
        assert(rhs.num == a.num * b.denom() + (-b.num) * a.denom());

        assert(ak.denom() == a.denom() * k.denom());
        assert(bk.denom() == b.denom() * k.denom());
        assert(lhs.denom() == ak.denom() * bk.denom());
        assert(rhs.denom() == a.denom() * b.denom());

        calc! {
            (==)
            lhs.num;
            {
                assert(lhs.num == ak.num * bk.denom() + (-bk.num) * ak.denom());
            }
            ak.num * bk.denom() + (-bk.num) * ak.denom();
            {
                assert(ak.num == a.num * k.denom() + k.num * a.denom());
                assert(bk.num == b.num * k.denom() + k.num * b.denom());
                assert(ak.denom() == a.denom() * k.denom());
                assert(bk.denom() == b.denom() * k.denom());
            }
            (a.num * k.denom() + k.num * a.denom()) * (b.denom() * k.denom())
                + (-(b.num * k.denom() + k.num * b.denom())) * (a.denom() * k.denom());
            {
                assert((a.num * k.denom() + k.num * a.denom()) * (b.denom() * k.denom())
                    + (-(b.num * k.denom() + k.num * b.denom())) * (a.denom() * k.denom())
                    == ((a.num * k.denom() + k.num * a.denom()) * b.denom()
                        + (-(b.num * k.denom() + k.num * b.denom())) * a.denom()) * k.denom())
                    by (nonlinear_arith);
                assert(((a.num * k.denom() + k.num * a.denom()) * b.denom()
                        + (-(b.num * k.denom() + k.num * b.denom())) * a.denom())
                    == (a.num * b.denom() + (-b.num) * a.denom()) * k.denom())
                    by (nonlinear_arith);
            }
            ((a.num * b.denom() + (-b.num) * a.denom()) * k.denom()) * k.denom();
            {
                assert(((a.num * b.denom() + (-b.num) * a.denom()) * k.denom()) * k.denom()
                    == (a.num * b.denom() + (-b.num) * a.denom()) * (k.denom() * k.denom()))
                    by (nonlinear_arith);
            }
            (a.num * b.denom() + (-b.num) * a.denom()) * (k.denom() * k.denom());
        }

        calc! {
            (==)
            lhs.denom();
            {
                assert(lhs.denom() == ak.denom() * bk.denom());
                assert(ak.denom() == a.denom() * k.denom());
                assert(bk.denom() == b.denom() * k.denom());
            }
            (a.denom() * k.denom()) * (b.denom() * k.denom());
            {
                assert((a.denom() * k.denom()) * (b.denom() * k.denom())
                    == (a.denom() * b.denom()) * (k.denom() * k.denom()))
                    by (nonlinear_arith);
            }
            (a.denom() * b.denom()) * (k.denom() * k.denom());
        }

        assert(lhs.eqv_spec(rhs) == (lhs.num * rhs.denom() == rhs.num * lhs.denom()));
        assert(lhs.num == (a.num * b.denom() + (-b.num) * a.denom()) * (k.denom() * k.denom()));
        assert(lhs.denom() == (a.denom() * b.denom()) * (k.denom() * k.denom()));
        assert(rhs.num == a.num * b.denom() + (-b.num) * a.denom());
        assert(rhs.denom() == a.denom() * b.denom());
        assert(lhs.num * rhs.denom()
            == ((a.num * b.denom() + (-b.num) * a.denom()) * (k.denom() * k.denom())) * (a.denom() * b.denom()));
        assert(rhs.num * lhs.denom()
            == (a.num * b.denom() + (-b.num) * a.denom()) * ((a.denom() * b.denom()) * (k.denom() * k.denom())));
        assert(((a.num * b.denom() + (-b.num) * a.denom()) * (k.denom() * k.denom())) * (a.denom() * b.denom())
            == (a.num * b.denom() + (-b.num) * a.denom()) * ((a.denom() * b.denom()) * (k.denom() * k.denom())))
            by (nonlinear_arith);
        assert(lhs.num * rhs.denom() == rhs.num * lhs.denom());
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_eqv_sub_chain(a: Self, b: Self, c: Self)
        ensures
            a.sub_spec(c).eqv_spec(a.sub_spec(b).add_spec(b.sub_spec(c))),
    {
        let lhs = a.sub_spec(c);
        let ab = a.sub_spec(b);
        let bc = b.sub_spec(c);
        let rhs = ab.add_spec(bc);

        Self::lemma_sub_denom_product_int(a, c);
        Self::lemma_sub_denom_product_int(a, b);
        Self::lemma_sub_denom_product_int(b, c);
        Self::lemma_add_denom_product_int(ab, bc);

        assert(lhs.num == a.num * c.denom() + (-c.num) * a.denom());
        assert(ab.num == a.num * b.denom() + (-b.num) * a.denom());
        assert(bc.num == b.num * c.denom() + (-c.num) * b.denom());
        assert(rhs.num == ab.num * bc.denom() + bc.num * ab.denom());

        assert(lhs.denom() == a.denom() * c.denom());
        assert(ab.denom() == a.denom() * b.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(rhs.denom() == ab.denom() * bc.denom());

        assert(lhs.eqv_spec(rhs) == (lhs.num * rhs.denom() == rhs.num * lhs.denom()));
        assert(
            (a.num * b.denom() + (-b.num) * a.denom()) * c.denom()
            + (b.num * c.denom() + (-c.num) * b.denom()) * a.denom()
            == (a.num * c.denom() + (-c.num) * a.denom()) * b.denom()
        ) by (nonlinear_arith);

        calc! {
            (==)
            ab.num * c.denom() + bc.num * a.denom();
            {
                assert(ab.num == a.num * b.denom() + (-b.num) * a.denom());
                assert(bc.num == b.num * c.denom() + (-c.num) * b.denom());
            }
            (a.num * b.denom() + (-b.num) * a.denom()) * c.denom()
                + (b.num * c.denom() + (-c.num) * b.denom()) * a.denom();
            { }
            (a.num * c.denom() + (-c.num) * a.denom()) * b.denom();
            {
                assert(lhs.num == a.num * c.denom() + (-c.num) * a.denom());
            }
            lhs.num * b.denom();
        }

        calc! {
            (==)
            rhs.num;
            { assert(rhs.num == ab.num * bc.denom() + bc.num * ab.denom()); }
            ab.num * bc.denom() + bc.num * ab.denom();
            {
                assert(bc.denom() == b.denom() * c.denom());
                assert(ab.denom() == a.denom() * b.denom());
            }
            ab.num * (b.denom() * c.denom()) + bc.num * (a.denom() * b.denom());
            {
                assert(ab.num * (b.denom() * c.denom()) + bc.num * (a.denom() * b.denom())
                    == b.denom() * (ab.num * c.denom() + bc.num * a.denom())) by (nonlinear_arith);
            }
            b.denom() * (ab.num * c.denom() + bc.num * a.denom());
            {
                assert(ab.num * c.denom() + bc.num * a.denom() == lhs.num * b.denom());
            }
            b.denom() * (lhs.num * b.denom());
        }

        calc! {
            (==)
            rhs.num * lhs.denom();
            {
                assert(lhs.denom() == a.denom() * c.denom());
                assert(rhs.num == b.denom() * (lhs.num * b.denom()));
            }
            (b.denom() * (lhs.num * b.denom())) * (a.denom() * c.denom());
        }

        calc! {
            (==)
            lhs.num * rhs.denom();
            {
                assert(rhs.denom() == ab.denom() * bc.denom());
                assert(ab.denom() == a.denom() * b.denom());
                assert(bc.denom() == b.denom() * c.denom());
            }
            lhs.num * ((a.denom() * b.denom()) * (b.denom() * c.denom()));
        }

        assert((b.denom() * (lhs.num * b.denom())) * (a.denom() * c.denom())
            == lhs.num * ((a.denom() * b.denom()) * (b.denom() * c.denom()))) by (nonlinear_arith);
        assert(lhs.num * rhs.denom() == rhs.num * lhs.denom());
        assert(lhs.eqv_spec(rhs));
    }

}

} // verus!
