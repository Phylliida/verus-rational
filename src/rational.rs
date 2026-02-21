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

/// Exact rational number.
///
/// `den` stores `(effective_denominator - 1)`, so effective denominator is
/// always at least `1`.
pub struct Rational {
    pub num: int,
    pub den: nat,
}

impl Rational {
    pub proof fn lemma_nat_mul_cast(a: nat, b: nat)
        ensures
            (a * b) as int == (a as int) * (b as int),
    {
        assert((a * b) as int == (a as int) * (b as int)) by (nonlinear_arith);
    }

    pub open spec fn denom_nat(self) -> nat {
        self.den + 1
    }

    pub open spec fn denom(self) -> int {
        self.denom_nat() as int
    }

    pub open spec fn as_real(self) -> real {
        self.num as real / self.denom_nat() as real
    }

    pub open spec fn from_int_spec(value: int) -> Self {
        Rational { num: value, den: 0 }
    }

    pub proof fn new(value: int) -> (s: Self)
        ensures
            s == Self::from_int_spec(value),
    {
        Rational { num: value, den: 0 }
    }

    pub proof fn from_int(value: int) -> (s: Self)
        ensures
            s == Self::from_int_spec(value),
    {
        Self::new(value)
    }

    pub proof fn from_frac(num: int, den: nat) -> (s: Self)
        requires
            den > 0,
        ensures
            s.num == num,
    {
        let dm1 = (den as int - 1) as nat;
        Rational { num, den: dm1 }
    }

    pub proof fn zero() -> (s: Self)
        ensures
            s == Self::from_int_spec(0),
    {
        Rational { num: 0, den: 0 }
    }

    pub proof fn one() -> (s: Self)
        ensures
            s == Self::from_int_spec(1),
    {
        Rational { num: 1, den: 0 }
    }

    pub open spec fn add_spec(self, rhs: Self) -> Self {
        let d1 = self.denom_nat();
        let d2 = rhs.denom_nat();
        Rational {
            num: self.num * (d2 as int) + rhs.num * (d1 as int),
            den: self.den * rhs.den + self.den + rhs.den,
        }
    }

    pub proof fn add(self, rhs: Self) -> (out: Self)
        ensures
            out == self.add_spec(rhs),
    {
        let d1 = self.denom_nat();
        let d2 = rhs.denom_nat();
        Rational {
            num: self.num * (d2 as int) + rhs.num * (d1 as int),
            den: self.den * rhs.den + self.den + rhs.den,
        }
    }

    pub open spec fn neg_spec(self) -> Self {
        Rational { num: -self.num, den: self.den }
    }

    pub proof fn neg(self) -> (out: Self)
        ensures
            out == self.neg_spec(),
    {
        Rational { num: -self.num, den: self.den }
    }

    pub open spec fn sub_spec(self, rhs: Self) -> Self {
        self.add_spec(rhs.neg_spec())
    }

    pub proof fn sub(self, rhs: Self) -> (out: Self)
        ensures
            out == self.sub_spec(rhs),
    {
        let neg_rhs = rhs.neg();
        self.add(neg_rhs)
    }

    pub open spec fn mul_spec(self, rhs: Self) -> Self {
        Rational {
            num: self.num * rhs.num,
            den: self.den * rhs.den + self.den + rhs.den,
        }
    }

    pub proof fn mul(self, rhs: Self) -> (out: Self)
        ensures
            out == self.mul_spec(rhs),
    {
        Rational {
            num: self.num * rhs.num,
            den: self.den * rhs.den + self.den + rhs.den,
        }
    }

    /// Spec-level reciprocal: flips numerator and denominator.
    /// Only meaningful when self.num != 0.
    pub open spec fn reciprocal_spec(self) -> Self {
        if self.num > 0 {
            Rational { num: self.denom(), den: (self.num as nat - 1) as nat }
        } else if self.num < 0 {
            Rational { num: -self.denom(), den: ((-self.num) as nat - 1) as nat }
        } else {
            // Arbitrary for zero; callers must ensure num != 0
            self
        }
    }

    /// Division as multiplication by reciprocal: a / b := a * inv(b).
    /// Requires b.num != 0 (ensured by callers at proof level).
    pub open spec fn div_spec(self, rhs: Self) -> Self {
        self.mul_spec(rhs.reciprocal_spec())
    }

    pub open spec fn signum(self) -> int {
        if self.num > 0 {
            1
        } else if self.num < 0 {
            -1
        } else {
            0
        }
    }

    pub open spec fn abs_spec(self) -> Self {
        if self.num >= 0 {
            self
        } else {
            self.neg_spec()
        }
    }

    pub open spec fn min_spec(self, rhs: Self) -> Self {
        if self.le_spec(rhs) {
            self
        } else {
            rhs
        }
    }

    pub open spec fn max_spec(self, rhs: Self) -> Self {
        if self.le_spec(rhs) {
            rhs
        } else {
            self
        }
    }

    pub open spec fn eqv_spec(self, rhs: Self) -> bool {
        self.num * rhs.denom() == rhs.num * self.denom()
    }

    pub open spec fn le_spec(self, rhs: Self) -> bool {
        self.num * rhs.denom() <= rhs.num * self.denom()
    }

    pub open spec fn lt_spec(self, rhs: Self) -> bool {
        self.num * rhs.denom() < rhs.num * self.denom()
    }

    pub proof fn lemma_denom_positive(a: Self)
        ensures
            a.denom_nat() > 0,
            a.denom() > 0,
    {
        assert(a.denom_nat() > 0);
        assert(a.denom() == a.denom_nat() as int);
        assert(a.denom() > 0);
    }

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

    pub proof fn lemma_mul_commutative(a: Self, b: Self)
        ensures
            a.mul_spec(b) == b.mul_spec(a),
    {
        let lhs = a.mul_spec(b);
        let rhs = b.mul_spec(a);
        assert(lhs.num == a.num * b.num);
        assert(rhs.num == b.num * a.num);
        assert(a.num * b.num == b.num * a.num) by (nonlinear_arith);
        assert(lhs.num == rhs.num);

        assert(lhs.den == a.den * b.den + a.den + b.den);
        assert(rhs.den == b.den * a.den + b.den + a.den);
        assert(a.den * b.den + a.den + b.den == b.den * a.den + b.den + a.den) by (nonlinear_arith);
        assert(lhs.den == rhs.den);
    }

    pub proof fn lemma_sub_is_add_neg(a: Self, b: Self)
        ensures
            a.sub_spec(b) == a.add_spec(b.neg_spec()),
    {
        assert(a.sub_spec(b) == a.add_spec(b.neg_spec()));
    }

    pub proof fn lemma_neg_involution(a: Self)
        ensures
            a.neg_spec().neg_spec() == a,
    {
        let n = a.neg_spec().neg_spec();
        assert(n.num == -(-a.num));
        assert(-(-a.num) == a.num);
        assert(n.num == a.num);
        assert(n.den == a.den);
        assert(n == a);
    }

    pub proof fn lemma_add_commutative(a: Self, b: Self)
        ensures
            a.add_spec(b).eqv_spec(b.add_spec(a)),
    {
        let l = a.add_spec(b);
        let r = b.add_spec(a);
        let da = a.denom();
        let db = b.denom();
        Self::lemma_add_denom_product_int(a, b);
        Self::lemma_add_denom_product_int(b, a);
        assert(l.num == a.num * db + b.num * da);
        assert(r.num == b.num * da + a.num * db);
        assert(l.denom() == da * db);
        assert(r.denom() == db * da);
        assert(l.eqv_spec(r) == (l.num * r.denom() == r.num * l.denom()));
        calc! {
            (==)
            l.num * r.denom();
            {
                assert(l.num == a.num * db + b.num * da);
                assert(r.denom() == db * da);
            }
            (a.num * db + b.num * da) * (db * da);
            {
                assert((a.num * db + b.num * da) * (db * da)
                    == (b.num * da + a.num * db) * (da * db)) by (nonlinear_arith);
            }
            (b.num * da + a.num * db) * (da * db);
            {
                assert(r.num == b.num * da + a.num * db);
                assert(l.denom() == da * db);
            }
            r.num * l.denom();
        }
        assert(l.num * r.denom() == r.num * l.denom());
        assert(l.eqv_spec(r));
    }

    pub proof fn lemma_add_associative(a: Self, b: Self, c: Self)
        ensures
            a.add_spec(b).add_spec(c).eqv_spec(a.add_spec(b.add_spec(c))),
    {
        let da = a.denom();
        let db = b.denom();
        let dc = c.denom();
        let ab = a.add_spec(b);
        let bc = b.add_spec(c);
        let lhs = ab.add_spec(c);
        let rhs = a.add_spec(bc);

        Self::lemma_add_denom_product_int(a, b);
        Self::lemma_add_denom_product_int(b, c);
        Self::lemma_add_denom_product_int(ab, c);
        Self::lemma_add_denom_product_int(a, bc);

        assert(ab.num == a.num * db + b.num * da);
        assert(bc.num == b.num * dc + c.num * db);
        assert(ab.denom() == da * db);
        assert(bc.denom() == db * dc);

        assert(lhs.num == ab.num * dc + c.num * ab.denom());
        assert(rhs.num == a.num * bc.denom() + bc.num * da);
        assert(lhs.denom() == ab.denom() * dc);
        assert(rhs.denom() == da * bc.denom());
        assert(lhs.denom() == (da * db) * dc);
        assert(rhs.denom() == da * (db * dc));
        assert(lhs.num == (a.num * db + b.num * da) * dc + c.num * (da * db));
        assert(rhs.num == a.num * (db * dc) + (b.num * dc + c.num * db) * da);
        assert((a.num * db + b.num * da) * dc == (a.num * db) * dc + (b.num * da) * dc)
            by (nonlinear_arith);
        lemma_mul_is_associative(a.num, db, dc);
        assert((a.num * db) * dc == a.num * (db * dc));
        lemma_mul_is_associative(b.num, da, dc);
        assert((b.num * da) * dc == b.num * (da * dc));
        lemma_mul_is_commutative(da, db);
        assert(da * db == db * da);
        assert(c.num * (da * db) == c.num * (db * da));
        assert(b.num * (da * dc) == (b.num * dc) * da) by (nonlinear_arith);
        assert(c.num * (db * da) == (c.num * db) * da) by (nonlinear_arith);
        assert(lhs.num == a.num * (db * dc) + (b.num * dc) * da + (c.num * db) * da);
        assert((b.num * dc + c.num * db) * da == (b.num * dc) * da + (c.num * db) * da)
            by (nonlinear_arith);
        assert(rhs.num == a.num * (db * dc) + (b.num * dc) * da + (c.num * db) * da);
        assert(lhs.num == rhs.num);
        lemma_mul_is_associative(da, db, dc);
        assert((da * db) * dc == da * (db * dc));
        assert(lhs.denom() == rhs.denom());

        assert(lhs.eqv_spec(rhs) == (lhs.num * rhs.denom() == rhs.num * lhs.denom()));
        assert(lhs.num * rhs.denom() == lhs.num * lhs.denom());
        assert(rhs.num * lhs.denom() == lhs.num * lhs.denom());
        assert(lhs.num * rhs.denom() == rhs.num * lhs.denom());
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_add_rearrange_2x2(a: Self, b: Self, c: Self, d: Self)
        ensures
            a.add_spec(b).add_spec(c.add_spec(d)).eqv_spec(a.add_spec(c).add_spec(b.add_spec(d))),
    {
        let e0 = a.add_spec(b).add_spec(c.add_spec(d));
        let e1 = a.add_spec(b.add_spec(c.add_spec(d)));
        let e2 = a.add_spec(c.add_spec(d).add_spec(b));
        let e3 = a.add_spec(c.add_spec(d.add_spec(b)));
        let e4 = a.add_spec(c.add_spec(b.add_spec(d)));
        let e5 = a.add_spec(c.add_spec(b).add_spec(d));
        let e6 = a.add_spec(c.add_spec(b)).add_spec(d);
        let e7 = a.add_spec(c).add_spec(b).add_spec(d);
        let e8 = a.add_spec(c).add_spec(b.add_spec(d));

        Self::lemma_add_associative(a, b, c.add_spec(d));
        assert(e0.eqv_spec(e1));

        Self::lemma_add_commutative(b, c.add_spec(d));
        Self::lemma_eqv_reflexive(a);
        Self::lemma_eqv_add_congruence(a, a, b.add_spec(c.add_spec(d)), c.add_spec(d).add_spec(b));
        assert(e1.eqv_spec(e2));

        Self::lemma_add_associative(c, d, b);
        Self::lemma_eqv_reflexive(a);
        Self::lemma_eqv_add_congruence(a, a, c.add_spec(d).add_spec(b), c.add_spec(d.add_spec(b)));
        assert(e2.eqv_spec(e3));

        Self::lemma_add_commutative(d, b);
        Self::lemma_eqv_reflexive(c);
        Self::lemma_eqv_add_congruence(c, c, d.add_spec(b), b.add_spec(d));
        assert(c.add_spec(d.add_spec(b)).eqv_spec(c.add_spec(b.add_spec(d))));
        Self::lemma_eqv_reflexive(a);
        Self::lemma_eqv_add_congruence(a, a, c.add_spec(d.add_spec(b)), c.add_spec(b.add_spec(d)));
        assert(e3.eqv_spec(e4));

        Self::lemma_add_associative(c, b, d);
        Self::lemma_eqv_symmetric(c.add_spec(b).add_spec(d), c.add_spec(b.add_spec(d)));
        assert(c.add_spec(b.add_spec(d)).eqv_spec(c.add_spec(b).add_spec(d)));
        Self::lemma_eqv_reflexive(a);
        Self::lemma_eqv_add_congruence(a, a, c.add_spec(b.add_spec(d)), c.add_spec(b).add_spec(d));
        assert(e4.eqv_spec(e5));

        Self::lemma_add_associative(a, c.add_spec(b), d);
        Self::lemma_eqv_symmetric(a.add_spec(c.add_spec(b)).add_spec(d), a.add_spec(c.add_spec(b).add_spec(d)));
        assert(a.add_spec(c.add_spec(b).add_spec(d)).eqv_spec(a.add_spec(c.add_spec(b)).add_spec(d)));
        assert(e5.eqv_spec(e6));

        Self::lemma_add_associative(a, c, b);
        Self::lemma_eqv_symmetric(a.add_spec(c).add_spec(b), a.add_spec(c.add_spec(b)));
        assert(a.add_spec(c.add_spec(b)).eqv_spec(a.add_spec(c).add_spec(b)));
        Self::lemma_eqv_reflexive(d);
        Self::lemma_eqv_add_congruence(a.add_spec(c.add_spec(b)), a.add_spec(c).add_spec(b), d, d);
        assert(e6.eqv_spec(e7));

        Self::lemma_add_associative(a.add_spec(c), b, d);
        assert(e7.eqv_spec(e8));

        Self::lemma_eqv_transitive(e0, e1, e2);
        Self::lemma_eqv_transitive(e0, e2, e3);
        Self::lemma_eqv_transitive(e0, e3, e4);
        Self::lemma_eqv_transitive(e0, e4, e5);
        Self::lemma_eqv_transitive(e0, e5, e6);
        Self::lemma_eqv_transitive(e0, e6, e7);
        Self::lemma_eqv_transitive(e0, e7, e8);
        assert(e0.eqv_spec(e8));
    }

    pub proof fn lemma_neg_add(a: Self, b: Self)
        ensures
            a.add_spec(b).neg_spec() == a.neg_spec().add_spec(b.neg_spec()),
    {
        let lhs = a.add_spec(b).neg_spec();
        let rhs = a.neg_spec().add_spec(b.neg_spec());
        assert(lhs.num == -(a.num * b.denom() + b.num * a.denom()));
        assert(rhs.num == (-a.num) * b.neg_spec().denom() + b.neg_spec().num * a.neg_spec().denom());
        assert(b.neg_spec().denom() == b.denom());
        assert(a.neg_spec().denom() == a.denom());
        assert(b.neg_spec().num == -b.num);
        assert(rhs.num == (-a.num) * b.denom() + (-b.num) * a.denom());
        assert(-(a.num * b.denom() + b.num * a.denom())
            == (-a.num) * b.denom() + (-b.num) * a.denom()) by (nonlinear_arith);
        assert(lhs.num == rhs.num);
        assert(lhs.den == a.add_spec(b).den);
        assert(a.add_spec(b).den == a.den * b.den + a.den + b.den);
        assert(rhs.den == a.neg_spec().den * b.neg_spec().den + a.neg_spec().den + b.neg_spec().den);
        assert(a.neg_spec().den == a.den);
        assert(b.neg_spec().den == b.den);
        assert(rhs.den == a.den * b.den + a.den + b.den);
        assert(lhs.den == rhs.den);
    }

    pub proof fn lemma_sub_add_distributes(a: Self, b: Self, c: Self, d: Self)
        ensures
            a.add_spec(b).sub_spec(c.add_spec(d)).eqv_spec(a.sub_spec(c).add_spec(b.sub_spec(d))),
    {
        let lhs = a.add_spec(b).sub_spec(c.add_spec(d));
        let t1 = a.add_spec(b).sub_spec(c);
        let t2 = c.sub_spec(c.add_spec(d));
        let t3 = t1.add_spec(t2);
        let u1 = a.add_spec(b).sub_spec(a);
        let u2 = a.sub_spec(c);
        let u3 = u1.add_spec(u2);
        let u4 = b.add_spec(u2);
        let u5 = u2.add_spec(b);
        let v1 = c.add_spec(d).sub_spec(c);
        let v2 = v1.neg_spec();
        let v3 = d.neg_spec();
        let w1 = u5.add_spec(v2);
        let w2 = u5.add_spec(v3);
        let rhs = a.sub_spec(c).add_spec(b.sub_spec(d));

        Self::lemma_eqv_sub_chain(a.add_spec(b), c, c.add_spec(d));
        assert(lhs.eqv_spec(t3));

        Self::lemma_eqv_sub_chain(a.add_spec(b), a, c);
        assert(t1.eqv_spec(u3));
        Self::lemma_add_then_sub_cancel(a, b);
        assert(u1.eqv_spec(b));
        Self::lemma_eqv_reflexive(u2);
        Self::lemma_eqv_add_congruence(u1, b, u2, u2);
        assert(u3.eqv_spec(u4));
        Self::lemma_add_commutative(b, u2);
        assert(u4.eqv_spec(u5));
        Self::lemma_eqv_transitive(t1, u3, u4);
        Self::lemma_eqv_transitive(t1, u4, u5);
        assert(t1.eqv_spec(u5));

        Self::lemma_sub_antisymmetric(c, c.add_spec(d));
        assert(t2 == v1.neg_spec());
        Self::lemma_add_then_sub_cancel(c, d);
        assert(v1.eqv_spec(d));
        Self::lemma_eqv_neg_congruence(v1, d);
        assert(v2.eqv_spec(v3));
        Self::lemma_eqv_reflexive(u5);
        Self::lemma_eqv_add_congruence(u5, u5, v2, v3);
        assert(w1.eqv_spec(w2));
        Self::lemma_eqv_sub_chain(b, d, Self::from_int_spec(0));
        Self::lemma_sub_is_add_neg(b, d);
        assert(b.sub_spec(d) == b.add_spec(d.neg_spec()));
        assert(w2 == u2.add_spec(b).add_spec(d.neg_spec()));
        Self::lemma_add_associative(u2, b, d.neg_spec());
        assert(w2.eqv_spec(u2.add_spec(b.add_spec(d.neg_spec()))));
        assert(u2.add_spec(b.add_spec(d.neg_spec())) == u2.add_spec(b.sub_spec(d)));
        assert(rhs == u2.add_spec(b.sub_spec(d)));
        assert(w2.eqv_spec(rhs));

        Self::lemma_eqv_add_congruence(t1, u5, t2, v2);
        assert(t3.eqv_spec(w1));
        Self::lemma_eqv_transitive(t3, w1, w2);
        Self::lemma_eqv_transitive(t3, w2, rhs);
        Self::lemma_eqv_transitive(lhs, t3, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_sub_mul_right(a: Self, b: Self, k: Self)
        ensures
            a.sub_spec(b).mul_spec(k).eqv_spec(a.mul_spec(k).sub_spec(b.mul_spec(k))),
    {
        let lhs = a.sub_spec(b).mul_spec(k);
        let rhs = a.mul_spec(k).sub_spec(b.mul_spec(k));
        let s = a.sub_spec(b);
        let ks = k.mul_spec(s);
        let ka = k.mul_spec(a);
        let kbn = k.mul_spec(b.neg_spec());
        let kb = k.mul_spec(b);
        let mid = ka.add_spec(kbn);

        Self::lemma_sub_is_add_neg(a, b);
        assert(s == a.add_spec(b.neg_spec()));
        assert(lhs == s.mul_spec(k));
        Self::lemma_mul_commutative(s, k);
        assert(s.mul_spec(k) == ks);
        assert(lhs == ks);

        Self::lemma_eqv_mul_distributive_left(k, a, b.neg_spec());
        assert(ks.eqv_spec(ka.add_spec(kbn)));
        assert(lhs.eqv_spec(mid));

        Self::lemma_mul_neg_right(k, b);
        assert(kbn == kb.neg_spec());
        assert(mid == ka.add_spec(kb.neg_spec()));
        assert(rhs == a.mul_spec(k).add_spec(b.mul_spec(k).neg_spec()));
        assert(ka == a.mul_spec(k));
        assert(kb == b.mul_spec(k));
        assert(mid == rhs);
        Self::lemma_eqv_reflexive(rhs);
        assert(mid.eqv_spec(rhs));
        Self::lemma_eqv_transitive(lhs, mid, rhs);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_add_zero_identity(a: Self)
        ensures
            a.add_spec(Self::from_int_spec(0)) == a,
            Self::from_int_spec(0).add_spec(a) == a,
    {
        let z = Self::from_int_spec(0);
        let l = a.add_spec(z);
        let r = z.add_spec(a);
        let da = a.denom();
        assert(z.num == 0);
        assert(z.den == 0);
        assert(z.denom() == 1);
        assert(a.denom() == da);

        assert(l.num == a.num * z.denom() + z.num * da);
        assert(l.num == a.num * 1 + 0 * da);
        assert(a.num * 1 == a.num) by (nonlinear_arith);
        assert(0 * da == 0) by (nonlinear_arith);
        assert(l.num == a.num);
        assert(l.den == a.den * z.den + a.den + z.den);
        assert(l.den == a.den * 0 + a.den + 0);
        assert(a.den * 0 == 0);
        assert(l.den == 0 + a.den + 0);
        assert(l.den == a.den);
        assert(l == a);

        assert(r.num == z.num * da + a.num * z.denom());
        assert(r.num == 0 * da + a.num * 1);
        assert(0 * da == 0) by (nonlinear_arith);
        assert(a.num * 1 == a.num) by (nonlinear_arith);
        assert(r.num == a.num);
        assert(r.den == z.den * a.den + z.den + a.den);
        assert(r.den == 0 * a.den + 0 + a.den);
        assert(0 * a.den == 0);
        assert(r.den == 0 + 0 + a.den);
        assert(r.den == a.den);
        assert(r == a);
    }

    pub proof fn lemma_add_inverse(a: Self)
        ensures
            a.add_spec(a.neg_spec()).eqv_spec(Self::from_int_spec(0)),
            a.neg_spec().add_spec(a).eqv_spec(Self::from_int_spec(0)),
    {
        let z = Self::from_int_spec(0);
        let l = a.add_spec(a.neg_spec());
        let r = a.neg_spec().add_spec(a);
        let d = a.denom();
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(a.neg_spec().denom() == d);
        assert(a.denom() == d);
        assert(a.neg_spec().num == -a.num);
        assert(l.num == a.num * a.neg_spec().denom() + a.neg_spec().num * a.denom());
        assert(r.num == a.neg_spec().num * a.denom() + a.num * a.neg_spec().denom());
        assert(l.num == a.num * d + (-a.num) * d);
        assert(r.num == (-a.num) * d + a.num * d);
        calc! {
            (==)
            l.num;
            { }
            a.num * d + (-a.num) * d;
            {
                assert(a.num * d + (-a.num) * d == 0) by (nonlinear_arith);
            }
            0;
        }
        calc! {
            (==)
            r.num;
            { }
            (-a.num) * d + a.num * d;
            {
                assert((-a.num) * d + a.num * d == 0) by (nonlinear_arith);
            }
            0;
        }
        assert(l.eqv_spec(z) == (l.num * z.denom() == z.num * l.denom()));
        assert(r.eqv_spec(z) == (r.num * z.denom() == z.num * r.denom()));
        calc! {
            (==)
            l.num * z.denom();
            { assert(l.num == 0); assert(z.denom() == 1); }
            0int * 1int;
            { }
            0int;
        }
        calc! {
            (==)
            z.num * l.denom();
            { assert(z.num == 0); }
            0 * l.denom();
            {
                lemma_mul_by_zero_is_zero(l.denom());
                assert(0 * l.denom() == 0);
            }
            0;
        }
        assert(l.num * z.denom() == z.num * l.denom());
        calc! {
            (==)
            r.num * z.denom();
            { assert(r.num == 0); assert(z.denom() == 1); }
            0int * 1int;
            { }
            0int;
        }
        calc! {
            (==)
            z.num * r.denom();
            { assert(z.num == 0); }
            0 * r.denom();
            {
                lemma_mul_by_zero_is_zero(r.denom());
                assert(0 * r.denom() == 0);
            }
            0;
        }
        assert(r.num * z.denom() == z.num * r.denom());
        assert(l.eqv_spec(z));
        assert(r.eqv_spec(z));
    }

    pub proof fn lemma_mul_one_identity(a: Self)
        ensures
            a.mul_spec(Self::from_int_spec(1)) == a,
            Self::from_int_spec(1).mul_spec(a) == a,
    {
        let o = Self::from_int_spec(1);
        let l = a.mul_spec(o);
        let r = o.mul_spec(a);
        let da = a.denom();
        assert(o.num == 1);
        assert(o.den == 0);
        assert(o.denom() == 1);

        assert(l.num == a.num * o.num);
        assert(a.num * 1 == a.num) by (nonlinear_arith);
        assert(l.num == a.num);
        assert(l.den == a.den * o.den + a.den + o.den);
        assert(l.den == a.den * 0 + a.den + 0);
        assert(a.den * 0 == 0);
        assert(l.den == 0 + a.den + 0);
        assert(l.den == a.den);
        assert(l == a);

        assert(r.num == o.num * a.num);
        assert(1 * a.num == a.num) by (nonlinear_arith);
        assert(r.num == a.num);
        assert(r.den == o.den * a.den + o.den + a.den);
        assert(r.den == 0 * a.den + 0 + a.den);
        assert(0 * a.den == 0);
        assert(r.den == 0 + 0 + a.den);
        assert(r.den == a.den);
        assert(a.denom() == da);
        assert(r == a);
    }

    pub proof fn lemma_mul_associative(a: Self, b: Self, c: Self)
        ensures
            a.mul_spec(b).mul_spec(c).eqv_spec(a.mul_spec(b.mul_spec(c))),
    {
        let da = a.denom();
        let db = b.denom();
        let dc = c.denom();
        let ab = a.mul_spec(b);
        let bc = b.mul_spec(c);
        let lhs = ab.mul_spec(c);
        let rhs = a.mul_spec(bc);

        Self::lemma_mul_denom_product_int(a, b);
        Self::lemma_mul_denom_product_int(b, c);
        Self::lemma_mul_denom_product_int(ab, c);
        Self::lemma_mul_denom_product_int(a, bc);

        assert(ab.num == a.num * b.num);
        assert(bc.num == b.num * c.num);
        assert(lhs.num == ab.num * c.num);
        assert(rhs.num == a.num * bc.num);
        assert(lhs.num == (a.num * b.num) * c.num);
        assert(rhs.num == a.num * (b.num * c.num));

        assert(ab.denom() == da * db);
        assert(bc.denom() == db * dc);
        assert(lhs.denom() == ab.denom() * dc);
        assert(rhs.denom() == da * bc.denom());
        assert(lhs.denom() == (da * db) * dc);
        assert(rhs.denom() == da * (db * dc));

        assert(lhs.eqv_spec(rhs) == (lhs.num * rhs.denom() == rhs.num * lhs.denom()));
        lemma_mul_is_associative(a.num, b.num, c.num);
        assert((a.num * b.num) * c.num == a.num * (b.num * c.num));
        assert(lhs.num == rhs.num);
        lemma_mul_is_associative(da, db, dc);
        assert((da * db) * dc == da * (db * dc));
        assert(lhs.denom() == rhs.denom());
        assert(lhs.num * rhs.denom() == lhs.num * lhs.denom());
        assert(rhs.num * lhs.denom() == lhs.num * lhs.denom());
        assert(lhs.num * rhs.denom() == rhs.num * lhs.denom());
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_mul_zero(a: Self)
        ensures
            a.mul_spec(Self::from_int_spec(0)).eqv_spec(Self::from_int_spec(0)),
            Self::from_int_spec(0).mul_spec(a).eqv_spec(Self::from_int_spec(0)),
    {
        let z = Self::zero();
        let l = a.mul_spec(z);
        let r = z.mul_spec(a);
        assert(z.num == 0);
        Self::lemma_mul_right_zero_num(a, z);
        Self::lemma_mul_left_zero_num(z, a);
        assert(l.num == 0);
        assert(r.num == 0);
        assert(l.eqv_spec(z) == (l.num * z.denom() == z.num * l.denom()));
        assert(r.eqv_spec(z) == (r.num * z.denom() == z.num * r.denom()));
        assert(l.eqv_spec(z));
        assert(r.eqv_spec(z));
    }

    pub proof fn lemma_mul_distributes_over_add(a: Self, b: Self, c: Self)
        ensures
            a.mul_spec(b.add_spec(c)).eqv_spec(a.mul_spec(b).add_spec(a.mul_spec(c))),
    {
        Self::lemma_eqv_mul_distributive_left(a, b, c);
        assert(a.mul_spec(b.add_spec(c)).eqv_spec(a.mul_spec(b).add_spec(a.mul_spec(c))));
    }

    pub proof fn lemma_mul_zero_implies_factor_zero(a: Self, b: Self)
        requires
            a.mul_spec(b).num == 0,
        ensures
            a.num == 0 || b.num == 0,
    {
        assert(a.mul_spec(b).num == a.num * b.num);
        assert(a.num * b.num == 0);
        assert((a.num * b.num == 0) ==> (a.num == 0 || b.num == 0)) by (nonlinear_arith);
        assert(a.num == 0 || b.num == 0);
    }

    pub proof fn lemma_mul_reciprocal_positive_num(a: Self)
        requires
            a.num > 0,
        ensures
            {
                let an = a.num as nat;
                let inv = Rational { num: a.denom(), den: (an - 1) as nat };
                a.mul_spec(inv).eqv_spec(Self::from_int_spec(1))
            },
            {
                let an = a.num as nat;
                let inv = Rational { num: a.denom(), den: (an - 1) as nat };
                inv.mul_spec(a).eqv_spec(Self::from_int_spec(1))
            },
    {
        let one = Self::from_int_spec(1);
        let an = a.num as nat;
        assert(an > 0);
        assert((a.num as nat) as int == a.num);
        let inv = Rational { num: a.denom(), den: (an - 1) as nat };
        let prod = a.mul_spec(inv);
        let rprod = inv.mul_spec(a);
        Self::lemma_mul_denom_product_int(a, inv);
        assert(inv.denom_nat() == (an - 1) + 1);
        assert((an - 1) + 1 == an) by (nonlinear_arith);
        assert(inv.denom_nat() == an);
        assert(inv.denom() == inv.denom_nat() as int);
        assert(inv.denom() == an as int);
        assert(inv.denom() == a.num);
        assert(prod.num == a.num * inv.num);
        assert(inv.num == a.denom());
        assert(prod.num == a.num * a.denom());
        assert(prod.denom() == a.denom() * inv.denom());
        assert(prod.denom() == a.denom() * a.num);
        assert(prod.eqv_spec(one) == (prod.num * one.denom() == one.num * prod.denom()));
        assert(one.denom() == 1);
        assert(one.num == 1);
        assert((prod.num * 1 == 1 * prod.denom()) == (prod.num == prod.denom())) by (nonlinear_arith);
        assert(prod.eqv_spec(one) == (prod.num == prod.denom()));
        assert(a.num * a.denom() == a.denom() * a.num) by (nonlinear_arith);
        assert(prod.num == prod.denom());
        assert(prod.eqv_spec(one));

        Self::lemma_mul_commutative(inv, a);
        assert(rprod == prod);
        Self::lemma_eqv_reflexive(prod);
        assert(rprod.eqv_spec(prod));
        Self::lemma_eqv_transitive(rprod, prod, one);
        assert(rprod.eqv_spec(one));
    }

    pub proof fn reciprocal_constructive(a: Self) -> (inv: Self)
        requires
            a.num != 0,
        ensures
            a.mul_spec(inv).eqv_spec(Self::from_int_spec(1)),
            inv.mul_spec(a).eqv_spec(Self::from_int_spec(1)),
            inv == a.reciprocal_spec(),
    {
        if a.num > 0 {
            let an = a.num as nat;
            let inv = Rational { num: a.denom(), den: (an - 1) as nat };
            Self::lemma_mul_reciprocal_positive_num(a);
            assert(inv == a.reciprocal_spec());
            inv
        } else {
            let one = Self::from_int_spec(1);
            assert(a.num < 0);
            assert((a.num < 0) ==> (0 - a.num > 0)) by (nonlinear_arith);
            assert(0 - a.num > 0);
            assert(-a.num == 0 - a.num);
            assert(-a.num > 0);
            let an = (-a.num) as nat;
            assert(an > 0);
            assert(((-a.num) as nat) as int == -a.num);
            let inv = Rational { num: -a.denom(), den: (an - 1) as nat };
            let prod = a.mul_spec(inv);
            let rprod = inv.mul_spec(a);
            Self::lemma_mul_denom_product_int(a, inv);
            assert(inv.denom_nat() == (an - 1) + 1);
            assert((an - 1) + 1 == an) by (nonlinear_arith);
            assert(inv.denom_nat() == an);
            assert(inv.denom() == inv.denom_nat() as int);
            assert(inv.denom() == an as int);
            assert(inv.denom() == -a.num);
            assert(prod.num == a.num * inv.num);
            assert(inv.num == -a.denom());
            assert(prod.num == a.num * (-a.denom()));
            assert(prod.denom() == a.denom() * inv.denom());
            assert(prod.denom() == a.denom() * (-a.num));
            assert(prod.eqv_spec(one) == (prod.num * one.denom() == one.num * prod.denom()));
            assert(one.denom() == 1);
            assert(one.num == 1);
            assert((prod.num * 1 == 1 * prod.denom()) == (prod.num == prod.denom())) by (nonlinear_arith);
            assert(prod.eqv_spec(one) == (prod.num == prod.denom()));
            assert(a.num * (-a.denom()) == a.denom() * (-a.num)) by (nonlinear_arith);
            assert(prod.num == prod.denom());
            assert(prod.eqv_spec(one));

            Self::lemma_mul_commutative(inv, a);
            assert(rprod == prod);
            Self::lemma_eqv_reflexive(prod);
            assert(rprod.eqv_spec(prod));
            Self::lemma_eqv_transitive(rprod, prod, one);
            assert(rprod.eqv_spec(one));
            assert(inv == a.reciprocal_spec());
            inv
        }
    }

    pub proof fn lemma_le_add_monotone_strong(a: Self, b: Self, c: Self)
        requires
            a.le_spec(b),
        ensures
            a.add_spec(c).le_spec(b.add_spec(c)),
    {
        let ac = a.add_spec(c);
        let bc = b.add_spec(c);
        Self::lemma_add_denom_product_int(a, c);
        Self::lemma_add_denom_product_int(b, c);
        assert(ac.num == a.num * c.denom() + c.num * a.denom());
        assert(bc.num == b.num * c.denom() + c.num * b.denom());
        assert(ac.denom() == a.denom() * c.denom());
        assert(bc.denom() == b.denom() * c.denom());
        assert(ac.le_spec(bc) == (ac.num * bc.denom() <= bc.num * ac.denom()));
        assert(a.le_spec(b) == (a.num * b.denom() <= b.num * a.denom()));
        assert(a.num * b.denom() <= b.num * a.denom());
        assert((a.num * b.denom() <= b.num * a.denom())
            ==> ((a.num * c.denom() + c.num * a.denom()) * (b.denom() * c.denom())
                <= (b.num * c.denom() + c.num * b.denom()) * (a.denom() * c.denom())))
            by (nonlinear_arith);
        assert((a.num * c.denom() + c.num * a.denom()) * (b.denom() * c.denom())
            <= (b.num * c.denom() + c.num * b.denom()) * (a.denom() * c.denom()));
        assert(ac.num * bc.denom() == (a.num * c.denom() + c.num * a.denom()) * (b.denom() * c.denom()));
        assert(bc.num * ac.denom() == (b.num * c.denom() + c.num * b.denom()) * (a.denom() * c.denom()));
        assert(ac.num * bc.denom() <= bc.num * ac.denom());
        assert(ac.le_spec(bc));
    }

    pub proof fn lemma_le_add_monotone(a: Self, b: Self, c: Self)
        requires
            a.le_spec(b),
        ensures
            a.add_spec(c).le_spec(b.add_spec(c)),
    {
        Self::lemma_le_add_monotone_strong(a, b, c);
        assert(a.add_spec(c).le_spec(b.add_spec(c)));
    }

    pub proof fn lemma_le_mul_monotone_nonnegative_strong(a: Self, b: Self, c: Self)
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
        assert(z.le_spec(c) == (z.num * c.denom() <= c.num * z.denom()));
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(z.le_spec(c) == (0 * c.denom() <= c.num * 1));
        lemma_mul_by_zero_is_zero(c.denom());
        assert(0 * c.denom() == 0);
        assert(0 <= c.num * 1);
        assert((0 <= c.num * 1) ==> (0 <= c.num)) by (nonlinear_arith);
        assert(c.num >= 0);
        assert((a.num * b.denom() <= b.num * a.denom() && c.num >= 0 && c.denom() > 0)
            ==> ((a.num * c.num) * (b.denom() * c.denom())
                <= (b.num * c.num) * (a.denom() * c.denom())))
            by (nonlinear_arith);
        assert((a.num * c.num) * (b.denom() * c.denom())
            <= (b.num * c.num) * (a.denom() * c.denom()));
        assert(ac.num * bc.denom() == (a.num * c.num) * (b.denom() * c.denom()));
        assert(bc.num * ac.denom() == (b.num * c.num) * (a.denom() * c.denom()));
        assert(ac.num * bc.denom() <= bc.num * ac.denom());
        assert(ac.le_spec(bc));
    }

    pub proof fn lemma_le_mul_monotone_nonnegative(a: Self, b: Self, c: Self)
        requires
            a.le_spec(b),
            Self::from_int_spec(0).le_spec(c),
        ensures
            a.mul_spec(c).le_spec(b.mul_spec(c)),
    {
        Self::lemma_le_mul_monotone_nonnegative_strong(a, b, c);
        assert(a.mul_spec(c).le_spec(b.mul_spec(c)));
    }

    pub proof fn lemma_add_right_cancel_strong(a: Self, b: Self, k: Self)
        requires
            a.add_spec(k).eqv_spec(b.add_spec(k)),
        ensures
            a.eqv_spec(b),
    {
        let ak = a.add_spec(k);
        let bk = b.add_spec(k);
        let lhs = ak.sub_spec(bk);
        let s = a.sub_spec(b);
        let z = Self::from_int_spec(0);

        Self::lemma_eqv_reflexive(bk);
        Self::lemma_eqv_sub_congruence(ak, bk, bk, bk);
        assert(lhs.eqv_spec(bk.sub_spec(bk)));

        Self::lemma_sub_self_zero_num(bk);
        assert(bk.sub_spec(bk).num == 0);
        assert(z.num == 0);
        assert(bk.sub_spec(bk).eqv_spec(z)
            == (bk.sub_spec(bk).num * z.denom() == z.num * bk.sub_spec(bk).denom()));
        assert(bk.sub_spec(bk).num * z.denom() == 0 * z.denom());
        assert(z.num * bk.sub_spec(bk).denom() == 0 * bk.sub_spec(bk).denom());
        lemma_mul_by_zero_is_zero(z.denom());
        lemma_mul_by_zero_is_zero(bk.sub_spec(bk).denom());
        assert(0 * z.denom() == 0);
        assert(0 * bk.sub_spec(bk).denom() == 0);
        assert(bk.sub_spec(bk).num * z.denom() == z.num * bk.sub_spec(bk).denom());
        assert(bk.sub_spec(bk).eqv_spec(z));
        Self::lemma_eqv_transitive(lhs, bk.sub_spec(bk), z);
        assert(lhs.eqv_spec(z));

        Self::lemma_eqv_sub_cancel_right(a, b, k);
        assert(lhs.eqv_spec(s));
        Self::lemma_eqv_symmetric(lhs, s);
        assert(s.eqv_spec(lhs));
        Self::lemma_eqv_transitive(s, lhs, z);
        assert(s.eqv_spec(z));

        assert(s.eqv_spec(z) == (s.num * z.denom() == z.num * s.denom()));
        assert(z.num == 0);
        assert(z.denom() == 1);
        assert(s.num * z.denom() == z.num * s.denom());
        assert(s.num * 1 == 0 * s.denom());
        lemma_mul_by_zero_is_zero(s.denom());
        assert(0 * s.denom() == 0);
        assert(s.num == 0);
        assert(s.num == a.num * b.denom() + (-b.num) * a.denom());
        assert(a.num * b.denom() + (-b.num) * a.denom() == a.num * b.denom() - b.num * a.denom())
            by (nonlinear_arith);
        assert(a.num * b.denom() - b.num * a.denom() == 0);
        assert((a.num * b.denom() - b.num * a.denom() == 0) ==> (a.num * b.denom() == b.num * a.denom()))
            by (nonlinear_arith);
        assert(a.num * b.denom() == b.num * a.denom());
        assert(a.eqv_spec(b));
    }

    pub proof fn lemma_add_right_cancel(a: Self, b: Self, k: Self)
        requires
            a.add_spec(k).eqv_spec(b.add_spec(k)),
        ensures
            a.eqv_spec(b),
    {
        Self::lemma_add_right_cancel_strong(a, b, k);
        assert(a.eqv_spec(b));
    }

    pub proof fn lemma_add_left_cancel_strong(a: Self, b: Self, k: Self)
        requires
            k.add_spec(a).eqv_spec(k.add_spec(b)),
        ensures
            a.eqv_spec(b),
    {
        let ka = k.add_spec(a);
        let kb = k.add_spec(b);
        let ak = a.add_spec(k);
        let bk = b.add_spec(k);

        Self::lemma_add_commutative(k, a);
        Self::lemma_add_commutative(k, b);
        assert(ka.eqv_spec(ak));
        assert(kb.eqv_spec(bk));
        Self::lemma_eqv_symmetric(ka, ak);
        assert(ak.eqv_spec(ka));
        Self::lemma_eqv_transitive(ak, ka, kb);
        assert(ak.eqv_spec(kb));
        Self::lemma_eqv_transitive(ak, kb, bk);
        assert(ak.eqv_spec(bk));

        Self::lemma_add_right_cancel_strong(a, b, k);
        assert(a.eqv_spec(b));
    }

    pub proof fn lemma_add_left_cancel(a: Self, b: Self, k: Self)
        requires
            k.add_spec(a).eqv_spec(k.add_spec(b)),
        ensures
            a.eqv_spec(b),
    {
        Self::lemma_add_left_cancel_strong(a, b, k);
        assert(a.eqv_spec(b));
    }

    pub proof fn lemma_add_then_sub_cancel(a: Self, b: Self)
        ensures
            a.add_spec(b).sub_spec(a).eqv_spec(b),
    {
        let lhs = a.add_spec(b).sub_spec(a);
        let z = Self::from_int_spec(0);
        let mid1 = b.add_spec(a).sub_spec(z.add_spec(a));
        let mid2 = b.sub_spec(z);

        Self::lemma_add_zero_identity(a);
        Self::lemma_add_zero_identity(b);
        Self::lemma_add_commutative(a, b);
        assert(z.add_spec(a) == a);

        Self::lemma_eqv_reflexive(a);
        assert(a.eqv_spec(z.add_spec(a)));
        Self::lemma_eqv_sub_congruence(a.add_spec(b), b.add_spec(a), a, z.add_spec(a));
        assert(lhs.eqv_spec(mid1));

        Self::lemma_eqv_sub_cancel_right(b, z, a);
        assert(mid1.eqv_spec(mid2));

        assert(mid2 == b.sub_spec(z));
        assert(b.sub_spec(z) == b.add_spec(z.neg_spec()));
        assert(z.num == 0);
        assert(z.neg_spec().num == -z.num);
        assert(z.neg_spec().num == 0);
        assert(z.neg_spec().den == z.den);
        assert(z.neg_spec() == z);
        assert(b.add_spec(z.neg_spec()) == b.add_spec(z));
        assert(b.add_spec(z) == b);
        Self::lemma_eqv_reflexive(b);
        assert(mid2.eqv_spec(b));

        Self::lemma_eqv_transitive(lhs, mid1, mid2);
        Self::lemma_eqv_transitive(lhs, mid2, b);
        assert(lhs.eqv_spec(b));
    }

    pub proof fn lemma_sub_then_add_cancel(a: Self, b: Self)
        ensures
            b.add_spec(a.sub_spec(b)).eqv_spec(a),
    {
        let lhs = b.add_spec(a.sub_spec(b));
        let rhs = a;
        let k = b.neg_spec();
        let z = Self::from_int_spec(0);

        let lhs_swap = a.sub_spec(b).add_spec(b);
        Self::lemma_add_commutative(b, a.sub_spec(b));
        assert(lhs.eqv_spec(lhs_swap));

        let lhsk = lhs.add_spec(k);
        let s1 = lhs_swap.add_spec(k);
        Self::lemma_eqv_reflexive(k);
        Self::lemma_eqv_add_congruence(lhs, lhs_swap, k, k);
        assert(lhsk.eqv_spec(s1));

        let s2 = a.sub_spec(b).add_spec(b.add_spec(k));
        Self::lemma_add_associative(a.sub_spec(b), b, k);
        assert(s1.eqv_spec(s2));

        Self::lemma_add_inverse(b);
        assert(k == b.neg_spec());
        assert(b.add_spec(k).eqv_spec(z));
        Self::lemma_eqv_reflexive(a.sub_spec(b));
        Self::lemma_eqv_add_congruence(a.sub_spec(b), a.sub_spec(b), b.add_spec(k), z);
        assert(s2.eqv_spec(a.sub_spec(b).add_spec(z)));

        Self::lemma_add_zero_identity(a.sub_spec(b));
        assert(a.sub_spec(b).add_spec(z) == a.sub_spec(b));
        Self::lemma_eqv_reflexive(a.sub_spec(b));
        assert(a.sub_spec(b).add_spec(z).eqv_spec(a.sub_spec(b)));

        Self::lemma_eqv_transitive(s1, s2, a.sub_spec(b).add_spec(z));
        Self::lemma_eqv_transitive(s1, a.sub_spec(b).add_spec(z), a.sub_spec(b));
        assert(s1.eqv_spec(a.sub_spec(b)));

        let rhsk = rhs.add_spec(k);
        Self::lemma_sub_is_add_neg(a, b);
        assert(rhsk == a.add_spec(b.neg_spec()));
        assert(a.sub_spec(b) == a.add_spec(b.neg_spec()));
        assert(rhsk == a.sub_spec(b));
        Self::lemma_eqv_reflexive(a.sub_spec(b));
        assert(rhsk.eqv_spec(a.sub_spec(b)));

        Self::lemma_eqv_transitive(lhsk, s1, a.sub_spec(b));
        assert(lhsk.eqv_spec(a.sub_spec(b)));
        Self::lemma_eqv_symmetric(rhsk, a.sub_spec(b));
        assert(a.sub_spec(b).eqv_spec(rhsk));
        Self::lemma_eqv_transitive(lhsk, a.sub_spec(b), rhsk);
        assert(lhsk.eqv_spec(rhsk));

        Self::lemma_add_right_cancel_strong(lhs, rhs, k);
        assert(lhs.eqv_spec(rhs));
    }

    pub proof fn lemma_sub_eqv_zero_iff_eqv(a: Self, b: Self)
        ensures
            a.sub_spec(b).eqv_spec(Self::from_int_spec(0)) == a.eqv_spec(b),
    {
        let s = a.sub_spec(b);
        let z = Self::from_int_spec(0);

        if s.eqv_spec(z) {
            let bs = b.add_spec(s);
            Self::lemma_sub_then_add_cancel(a, b);
            assert(bs.eqv_spec(a));
            Self::lemma_eqv_reflexive(b);
            Self::lemma_eqv_add_congruence(b, b, s, z);
            assert(bs.eqv_spec(b.add_spec(z)));
            Self::lemma_add_zero_identity(b);
            assert(b.add_spec(z) == b);
            Self::lemma_eqv_reflexive(b);
            assert(bs.eqv_spec(b));
            Self::lemma_eqv_symmetric(bs, b);
            assert(b.eqv_spec(bs));
            Self::lemma_eqv_transitive(b, bs, a);
            assert(b.eqv_spec(a));
            Self::lemma_eqv_symmetric(b, a);
            assert(a.eqv_spec(b));
        }

        if a.eqv_spec(b) {
            Self::lemma_eqv_reflexive(b);
            Self::lemma_eqv_sub_congruence(a, b, b, b);
            assert(a.sub_spec(b).eqv_spec(b.sub_spec(b)));
            Self::lemma_sub_self_zero_num(b);
            assert(b.sub_spec(b).num == 0);
            Self::lemma_eqv_zero_iff_num_zero(b.sub_spec(b));
            assert(b.sub_spec(b).eqv_spec(z) == (b.sub_spec(b).num == 0));
            assert(b.sub_spec(b).eqv_spec(z));
            Self::lemma_eqv_transitive(a.sub_spec(b), b.sub_spec(b), z);
            assert(a.sub_spec(b).eqv_spec(z));
        }
        assert((a.sub_spec(b).eqv_spec(z)) == a.eqv_spec(b));
    }

    pub proof fn lemma_sub_antisymmetric(a: Self, b: Self)
        ensures
            a.sub_spec(b) == b.sub_spec(a).neg_spec(),
    {
        let lhs = a.sub_spec(b);
        let rhs = b.sub_spec(a).neg_spec();
        assert(lhs == a.add_spec(b.neg_spec()));
        assert(rhs == b.add_spec(a.neg_spec()).neg_spec());

        assert(lhs.num == a.num * b.denom() + (-b.num) * a.denom());
        assert(rhs.num == -(b.num * a.denom() + (-a.num) * b.denom()));
        assert(a.num * b.denom() + (-b.num) * a.denom()
            == -(b.num * a.denom() + (-a.num) * b.denom())) by (nonlinear_arith);
        assert(lhs.num == rhs.num);

        assert(lhs.den == a.den * b.den + a.den + b.den);
        assert(rhs.den == b.den * a.den + b.den + a.den);
        assert(a.den * b.den + a.den + b.den == b.den * a.den + b.den + a.den) by (nonlinear_arith);
        assert(lhs.den == rhs.den);
    }

    pub proof fn lemma_mul_neg_right(a: Self, b: Self)
        ensures
            a.mul_spec(b.neg_spec()) == a.mul_spec(b).neg_spec(),
    {
        let lhs = a.mul_spec(b.neg_spec());
        let rhs = a.mul_spec(b).neg_spec();

        assert(lhs.num == a.num * (-b.num));
        assert(rhs.num == -(a.num * b.num));
        assert(a.num * (-b.num) == -(a.num * b.num)) by (nonlinear_arith);
        assert(lhs.num == rhs.num);

        assert(lhs.den == a.den * b.neg_spec().den + a.den + b.neg_spec().den);
        assert(rhs.den == a.mul_spec(b).den);
        assert(b.neg_spec().den == b.den);
        assert(a.mul_spec(b).den == a.den * b.den + a.den + b.den);
        assert(lhs.den == a.den * b.den + a.den + b.den);
        assert(lhs.den == rhs.den);
    }

    pub proof fn lemma_sub_neg_both(a: Self, b: Self)
        ensures
            a.neg_spec().sub_spec(b.neg_spec()) == a.sub_spec(b).neg_spec(),
    {
        let lhs = a.neg_spec().sub_spec(b.neg_spec());
        let rhs = a.sub_spec(b).neg_spec();

        assert(lhs.num == (-a.num) * b.neg_spec().denom() + (-b.neg_spec().num) * a.neg_spec().denom());
        assert(rhs.num == -(a.num * b.denom() + (-b.num) * a.denom()));
        assert(b.neg_spec().denom() == b.denom());
        assert(a.neg_spec().denom() == a.denom());
        assert(b.neg_spec().num == -b.num);
        assert(-b.neg_spec().num == b.num) by (nonlinear_arith);
        calc! {
            (==)
            lhs.num;
            { }
            (-a.num) * b.neg_spec().denom() + (-b.neg_spec().num) * a.neg_spec().denom();
            {
                assert(b.neg_spec().denom() == b.denom());
                assert(a.neg_spec().denom() == a.denom());
                assert(-b.neg_spec().num == b.num);
            }
            (-a.num) * b.denom() + b.num * a.denom();
        }
        calc! {
            (==)
            rhs.num;
            { }
            -(a.num * b.denom() + (-b.num) * a.denom());
            {
                assert(-(a.num * b.denom() + (-b.num) * a.denom())
                    == (-a.num) * b.denom() + b.num * a.denom()) by (nonlinear_arith);
            }
            (-a.num) * b.denom() + b.num * a.denom();
        }
        assert(lhs.num == rhs.num);

        assert(lhs.den == a.neg_spec().den * b.neg_spec().den + a.neg_spec().den + b.neg_spec().den);
        assert(rhs.den == a.sub_spec(b).den);
        assert(a.neg_spec().den == a.den);
        assert(b.neg_spec().den == b.den);
        assert(a.sub_spec(b).den == a.den * b.den + a.den + b.den);
        assert(lhs.den == a.den * b.den + a.den + b.den);
        assert(lhs.den == rhs.den);
    }

    pub proof fn lemma_sub_self_zero_num(a: Self)
        ensures
            a.sub_spec(a).num == 0,
    {
        let d = a.denom();
        let s = a.sub_spec(a);
        assert(s == a.add_spec(a.neg_spec()));
        assert(s.num == a.num * d + (-a.num) * d);
        assert(a.num * d + (-a.num) * d == a.num * d - a.num * d) by (nonlinear_arith);
        assert(a.num * d - a.num * d == 0) by (nonlinear_arith);
        assert(s.num == 0);
    }

    pub proof fn lemma_sub_self_zero_signum(a: Self)
        ensures
            a.sub_spec(a).signum() == 0,
    {
        let s = a.sub_spec(a);
        Self::lemma_sub_self_zero_num(a);
        assert(s.num == 0);
        Self::lemma_signum_zero_iff(s);
        assert((s.signum() == 0) == (s.num == 0));
        assert(s.signum() == 0);
    }

    pub proof fn lemma_mul_left_zero_num(a: Self, b: Self)
        requires
            a.num == 0,
        ensures
            a.mul_spec(b).num == 0,
    {
        let p = a.mul_spec(b);
        assert(a.num == 0);
        calc! {
            (==)
            a.num * b.num;
            { assert(a.num == 0); }
            0 * b.num;
            {
                lemma_mul_by_zero_is_zero(b.num);
                assert(0 * b.num == 0);
            }
            0;
        }
        assert(p.num == a.num * b.num);
        assert(p.num == 0);
    }

    pub proof fn lemma_mul_right_zero_num(a: Self, b: Self)
        requires
            b.num == 0,
        ensures
            a.mul_spec(b).num == 0,
    {
        let p = a.mul_spec(b);
        assert(b.num == 0);
        calc! {
            (==)
            a.num * b.num;
            { assert(b.num == 0); }
            a.num * 0;
            {
                lemma_mul_by_zero_is_zero(a.num);
                assert(a.num * 0 == 0);
            }
            0;
        }
        assert(p.num == a.num * b.num);
        assert(p.num == 0);
    }

    pub proof fn lemma_sub_both_zero_num(a: Self, b: Self)
        requires
            a.num == 0,
            b.num == 0,
        ensures
            a.sub_spec(b).num == 0,
    {
        let s = a.sub_spec(b);
        assert(a.num == 0);
        assert(b.num == 0);
        calc! {
            (==)
            -b.num;
            { assert(b.num == 0); }
            -0;
            { }
            0;
        }
        calc! {
            (==)
            a.num * b.neg_spec().denom();
            { assert(a.num == 0); }
            0 * b.neg_spec().denom();
            {
                lemma_mul_by_zero_is_zero(b.neg_spec().denom());
                assert(0 * b.neg_spec().denom() == 0);
            }
            0;
        }
        calc! {
            (==)
            (-b.num) * a.denom();
            { assert(-b.num == 0); }
            0 * a.denom();
            {
                lemma_mul_by_zero_is_zero(a.denom());
                assert(0 * a.denom() == 0);
            }
            0;
        }
        assert(s == a.add_spec(b.neg_spec()));
        assert(s.num == a.num * b.neg_spec().denom() + (-b.num) * a.denom());
        assert(s.num == 0 + 0);
        assert(s.num == 0);
    }

    pub proof fn lemma_eqv_reflexive(a: Self)
        ensures
            a.eqv_spec(a),
    {
        assert(a.num * a.denom() == a.num * a.denom());
    }

    pub proof fn lemma_eqv_symmetric(a: Self, b: Self)
        ensures
            a.eqv_spec(b) == b.eqv_spec(a),
    {
        assert(a.eqv_spec(b) == (a.num * b.denom() == b.num * a.denom()));
        assert(b.eqv_spec(a) == (b.num * a.denom() == a.num * b.denom()));
    }

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
        // (1 - t) + t ≡ 1, i.e. s + t ≡ 1
        // Actually sub_then_add_cancel gives s.add_spec(t) ≡ one? Let me check.
        // lemma_sub_then_add_cancel(a, b): (a - b) + b ≡ a
        // So (one - t) + t ≡ one, i.e. s.add_spec(t) ≡ one. ✓

        // a * (s + t) ≡ a * 1 ≡ a by congruence
        Self::lemma_eqv_mul_congruence_right(a, s.add_spec(t), one);
        // a * (s+t) ≡ a * 1
        // a * (s+t) ≡ a*s + a*t by distributivity
        Self::lemma_eqv_mul_distributive_left(a, s, t);
        // a * (s+t) ≡ a*s + a*t

        // Now a*t ≤ b*t (since a ≤ b and t ≥ 0)
        Self::lemma_le_mul_nonneg(a, b, t);

        // a*s + a*t ≤ a*s + b*t by add monotonicity on second component
        Self::lemma_add_commutative(a.mul_spec(s), a.mul_spec(t));
        Self::lemma_add_commutative(a.mul_spec(s), b.mul_spec(t));
        Self::lemma_le_add_monotone(a.mul_spec(t), b.mul_spec(t), a.mul_spec(s));
        // a*t + a*s ≤ b*t + a*s, i.e. a*s + a*t ≤ a*s + b*t (by commutativity ==)

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
        // v3 ≤ v4 (monotonicity)

        // a ≡ v1 ≡ v2 ≡ v3, so a ≡ v3
        Self::lemma_eqv_transitive(a, v1, v2);
        Self::lemma_eqv_transitive(a, v2, v3);
        // a ≡ v3 → a ≤ v3
        Self::lemma_eqv_implies_le(a, v3);
        // v3 ≤ v4
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
}

/// Alias for backward compatibility with code that used the RationalModel name.
pub type RationalModel = Rational;

} // verus!
