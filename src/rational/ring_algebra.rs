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

}

} // verus!
