use super::Rational;
use vstd::prelude::*;

verus! {

impl Rational {
    //  ── 2×2 determinant & Cramer's rule ────────────────────

    pub open spec fn det2_spec(a: Self, b: Self, c: Self, d: Self) -> Self {
        a.mul_spec(d).sub_spec(b.mul_spec(c))
    }

    ///  Swapping rows negates the determinant.
    pub proof fn lemma_det2_antisymmetric(a: Self, b: Self, c: Self, d: Self)
        ensures
            Self::det2_spec(c, d, a, b).eqv_spec(
                Self::det2_spec(a, b, c, d).neg_spec()),
    {
        //  det2(c,d,a,b) = c*b - d*a
        //  det2(a,b,c,d) = a*d - b*c
        //  -(a*d - b*c) = b*c - a*d
        //  Need: c*b - d*a ≡ b*c - a*d
        let cb = c.mul_spec(b);
        let da = d.mul_spec(a);
        let ad = a.mul_spec(d);
        let bc = b.mul_spec(c);
        Self::lemma_mul_commutative(c, b);
        assert(cb == bc);
        Self::lemma_mul_commutative(d, a);
        assert(da == ad);
        //  det2(c,d,a,b) = cb - da = bc - ad
        //  -(det2(a,b,c,d)) = -(ad - bc) = bc - ad  by neg_sub
        Self::lemma_neg_sub(ad, bc);
        //  ad.sub_spec(bc).neg_spec() == bc.sub_spec(ad)
        Self::lemma_eqv_reflexive(bc.sub_spec(ad));
    }

    ///  det2 ≡ 0 ↔ a*d ≡ b*c (collinearity).
    pub proof fn lemma_det2_zero_iff_proportional(a: Self, b: Self, c: Self, d: Self)
        ensures
            Self::det2_spec(a, b, c, d).eqv_spec(Self::from_int_spec(0))
            == a.mul_spec(d).eqv_spec(b.mul_spec(c)),
    {
        Self::lemma_sub_eqv_zero_iff_eqv(a.mul_spec(d), b.mul_spec(c));
    }

    ///  Helper for Cramer's rule: proves a*x + b*y ≡ e.
    proof fn lemma_cramer2_eq1(
        a: Self, b: Self, c: Self, d: Self, e: Self, f: Self,
    )
        requires
            !Self::det2_spec(a, b, c, d).eqv_spec(Self::from_int_spec(0)),
        ensures ({
            let det = Self::det2_spec(a, b, c, d);
            let x = d.mul_spec(e).sub_spec(b.mul_spec(f)).div_spec(det);
            let y = a.mul_spec(f).sub_spec(c.mul_spec(e)).div_spec(det);
            a.mul_spec(x).add_spec(b.mul_spec(y)).eqv_spec(e)
        }),
    {
        let det = Self::det2_spec(a, b, c, d);
        let num_x = d.mul_spec(e).sub_spec(b.mul_spec(f));
        let num_y = a.mul_spec(f).sub_spec(c.mul_spec(e));
        let x = num_x.div_spec(det);
        let y = num_y.div_spec(det);

        Self::lemma_eqv_zero_iff_num_zero(det);

        //  x = num_x / det, so det * x ≡ num_x
        Self::lemma_div_cancel(det, num_x);
        //  det * x ≡ num_x = d*e - b*f

        //  y = num_y / det, so det * y ≡ num_y
        Self::lemma_div_cancel(det, num_y);
        //  det * y ≡ num_y = a*f - c*e

        //  We need: a*x + b*y ≡ e
        //  Multiply both sides by det: det*(a*x + b*y) ≡ det*e
        //  det*(a*x + b*y) ≡ det*a*x + det*b*y
        //                   ≡ a*(det*x) + b*(det*y)
        //                   ≡ a*num_x + b*num_y
        //                   = a*(d*e - b*f) + b*(a*f - c*e)
        //                   = a*d*e - a*b*f + a*b*f - b*c*e
        //                   = a*d*e - b*c*e
        //                   = (a*d - b*c)*e
        //                   = det * e
        //  So det*(a*x + b*y) ≡ det*e, cancel det to get a*x + b*y ≡ e.

        //  a*x: a * (num_x / det) = a * (num_x * inv_det)
        //     ≡ (a * num_x) / det  by div_mul_assoc (reversed)
        Self::lemma_div_mul_assoc(num_x, det, a);
        Self::lemma_mul_commutative(x, a);
        //  x * a = a * x structurally... no, x = num_x.div_spec(det) = num_x.mul_spec(inv)
        //  a.mul_spec(x) vs num_x.div_spec(det).mul_spec(a)... hmm

        //  Let me use a different approach: show det * (a*x + b*y) ≡ det * e
        //  then cancel.

        //  det * (a*x + b*y) ≡ det*a*x + det*b*y  by distributive
        let ax = a.mul_spec(x);
        let by_ = b.mul_spec(y);
        let sum = ax.add_spec(by_);
        Self::lemma_eqv_mul_distributive_left(det, ax, by_);
        //  det*ax ≡ a*(det*x) by commut+assoc
        Self::lemma_mul_commutative(det, ax);
        Self::lemma_mul_commutative(det, a);
        //  det*a = a*det structurally. det*ax = ax*det = (a*x)*det
        //  (a*x)*det ≡ a*(x*det) by assoc
        Self::lemma_mul_associative(a, x, det);
        Self::lemma_mul_commutative(x, det);
        //  x*det == det*x structurally
        //  a*(x*det) = a*(det*x) structurally
        //  det*x ≡ num_x (from div_cancel: det * (num_x/det) ≡ num_x)
        //  So a*(det*x) ≡ a*num_x
        Self::lemma_eqv_mul_congruence_right(
            a, det.mul_spec(x), num_x,
        );
        //  Chain: det*ax = ax*det ≡ a*(x*det) = a*(det*x) ≡ a*num_x
        assert(ax.mul_spec(det) == det.mul_spec(ax));
        Self::lemma_eqv_transitive(
            det.mul_spec(ax),
            a.mul_spec(x.mul_spec(det)),
            a.mul_spec(num_x),
        );

        //  Similarly for det*by ≡ b*num_y
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

        //  det*(ax+by) ≡ det*ax + det*by ≡ a*num_x + b*num_y
        Self::lemma_eqv_add_congruence(
            det.mul_spec(ax), a.mul_spec(num_x),
            det.mul_spec(by_), b.mul_spec(num_y),
        );
        Self::lemma_eqv_transitive(
            det.mul_spec(sum),
            det.mul_spec(ax).add_spec(det.mul_spec(by_)),
            a.mul_spec(num_x).add_spec(b.mul_spec(num_y)),
        );

        //  a*num_x + b*num_y = a*(d*e - b*f) + b*(a*f - c*e)
        //  Expand a*(d*e - b*f):
        Self::lemma_sub_mul_right(d.mul_spec(e), b.mul_spec(f), a);
        //  = a*d*e - a*b*f  (eqv)
        //  Expand b*(a*f - c*e):
        Self::lemma_sub_mul_right(a.mul_spec(f), c.mul_spec(e), b);
        //  = b*a*f - b*c*e  (eqv)

        //  Strategy: show det*(ax+by) ≡ a*num_x + b*num_y ≡ det*e, then cancel det.
        //  a * num_x = num_x * a (by commut)
        Self::lemma_mul_commutative(a, num_x);
        //  num_x * a ≡ de*a - bf*a (by sub_mul_right)
        let de = d.mul_spec(e);
        let bf = b.mul_spec(f);
        //  sub_mul_right(de, bf, a): (de - bf) * a ≡ de*a - bf*a
        //  But we also need: de*a ≡ a*d*e etc. This telescopes into many assoc/commut steps.

        //  This proof is getting extremely long. Let me use a much simpler approach:
        //  prove it directly at the numerator/denominator cross-multiplication level.
        //  This avoids all the algebraic manipulation.

        //  SIMPLIFIED APPROACH: prove eqv directly via cross-multiplication.
        //  For a*x + b*y ≡ e, we check:
        //  (a*x + b*y).num * e.denom() == e.num * (a*x + b*y).denom()
        //  This is tedious but mechanical and avoids the algebraic chain.

        //  Even simpler: just use the fact that det*(a*x + b*y) ≡ det*e,
        //  where det*e = (ad-bc)*e.
        //  Since we've shown det*(ax+by) ≡ a*num_x + b*num_y above,
        //  we need a*num_x + b*num_y ≡ det*e.
        //  This is an algebraic identity that we can verify at the num level.

        //  Actually the cleanest: note that a*(de-bf) + b*(af-ce) = ade-abf+baf-bce = ade-bce = (ad-bc)e = det*e.
        //  All these are eqv (not ==), so we need the chain.

        //  Let me try yet another approach: prove it for the FIRST equation only using a helper,
        //  and note the second is symmetric.

        //  FINAL APPROACH: Use the identity directly.
        //  We want: a*x + b*y ≡ e where x = num_x/det, y = num_y/det.
        //  Equivalently: (a*num_x + b*num_y)/det ≡ e.
        //  (a*num_x + b*num_y) = a*(de-bf) + b*(af-ce)
        //  We'll prove a*(de-bf) + b*(af-ce) ≡ det*e
        //  then use div_cancel to conclude (det*e)/det ≡ e.

        //  Let me use div_add_numerator: (a*num_x + b*num_y)/det = a*num_x/det + b*num_y/det
        Self::lemma_div_add_numerator(a.mul_spec(num_x), b.mul_spec(num_y), det);
        //  a*num_x/det ≡ a*(num_x/det) = a*x  by div_mul_assoc
        Self::lemma_div_mul_assoc(num_x, det, a);
        //  (num_x/det)*a ≡ (num_x*a)/det
        Self::lemma_mul_commutative(x, a);
        //  a*x = x*a = (num_x*inv)*a, and (num_x/det)*a = x*a structurally
        //  Similarly: b*num_y/det ≡ b*y by div_mul_assoc
        Self::lemma_div_mul_assoc(num_y, det, b);
        Self::lemma_mul_commutative(y, b);

        //  So (a*num_x + b*num_y)/det ≡ a*x + b*y
        //  And if a*num_x + b*num_y ≡ det*e, then (det*e)/det ≡ e by div_mul_cancel
        Self::lemma_div_mul_cancel(e, det);
        //  (e*det)/det ≡ e
        Self::lemma_mul_commutative(e, det);
        //  e*det = det*e structurally

        //  Now prove: a*num_x + b*num_y ≡ det*e
        //  a*(de-bf) + b*(af-ce) ≡ (ad-bc)*e
        //  Expand using sub_mul_right:
        //  (de-bf)*a ≡ de*a - bf*a
        Self::lemma_sub_mul_right(de, bf, a);
        //  (af-ce)*b ≡ af*b - ce*b
        let af = a.mul_spec(f);
        let ce = c.mul_spec(e);
        Self::lemma_sub_mul_right(af, ce, b);

        //  Now: num_x*a + num_y*b ≡ (de*a - bf*a) + (af*b - ce*b)
        //  We need a*num_x + b*num_y, but by commut:
        assert(a.mul_spec(num_x) == num_x.mul_spec(a));
        assert(b.mul_spec(num_y) == num_y.mul_spec(b));
        Self::lemma_eqv_add_congruence(
            num_x.mul_spec(a), de.mul_spec(a).sub_spec(bf.mul_spec(a)),
            num_y.mul_spec(b), af.mul_spec(b).sub_spec(ce.mul_spec(b)),
        );
        //  = (de*a - bf*a) + (af*b - ce*b)
        //  Use sub_add_distributes: (X-Y) + (Z-W) ≡ (X+Z) - (Y+W)... wait that's not right.
        //  Actually sub_add_distributes is: (a+b) - (c+d) ≡ (a-c) + (b-d)
        //  We need: (de*a - bf*a) + (af*b - ce*b)
        //  ≡ (de*a + af*b) - (bf*a + ce*b)  ... need to prove this

        //  This is getting extremely long. Let me take a completely different tack and
        //  prove it at the raw numerator level with nonlinear_arith.

        //  Actually, for a complex theorem like Cramer's rule, the most reliable approach
        //  in Verus is to unfold everything to numerators and use nonlinear_arith.
        //  Let me abandon the algebraic approach and do this directly.

        //  I'll assert the final result and let the SMT solver handle it with enough hints.
        //  The key insight: a*x + b*y ≡ e means
        //  (a*x + b*y).num * e.denom() == e.num * (a*x + b*y).denom()

        //  But even this would be incredibly complex at the numerator level because of
        //  the chain of additions and multiplications.

        //  PRAGMATIC APPROACH: Accept that Cramer's rule is too complex for a single proof
        //  and instead just prove the identity a*(de-bf) + b*(af-ce) ≡ (ad-bc)*e
        //  using the sub_add_distributes + cancellation lemmas we already have.

        //  Actually I realize I'm overcomplicating this. Let me use:
        //  1. det * (a*x + b*y) ≡ a*(det*x) + b*(det*y) ≡ a*num_x + b*num_y
        //  2. a*num_x + b*num_y ≡ det*e (algebraic identity)
        //  3. So det*(a*x + b*y) ≡ det*e, cancel det.

        //  For step 2, use sub_mul_right and cancellation.
        //  I've already started this. Let me continue more carefully.

        //  After sub_mul_right:
        //  num_x*a ≡ de*a - bf*a
        //  num_y*b ≡ af*b - ce*b
        //  We need their sum ≡ det*e

        //  de*a = d*e*a, bf*a = b*f*a, af*b = a*f*b, ce*b = c*e*b
        //  By mul commutative/associative:
        //  de*a ≡ a*d*e = (a*d)*e ≡ ad*e  (where ad = a*d = a.mul_spec(d))
        //  bf*a ≡ a*b*f   ... hmm not bf*a but b*f then *a

        //  I think the cleanest approach for Cramer's is to defer to a numerator-level proof.
        //  But that would be enormous. Let me try a simpler ensures instead:
        //  just verify it as an opaque identity. Actually no, I want it verified.

        //  OK let me commit to the algebraic approach step by step.

        //  I proved: det*(ax+by) ≡ a*num_x + b*num_y
        //                         = a*(de-bf) + b*(af-ce)
        //  Need: ≡ det*e = (ad-bc)*e

        //  a*(de-bf) + b*(af-ce)
        //  Expand using sub_mul_right (already called):
        //  ≡ (de*a - bf*a) + (af*b - ce*b)

        //  Now use commutative to rewrite:
        //  de*a: (d*e)*a ≡ d*(e*a) by assoc, e*a = a*e by commut, so d*(a*e) ≡ (d*a)*e by assoc back
        //        d*a = a*d by commut. So de*a ≡ ad*e.
        //  bf*a: (b*f)*a ≡ b*(f*a) by assoc, f*a = a*f by commut, so b*(a*f) ≡ (b*a)*f = (a*b)*f by commut
        //        So bf*a ≡ ab*f = a*b*f. Hmm we need bf*a ≡ af*b? Let me check:
        //        bf*a = b*f*a, af*b = a*f*b. By commut: b*f*a = a*b*f (via commut+assoc), a*f*b = a*b*f similarly.
        //        So bf*a ≡ af*b.
        //  af*b: same
        //  ce*b: (c*e)*b ≡ c*(e*b) = c*(b*e) ≡ (c*b)*e = (b*c)*e by commut

        //  So: (ad*e - af*b) + (af*b - bc*e)
        //    = ad*e - af*b + af*b - bc*e
        //    ≡ ad*e - bc*e  (after af*b cancels)
        //    ≡ (ad - bc)*e  by sub_mul_right backward
        //    = det*e  ✓

        //  This requires showing bf*a ≡ af*b and the cancellation.
        //  Since this is extremely involved, let me break it down:

        //  Step A: de*a ≡ ad*e
        let ad = a.mul_spec(d);
        let bc_ = b.mul_spec(c);
        Self::lemma_mul_associative(d, e, a);
        //  de*a ≡ d*(e*a)
        Self::lemma_mul_commutative(e, a);
        //  e*a == a*e structurally
        //  d*(a*e) ≡ (d*a)*e by assoc backward
        Self::lemma_mul_associative(d, a, e);
        Self::lemma_eqv_symmetric(d.mul_spec(a).mul_spec(e), d.mul_spec(a.mul_spec(e)));
        Self::lemma_mul_commutative(d, a);
        assert(d.mul_spec(a) == ad);
        //  de*a ≡ d*(e*a) = d*(a*e) ≡ (d*a)*e = ad*e
        Self::lemma_eqv_transitive(
            de.mul_spec(a), d.mul_spec(e.mul_spec(a)), d.mul_spec(a.mul_spec(e)),
        );
        Self::lemma_eqv_transitive(
            de.mul_spec(a), d.mul_spec(a.mul_spec(e)), ad.mul_spec(e),
        );

        //  Step B: bf*a ≡ af*b (these cancel)
        //  bf*a = (b*f)*a ≡ b*(f*a) by assoc
        Self::lemma_mul_associative(b, f, a);
        //  f*a == a*f structurally by commut
        Self::lemma_mul_commutative(f, a);
        //  So b*(f*a) == b*(a*f) structurally, i.e. bf*a ≡ b*(a*f)
        //  b*(a*f) ≡ (b*a)*f by assoc (backward)
        Self::lemma_mul_associative(b, a, f);
        Self::lemma_eqv_symmetric(b.mul_spec(a).mul_spec(f), b.mul_spec(a.mul_spec(f)));
        //  Chain: bf*a ≡ b*(a*f) ≡ (b*a)*f
        Self::lemma_eqv_transitive(
            bf.mul_spec(a), b.mul_spec(a.mul_spec(f)), b.mul_spec(a).mul_spec(f),
        );
        //  af*b = (a*f)*b ≡ a*(f*b) by assoc
        Self::lemma_mul_associative(a, f, b);
        //  f*b == b*f structurally by commut
        Self::lemma_mul_commutative(f, b);
        //  a*(f*b) == a*(b*f) structurally
        //  a*(b*f) ≡ (a*b)*f by assoc (backward)
        Self::lemma_mul_associative(a, b, f);
        Self::lemma_eqv_symmetric(a.mul_spec(b).mul_spec(f), a.mul_spec(b.mul_spec(f)));
        //  Chain: af*b ≡ a*(b*f) ≡ (a*b)*f
        Self::lemma_eqv_transitive(
            af.mul_spec(b), a.mul_spec(b.mul_spec(f)), a.mul_spec(b).mul_spec(f),
        );
        //  (b*a)*f == (a*b)*f since b*a == a*b structurally
        Self::lemma_mul_commutative(b, a);
        assert(b.mul_spec(a) == a.mul_spec(b));
        //  bf*a ≡ (a*b)*f and af*b ≡ (a*b)*f, so bf*a ≡ af*b
        Self::lemma_eqv_symmetric(af.mul_spec(b), a.mul_spec(b).mul_spec(f));
        Self::lemma_eqv_transitive(bf.mul_spec(a), a.mul_spec(b).mul_spec(f), af.mul_spec(b));

        //  Step C: ce*b ≡ bc*e
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

        //  Step D: (de*a - bf*a) + (af*b - ce*b) ≡ (ad*e - af*b) + (af*b - bc*e)
        //  de*a ≡ ad*e, bf*a ≡ af*b → de*a - bf*a ≡ ad*e - af*b
        Self::lemma_eqv_sub_congruence(de.mul_spec(a), ad.mul_spec(e), bf.mul_spec(a), af.mul_spec(b));
        //  af*b ≡ af*b (refl), ce*b ≡ bc*e → af*b - ce*b ≡ af*b - bc*e
        Self::lemma_eqv_reflexive(af.mul_spec(b));
        Self::lemma_eqv_sub_congruence(af.mul_spec(b), af.mul_spec(b), ce.mul_spec(b), bc_.mul_spec(e));
        //  Sum: ≡ (ad*e - af*b) + (af*b - bc*e)
        Self::lemma_eqv_add_congruence(
            de.mul_spec(a).sub_spec(bf.mul_spec(a)),
            ad.mul_spec(e).sub_spec(af.mul_spec(b)),
            af.mul_spec(b).sub_spec(ce.mul_spec(b)),
            af.mul_spec(b).sub_spec(bc_.mul_spec(e)),
        );

        //  Step E: (ad*e - af*b) + (af*b - bc*e) ≡ ad*e - bc*e
        //  This is X - Y + Y - Z ≡ X - Z
        //  Use: (X-Y)+(Y-Z) ≡ X-Z by eqv_sub_chain
        Self::lemma_eqv_sub_chain(ad.mul_spec(e), af.mul_spec(b), bc_.mul_spec(e));

        //  Step F: ad*e - bc*e ≡ (ad - bc)*e = det*e
        //  (ad - bc)*e ≡ ad*e - bc*e  by sub_mul_right
        Self::lemma_sub_mul_right(ad, bc_, e);
        Self::lemma_eqv_symmetric(ad.mul_spec(e).sub_spec(bc_.mul_spec(e)), det.mul_spec(e));

        //  Combine D+E+F: (de*a - bf*a) + (af*b - ce*b) ≡ det*e
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

        //  From sub_mul_right earlier:
        //  num_x*a ≡ de*a - bf*a
        //  num_y*b ≡ af*b - ce*b
        //  So a*num_x + b*num_y ≡ de*a - bf*a + af*b - ce*b ≡ det*e
        Self::lemma_eqv_transitive(
            num_x.mul_spec(a).add_spec(num_y.mul_spec(b)),
            de.mul_spec(a).sub_spec(bf.mul_spec(a)).add_spec(
                af.mul_spec(b).sub_spec(ce.mul_spec(b))),
            det.mul_spec(e),
        );

        //  We had: det*(ax+by) ≡ a*num_x + b*num_y = num_x*a + num_y*b
        Self::lemma_eqv_transitive(
            det.mul_spec(sum),
            num_x.mul_spec(a).add_spec(num_y.mul_spec(b)),
            det.mul_spec(e),
        );
        //  Cancel det: ax + by ≡ e
        Self::lemma_mul_cancel_left(sum, e, det);
    }

    ///  Helper for Cramer's rule: proves c*x + d*y ≡ f.
    proof fn lemma_cramer2_eq2(
        a: Self, b: Self, c: Self, d: Self, e: Self, f: Self,
    )
        requires
            !Self::det2_spec(a, b, c, d).eqv_spec(Self::from_int_spec(0)),
        ensures ({
            let det = Self::det2_spec(a, b, c, d);
            let x = d.mul_spec(e).sub_spec(b.mul_spec(f)).div_spec(det);
            let y = a.mul_spec(f).sub_spec(c.mul_spec(e)).div_spec(det);
            c.mul_spec(x).add_spec(d.mul_spec(y)).eqv_spec(f)
        }),
    {
        let det = Self::det2_spec(a, b, c, d);
        let num_x = d.mul_spec(e).sub_spec(b.mul_spec(f));
        let num_y = a.mul_spec(f).sub_spec(c.mul_spec(e));
        let x = num_x.div_spec(det);
        let y = num_y.div_spec(det);

        Self::lemma_eqv_zero_iff_num_zero(det);

        //  x = num_x / det, so det * x ≡ num_x
        Self::lemma_div_cancel(det, num_x);
        //  det * x ≡ num_x = d*e - b*f

        //  y = num_y / det, so det * y ≡ num_y
        Self::lemma_div_cancel(det, num_y);

        let de = d.mul_spec(e);
        let bf = b.mul_spec(f);
        let af = a.mul_spec(f);
        let ce = c.mul_spec(e);
        let ad = a.mul_spec(d);
        let bc_ = b.mul_spec(c);

        Self::lemma_sub_mul_right(de, bf, c);
        Self::lemma_sub_mul_right(af, ce, d);

        //  So same structure. Let me do it.
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

        //  c*num_x + d*num_y ≡ det*f (same algebraic identity)
        assert(c.mul_spec(num_x) == num_x.mul_spec(c));
        assert(d.mul_spec(num_y) == num_y.mul_spec(d));
        Self::lemma_sub_mul_right(de, bf, c);
        Self::lemma_sub_mul_right(af, ce, d);
        Self::lemma_eqv_add_congruence(
            num_x.mul_spec(c), de.mul_spec(c).sub_spec(bf.mul_spec(c)),
            num_y.mul_spec(d), af.mul_spec(d).sub_spec(ce.mul_spec(d)),
        );

        //  de*c ≡ cd*e, bf*c ≡ bc*f... wait let me redo for second eq.
        //  de*c: (d*e)*c ≡ d*(e*c) = d*(c*e) ≡ (d*c)*e = (c*d)*e
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
        //  cd*e ≡ dc*e = de*c is what we showed. So de*c ≡ cd*e.

        //  ce*d: (c*e)*d ≡ c*(e*d) = c*(d*e) ≡ (c*d)*e = cd*e
        Self::lemma_mul_associative(c, e, d);
        Self::lemma_mul_commutative(e, d);
        Self::lemma_mul_associative(c, d, e);
        Self::lemma_eqv_symmetric(cd.mul_spec(e), c.mul_spec(d.mul_spec(e)));
        Self::lemma_eqv_transitive(
            ce.mul_spec(d), c.mul_spec(e.mul_spec(d)), c.mul_spec(d.mul_spec(e)),
        );
        Self::lemma_eqv_transitive(ce.mul_spec(d), c.mul_spec(d.mul_spec(e)), cd.mul_spec(e));
        //  So de*c ≡ cd*e and ce*d ≡ cd*e, hence de*c ≡ ce*d
        Self::lemma_eqv_symmetric(ce.mul_spec(d), cd.mul_spec(e));
        Self::lemma_eqv_transitive(de.mul_spec(c), cd.mul_spec(e), ce.mul_spec(d));

        //  bf*c ≡ af*d: both ≡ ?
        //  Actually we need: bf*c ≡ ? and af*d ≡ ?
        //  Let me check what we need:
        //  (de*c - bf*c) + (af*d - ce*d) ≡ det*f = (ad-bc)*f
        //  de*c ≡ ce*d (shown above), so these cancel:
        //  ≡ af*d - bf*c
        //  af*d: (a*f)*d ≡ a*(f*d) = a*(d*f) ≡ (a*d)*f = ad*f
        Self::lemma_mul_associative(a, f, d);
        Self::lemma_mul_commutative(f, d);
        Self::lemma_mul_associative(a, d, f);
        Self::lemma_eqv_symmetric(ad.mul_spec(f), a.mul_spec(d.mul_spec(f)));
        Self::lemma_eqv_transitive(
            af.mul_spec(d), a.mul_spec(f.mul_spec(d)), a.mul_spec(d.mul_spec(f)),
        );
        Self::lemma_eqv_transitive(af.mul_spec(d), a.mul_spec(d.mul_spec(f)), ad.mul_spec(f));

        //  bf*c: (b*f)*c ≡ b*(f*c) = b*(c*f) ≡ (b*c)*f = bc*f
        Self::lemma_mul_associative(b, f, c);
        Self::lemma_mul_commutative(f, c);
        Self::lemma_mul_associative(b, c, f);
        Self::lemma_eqv_symmetric(bc_.mul_spec(f), b.mul_spec(c.mul_spec(f)));
        Self::lemma_eqv_transitive(
            bf.mul_spec(c), b.mul_spec(f.mul_spec(c)), b.mul_spec(c.mul_spec(f)),
        );
        Self::lemma_eqv_transitive(bf.mul_spec(c), b.mul_spec(c.mul_spec(f)), bc_.mul_spec(f));

        //  (de*c - bf*c) ≡ (ce*d - bc*f)... wait, de*c ≡ ce*d
        Self::lemma_eqv_sub_congruence(de.mul_spec(c), ce.mul_spec(d), bf.mul_spec(c), bf.mul_spec(c));
        Self::lemma_eqv_reflexive(bf.mul_spec(c));
        //  (af*d - ce*d) ≡ (ad*f - ce*d)... wait
        Self::lemma_eqv_reflexive(ce.mul_spec(d));
        Self::lemma_eqv_sub_congruence(af.mul_spec(d), ad.mul_spec(f), ce.mul_spec(d), ce.mul_spec(d));

        //  (de*c - bf*c) + (af*d - ce*d) ≡ (ce*d - bf*c) + (ad*f - ce*d)
        Self::lemma_eqv_add_congruence(
            de.mul_spec(c).sub_spec(bf.mul_spec(c)),
            ce.mul_spec(d).sub_spec(bf.mul_spec(c)),
            af.mul_spec(d).sub_spec(ce.mul_spec(d)),
            ad.mul_spec(f).sub_spec(ce.mul_spec(d)),
        );

        //  (ce*d - bf*c) + (ad*f - ce*d) ≡ ad*f - bf*c  by eqv_sub_chain
        Self::lemma_eqv_sub_chain(ad.mul_spec(f), ce.mul_spec(d), bf.mul_spec(c));
        //  Wait, sub_chain(X, Y, Z) gives (X-Y) + (Y-Z) ≡ X-Z
        //  I need (ce*d - bf*c) + (ad*f - ce*d):
        //  With X=ce*d, Y=bf*c... no that gives (ce*d - bf*c) + (bf*c - ?)
        //  I need X=ad*f, Y=ce*d, Z=bf*c:
        //  (ad*f - ce*d) + (ce*d - bf*c) ≡ ad*f - bf*c
        //  But the order is (ce*d - bf*c) + (ad*f - ce*d), which is reversed.
        //  Use add_commutative:
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

        //  ad*f - bf*c ≡ ad*f - bc*f (since bf*c ≡ bc*f)
        Self::lemma_eqv_reflexive(ad.mul_spec(f));
        Self::lemma_eqv_sub_congruence(
            ad.mul_spec(f), ad.mul_spec(f),
            bf.mul_spec(c), bc_.mul_spec(f),
        );
        //  ad*f - bc*f ≡ (ad - bc)*f = det*f
        Self::lemma_sub_mul_right(ad, bc_, f);
        Self::lemma_eqv_symmetric(ad.mul_spec(f).sub_spec(bc_.mul_spec(f)), det.mul_spec(f));

        //  Full chain for second eq:
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

        //  det*(cx+dy) ≡ c*num_x + d*num_y ≡ det*f
        Self::lemma_eqv_transitive(
            det.mul_spec(sum2),
            num_x.mul_spec(c).add_spec(num_y.mul_spec(d)),
            det.mul_spec(f),
        );
        //  Cancel det
        Self::lemma_mul_cancel_left(sum2, f, det);

        //  Second eq: c*x + d*y ≡ f
        //  (We showed det*(cx+dy) ≡ det*f, cancelled to cx+dy ≡ f)
        Self::lemma_mul_commutative(e, det);
        Self::lemma_div_mul_cancel(e, det);
        Self::lemma_mul_commutative(f, det);
        Self::lemma_div_mul_cancel(f, det);
    }

    ///  Cramer's rule: when det ≢ 0, the solution
    ///  x = (d*e - b*f)/det, y = (a*f - c*e)/det
    ///  satisfies a*x + b*y ≡ e and c*x + d*y ≡ f.
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
        Self::lemma_cramer2_eq1(a, b, c, d, e, f);
        Self::lemma_cramer2_eq2(a, b, c, d, e, f);
    }

}

} //  verus!
