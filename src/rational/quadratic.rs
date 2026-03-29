use super::Rational;
use vstd::prelude::*;

verus! {

impl Rational {
    //  ── Quadratic discriminant ────────────────────────────

    pub open spec fn discriminant_spec(a: Self, b: Self, c: Self) -> Self {
        b.mul_spec(b).sub_spec(
            Self::from_int_spec(4).mul_spec(a.mul_spec(c)))
    }

    ///  If t is a rational root of ax²+bx+c, verify it satisfies the equation.
    pub proof fn lemma_quadratic_at_rational_root(a: Self, b: Self, c: Self, t: Self)
        requires
            a.mul_spec(t.mul_spec(t)).add_spec(b.mul_spec(t)).add_spec(c)
                .eqv_spec(Self::from_int_spec(0)),
        ensures
            a.mul_spec(t).mul_spec(t).add_spec(b.mul_spec(t)).add_spec(c)
                .eqv_spec(Self::from_int_spec(0)),
    {
        //  a*(t*t) ≡ (a*t)*t by associativity (backward)
        Self::lemma_mul_associative(a, t, t);
        Self::lemma_eqv_symmetric(
            a.mul_spec(t).mul_spec(t),
            a.mul_spec(t.mul_spec(t)),
        );
        //  Replace a*(t*t) with (a*t)*t in the sum
        Self::lemma_eqv_add_congruence_left(
            a.mul_spec(t.mul_spec(t)),
            a.mul_spec(t).mul_spec(t),
            b.mul_spec(t),
        );
        Self::lemma_eqv_add_congruence_left(
            a.mul_spec(t.mul_spec(t)).add_spec(b.mul_spec(t)),
            a.mul_spec(t).mul_spec(t).add_spec(b.mul_spec(t)),
            c,
        );
        Self::lemma_eqv_transitive(
            a.mul_spec(t).mul_spec(t).add_spec(b.mul_spec(t)).add_spec(c),
            a.mul_spec(t.mul_spec(t)).add_spec(b.mul_spec(t)).add_spec(c),
            Self::from_int_spec(0),
        );
    }

    ///  When disc = 0 and a ≢ 0, the double root -b/(2a) satisfies ax²+bx+c = 0.
    pub proof fn lemma_quadratic_double_root(a: Self, b: Self, c: Self)
        requires
            !a.eqv_spec(Self::from_int_spec(0)),
            Self::discriminant_spec(a, b, c).eqv_spec(Self::from_int_spec(0)),
        ensures ({
            let two_a = Self::from_int_spec(2).mul_spec(a);
            let t = b.neg_spec().div_spec(two_a);
            a.mul_spec(t.mul_spec(t)).add_spec(b.mul_spec(t)).add_spec(c)
                .eqv_spec(Self::from_int_spec(0))
        }),
    {
        let z = Self::from_int_spec(0);
        let two = Self::from_int_spec(2);
        let four = Self::from_int_spec(4);
        let two_a = two.mul_spec(a);
        let nb = b.neg_spec();
        let t = nb.div_spec(two_a);

        Self::lemma_eqv_zero_iff_num_zero(a);
        //  2a ≢ 0 since a ≢ 0
        Self::lemma_eqv_zero_iff_num_zero(two_a);
        Self::lemma_mul_denom_product_int(two, a);
        assert(two.num == 2);
        assert(two.denom() == 1);
        assert(two_a.num == 2 * a.num);
        assert(two_a.num != 0) by (nonlinear_arith)
            requires a.num != 0, two_a.num == 2 * a.num;

        //  Algebraic approach: factor a*t²+b*t = t*(a*t+b), show a*t+b ≡ b/2,
        //  then show (b/2)*t + c ≡ 0 using disc=0.

        //  Step 1: 2a*t ≡ -b (from div_cancel)
        Self::lemma_div_cancel(two_a, nb);
        //  two_a * t ≡ nb

        //  Step 2: Derive 2*(a*t) ≡ -b using associativity
        let at_ = a.mul_spec(t);
        Self::lemma_mul_associative(two, a, t);
        //  (two*a)*t ≡ two*(a*t), i.e., two_a*t ≡ two*at_
        Self::lemma_eqv_symmetric(two.mul_spec(a).mul_spec(t), two.mul_spec(a.mul_spec(t)));
        //  two*at_ ≡ two_a*t
        Self::lemma_eqv_transitive(two.mul_spec(at_), two_a.mul_spec(t), nb);
        //  two*at_ ≡ nb

        //  Step 3: a*t ≡ -b/2 by cancellation
        let recip_two = two.reciprocal_spec();
        let half_nb = nb.div_spec(two);   //  = nb * recip(2) = -b/2
        let half_b = b.div_spec(two);     //  = b * recip(2) = b/2

        Self::lemma_eqv_zero_iff_num_zero(two);
        Self::lemma_div_cancel(two, nb);
        //  two * half_nb ≡ nb
        Self::lemma_eqv_symmetric(two.mul_spec(half_nb), nb);
        //  nb ≡ two * half_nb
        Self::lemma_eqv_transitive(two.mul_spec(at_), nb, two.mul_spec(half_nb));
        //  two*at_ ≡ two*half_nb
        Self::lemma_mul_cancel_left(at_, half_nb, two);
        //  at_ ≡ half_nb, i.e., a*t ≡ -b/2

        //  Step 4: Show half_nb == half_b.neg_spec() (structural)
        Self::lemma_mul_commutative(nb, recip_two);
        Self::lemma_mul_neg_right(recip_two, b);
        Self::lemma_mul_commutative(recip_two, b);
        //  half_nb = nb * recip_two == recip_two * nb == recip_two * b.neg_spec()
        //          == (recip_two * b).neg_spec() == (b * recip_two).neg_spec()
        //          == half_b.neg_spec()
        assert(half_nb == half_b.neg_spec());

        //  Step 5: a*t + b ≡ half_b
        //  First show b ≡ half_b + half_b:
        Self::lemma_div_cancel(two, b);
        //  two * half_b ≡ b
        Self::lemma_double(half_b);
        //  half_b + half_b ≡ two * half_b
        Self::lemma_eqv_transitive(
            half_b.add_spec(half_b), two.mul_spec(half_b), b);
        //  half_b + half_b ≡ b
        Self::lemma_eqv_symmetric(half_b.add_spec(half_b), b);
        //  b ≡ half_b + half_b

        //  at_ + b ≡ half_nb + b (by congruence with at_ ≡ half_nb)
        Self::lemma_eqv_add_congruence_left(at_, half_nb, b);
        //  at_ + b ≡ half_nb + b

        //  half_nb + b ≡ half_nb + (half_b + half_b) (by congruence)
        Self::lemma_eqv_add_congruence_right(half_nb, b, half_b.add_spec(half_b));
        //  half_nb + b ≡ half_nb + (half_b + half_b)

        //  (half_nb + half_b) + half_b ≡ half_nb + (half_b + half_b) (associativity)
        Self::lemma_add_associative(half_nb, half_b, half_b);
        Self::lemma_eqv_symmetric(
            half_nb.add_spec(half_b).add_spec(half_b),
            half_nb.add_spec(half_b.add_spec(half_b)));
        //  half_nb + (half_b + half_b) ≡ (half_nb + half_b) + half_b

        //  half_nb + half_b ≡ 0 (since half_nb == -half_b)
        Self::lemma_add_commutative(half_nb, half_b);
        //  half_nb + half_b ≡ half_b + half_nb
        //  half_nb == half_b.neg_spec(), so half_b + half_nb == half_b + half_b.neg_spec()
        //                               == half_b.sub_spec(half_b)
        Self::lemma_sub_self(half_b);
        //  half_b.sub_spec(half_b) ≡ 0
        //  half_b + half_b.neg_spec() == half_b.sub_spec(half_b) [structural from sub_spec def]
        Self::lemma_eqv_transitive(
            half_nb.add_spec(half_b),
            half_b.add_spec(half_nb),
            Self::from_int_spec(0));
        //  half_nb + half_b ≡ 0

        //  (half_nb + half_b) + half_b ≡ 0 + half_b (congruence)
        Self::lemma_eqv_add_congruence_left(
            half_nb.add_spec(half_b),
            Self::from_int_spec(0),
            half_b);
        //  0 + half_b == half_b (structural from add_zero_identity)
        Self::lemma_add_zero_identity(half_b);

        //  Chain: at_ + b ≡ half_nb + b ≡ half_nb + (half_b + half_b)
        //         ≡ (half_nb + half_b) + half_b ≡ 0 + half_b == half_b
        Self::lemma_eqv_transitive(
            at_.add_spec(b), half_nb.add_spec(b),
            half_nb.add_spec(half_b.add_spec(half_b)));
        Self::lemma_eqv_transitive(
            at_.add_spec(b),
            half_nb.add_spec(half_b.add_spec(half_b)),
            half_nb.add_spec(half_b).add_spec(half_b));
        Self::lemma_eqv_transitive(
            at_.add_spec(b),
            half_nb.add_spec(half_b).add_spec(half_b),
            Self::from_int_spec(0).add_spec(half_b));
        //  at_ + b ≡ 0 + half_b == half_b
        //  So at_ + b ≡ half_b (via eqv with the structural == step)
        Self::lemma_eqv_reflexive(half_b);

        //  Step 6: Factor: a*(t*t) + b*t ≡ (a*t + b) * t
        let tt = t.mul_spec(t);
        let att = a.mul_spec(tt);
        let bt = b.mul_spec(t);
        let att_bt = att.add_spec(bt);
        let at_b = at_.add_spec(b);
        let at_b_t = at_b.mul_spec(t);

        //  (a*t + b)*t ≡ (a*t)*t + b*t  [distributive]
        Self::lemma_eqv_mul_distributive_right(at_, b, t);
        //  at_b * t ≡ at_*t + b*t

        //  (a*t)*t ≡ a*(t*t)  [associativity]
        Self::lemma_mul_associative(a, t, t);
        Self::lemma_eqv_add_congruence_left(
            a.mul_spec(t).mul_spec(t), a.mul_spec(t.mul_spec(t)), bt);
        //  (a*t)*t + bt ≡ a*(t*t) + bt = att + bt = att_bt

        //  at_b_t ≡ at_*t + bt ≡ att_bt
        Self::lemma_eqv_transitive(at_b_t, at_.mul_spec(t).add_spec(bt), att_bt);
        //  att_bt ≡ at_b_t [symmetric]
        Self::lemma_eqv_symmetric(at_b_t, att_bt);

        //  Step 7: att_bt ≡ half_b * t (via congruence)
        let half_b_t = half_b.mul_spec(t);
        //  at_b ≡ half_b (from step 5, eqv chain above)
        //  We need to establish at_b ≡ half_b properly for mul_congruence
        //  at_ + b ≡ z + half_b, and z + half_b == half_b structurally
        //  So at_b.eqv_spec(half_b)
        Self::lemma_eqv_mul_congruence_left(at_b, half_b, t);
        //  at_b_t ≡ half_b_t

        //  att_bt ≡ at_b_t ≡ half_b_t
        Self::lemma_eqv_transitive(att_bt, at_b_t, half_b_t);
        //  att_bt ≡ half_b_t

        //  Step 8: expr = att_bt + c ≡ half_b_t + c
        let expr = att_bt.add_spec(c);
        let result = half_b_t.add_spec(c);
        Self::lemma_eqv_add_congruence_left(att_bt, half_b_t, c);
        //  expr ≡ result

        //  Step 9: Show result ≡ 0 at the numerator level.
        //  half_b.num = b.num, half_b.denom() = 2 * b.denom()
        //  (since from_int(2).reciprocal_spec() = Rational{num:1, den:1},
        //   so half_b = b * Rational{num:1, den:1}, half_b.num = b.num*1,
        //   half_b.denom() = b.denom() * 2)
        Self::lemma_mul_denom_product_int(b, recip_two);
        assert(recip_two.num == 1);
        assert(recip_two.denom() == 2);
        assert(half_b.num == b.num);
        assert(half_b.denom() == b.denom() * 2);

        Self::lemma_mul_denom_product_int(half_b, t);
        Self::lemma_add_denom_product_int(half_b_t, c);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        Self::lemma_denom_positive(t);

        let ghost bn = b.num;
        let ghost bd = b.denom();
        let ghost cn = c.num;
        let ghost cd = c.denom();
        let ghost tn = t.num;
        let ghost td = t.denom();
        let ghost an = a.num;
        let ghost ad = a.denom();

        //  half_b_t.num = half_b.num * t.num = bn * tn
        //  half_b_t.denom() = half_b.denom() * t.denom() = 2*bd * td
        //  result.num = half_b_t.num * c.denom() + c.num * half_b_t.denom()
        //             = bn*tn*cd + cn*2*bd*td
        assert(result.num == bn * tn * cd + cn * (2 * bd) * td) by (nonlinear_arith)
            requires
                result.num == half_b_t.num * cd + cn * half_b_t.denom(),
                half_b_t.num == bn * tn,
                half_b_t.denom() == (bd * 2) * td;

        //  From 2a*t ≡ -b, extract cross-multiplication:
        Self::lemma_mul_denom_product_int(two_a, t);
        assert(2 * an * tn * bd == -(bn * ad * td)) by (nonlinear_arith)
            requires
                two_a.mul_spec(t).num * nb.denom() == nb.num * two_a.mul_spec(t).denom(),
                two_a.mul_spec(t).num == two_a.num * tn,
                two_a.num == 2 * an,
                two_a.mul_spec(t).denom() == two_a.denom() * td,
                two_a.denom() == ad,
                nb.num == -bn,
                nb.denom() == bd;

        //  From disc ≡ 0: b² ≡ 4ac (cross-multiplication)
        let bb = b.mul_spec(b);
        let ac_ = a.mul_spec(c);
        let four_ac = four.mul_spec(ac_);
        Self::lemma_sub_eqv_zero_iff_eqv(bb, four_ac);
        Self::lemma_mul_denom_product_int(b, b);
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_mul_denom_product_int(four, ac_);
        assert(bn * bn * (ad * cd) == 4 * an * cn * (bd * bd)) by (nonlinear_arith)
            requires
                bb.num * four_ac.denom() == four_ac.num * bb.denom(),
                bb.num == bn * bn,
                bb.denom() == bd * bd,
                four_ac.num == four.num * ac_.num,
                four.num == 4,
                ac_.num == an * cn,
                four_ac.denom() == four.denom() * ac_.denom(),
                four.denom() == 1,
                ac_.denom() == ad * cd;

        //  Show result.num == 0 by case split on bn
        //  (bn*tn*cd + 2*cn*bd*td) * (bn*ad) = 0, using both constraints
        if bn == 0 {
            //  From disc: 0 = 4*an*cn*bd², so cn = 0
            assert(cn == 0) by (nonlinear_arith)
                requires bn * bn * (ad * cd) == 4 * an * cn * (bd * bd),
                    bn == 0, an != 0, bd > 0;
            assert(result.num == 0) by (nonlinear_arith)
                requires result.num == bn * tn * cd + cn * (2 * bd) * td,
                    bn == 0, cn == 0;
        } else {
            //  Multiply (bn*tn*cd) by (bn*ad), use (**):
            //  bn*ad*(bn*tn*cd) = bn²*ad*cd*tn
            //  From (*): bn²*ad*cd = 4*an*cn*bd²
            //  So = 4*an*cn*bd²*tn

            //  Multiply (2*cn*bd*td) by (bn*ad), use (**):
            //  bn*ad*(2*cn*bd*td) = 2*cn*bd*(bn*ad*td) = 2*cn*bd*(-2*an*tn*bd)
            //  = -4*an*cn*bd²*tn

            //  Sum = 4*an*cn*bd²*tn - 4*an*cn*bd²*tn = 0
            let ghost P = bn * tn * cd;
            let ghost Q = 2 * cn * bd * td;
            let ghost ba = bn * ad;

            //  P*ba = bn²*ad*tn*cd = (bn²*ad*cd)*tn = 4*an*cn*bd²*tn
            let ghost P_ba = P * ba;
            let ghost disc_factor = bn * bn * ad * cd;
            assert(disc_factor == 4 * an * cn * bd * bd) by (nonlinear_arith)
                requires bn * bn * (ad * cd) == 4 * an * cn * (bd * bd),
                    disc_factor == bn * bn * ad * cd;
            assert(P_ba == disc_factor * tn) by (nonlinear_arith)
                requires P == bn * tn * cd, ba == bn * ad, P_ba == P * ba,
                    disc_factor == bn * bn * ad * cd;
            assert(P_ba == 4 * an * cn * bd * bd * tn) by (nonlinear_arith)
                requires P_ba == disc_factor * tn,
                    disc_factor == 4 * an * cn * bd * bd;

            //  Q*ba = 2*cn*bd*td*bn*ad = 2*cn*bd*(bn*ad*td)
            let ghost Q_ba = Q * ba;
            let ghost bat = bn * ad * td;
            assert(bat == -(2 * an * tn * bd)) by (nonlinear_arith)
                requires 2 * an * tn * bd == -(bn * ad * td), bat == bn * ad * td;
            assert(Q_ba == 2 * cn * bd * bat) by (nonlinear_arith)
                requires Q == 2 * cn * bd * td, ba == bn * ad,
                    Q_ba == Q * ba, bat == bn * ad * td;
            assert(Q_ba == -(4 * an * cn * bd * bd * tn)) by (nonlinear_arith)
                requires Q_ba == 2 * cn * bd * bat,
                    bat == -(2 * an * tn * bd);

            //  (P + Q) * ba = P_ba + Q_ba = 0
            assert(P_ba + Q_ba == 0) by (nonlinear_arith)
                requires P_ba == 4 * an * cn * bd * bd * tn,
                    Q_ba == -(4 * an * cn * bd * bd * tn);
            assert((P + Q) * ba == 0) by (nonlinear_arith)
                requires P_ba + Q_ba == 0, P_ba == P * ba, Q_ba == Q * ba;
            assert(P + Q == 0) by (nonlinear_arith)
                requires (P + Q) * ba == 0, ba == bn * ad, bn != 0, ad > 0;
            //  Bridge: cn*(2*bd)*td == 2*cn*bd*td
            assert(result.num == P + Q) by (nonlinear_arith)
                requires result.num == bn * tn * cd + cn * (2 * bd) * td,
                    P == bn * tn * cd, Q == 2 * cn * bd * td;
            assert(result.num == 0) by (nonlinear_arith)
                requires result.num == P + Q, P + Q == 0;
        }

        Self::lemma_eqv_zero_iff_num_zero(result);
        //  result ≡ 0, and expr ≡ result
        Self::lemma_eqv_transitive(expr, result, Self::from_int_spec(0));
    }

    ///  Helper: completing the square shows w² = (β²-4αγ)·td² where inner=0.
    proof fn lemma_complete_square(
        alpha: int, beta: int, gamma: int, tn: int, td_: int,
    )
        requires
            alpha * tn * tn + beta * tn * td_ + gamma * td_ * td_ == 0,
            td_ > 0,
        ensures ({
            let w = 2 * alpha * tn + beta * td_;
            w * w == (beta * beta - 4 * alpha * gamma) * td_ * td_
        }),
    {
        let ghost inner = alpha * tn * tn + beta * tn * td_ + gamma * td_ * td_;
        let ghost w = 2 * alpha * tn + beta * td_;

        //  w² via FOIL: w = p + q where p = 2αtn, q = βtd
        let ghost w_sq = w * w;
        let ghost p = 2 * alpha * tn;
        let ghost q = beta * td_;
        let ghost pp = p * p;
        let ghost pq = p * q;
        let ghost qq = q * q;
        assert(w_sq == pp + 2 * pq + qq) by (nonlinear_arith)
            requires w == p + q, w_sq == w * w,
                pp == p * p, pq == p * q, qq == q * q;
        let ghost expand1 = 4 * alpha * alpha * tn * tn;
        let ghost expand2 = 4 * alpha * beta * tn * td_;
        let ghost expand3 = beta * beta * td_ * td_;
        assert(pp == expand1) by (nonlinear_arith)
            requires pp == p * p, p == 2 * alpha * tn,
                expand1 == 4 * alpha * alpha * tn * tn;
        assert(2 * pq == expand2) by (nonlinear_arith)
            requires pq == p * q, p == 2 * alpha * tn, q == beta * td_,
                expand2 == 4 * alpha * beta * tn * td_;
        assert(qq == expand3) by (nonlinear_arith)
            requires qq == q * q, q == beta * td_,
                expand3 == beta * beta * td_ * td_;
        assert(w_sq == expand1 + expand2 + expand3) by (nonlinear_arith)
            requires w_sq == pp + 2 * pq + qq,
                pp == expand1, 2 * pq == expand2, qq == expand3;

        //  From inner == 0: 4*alpha*(alpha*tn² + beta*tn*td) = -4*alpha*gamma*td²
        let ghost four_alpha_inner_part = 4 * alpha * (alpha * tn * tn + beta * tn * td_);
        assert(four_alpha_inner_part == -(4 * alpha * gamma * td_ * td_))
            by (nonlinear_arith)
            requires
                inner == 0,
                inner == alpha * tn * tn + beta * tn * td_ + gamma * td_ * td_,
                four_alpha_inner_part == 4 * alpha * (alpha * tn * tn + beta * tn * td_);

        assert(expand1 + expand2 == four_alpha_inner_part) by (nonlinear_arith)
            requires
                expand1 == 4 * alpha * alpha * tn * tn,
                expand2 == 4 * alpha * beta * tn * td_,
                four_alpha_inner_part == 4 * alpha * (alpha * tn * tn + beta * tn * td_);

        assert(w_sq == expand3 - 4 * alpha * gamma * td_ * td_) by (nonlinear_arith)
            requires
                w_sq == expand1 + expand2 + expand3,
                expand1 + expand2 == four_alpha_inner_part,
                four_alpha_inner_part == -(4 * alpha * gamma * td_ * td_);

        assert(w_sq == (beta * beta - 4 * alpha * gamma) * td_ * td_)
            by (nonlinear_arith)
            requires
                w_sq == expand3 - 4 * alpha * gamma * td_ * td_,
                expand3 == beta * beta * td_ * td_;
    }

    ///  Helper: show disc_num * ad_ * cd_ == beta² - 4*alpha*gamma.
    proof fn lemma_disc_num_relation(
        an: int, bn: int, cn: int, ad_: int, bd_: int, cd_: int,
        disc_num: int,
    )
        requires
            disc_num == bn * bn * (ad_ * cd_) + (-(4 * (an * cn))) * (bd_ * bd_),
            ad_ > 0, bd_ > 0, cd_ > 0,
        ensures ({
            let alpha = an * bd_ * cd_;
            let beta = bn * ad_ * cd_;
            let gamma = cn * ad_ * bd_;
            disc_num * ad_ * cd_ == beta * beta - 4 * alpha * gamma
        }),
    {
        let ghost alpha = an * bd_ * cd_;
        let ghost beta = bn * ad_ * cd_;
        let ghost gamma = cn * ad_ * bd_;

        let ghost beta_sq = beta * beta;
        assert(beta_sq == bn * bn * ad_ * ad_ * cd_ * cd_) by (nonlinear_arith)
            requires beta == bn * ad_ * cd_, beta_sq == beta * beta;

        let ghost four_ag = 4 * alpha * gamma;
        assert(four_ag == 4 * an * cn * ad_ * bd_ * bd_ * cd_) by (nonlinear_arith)
            requires alpha == an * bd_ * cd_, gamma == cn * ad_ * bd_,
                four_ag == 4 * alpha * gamma;

        let ghost dn_flat = bn * bn * ad_ * cd_ - 4 * an * cn * bd_ * bd_;
        assert(disc_num == dn_flat) by (nonlinear_arith)
            requires
                disc_num == bn * bn * (ad_ * cd_) + (-(4 * (an * cn))) * (bd_ * bd_),
                dn_flat == bn * bn * ad_ * cd_ - 4 * an * cn * bd_ * bd_;

        let ghost part1 = bn * bn * ad_ * cd_ * ad_ * cd_;
        let ghost part2 = 4 * an * cn * bd_ * bd_ * ad_ * cd_;
        assert(dn_flat * ad_ * cd_ == part1 - part2) by (nonlinear_arith)
            requires dn_flat == bn * bn * ad_ * cd_ - 4 * an * cn * bd_ * bd_,
                part1 == bn * bn * ad_ * cd_ * ad_ * cd_,
                part2 == 4 * an * cn * bd_ * bd_ * ad_ * cd_;
        assert(part1 == beta_sq) by (nonlinear_arith)
            requires
                part1 == bn * bn * ad_ * cd_ * ad_ * cd_,
                beta_sq == bn * bn * ad_ * ad_ * cd_ * cd_;
        assert(part2 == four_ag) by (nonlinear_arith)
            requires
                part2 == 4 * an * cn * bd_ * bd_ * ad_ * cd_,
                four_ag == 4 * an * cn * ad_ * bd_ * bd_ * cd_;
        assert(disc_num * ad_ * cd_ == beta_sq - four_ag) by (nonlinear_arith)
            requires
                disc_num == dn_flat,
                dn_flat * ad_ * cd_ == part1 - part2,
                part1 == beta_sq, part2 == four_ag;
    }

    ///  If a*t²+b*t+c ≡ 0 and a ≢ 0, then discriminant b²-4ac ≥ 0.
    pub proof fn lemma_discriminant_nonneg_square(a: Self, b: Self, c: Self, t: Self)
        requires
            a.mul_spec(t.mul_spec(t)).add_spec(b.mul_spec(t)).add_spec(c)
                .eqv_spec(Self::from_int_spec(0)),
            !a.eqv_spec(Self::from_int_spec(0)),
        ensures
            Self::from_int_spec(0).le_spec(Self::discriminant_spec(a, b, c)),
    {
        let tt = t.mul_spec(t);
        let att = a.mul_spec(tt);
        let bt = b.mul_spec(t);
        let att_bt = att.add_spec(bt);
        let expr = att_bt.add_spec(c);

        //  expr ≡ 0 ↔ expr.num == 0
        Self::lemma_eqv_zero_iff_num_zero(expr);
        //  a ≢ 0 ↔ a.num != 0
        Self::lemma_eqv_zero_iff_num_zero(a);

        //  Structural facts
        Self::lemma_mul_denom_product_int(t, t);
        Self::lemma_mul_denom_product_int(a, tt);
        Self::lemma_mul_denom_product_int(b, t);
        Self::lemma_add_denom_product_int(att, bt);
        Self::lemma_add_denom_product_int(att_bt, c);
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        Self::lemma_denom_positive(t);

        //  Discriminant structural facts
        let bb = b.mul_spec(b);
        let ac_ = a.mul_spec(c);
        let four = Self::from_int_spec(4);
        let four_ac = four.mul_spec(ac_);
        let disc = Self::discriminant_spec(a, b, c);
        Self::lemma_mul_denom_product_int(b, b);
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_mul_denom_product_int(four, ac_);
        Self::lemma_add_denom_product_int(bb, four_ac.neg_spec());
        Self::lemma_denom_positive(bb);
        Self::lemma_denom_positive(four_ac);

        let ghost an = a.num;
        let ghost ad_ = a.denom();
        let ghost bn = b.num;
        let ghost bd_ = b.denom();
        let ghost cn = c.num;
        let ghost cd_ = c.denom();
        let ghost tn = t.num;
        let ghost td_ = t.denom();

        //  disc.num = bn²*ad*cd - 4*an*cn*bd²
        assert(four.num == 4);
        assert(four.denom() == 1);
        assert(disc.num == bn * bn * (ad_ * cd_) + (-(4 * (an * cn))) * (bd_ * bd_));

        let ghost disc_num = bn * bn * (ad_ * cd_) + (-(4 * (an * cn))) * (bd_ * bd_);

        //  Ghost variables for completing the square
        let ghost alpha = an * bd_ * cd_;
        let ghost beta = bn * ad_ * cd_;
        let ghost gamma = cn * ad_ * bd_;

        //  Step 1: Factor expr.num as td * (alpha*tn² + beta*tn*td + gamma*td²)
        let ghost t1 = ((an * (tn * tn)) * (bd_ * td_)) * cd_;
        assert(t1 == alpha * tn * tn * td_) by (nonlinear_arith)
            requires t1 == ((an * (tn * tn)) * (bd_ * td_)) * cd_,
                alpha == an * bd_ * cd_;

        let ghost t2 = ((bn * tn) * (ad_ * (td_ * td_))) * cd_;
        assert(t2 == beta * tn * td_ * td_) by (nonlinear_arith)
            requires t2 == ((bn * tn) * (ad_ * (td_ * td_))) * cd_,
                beta == bn * ad_ * cd_;

        let ghost t3 = cn * ((ad_ * (td_ * td_)) * (bd_ * td_));
        assert(t3 == gamma * td_ * td_ * td_) by (nonlinear_arith)
            requires t3 == cn * ((ad_ * (td_ * td_)) * (bd_ * td_)),
                gamma == cn * ad_ * bd_;

        assert(expr.num == t1 + t2 + t3) by (nonlinear_arith)
            requires
                expr.num == (att_bt.num) * cd_ + cn * att_bt.denom(),
                att_bt.num == (an * (tn * tn)) * (bd_ * td_) + (bn * tn) * (ad_ * (td_ * td_)),
                att_bt.denom() == (ad_ * (td_ * td_)) * (bd_ * td_),
                t1 == ((an * (tn * tn)) * (bd_ * td_)) * cd_,
                t2 == ((bn * tn) * (ad_ * (td_ * td_))) * cd_,
                t3 == cn * ((ad_ * (td_ * td_)) * (bd_ * td_));

        let ghost inner = alpha * tn * tn + beta * tn * td_ + gamma * td_ * td_;
        assert(t1 + t2 + t3 == td_ * inner) by (nonlinear_arith)
            requires
                t1 == alpha * tn * tn * td_,
                t2 == beta * tn * td_ * td_,
                t3 == gamma * td_ * td_ * td_,
                inner == alpha * tn * tn + beta * tn * td_ + gamma * td_ * td_;

        assert(inner == 0) by (nonlinear_arith)
            requires expr.num == 0,
                expr.num == t1 + t2 + t3,
                t1 + t2 + t3 == td_ * inner,
                td_ > 0;

        //  Steps 2-3: completing the square + disc_num relationship (via helpers)
        Self::lemma_complete_square(alpha, beta, gamma, tn, td_);
        Self::lemma_disc_num_relation(an, bn, cn, ad_, bd_, cd_, disc_num);

        //  Step 4: Conclude disc_num ≥ 0
        let ghost w = 2 * alpha * tn + beta * td_;
        let ghost w_sq = w * w;
        assert(w_sq >= 0int) by (nonlinear_arith)
            requires w_sq == w * w;
        assert(disc_num * (ad_ * cd_ * td_ * td_) >= 0) by (nonlinear_arith)
            requires
                w_sq == (beta * beta - 4 * alpha * gamma) * td_ * td_,
                disc_num * ad_ * cd_ == beta * beta - 4 * alpha * gamma,
                w_sq >= 0int;
        assert(disc_num >= 0) by (nonlinear_arith)
            requires
                disc_num * (ad_ * cd_ * td_ * td_) >= 0,
                ad_ > 0, cd_ > 0, td_ > 0;

        //  le_spec: from_int(0).le_spec(disc) ↔ 0 * disc.denom() <= disc.num * 1
        //         ↔ disc.num >= 0
        assert(disc.num == disc_num);
    }

}

} //  verus!
