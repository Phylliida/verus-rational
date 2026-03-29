use super::Rational;
use vstd::prelude::*;

verus! {

impl Rational {
    //  ── Cauchy-Schwarz squared form ─────────────────────────

    pub proof fn lemma_cauchy_schwarz_2d(a: Self, b: Self, c: Self, d: Self)
        ensures
            a.mul_spec(c).add_spec(b.mul_spec(d))
                .mul_spec(a.mul_spec(c).add_spec(b.mul_spec(d)))
                .le_spec(
                    a.mul_spec(a).add_spec(b.mul_spec(b)).mul_spec(
                        c.mul_spec(c).add_spec(d.mul_spec(d)))),
    {
        //  Cauchy-Schwarz: (ac+bd)² ≤ (a²+b²)(c²+d²)
        //  Equivalently: (a²+b²)(c²+d²) - (ac+bd)² ≥ 0
        //  Expansion: a²c² + a²d² + b²c² + b²d² - a²c² - 2abcd - b²d² = a²d² - 2abcd + b²c²
        //  = (ad - bc)² ≥ 0
        //  So this reduces to proving (ad - bc)² ≥ 0, which is lemma_square_le_nonneg.

        let ac = a.mul_spec(c);
        let bd = b.mul_spec(d);
        let dot = ac.add_spec(bd);
        let dot_sq = dot.mul_spec(dot);
        let aa = a.mul_spec(a);
        let bb = b.mul_spec(b);
        let cc = c.mul_spec(c);
        let dd = d.mul_spec(d);
        let norm_a = aa.add_spec(bb);
        let norm_c = cc.add_spec(dd);
        let prod = norm_a.mul_spec(norm_c);

        //  Strategy: reduce to standard Cauchy-Schwarz in 4 ghost variables.
        //  Key observation: dot_sq.denom() == prod.denom() (both = ad²bd²cd²dd²),
        //  so le_spec reduces to dot.num² ≤ norm_a.num * norm_c.num.

        //  Establish denom products
        Self::lemma_mul_denom_product_int(a, c);
        Self::lemma_mul_denom_product_int(b, d);
        Self::lemma_mul_denom_product_int(a, a);
        Self::lemma_mul_denom_product_int(b, b);
        Self::lemma_mul_denom_product_int(c, c);
        Self::lemma_mul_denom_product_int(d, d);
        Self::lemma_add_denom_product_int(ac, bd);
        Self::lemma_add_denom_product_int(aa, bb);
        Self::lemma_add_denom_product_int(cc, dd);
        Self::lemma_mul_denom_product_int(dot, dot);
        Self::lemma_mul_denom_product_int(norm_a, norm_c);
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        Self::lemma_denom_positive(d);

        let ghost an = a.num;
        let ghost bn = b.num;
        let ghost cn = c.num;
        let ghost dn = d.num;
        let ghost ad_ = a.denom();
        let ghost bd_ = b.denom();
        let ghost cd_ = c.denom();
        let ghost dd_ = d.denom();

        //  Ghost variables for the Cauchy-Schwarz reduction
        let ghost x1 = an * bd_;
        let ghost x2 = bn * ad_;
        let ghost y1 = cn * dd_;
        let ghost y2 = dn * cd_;

        //  dot.num = x1*y1 + x2*y2 (break into two product identities)
        let ghost p1 = (an * cn) * (bd_ * dd_);
        let ghost p2 = (bn * dn) * (ad_ * cd_);
        assert(p1 == x1 * y1) by (nonlinear_arith)
            requires p1 == (an * cn) * (bd_ * dd_),
                x1 == an * bd_, y1 == cn * dd_;
        assert(p2 == x2 * y2) by (nonlinear_arith)
            requires p2 == (bn * dn) * (ad_ * cd_),
                x2 == bn * ad_, y2 == dn * cd_;
        assert(dot.num == x1 * y1 + x2 * y2) by (nonlinear_arith)
            requires
                dot.num == p1 + p2,
                p1 == x1 * y1, p2 == x2 * y2;

        //  norm_a.num = x1² + x2²
        assert(norm_a.num == x1 * x1 + x2 * x2) by (nonlinear_arith)
            requires
                norm_a.num == (an * an) * (bd_ * bd_) + (bn * bn) * (ad_ * ad_),
                x1 == an * bd_, x2 == bn * ad_;

        //  norm_c.num = y1² + y2²
        assert(norm_c.num == y1 * y1 + y2 * y2) by (nonlinear_arith)
            requires
                norm_c.num == (cn * cn) * (dd_ * dd_) + (dn * dn) * (cd_ * cd_),
                y1 == cn * dd_, y2 == dn * cd_;

        //  Cauchy-Schwarz: (x1y1+x2y2)² ≤ (x1²+x2²)(y1²+y2²)
        //  Proof: RHS - LHS = (x1y2 - x2y1)² ≥ 0
        let ghost z = x1 * y2 - x2 * y1;
        assert(z * z >= 0int) by (nonlinear_arith)
            requires z == x1 * y2 - x2 * y1;
        //  Lagrange identity via aij = xi*yj decomposition
        let ghost a11 = x1 * y1;
        let ghost a12 = x1 * y2;
        let ghost a21 = x2 * y1;
        let ghost a22 = x2 * y2;
        //  (x1²+x2²)(y1²+y2²) = a11²+a12²+a21²+a22² via distribution
        let ghost x1sq = x1 * x1;
        let ghost x2sq = x2 * x2;
        //  x1² * nc = a11² + a12²
        assert(x1sq * norm_c.num == a11 * a11 + a12 * a12) by (nonlinear_arith)
            requires
                norm_c.num == y1 * y1 + y2 * y2,
                x1sq == x1 * x1,
                a11 == x1 * y1, a12 == x1 * y2;
        //  x2² * nc = a21² + a22²
        assert(x2sq * norm_c.num == a21 * a21 + a22 * a22) by (nonlinear_arith)
            requires
                norm_c.num == y1 * y1 + y2 * y2,
                x2sq == x2 * x2,
                a21 == x2 * y1, a22 == x2 * y2;
        //  na * nc = (x1²+x2²)*nc = x1²*nc + x2²*nc
        assert(norm_a.num * norm_c.num == a11 * a11 + a12 * a12 + a21 * a21 + a22 * a22)
            by (nonlinear_arith)
            requires
                norm_a.num == x1sq + x2sq,
                x1sq * norm_c.num == a11 * a11 + a12 * a12,
                x2sq * norm_c.num == a21 * a21 + a22 * a22,
                x1sq == x1 * x1, x2sq == x2 * x2;
        //  a11*a22 == a12*a21 (both = x1*x2*y1*y2)
        assert(a11 * a22 == a12 * a21) by (nonlinear_arith)
            requires
                a11 == x1 * y1, a12 == x1 * y2,
                a21 == x2 * y1, a22 == x2 * y2;
        //  dot² + z² = (a11+a22)² + (a12-a21)² = a11²+a12²+a21²+a22² + 2(a11*a22-a12*a21)
        let ghost dot_sq_val = dot.num * dot.num;
        let ghost sum_sq = a11 * a11 + a12 * a12 + a21 * a21 + a22 * a22;
        assert(dot_sq_val + z * z == sum_sq) by (nonlinear_arith)
            requires
                dot.num == a11 + a22,
                z == a12 - a21,
                dot_sq_val == dot.num * dot.num,
                sum_sq == a11 * a11 + a12 * a12 + a21 * a21 + a22 * a22,
                a11 * a22 == a12 * a21;
        assert(dot.num * dot.num <= norm_a.num * norm_c.num) by (nonlinear_arith)
            requires
                dot_sq_val == dot.num * dot.num,
                dot_sq_val + z * z == sum_sq,
                norm_a.num * norm_c.num == sum_sq,
                z * z >= 0int;

        //  Show dot_sq.denom() == prod.denom()
        //  Both equal ad²bd²cd²dd² (just different parenthesization)
        let ghost D1 = ad_ * cd_;
        let ghost D2 = bd_ * dd_;
        let ghost D1sq = D1 * D1;
        let ghost D2sq = D2 * D2;
        assert((D1 * D2) * (D1 * D2) == D1sq * D2sq) by (nonlinear_arith)
            requires D1sq == D1 * D1, D2sq == D2 * D2;
        assert(dot_sq.denom() == D1sq * D2sq) by (nonlinear_arith)
            requires
                dot_sq.denom() == dot.denom() * dot.denom(),
                dot.denom() == D1 * D2,
                D1sq == D1 * D1, D2sq == D2 * D2;

        let ghost na_d = ad_ * ad_ * (bd_ * bd_);
        let ghost nc_d = cd_ * cd_ * (dd_ * dd_);
        assert(prod.denom() == na_d * nc_d) by (nonlinear_arith)
            requires
                prod.denom() == norm_a.denom() * norm_c.denom(),
                norm_a.denom() == (ad_ * ad_) * (bd_ * bd_),
                norm_c.denom() == (cd_ * cd_) * (dd_ * dd_),
                na_d == ad_ * ad_ * (bd_ * bd_),
                nc_d == cd_ * cd_ * (dd_ * dd_);

        assert(D1sq * D2sq == na_d * nc_d) by (nonlinear_arith)
            requires
                D1sq == (ad_ * cd_) * (ad_ * cd_),
                D2sq == (bd_ * dd_) * (bd_ * dd_),
                na_d == ad_ * ad_ * (bd_ * bd_),
                nc_d == cd_ * cd_ * (dd_ * dd_),
                D1 == ad_ * cd_, D2 == bd_ * dd_;

        assert(dot_sq.denom() == prod.denom()) by (nonlinear_arith)
            requires
                dot_sq.denom() == D1sq * D2sq,
                prod.denom() == na_d * nc_d,
                D1sq * D2sq == na_d * nc_d;

        //  prod.denom() > 0
        assert(prod.denom() > 0) by (nonlinear_arith)
            requires
                prod.denom() == na_d * nc_d,
                na_d == ad_ * ad_ * (bd_ * bd_),
                nc_d == cd_ * cd_ * (dd_ * dd_),
                ad_ > 0, bd_ > 0, cd_ > 0, dd_ > 0;

        //  Final: since dot_sq.denom() == prod.denom() and
        //  dot.num² ≤ norm_a.num * norm_c.num,
        //  we get dot_sq.num * prod.denom() ≤ prod.num * dot_sq.denom()
        assert(dot_sq.num * prod.denom() <= prod.num * dot_sq.denom())
            by (nonlinear_arith)
            requires
                dot_sq.num == dot.num * dot.num,
                prod.num == norm_a.num * norm_c.num,
                dot_sq.denom() == prod.denom(),
                dot.num * dot.num <= norm_a.num * norm_c.num,
                prod.denom() > 0;
    }

    ///  Helper: norm.num == v1² + v2² + v3² given rational add/mul structure.
    proof fn lemma_norm_num_sum_squares_3d(
        norm_num: int, ab_num: int, ab_D: int,
        xn: int, yn: int, zn: int,
        dx: int, dy: int, dz: int,
    )
        requires
            norm_num == ab_num * (dz * dz) + (zn * zn) * ab_D,
            ab_num == (xn * xn) * (dy * dy) + (yn * yn) * (dx * dx),
            ab_D == (dx * dx) * (dy * dy),
        ensures
            norm_num == (xn * dy * dz) * (xn * dy * dz)
                + (yn * dx * dz) * (yn * dx * dz)
                + (zn * dx * dy) * (zn * dx * dy),
    {
        let ghost v1 = xn * dy * dz;
        let ghost v2 = yn * dx * dz;
        let ghost v3 = zn * dx * dy;

        let ghost t1 = ((xn * xn) * (dy * dy)) * (dz * dz);
        let ghost t2 = ((yn * yn) * (dx * dx)) * (dz * dz);
        let ghost t3 = (zn * zn) * ((dx * dx) * (dy * dy));
        assert(t1 == v1 * v1) by (nonlinear_arith)
            requires t1 == ((xn * xn) * (dy * dy)) * (dz * dz),
                v1 == xn * dy * dz;
        assert(t2 == v2 * v2) by (nonlinear_arith)
            requires t2 == ((yn * yn) * (dx * dx)) * (dz * dz),
                v2 == yn * dx * dz;
        assert(t3 == v3 * v3) by (nonlinear_arith)
            requires t3 == (zn * zn) * ((dx * dx) * (dy * dy)),
                v3 == zn * dx * dy;

        assert(norm_num == t1 + t2 + t3) by (nonlinear_arith)
            requires
                norm_num == ab_num * (dz * dz) + (zn * zn) * ab_D,
                ab_num == (xn * xn) * (dy * dy) + (yn * yn) * (dx * dx),
                ab_D == (dx * dx) * (dy * dy),
                t1 == ((xn * xn) * (dy * dy)) * (dz * dz),
                t2 == ((yn * yn) * (dx * dx)) * (dz * dz),
                t3 == (zn * zn) * ((dx * dx) * (dy * dy));

        assert(norm_num == v1 * v1 + v2 * v2 + v3 * v3) by (nonlinear_arith)
            requires norm_num == t1 + t2 + t3,
                t1 == v1 * v1, t2 == v2 * v2, t3 == v3 * v3;
    }

    ///  Helper: Lagrange identity — dot² + z1² + z2² + z3² = sum of all aij².
    proof fn lemma_lagrange_identity_3d(
        a11: int, a12: int, a13: int,
        a21: int, a22: int, a23: int,
        a31: int, a32: int, a33: int,
        dot_num: int,
    )
        requires
            dot_num == a11 + a22 + a33,
            a11 * a22 == a12 * a21,
            a11 * a33 == a13 * a31,
            a22 * a33 == a23 * a32,
        ensures
            dot_num * dot_num + (a12 - a21)*(a12 - a21)
                + (a13 - a31)*(a13 - a31) + (a23 - a32)*(a23 - a32)
                == a11*a11 + a12*a12 + a13*a13
                    + a21*a21 + a22*a22 + a23*a23
                    + a31*a31 + a32*a32 + a33*a33,
            (a12 - a21)*(a12 - a21) >= 0int,
            (a13 - a31)*(a13 - a31) >= 0int,
            (a23 - a32)*(a23 - a32) >= 0int,
    {
        let ghost z1 = a12 - a21;
        let ghost z2 = a13 - a31;
        let ghost z3 = a23 - a32;
        let ghost dot_sq_val = dot_num * dot_num;

        let ghost diag_sq = a11*a11 + a22*a22 + a33*a33;
        let ghost cross_diag = 2 * (a11*a22 + a11*a33 + a22*a33);
        assert(dot_sq_val == diag_sq + cross_diag) by (nonlinear_arith)
            requires
                dot_num == a11 + a22 + a33,
                dot_sq_val == dot_num * dot_num,
                diag_sq == a11*a11 + a22*a22 + a33*a33,
                cross_diag == 2 * (a11*a22 + a11*a33 + a22*a33);

        let ghost off_diag_sq = a12*a12 + a21*a21 + a13*a13 + a31*a31 + a23*a23 + a32*a32;
        let ghost cross_off = 2 * (a12*a21 + a13*a31 + a23*a32);
        assert(z1*z1 + z2*z2 + z3*z3 == off_diag_sq - cross_off) by (nonlinear_arith)
            requires
                z1 == a12 - a21, z2 == a13 - a31, z3 == a23 - a32,
                off_diag_sq == a12*a12 + a21*a21 + a13*a13 + a31*a31 + a23*a23 + a32*a32,
                cross_off == 2 * (a12*a21 + a13*a31 + a23*a32);

        assert(cross_diag == cross_off) by (nonlinear_arith)
            requires
                cross_diag == 2 * (a11*a22 + a11*a33 + a22*a33),
                cross_off == 2 * (a12*a21 + a13*a31 + a23*a32),
                a11 * a22 == a12 * a21,
                a11 * a33 == a13 * a31,
                a22 * a33 == a23 * a32;

        let ghost sum_sq = a11*a11 + a12*a12 + a13*a13
            + a21*a21 + a22*a22 + a23*a23
            + a31*a31 + a32*a32 + a33*a33;

        assert(dot_sq_val + z1*z1 + z2*z2 + z3*z3 == sum_sq) by (nonlinear_arith)
            requires
                dot_sq_val == diag_sq + cross_diag,
                z1*z1 + z2*z2 + z3*z3 == off_diag_sq - cross_off,
                cross_diag == cross_off,
                sum_sq == a11*a11 + a12*a12 + a13*a13
                    + a21*a21 + a22*a22 + a23*a23
                    + a31*a31 + a32*a32 + a33*a33,
                diag_sq == a11*a11 + a22*a22 + a33*a33,
                off_diag_sq == a12*a12 + a21*a21 + a13*a13 + a31*a31 + a23*a23 + a32*a32;

        assert(z1*z1 >= 0int) by (nonlinear_arith);
        assert(z2*z2 >= 0int) by (nonlinear_arith);
        assert(z3*z3 >= 0int) by (nonlinear_arith);
    }

    ///  Integer Cauchy-Schwarz: (x1y1+x2y2+x3y3)² ≤ (x1²+x2²+x3²)(y1²+y2²+y3²).
    proof fn lemma_cauchy_schwarz_int_3d(
        norm_l_num: int, norm_r_num: int, dot_num: int,
        x1: int, x2: int, x3: int,
        y1: int, y2: int, y3: int,
    )
        requires
            norm_l_num == x1*x1 + x2*x2 + x3*x3,
            norm_r_num == y1*y1 + y2*y2 + y3*y3,
            dot_num == x1*y1 + x2*y2 + x3*y3,
        ensures
            dot_num * dot_num <= norm_l_num * norm_r_num,
    {
        let ghost a11 = x1 * y1;
        let ghost a12 = x1 * y2;
        let ghost a13 = x1 * y3;
        let ghost a21 = x2 * y1;
        let ghost a22 = x2 * y2;
        let ghost a23 = x2 * y3;
        let ghost a31 = x3 * y1;
        let ghost a32 = x3 * y2;
        let ghost a33 = x3 * y3;

        let ghost x1sq = x1 * x1;
        let ghost x2sq = x2 * x2;
        let ghost x3sq = x3 * x3;
        let ghost y1sq = y1 * y1;
        let ghost y2sq = y2 * y2;
        let ghost y3sq = y3 * y3;

        //  Distribution: decompose xi² * yj² = aij² first, then combine
        assert(x1sq * y1sq == a11*a11) by (nonlinear_arith)
            requires x1sq == x1*x1, y1sq == y1*y1, a11 == x1*y1;
        assert(x1sq * y2sq == a12*a12) by (nonlinear_arith)
            requires x1sq == x1*x1, y2sq == y2*y2, a12 == x1*y2;
        assert(x1sq * y3sq == a13*a13) by (nonlinear_arith)
            requires x1sq == x1*x1, y3sq == y3*y3, a13 == x1*y3;
        assert(x1sq * norm_r_num == a11*a11 + a12*a12 + a13*a13)
            by (nonlinear_arith)
            requires norm_r_num == y1sq + y2sq + y3sq,
                x1sq * y1sq == a11*a11, x1sq * y2sq == a12*a12,
                x1sq * y3sq == a13*a13;

        assert(x2sq * y1sq == a21*a21) by (nonlinear_arith)
            requires x2sq == x2*x2, y1sq == y1*y1, a21 == x2*y1;
        assert(x2sq * y2sq == a22*a22) by (nonlinear_arith)
            requires x2sq == x2*x2, y2sq == y2*y2, a22 == x2*y2;
        assert(x2sq * y3sq == a23*a23) by (nonlinear_arith)
            requires x2sq == x2*x2, y3sq == y3*y3, a23 == x2*y3;
        assert(x2sq * norm_r_num == a21*a21 + a22*a22 + a23*a23)
            by (nonlinear_arith)
            requires norm_r_num == y1sq + y2sq + y3sq,
                x2sq * y1sq == a21*a21, x2sq * y2sq == a22*a22,
                x2sq * y3sq == a23*a23;

        assert(x3sq * y1sq == a31*a31) by (nonlinear_arith)
            requires x3sq == x3*x3, y1sq == y1*y1, a31 == x3*y1;
        assert(x3sq * y2sq == a32*a32) by (nonlinear_arith)
            requires x3sq == x3*x3, y2sq == y2*y2, a32 == x3*y2;
        assert(x3sq * y3sq == a33*a33) by (nonlinear_arith)
            requires x3sq == x3*x3, y3sq == y3*y3, a33 == x3*y3;
        assert(x3sq * norm_r_num == a31*a31 + a32*a32 + a33*a33)
            by (nonlinear_arith)
            requires norm_r_num == y1sq + y2sq + y3sq,
                x3sq * y1sq == a31*a31, x3sq * y2sq == a32*a32,
                x3sq * y3sq == a33*a33;

        let ghost sum_sq = a11*a11 + a12*a12 + a13*a13
            + a21*a21 + a22*a22 + a23*a23
            + a31*a31 + a32*a32 + a33*a33;
        assert(norm_l_num * norm_r_num == sum_sq) by (nonlinear_arith)
            requires
                norm_l_num == x1sq + x2sq + x3sq,
                x1sq * norm_r_num == a11*a11 + a12*a12 + a13*a13,
                x2sq * norm_r_num == a21*a21 + a22*a22 + a23*a23,
                x3sq * norm_r_num == a31*a31 + a32*a32 + a33*a33,
                sum_sq == a11*a11 + a12*a12 + a13*a13
                    + a21*a21 + a22*a22 + a23*a23
                    + a31*a31 + a32*a32 + a33*a33;

        //  Cross equalities
        assert(a11 * a22 == a12 * a21) by (nonlinear_arith)
            requires a11==x1*y1, a22==x2*y2, a12==x1*y2, a21==x2*y1;
        assert(a11 * a33 == a13 * a31) by (nonlinear_arith)
            requires a11==x1*y1, a33==x3*y3, a13==x1*y3, a31==x3*y1;
        assert(a22 * a33 == a23 * a32) by (nonlinear_arith)
            requires a22==x2*y2, a33==x3*y3, a23==x2*y3, a32==x3*y2;

        //  Lagrange identity
        Self::lemma_lagrange_identity_3d(
            a11, a12, a13, a21, a22, a23, a31, a32, a33, dot_num,
        );

        //  Final: dot² ≤ norm_l * norm_r
        assert(dot_num * dot_num <= norm_l_num * norm_r_num) by (nonlinear_arith)
            requires
                dot_num * dot_num + (a12 - a21)*(a12 - a21)
                    + (a13 - a31)*(a13 - a31) + (a23 - a32)*(a23 - a32)
                    == a11*a11 + a12*a12 + a13*a13
                        + a21*a21 + a22*a22 + a23*a23
                        + a31*a31 + a32*a32 + a33*a33,
                norm_l_num * norm_r_num == sum_sq,
                sum_sq == a11*a11 + a12*a12 + a13*a13
                    + a21*a21 + a22*a22 + a23*a23
                    + a31*a31 + a32*a32 + a33*a33,
                (a12 - a21)*(a12 - a21) >= 0int,
                (a13 - a31)*(a13 - a31) >= 0int,
                (a23 - a32)*(a23 - a32) >= 0int;
    }

    ///  Helper: ((da*dd_)*(db*de)*(dc*df))² == (da²*db²*dc²)*(dd_²*de²*df²).
    proof fn lemma_denom_sq_three_factors(
        da: int, db: int, dc: int, dd_: int, de: int, df: int,
    )
        ensures
            ((da * dd_) * (db * de) * (dc * df))
                * ((da * dd_) * (db * de) * (dc * df))
                == ((da * da) * (db * db) * (dc * dc))
                    * ((dd_ * dd_) * (de * de) * (df * df)),
    {
        let ghost g1 = da * dd_;
        let ghost g2 = db * de;
        let ghost g3 = dc * df;
        let ghost D_dot = (da * dd_) * (db * de) * (dc * df);
        let ghost Dsq = D_dot * D_dot;
        let ghost nl_d = (da * da) * (db * db) * (dc * dc);
        let ghost nr_d = (dd_ * dd_) * (de * de) * (df * df);

        assert(D_dot == g1 * g2 * g3) by (nonlinear_arith)
            requires D_dot == (da * dd_) * (db * de) * (dc * df),
                g1 == da * dd_, g2 == db * de, g3 == dc * df;
        let ghost g1s = g1 * g1;
        let ghost g2s = g2 * g2;
        let ghost g3s = g3 * g3;
        let ghost g12 = g1 * g2;
        assert(D_dot == g12 * g3) by (nonlinear_arith)
            requires D_dot == g1 * g2 * g3, g12 == g1 * g2;
        let ghost g12s = g12 * g12;
        assert(Dsq == g12s * g3s) by (nonlinear_arith)
            requires Dsq == D_dot * D_dot, D_dot == g12 * g3,
                g12s == g12 * g12, g3s == g3 * g3;
        assert(g12s == g1s * g2s) by (nonlinear_arith)
            requires g12s == g12 * g12, g12 == g1 * g2,
                g1s == g1 * g1, g2s == g2 * g2;
        assert(Dsq == g1s * g2s * g3s) by (nonlinear_arith)
            requires Dsq == g12s * g3s, g12s == g1s * g2s;

        assert(g1s == da * da * (dd_ * dd_)) by (nonlinear_arith)
            requires g1s == g1 * g1, g1 == da * dd_;
        assert(g2s == db * db * (de * de)) by (nonlinear_arith)
            requires g2s == g2 * g2, g2 == db * de;
        assert(g3s == dc * dc * (df * df)) by (nonlinear_arith)
            requires g3s == g3 * g3, g3 == dc * df;

        let ghost da2 = da * da;
        let ghost db2 = db * db;
        let ghost dc2 = dc * dc;
        let ghost dd2 = dd_ * dd_;
        let ghost de2 = de * de;
        let ghost df2 = df * df;
        let ghost nl_nr = nl_d * nr_d;
        assert(nl_d == da2 * db2 * dc2) by (nonlinear_arith)
            requires nl_d == (da * da) * (db * db) * (dc * dc),
                da2 == da * da, db2 == db * db, dc2 == dc * dc;
        assert(nr_d == dd2 * de2 * df2) by (nonlinear_arith)
            requires nr_d == (dd_ * dd_) * (de * de) * (df * df),
                dd2 == dd_ * dd_, de2 == de * de, df2 == df * df;
        let ghost h12 = g1s * g2s;
        assert(h12 == da2 * dd2 * db2 * de2) by (nonlinear_arith)
            requires h12 == g1s * g2s,
                g1s == da2 * dd2, g2s == db2 * de2;
        let ghost h123 = h12 * g3s;
        assert(h123 == da2 * dd2 * db2 * de2 * dc2 * df2) by (nonlinear_arith)
            requires h123 == h12 * g3s,
                h12 == da2 * dd2 * db2 * de2,
                g3s == dc2 * df2;
        let ghost nl_nr_flat = da2 * db2 * dc2 * dd2 * de2 * df2;
        assert(nl_nr == nl_nr_flat) by (nonlinear_arith)
            requires nl_nr == nl_d * nr_d,
                nl_d == da2 * db2 * dc2,
                nr_d == dd2 * de2 * df2,
                nl_nr_flat == da2 * db2 * dc2 * dd2 * de2 * df2;
        assert(h123 == nl_nr_flat) by (nonlinear_arith)
            requires
                h123 == da2 * dd2 * db2 * de2 * dc2 * df2,
                nl_nr_flat == da2 * db2 * dc2 * dd2 * de2 * df2;
        assert(nl_d * nr_d == g1s * g2s * g3s) by (nonlinear_arith)
            requires nl_nr == nl_nr_flat, h123 == nl_nr_flat,
                h123 == h12 * g3s, h12 == g1s * g2s, nl_nr == nl_d * nr_d;

        assert(Dsq == nl_d * nr_d) by (nonlinear_arith)
            requires Dsq == g1s * g2s * g3s,
                nl_d * nr_d == g1s * g2s * g3s;
    }

    ///  (a*d + b*e + c*f)² ≤ (a² + b² + c²)(d² + e² + f²).
    pub proof fn lemma_cauchy_schwarz_3d(
        a: Self, b: Self, c: Self, d: Self, e: Self, f: Self,
    )
        ensures
            a.mul_spec(d).add_spec(b.mul_spec(e)).add_spec(c.mul_spec(f))
                .mul_spec(
                    a.mul_spec(d).add_spec(b.mul_spec(e)).add_spec(c.mul_spec(f)))
                .le_spec(
                    a.mul_spec(a).add_spec(b.mul_spec(b)).add_spec(c.mul_spec(c))
                        .mul_spec(
                            d.mul_spec(d).add_spec(e.mul_spec(e)).add_spec(f.mul_spec(f)))),
    {
        //  Build the dot product: dot = a*d + b*e + c*f
        let ad_ = a.mul_spec(d);
        let be = b.mul_spec(e);
        let cf = c.mul_spec(f);
        let ad_be = ad_.add_spec(be);
        let dot = ad_be.add_spec(cf);
        let dot_sq = dot.mul_spec(dot);

        //  Build the norms
        let aa = a.mul_spec(a);
        let bb = b.mul_spec(b);
        let cc = c.mul_spec(c);
        let dd = d.mul_spec(d);
        let ee = e.mul_spec(e);
        let ff = f.mul_spec(f);
        let aa_bb = aa.add_spec(bb);
        let norm_l = aa_bb.add_spec(cc);
        let dd_ee = dd.add_spec(ee);
        let norm_r = dd_ee.add_spec(ff);
        let prod = norm_l.mul_spec(norm_r);

        //  Establish denom products
        Self::lemma_mul_denom_product_int(a, d);
        Self::lemma_mul_denom_product_int(b, e);
        Self::lemma_mul_denom_product_int(c, f);
        Self::lemma_add_denom_product_int(ad_, be);
        Self::lemma_add_denom_product_int(ad_be, cf);
        Self::lemma_mul_denom_product_int(a, a);
        Self::lemma_mul_denom_product_int(b, b);
        Self::lemma_mul_denom_product_int(c, c);
        Self::lemma_mul_denom_product_int(d, d);
        Self::lemma_mul_denom_product_int(e, e);
        Self::lemma_mul_denom_product_int(f, f);
        Self::lemma_add_denom_product_int(aa, bb);
        Self::lemma_add_denom_product_int(aa_bb, cc);
        Self::lemma_add_denom_product_int(dd, ee);
        Self::lemma_add_denom_product_int(dd_ee, ff);
        Self::lemma_mul_denom_product_int(dot, dot);
        Self::lemma_mul_denom_product_int(norm_l, norm_r);
        Self::lemma_denom_positive(a);
        Self::lemma_denom_positive(b);
        Self::lemma_denom_positive(c);
        Self::lemma_denom_positive(d);
        Self::lemma_denom_positive(e);
        Self::lemma_denom_positive(f);

        let ghost an = a.num;
        let ghost bn = b.num;
        let ghost cn = c.num;
        let ghost dn = d.num;
        let ghost en_ = e.num;
        let ghost fn_ = f.num;
        let ghost da = a.denom();
        let ghost db = b.denom();
        let ghost dc = c.denom();
        let ghost dd_ = d.denom();
        let ghost de = e.denom();
        let ghost df = f.denom();

        //  Ghost variables for the 3D Cauchy-Schwarz reduction
        let ghost x1 = an * db * dc;
        let ghost x2 = bn * da * dc;
        let ghost x3 = cn * da * db;
        let ghost y1 = dn * de * df;
        let ghost y2 = en_ * dd_ * df;
        let ghost y3 = fn_ * dd_ * de;

        //  ── Show dot.num = x1*y1 + x2*y2 + x3*y3 ──
        let ghost p1 = ((an * dn) * (db * de)) * (dc * df);
        assert(p1 == x1 * y1) by (nonlinear_arith)
            requires p1 == ((an * dn) * (db * de)) * (dc * df),
                x1 == an * db * dc, y1 == dn * de * df;

        let ghost p2 = ((bn * en_) * (da * dd_)) * (dc * df);
        assert(p2 == x2 * y2) by (nonlinear_arith)
            requires p2 == ((bn * en_) * (da * dd_)) * (dc * df),
                x2 == bn * da * dc, y2 == en_ * dd_ * df;

        let ghost p3 = (cn * fn_) * ((da * dd_) * (db * de));
        //  Break into two factors, then recombine
        let ghost inner3 = (da * dd_) * (db * de);
        let ghost inner3a = da * db;
        let ghost inner3b = dd_ * de;
        assert(inner3 == inner3a * inner3b) by (nonlinear_arith)
            requires inner3 == (da * dd_) * (db * de),
                inner3a == da * db, inner3b == dd_ * de;
        assert(p3 == (cn * fn_) * (inner3a * inner3b)) by (nonlinear_arith)
            requires p3 == (cn * fn_) * inner3, inner3 == inner3a * inner3b;
        assert(p3 == (cn * inner3a) * (fn_ * inner3b)) by (nonlinear_arith)
            requires p3 == (cn * fn_) * (inner3a * inner3b),
                inner3a == da * db, inner3b == dd_ * de;
        assert(p3 == x3 * y3) by (nonlinear_arith)
            requires p3 == (cn * inner3a) * (fn_ * inner3b),
                x3 == cn * da * db, y3 == fn_ * dd_ * de,
                inner3a == da * db, inner3b == dd_ * de;

        assert(dot.num == p1 + p2 + p3) by (nonlinear_arith)
            requires
                dot.num == ad_be.num * (dc * df) + (cn * fn_) * ad_be.denom(),
                ad_be.num == (an * dn) * (db * de) + (bn * en_) * (da * dd_),
                ad_be.denom() == (da * dd_) * (db * de),
                p1 == ((an * dn) * (db * de)) * (dc * df),
                p2 == ((bn * en_) * (da * dd_)) * (dc * df),
                p3 == (cn * fn_) * ((da * dd_) * (db * de));

        assert(dot.num == x1 * y1 + x2 * y2 + x3 * y3) by (nonlinear_arith)
            requires dot.num == p1 + p2 + p3,
                p1 == x1 * y1, p2 == x2 * y2, p3 == x3 * y3;

        //  ── norm_l.num = x1² + x2² + x3² ──
        Self::lemma_norm_num_sum_squares_3d(
            norm_l.num, aa_bb.num, aa_bb.denom(),
            an, bn, cn, da, db, dc,
        );

        //  ── norm_r.num = y1² + y2² + y3² ──
        Self::lemma_norm_num_sum_squares_3d(
            norm_r.num, dd_ee.num, dd_ee.denom(),
            dn, en_, fn_, dd_, de, df,
        );

        //  ── Integer Cauchy-Schwarz: dot² ≤ norm_l * norm_r ──
        Self::lemma_cauchy_schwarz_int_3d(
            norm_l.num, norm_r.num, dot.num,
            x1, x2, x3, y1, y2, y3,
        );

        //  ── Show dot_sq.denom() == prod.denom() ──
        //  dot.denom() = (da*dd_)*(db*de)*(dc*df)
        //  dot_sq.denom() = dot.denom()²
        //  prod.denom() = norm_l.denom() * norm_r.denom()
        //               = (da²*db²*dc²) * (dd_²*de²*df²)
        let ghost D_dot = (da * dd_) * (db * de) * (dc * df);
        assert(dot.denom() == D_dot) by (nonlinear_arith)
            requires
                dot.denom() == ad_be.denom() * (dc * df),
                ad_be.denom() == (da * dd_) * (db * de),
                D_dot == (da * dd_) * (db * de) * (dc * df);

        let ghost Dsq = D_dot * D_dot;
        assert(dot_sq.denom() == Dsq) by (nonlinear_arith)
            requires
                dot_sq.denom() == dot.denom() * dot.denom(),
                dot.denom() == D_dot,
                Dsq == D_dot * D_dot;

        let ghost nl_d = (da * da) * (db * db) * (dc * dc);
        assert(norm_l.denom() == nl_d) by (nonlinear_arith)
            requires
                norm_l.denom() == aa_bb.denom() * (dc * dc),
                aa_bb.denom() == (da * da) * (db * db),
                nl_d == (da * da) * (db * db) * (dc * dc);

        let ghost nr_d = (dd_ * dd_) * (de * de) * (df * df);
        assert(norm_r.denom() == nr_d) by (nonlinear_arith)
            requires
                norm_r.denom() == dd_ee.denom() * (df * df),
                dd_ee.denom() == (dd_ * dd_) * (de * de),
                nr_d == (dd_ * dd_) * (de * de) * (df * df);

        assert(prod.denom() == nl_d * nr_d) by (nonlinear_arith)
            requires
                prod.denom() == norm_l.denom() * norm_r.denom(),
                norm_l.denom() == nl_d, norm_r.denom() == nr_d;

        //  Dsq == nl_d * nr_d via helper
        Self::lemma_denom_sq_three_factors(da, db, dc, dd_, de, df);

        assert(dot_sq.denom() == prod.denom()) by (nonlinear_arith)
            requires
                dot_sq.denom() == Dsq,
                prod.denom() == nl_d * nr_d,
                Dsq == D_dot * D_dot,
                D_dot == (da * dd_) * (db * de) * (dc * df),
                ((da * dd_) * (db * de) * (dc * df))
                    * ((da * dd_) * (db * de) * (dc * df))
                    == nl_d * nr_d;

        //  prod.denom() > 0
        assert(prod.denom() > 0) by (nonlinear_arith)
            requires
                prod.denom() == nl_d * nr_d,
                nl_d == (da * da) * (db * db) * (dc * dc),
                nr_d == (dd_ * dd_) * (de * de) * (df * df),
                da > 0, db > 0, dc > 0, dd_ > 0, de > 0, df > 0;

        //  Final: dot_sq.num * prod.denom() ≤ prod.num * dot_sq.denom()
        assert(dot_sq.num * prod.denom() <= prod.num * dot_sq.denom())
            by (nonlinear_arith)
            requires
                dot_sq.num == dot.num * dot.num,
                prod.num == norm_l.num * norm_r.num,
                dot_sq.denom() == prod.denom(),
                dot.num * dot.num <= norm_l.num * norm_r.num,
                prod.denom() > 0;
    }

}

} //  verus!
