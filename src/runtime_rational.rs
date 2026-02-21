#[cfg(verus_keep_ghost)]
use crate::rational::RationalModel;
#[cfg(verus_keep_ghost)]
use vstd::arithmetic::mul::{lemma_mul_basics, lemma_mul_strict_inequality};
#[cfg(verus_keep_ghost)]
use vstd::prelude::*;
#[cfg(verus_keep_ghost)]
use vstd::view::View;

use verus_bigint::{RuntimeBigIntWitness, RuntimeBigNatWitness};

/// Runtime rational number backed by `RuntimeBigIntWitness` (numerator) and
/// `RuntimeBigNatWitness` (denominator).
///
/// The proof model remains in `RationalModel`.
#[cfg(not(verus_keep_ghost))]
compile_error!(
    "verus-rational exposes a single verified implementation; \
     build with Verus (`cfg(verus_keep_ghost)`, e.g. `cargo verus verify`)"
);

#[cfg(not(verus_keep_ghost))]
pub struct RuntimeRational;

#[cfg(verus_keep_ghost)]
verus! {

pub struct RuntimeRational {
    pub numerator: RuntimeBigIntWitness,
    pub denominator: RuntimeBigNatWitness,
    pub model: Ghost<RationalModel>,
}

impl RuntimeRational {
    /// Well-formedness predicate: the runtime witnesses are consistent with
    /// the ghost model.
    ///
    /// The key invariant is:
    ///   numerator.model@ * model@.denom() == model@.num * (denominator.model@ as int)
    ///
    /// This relates the witness numerator/denominator to the model's num/den
    /// through cross-multiplication, allowing them to differ by a common factor.
    pub open spec fn wf_spec(&self) -> bool {
        &&& self.numerator.wf_spec()
        &&& self.denominator.wf_spec()
        &&& self.denominator.model@ > 0
        &&& self.numerator.model@ * self@.denom()
                == self@.num * (self.denominator.model@ as int)
    }

    proof fn lemma_nat_product_positive(a: nat, b: nat)
        requires
            a > 0,
            b > 0,
        ensures
            a * b > 0,
    {
        assert(0 < a as int);
        assert(0 < b as int);
        lemma_mul_strict_inequality(0, a as int, b as int);
        lemma_mul_basics(b as int);
        assert(0 * (b as int) == 0);
        assert(0 < (a as int) * (b as int));
        assert((a * b) as int == (a as int) * (b as int)) by (nonlinear_arith);
        assert((a * b) as int > 0);
        assert(a * b > 0);
    }

    /// Construct a rational from an i64 integer value.
    pub fn from_int(value: i64) -> (out: Self)
        ensures
            out@ == RationalModel::from_int_spec(value as int),
            out.wf_spec(),
    {
        let numerator = RuntimeBigIntWitness::from_i64(value);
        let denominator = RuntimeBigNatWitness::from_u32(1);
        let out = RuntimeRational {
            numerator,
            denominator,
            model: Ghost(RationalModel::from_int_spec(value as int)),
        };
        proof {
            assert(out@ == RationalModel::from_int_spec(value as int));
            assert(out.numerator.model@ == value as int);
            assert(out.denominator.model@ == 1);
            assert(out@.denom() == 1);
            assert(out.denominator.model@ > 0);
            // numerator.model@ * model@.denom() == model@.num * denominator.model@
            // value * 1 == value * 1
            assert(out.numerator.model@ * out@.denom()
                == out@.num * (out.denominator.model@ as int));
            assert(out.wf_spec());
        }
        out
    }

    /// Addition: a/b + c/d = (a*d + c*b) / (b*d)
    pub fn add(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out@ == self@.add_spec(rhs@),
            out.wf_spec(),
    {
        // Convert denominators to BigInt for cross-multiplication
        let rhs_den_int = RuntimeBigIntWitness::from_unsigned(
            rhs.denominator.copy_small_total()
        );
        let self_den_int = RuntimeBigIntWitness::from_unsigned(
            self.denominator.copy_small_total()
        );

        // Cross-multiply: self.num * rhs.den + rhs.num * self.den
        let self_scaled = self.numerator.mul(&rhs_den_int);
        let rhs_scaled = rhs.numerator.mul(&self_den_int);
        let out_num = self_scaled.add(&rhs_scaled);

        // Denominator: self.den * rhs.den
        let out_den = self.denominator.mul_limbwise_small_total(&rhs.denominator);

        let ghost model = self@.add_spec(rhs@);
        let out = RuntimeRational {
            numerator: out_num,
            denominator: out_den,
            model: Ghost(model),
        };
        proof {
            assert(out@ == self@.add_spec(rhs@));

            // wf: numerator and denominator witnesses are well-formed
            assert(out.numerator.wf_spec());
            assert(out.denominator.wf_spec());

            // denominator > 0
            Self::lemma_nat_product_positive(self.denominator.model@, rhs.denominator.model@);
            assert(out.denominator.model@ == self.denominator.model@ * rhs.denominator.model@);
            assert(out.denominator.model@ > 0);

            // Prove the cross-multiplication invariant:
            // out_num.model@ * out@.denom() == out@.num * (out_den.model@ as int)
            let ghost sn = self.numerator.model@;   // self witness num
            let ghost sd = self.denominator.model@;  // self witness den (nat)
            let ghost rn = rhs.numerator.model@;     // rhs witness num
            let ghost rd = rhs.denominator.model@;   // rhs witness den (nat)
            let ghost sa = self@.denom();             // self model denom
            let ghost ra = rhs@.denom();              // rhs model denom
            let ghost n1 = self@.num;                 // self model num
            let ghost n2 = rhs@.num;                  // rhs model num

            // From input wf:
            // sn * sa == n1 * (sd as int)
            // rn * ra == n2 * (rd as int)

            // out numerator witness: sn * (rd as int) + rn * (sd as int)
            assert(out.numerator.model@ == sn * (rd as int) + rn * (sd as int));

            // out denominator witness: sd * rd
            assert(out.denominator.model@ as int == (sd * rd) as int);
            assert((sd * rd) as int == (sd as int) * (rd as int)) by (nonlinear_arith);

            // model denom product
            RationalModel::lemma_add_denom_product_int(self@, rhs@);
            assert(out@.denom() == sa * ra);

            // model numerator
            assert(out@.num == n1 * ra + n2 * sa);

            // Break the cross-multiplication into two parts:
            // Part 1: sn * (rd as int) * (sa * ra) == n1 * ra * (sd as int) * (rd as int)
            assert(
                (sn * (rd as int)) * (sa * ra)
                    == (n1 * ra) * ((sd as int) * (rd as int))
            ) by (nonlinear_arith)
                requires sn * sa == n1 * (sd as int);

            // Part 2: rn * (sd as int) * (sa * ra) == n2 * sa * (sd as int) * (rd as int)
            assert(
                (rn * (sd as int)) * (sa * ra)
                    == (n2 * sa) * ((sd as int) * (rd as int))
            ) by (nonlinear_arith)
                requires rn * ra == n2 * (rd as int);

            // Combine: (A + B) * C == A*C + B*C, then substitute
            assert(
                (sn * (rd as int) + rn * (sd as int)) * (sa * ra)
                    == (sn * (rd as int)) * (sa * ra) + (rn * (sd as int)) * (sa * ra)
            ) by (nonlinear_arith);

            assert(
                (n1 * ra + n2 * sa) * ((sd as int) * (rd as int))
                    == (n1 * ra) * ((sd as int) * (rd as int)) + (n2 * sa) * ((sd as int) * (rd as int))
            ) by (nonlinear_arith);

            assert(out.numerator.model@ * out@.denom()
                == out@.num * (out.denominator.model@ as int));
            assert(out.wf_spec());
        }
        out
    }

    /// Negation: -(a/b) = (-a)/b
    pub fn neg(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out@ == self@.neg_spec(),
            out.wf_spec(),
    {
        let out_num = self.numerator.neg();
        let out_den = self.denominator.copy_small_total();
        let out = RuntimeRational {
            numerator: out_num,
            denominator: out_den,
            model: Ghost(self@.neg_spec()),
        };
        proof {
            assert(out@ == self@.neg_spec());
            assert(out.numerator.wf_spec());
            assert(out.denominator.wf_spec());
            assert(out.denominator.model@ == self.denominator.model@);
            assert(out.denominator.model@ > 0);

            // out.numerator.model@ = -self.numerator.model@
            // out@.denom() = self@.denom()  (neg doesn't change den)
            // out@.num = -self@.num
            assert(out.numerator.model@ == -self.numerator.model@);
            assert(out@.denom() == self@.denom());
            assert(out@.num == -self@.num);

            // Need: out_num.model@ * out@.denom() == out@.num * (out_den.model@ as int)
            // i.e. (-sn) * sa == (-n1) * (sd as int)
            // From sn * sa == n1 * (sd as int), negate both sides
            let ghost sn = self.numerator.model@;
            let ghost sd = self.denominator.model@;
            let ghost sa = self@.denom();
            let ghost n1 = self@.num;
            assert((-sn) * sa == -(sn * sa)) by (nonlinear_arith);
            assert((-n1) * (sd as int) == -(n1 * (sd as int))) by (nonlinear_arith);
            assert(sn * sa == n1 * (sd as int));
            assert((-sn) * sa == (-n1) * (sd as int));
            assert(out.numerator.model@ * out@.denom()
                == out@.num * (out.denominator.model@ as int));
            assert(out.wf_spec());
        }
        out
    }

    /// Subtraction: a/b - c/d = a/b + (-(c/d))
    pub fn sub(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out@ == self@.sub_spec(rhs@),
            out.wf_spec(),
    {
        let neg_rhs = rhs.neg();
        let out = self.add(&neg_rhs);
        proof {
            RationalModel::lemma_sub_is_add_neg(self@, rhs@);
            assert(neg_rhs@ == rhs@.neg_spec());
            assert(out@ == self@.add_spec(neg_rhs@));
            assert(out@ == self@.sub_spec(rhs@));
        }
        out
    }

    /// Multiplication: (a/b) * (c/d) = (a*c) / (b*d)
    pub fn mul(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out@ == self@.mul_spec(rhs@),
            out.wf_spec(),
    {
        let out_num = self.numerator.mul(&rhs.numerator);
        let out_den = self.denominator.mul_limbwise_small_total(&rhs.denominator);

        let ghost model = self@.mul_spec(rhs@);
        let out = RuntimeRational {
            numerator: out_num,
            denominator: out_den,
            model: Ghost(model),
        };
        proof {
            assert(out@ == self@.mul_spec(rhs@));
            assert(out.numerator.wf_spec());
            assert(out.denominator.wf_spec());

            Self::lemma_nat_product_positive(self.denominator.model@, rhs.denominator.model@);
            assert(out.denominator.model@ == self.denominator.model@ * rhs.denominator.model@);
            assert(out.denominator.model@ > 0);

            let ghost sn = self.numerator.model@;
            let ghost sd = self.denominator.model@;
            let ghost rn = rhs.numerator.model@;
            let ghost rd = rhs.denominator.model@;
            let ghost sa = self@.denom();
            let ghost ra = rhs@.denom();
            let ghost n1 = self@.num;
            let ghost n2 = rhs@.num;

            // out.numerator.model@ = sn * rn
            assert(out.numerator.model@ == sn * rn);
            // out.denominator.model@ = sd * rd
            assert((sd * rd) as int == (sd as int) * (rd as int)) by (nonlinear_arith);

            // model
            RationalModel::lemma_mul_denom_product_int(self@, rhs@);
            assert(out@.denom() == sa * ra);
            assert(out@.num == n1 * n2);

            // Need: (sn * rn) * (sa * ra) == (n1 * n2) * ((sd as int) * (rd as int))
            // From sn * sa == n1 * (sd as int) and rn * ra == n2 * (rd as int):
            //   (sn * sa) * (rn * ra) = (n1 * sd) * (n2 * rd)
            //   sn * rn * sa * ra = n1 * n2 * sd * rd
            assert(
                (sn * rn) * (sa * ra) == (n1 * n2) * ((sd as int) * (rd as int))
            ) by (nonlinear_arith)
                requires
                    sn * sa == n1 * (sd as int),
                    rn * ra == n2 * (rd as int),
            ;

            assert(out.numerator.model@ * out@.denom()
                == out@.num * (out.denominator.model@ as int));
            assert(out.wf_spec());
        }
        out
    }

    /// Sign of the rational: 1, -1, or 0.
    pub fn signum(&self) -> (out: i8)
        requires
            self.wf_spec(),
        ensures
            (out == 1i8) == (self@.signum() == 1),
            (out == -1i8) == (self@.signum() == -1),
            (out == 0i8) == (self@.signum() == 0),
    {
        let s = self.numerator.signum();
        proof {
            RationalModel::lemma_denom_positive(self@);
            RationalModel::lemma_signum_positive_iff(self@);
            RationalModel::lemma_signum_negative_iff(self@);
            RationalModel::lemma_signum_zero_iff(self@);

            let ghost sn = self.numerator.model@;
            let ghost sd = self.denominator.model@;
            let ghost sa = self@.denom();
            let ghost n1 = self@.num;

            // From wf: sn * sa == n1 * (sd as int)
            // sa > 0 and sd > 0, so sign(sn) == sign(n1)
            if sn > 0 {
                assert((sn > 0 && sa > 0) ==> sn * sa > 0) by (nonlinear_arith);
                assert(sn * sa > 0);
                assert(n1 * (sd as int) > 0);
                assert(((sd as int) > 0 && n1 * (sd as int) > 0) ==> n1 > 0)
                    by (nonlinear_arith);
                assert(n1 > 0);
            } else if sn < 0 {
                assert((sn < 0 && sa > 0) ==> sn * sa < 0) by (nonlinear_arith);
                assert(sn * sa < 0);
                assert(n1 * (sd as int) < 0);
                assert(((sd as int) > 0 && n1 * (sd as int) < 0) ==> n1 < 0)
                    by (nonlinear_arith);
                assert(n1 < 0);
            } else {
                assert(sn == 0);
                assert((sn == 0) ==> sn * sa == 0) by (nonlinear_arith);
                assert(sn * sa == 0);
                assert(n1 * (sd as int) == 0);
                assert(((sd as int) > 0 && n1 * (sd as int) == 0) ==> n1 == 0)
                    by (nonlinear_arith);
                assert(n1 == 0);
            }
        }
        s
    }

    /// Reciprocal: (a/b) -> (b/a), returns None if zero.
    ///
    /// Note: the returned rational carries the correct ghost model but
    /// does not guarantee `wf_spec()`.  Callers that need wf should
    /// re-establish it (e.g. via a normalizing constructor).
    pub fn recip(&self) -> (out: Option<Self>)
        requires
            self.wf_spec(),
        ensures
            out.is_none() == self@.eqv_spec(RationalModel::from_int_spec(0)),
            match out {
                Option::None => true,
                Option::Some(r) => {
                    &&& !self@.eqv_spec(RationalModel::from_int_spec(0))
                    &&& self@.mul_spec(r@).eqv_spec(RationalModel::from_int_spec(1))
                    &&& r@.mul_spec(self@).eqv_spec(RationalModel::from_int_spec(1))
                },
            },
    {
        let s = self.signum();
        if s == 0i8 {
            proof {
                RationalModel::lemma_signum_zero_iff(self@);
                assert(self@.num == 0);
                RationalModel::lemma_eqv_zero_iff_num_zero(self@);
                assert(self@.eqv_spec(RationalModel::from_int_spec(0)));
            }
            Option::None
        } else {
            // Swap numerator abs and denominator
            let num_abs = self.numerator.abs();
            let new_den = num_abs;
            let new_num = RuntimeBigIntWitness::from_sign_and_magnitude(
                self.numerator.is_negative(),
                self.denominator.copy_small_total(),
            );

            let ghost inv = RationalModel::reciprocal_constructive(self@);
            let out = RuntimeRational {
                numerator: new_num,
                denominator: new_den,
                model: Ghost(inv),
            };
            proof {
                RationalModel::lemma_signum_zero_iff(self@);
                assert(self@.num != 0);
                RationalModel::lemma_eqv_zero_iff_num_zero(self@);
                assert(!self@.eqv_spec(RationalModel::from_int_spec(0)));

                assert(inv == out@);
                assert(self@.mul_spec(inv).eqv_spec(RationalModel::from_int_spec(1)));
                assert(inv.mul_spec(self@).eqv_spec(RationalModel::from_int_spec(1)));
            }
            Option::Some(out)
        }
    }

    /// Comparison: returns -1, 0, or 1.
    /// Compares self and rhs by cross-multiplying: self.num * rhs.denom() vs rhs.num * self.denom()
    pub fn cmp(&self, rhs: &Self) -> (out: i8)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            (out == 0i8) == self@.eqv_spec(rhs@),
            (out == -1i8) == self@.lt_spec(rhs@),
            (out == 1i8) == (!self@.eqv_spec(rhs@) && !self@.lt_spec(rhs@)),
    {
        // Compute self.num * rhs.den and rhs.num * self.den
        let rhs_den_int = RuntimeBigIntWitness::from_unsigned(
            rhs.denominator.copy_small_total()
        );
        let self_den_int = RuntimeBigIntWitness::from_unsigned(
            self.denominator.copy_small_total()
        );

        let lhs_cross = self.numerator.mul(&rhs_den_int);
        let rhs_cross = rhs.numerator.mul(&self_den_int);
        let c = lhs_cross.cmp(&rhs_cross);

        proof {
            let ghost sn = self.numerator.model@;
            let ghost sd = self.denominator.model@;
            let ghost rn = rhs.numerator.model@;
            let ghost rd = rhs.denominator.model@;
            let ghost sa = self@.denom();
            let ghost ra = rhs@.denom();
            let ghost n1 = self@.num;
            let ghost n2 = rhs@.num;

            // lhs_cross.model@ = sn * (rd as int)
            // rhs_cross.model@ = rn * (sd as int)
            assert(lhs_cross.model@ == sn * (rd as int));
            assert(rhs_cross.model@ == rn * (sd as int));

            // From wf: sn * sa == n1 * (sd as int) and rn * ra == n2 * (rd as int)
            // We need to relate sign(sn * rd - rn * sd) to sign(n1 * ra - n2 * sa)
            //
            // sn * rd * sa * ra = n1 * sd * rd * ra  [using sn*sa = n1*sd]
            // rn * sd * sa * ra = n2 * rd * sd * sa  [using rn*ra = n2*rd]
            //
            // (sn * rd - rn * sd) * (sa * ra) = (n1 * ra - n2 * sa) * (sd * rd)
            // Since sa > 0, ra > 0, sd > 0, rd > 0, both (sa*ra) and (sd*rd) are > 0
            // So sign(sn*rd - rn*sd) == sign(n1*ra - n2*sa)

            RationalModel::lemma_denom_positive(self@);
            RationalModel::lemma_denom_positive(rhs@);
            assert(sa > 0);
            assert(ra > 0);

            // Establish positive products
            assert((sa > 0 && ra > 0) ==> sa * ra > 0) by (nonlinear_arith);
            assert(sa * ra > 0);
            let ghost pos_w: int = sa * ra;

            Self::lemma_nat_product_positive(sd, rd);
            assert((sd * rd) as int == (sd as int) * (rd as int)) by (nonlinear_arith);
            assert(((sd as int) * (rd as int)) > 0);
            let ghost pos_m: int = (sd as int) * (rd as int);

            // Break the cross-multiplication into two parts:
            // Part 1: (sn * (rd as int)) * (sa * ra) == (n1 * ra) * ((sd as int) * (rd as int))
            assert(
                (sn * (rd as int)) * (sa * ra) == (n1 * ra) * ((sd as int) * (rd as int))
            ) by (nonlinear_arith)
                requires sn * sa == n1 * (sd as int);

            // Part 2: (rn * (sd as int)) * (sa * ra) == (n2 * sa) * ((sd as int) * (rd as int))
            assert(
                (rn * (sd as int)) * (sa * ra) == (n2 * sa) * ((sd as int) * (rd as int))
            ) by (nonlinear_arith)
                requires rn * ra == n2 * (rd as int);

            // Combine via distributivity: (A - B) * C == A*C - B*C
            let ghost diff_w: int = sn * (rd as int) - rn * (sd as int);
            let ghost diff_m: int = n1 * ra - n2 * sa;

            assert(
                (sn * (rd as int) - rn * (sd as int)) * (sa * ra)
                    == (sn * (rd as int)) * (sa * ra) - (rn * (sd as int)) * (sa * ra)
            ) by (nonlinear_arith);

            assert(
                (n1 * ra - n2 * sa) * ((sd as int) * (rd as int))
                    == (n1 * ra) * ((sd as int) * (rd as int)) - (n2 * sa) * ((sd as int) * (rd as int))
            ) by (nonlinear_arith);

            assert(diff_w * pos_w == diff_m * pos_m);

            assert(self@.eqv_spec(rhs@) == (n1 * ra == n2 * sa));
            assert(self@.lt_spec(rhs@) == (n1 * ra < n2 * sa));

            // Transfer sign from witness domain to model domain
            if diff_w == 0 {
                assert(diff_w * pos_w == 0);
                assert(diff_m * pos_m == 0);
                assert((pos_m > 0 && diff_m * pos_m == 0) ==> diff_m == 0)
                    by (nonlinear_arith);
                assert(diff_m == 0);
            } else if diff_w > 0 {
                assert((diff_w > 0 && pos_w > 0) ==> diff_w * pos_w > 0)
                    by (nonlinear_arith);
                assert(diff_w * pos_w > 0);
                assert(diff_m * pos_m > 0);
                assert((pos_m > 0 && diff_m * pos_m > 0) ==> diff_m > 0)
                    by (nonlinear_arith);
                assert(diff_m > 0);
            } else {
                assert(diff_w < 0);
                assert((diff_w < 0 && pos_w > 0) ==> diff_w * pos_w < 0)
                    by (nonlinear_arith);
                assert(diff_w * pos_w < 0);
                assert(diff_m * pos_m < 0);
                assert((pos_m > 0 && diff_m * pos_m < 0) ==> diff_m < 0)
                    by (nonlinear_arith);
                assert(diff_m < 0);
            }
        }
        c
    }

    /// Check if this rational is zero.
    pub fn is_zero(&self) -> (out: bool)
        requires
            self.wf_spec(),
        ensures
            out == self@.eqv_spec(RationalModel::from_int_spec(0)),
    {
        let z = self.numerator.is_zero();
        proof {
            RationalModel::lemma_signum_zero_iff(self@);
            RationalModel::lemma_eqv_zero_iff_num_zero(self@);

            let ghost sn = self.numerator.model@;
            let ghost sd = self.denominator.model@;
            let ghost sa = self@.denom();
            let ghost n1 = self@.num;

            if sn == 0 {
                assert((sn == 0) ==> sn * sa == 0) by (nonlinear_arith);
                assert(sn * sa == 0);
                assert(n1 * (sd as int) == 0);
                assert(((sd as int) > 0 && n1 * (sd as int) == 0) ==> n1 == 0)
                    by (nonlinear_arith);
                assert(n1 == 0);
            } else {
                assert(sn != 0);
                assert((sn != 0 && sa > 0) ==> sn * sa != 0) by (nonlinear_arith);
                assert(sn * sa != 0);
                assert(n1 * (sd as int) != 0);
                assert(((sd as int) > 0 && n1 * (sd as int) != 0) ==> n1 != 0)
                    by (nonlinear_arith);
                assert(n1 != 0);
            }
        }
        z
    }

    /// Verified semantic equality: true iff the two rationals represent the
    /// same value (cross-multiplication check).
    pub fn eq(&self, rhs: &Self) -> (out: bool)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out == self@.eqv_spec(rhs@),
    {
        let c = self.cmp(rhs);
        c == 0i8
    }

    /// Less-than comparison.
    pub fn lt(&self, rhs: &Self) -> (out: bool)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out == self@.lt_spec(rhs@),
    {
        let c = self.cmp(rhs);
        c == -1i8
    }

    /// Less-than-or-equal comparison.
    pub fn le(&self, rhs: &Self) -> (out: bool)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out == self@.le_spec(rhs@),
    {
        let c = self.cmp(rhs);
        proof {
            // le ↔ lt ∨ eqv
            // self@.le_spec(rhs@) == (self@.num * rhs@.denom() <= rhs@.num * self@.denom())
            // lt: self@.num * rhs@.denom() < rhs@.num * self@.denom()
            // eqv: self@.num * rhs@.denom() == rhs@.num * self@.denom()
            // so le == (lt || eqv) == (c == -1 || c == 0) == (c != 1)
        }
        c != 1i8
    }

    /// Greater-than comparison.
    pub fn gt(&self, rhs: &Self) -> (out: bool)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out == rhs@.lt_spec(self@),
    {
        rhs.lt(self)
    }

    /// Greater-than-or-equal comparison.
    pub fn ge(&self, rhs: &Self) -> (out: bool)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out == rhs@.le_spec(self@),
    {
        rhs.le(self)
    }

    /// Division: (a/b) / (c/d) = (a*d) / (b*c).
    /// Requires the divisor is nonzero.
    ///
    /// Postcondition: `rhs * out` is equivalent to `self`.
    pub fn div(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
            !rhs@.eqv_spec(RationalModel::from_int_spec(0)),
        ensures
            rhs@.mul_spec(out@).eqv_spec(self@),
    {
        // Build reciprocal witnesses directly:
        //   recip_num  = sign(rhs.num) * rhs.den   (BigInt)
        //   recip_den  = |rhs.num|                  (BigNat)
        let rhs_is_neg = rhs.numerator.is_negative();
        let recip_num = RuntimeBigIntWitness::from_sign_and_magnitude(
            rhs_is_neg,
            rhs.denominator.copy_small_total(),
        );
        let recip_den = rhs.numerator.abs();

        // Multiply: out_num = self.num * recip_num, out_den = self.den * recip_den
        let out_num = self.numerator.mul(&recip_num);
        let out_den = self.denominator.mul_limbwise_small_total(&recip_den);

        let ghost inv;
        proof {
            inv = RationalModel::reciprocal_constructive(rhs@);
        }
        let out = RuntimeRational {
            numerator: out_num,
            denominator: out_den,
            model: Ghost(self@.mul_spec(inv)),
        };
        proof {
            // Goal: rhs@ * out@ ≡ self@
            // where out@ = self@ * inv, and rhs@ * inv ≡ 1
            let ghost one = RationalModel::from_int_spec(1);
            assert(rhs@.mul_spec(inv).eqv_spec(one));
            assert(out@ == self@.mul_spec(inv));

            // Step 1: rhs@ * (self@ * inv) == (self@ * inv) * rhs@  [commutativity, structural]
            RationalModel::lemma_mul_commutative(rhs@, self@.mul_spec(inv));
            let ghost lhs = rhs@.mul_spec(self@.mul_spec(inv));
            let ghost mid1 = self@.mul_spec(inv).mul_spec(rhs@);
            assert(lhs == mid1);

            // Step 2: (self@ * inv) * rhs@ ≡ self@ * (inv * rhs@)  [associativity, eqv]
            RationalModel::lemma_mul_associative(self@, inv, rhs@);
            let ghost mid2 = self@.mul_spec(inv.mul_spec(rhs@));
            assert(mid1.eqv_spec(mid2));

            // Step 3: inv * rhs@ == rhs@ * inv  [commutativity, structural]
            RationalModel::lemma_mul_commutative(inv, rhs@);
            assert(inv.mul_spec(rhs@) == rhs@.mul_spec(inv));
            assert(mid2 == self@.mul_spec(rhs@.mul_spec(inv)));

            // Step 4: since rhs@*inv ≡ 1, self@*(rhs@*inv) ≡ self@*1  [congruence]
            RationalModel::lemma_eqv_mul_congruence_right(
                self@,
                rhs@.mul_spec(inv),
                one,
            );
            let ghost mid3 = self@.mul_spec(one);
            assert(self@.mul_spec(rhs@.mul_spec(inv)).eqv_spec(mid3));

            // Step 5: self@ * 1 ≡ self@  [identity]
            RationalModel::lemma_mul_one_identity(self@);
            assert(mid3.eqv_spec(self@));

            // Chain via eqv transitivity:
            // lhs == mid1 ≡ mid2 == self@*(rhs@*inv) ≡ mid3 ≡ self@

            // mid1 ≡ mid2 (from step 2), so lhs ≡ mid2
            RationalModel::lemma_eqv_reflexive(lhs);
            assert(lhs.eqv_spec(mid1));
            RationalModel::lemma_eqv_transitive(lhs, mid1, mid2);
            assert(lhs.eqv_spec(mid2));

            // mid2 == self@*(rhs@*inv) ≡ mid3
            assert(mid2 == self@.mul_spec(rhs@.mul_spec(inv)));
            assert(mid2.eqv_spec(mid3));

            // lhs ≡ mid3
            RationalModel::lemma_eqv_transitive(lhs, mid2, mid3);
            assert(lhs.eqv_spec(mid3));

            // lhs ≡ self@
            RationalModel::lemma_eqv_transitive(lhs, mid3, self@);
            assert(lhs.eqv_spec(self@));

            assert(rhs@.mul_spec(out@).eqv_spec(self@));
        }
        out
    }

    /// Absolute value: |a/b| = |a|/b.
    pub fn abs(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out@ == self@.abs_spec(),
            out.wf_spec(),
    {
        let is_neg = self.numerator.is_negative();
        if is_neg {
            let out = self.neg();
            proof {
                assert(self@.num < 0) by {
                    // is_negative means model@ < 0
                    assert(self.numerator.model@ < 0);
                    // From wf_spec: sn * sa == n1 * (sd as int)
                    let ghost sn = self.numerator.model@;
                    let ghost sd = self.denominator.model@;
                    let ghost sa = self@.denom();
                    let ghost n1 = self@.num;
                    assert(sn * sa == n1 * (sd as int));
                    RationalModel::lemma_denom_positive(self@);
                    assert(sa > 0);
                    assert(sd > 0);
                    assert((sn < 0 && sa > 0) ==> sn * sa < 0) by (nonlinear_arith);
                    assert(sn * sa < 0);
                    assert(n1 * (sd as int) < 0);
                    assert((n1 * (sd as int) < 0 && (sd as int) > 0) ==> n1 < 0)
                        by (nonlinear_arith);
                }
                assert(self@.abs_spec() == self@.neg_spec());
            }
            out
        } else {
            // Non-negative numerator: abs is identity
            let out = RuntimeRational {
                numerator: self.numerator.copy_small_total(),
                denominator: self.denominator.copy_small_total(),
                model: Ghost(self@.abs_spec()),
            };
            proof {
                assert(self.numerator.model@ >= 0) by {
                    assert(!self.numerator.is_negative);
                }
                let ghost sn = self.numerator.model@;
                let ghost sd = self.denominator.model@;
                let ghost sa = self@.denom();
                let ghost n1 = self@.num;
                assert(sn * sa == n1 * (sd as int));
                RationalModel::lemma_denom_positive(self@);
                if n1 < 0 {
                    assert((n1 < 0 && (sd as int) > 0) ==> n1 * (sd as int) < 0)
                        by (nonlinear_arith);
                    assert(sn * sa < 0);
                    assert((sn >= 0 && sa > 0) ==> sn * sa >= 0) by (nonlinear_arith);
                }
                assert(n1 >= 0);
                assert(self@.abs_spec() == self@);
            }
            out
        }
    }

    /// Minimum of two rationals.
    pub fn min(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out@ == self@.min_spec(rhs@),
            out.wf_spec(),
    {
        if self.le(rhs) {
            RuntimeRational {
                numerator: self.numerator.copy_small_total(),
                denominator: self.denominator.copy_small_total(),
                model: Ghost(self@),
            }
        } else {
            RuntimeRational {
                numerator: rhs.numerator.copy_small_total(),
                denominator: rhs.denominator.copy_small_total(),
                model: Ghost(rhs@),
            }
        }
    }

    /// Maximum of two rationals.
    pub fn max(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out@ == self@.max_spec(rhs@),
            out.wf_spec(),
    {
        if self.le(rhs) {
            RuntimeRational {
                numerator: rhs.numerator.copy_small_total(),
                denominator: rhs.denominator.copy_small_total(),
                model: Ghost(rhs@),
            }
        } else {
            RuntimeRational {
                numerator: self.numerator.copy_small_total(),
                denominator: self.denominator.copy_small_total(),
                model: Ghost(self@),
            }
        }
    }

    /// Midpoint: (a + b) / 2.
    pub fn midpoint(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
        ensures
            out@ == RationalModel::midpoint_spec(self@, rhs@),
            out.wf_spec(),
    {
        let sum = self.add(rhs);
        // Multiply by 1/2 = Rational { num: 1, den: 1 }
        // half has numerator = 1 (BigInt), denominator = 2 (BigNat with model = 2)
        let half_num = RuntimeBigIntWitness::from_i64(1);
        let half_den = RuntimeBigNatWitness::from_u32(2);
        let half = RuntimeRational {
            numerator: half_num,
            denominator: half_den,
            model: Ghost(RationalModel { num: 1, den: 1nat }),
        };
        proof {
            // Verify half.wf_spec()
            assert(half.numerator.wf_spec());
            assert(half.denominator.wf_spec());
            assert(half.denominator.model@ == 2);
            assert(half.denominator.model@ > 0);
            assert(half@.num == 1);
            assert(half@.denom() == 2);
            assert(half.numerator.model@ == 1);
            // 1 * 2 == 1 * 2  ✓
            assert(half.numerator.model@ * half@.denom()
                == half@.num * (half.denominator.model@ as int));
        }
        sum.mul(&half)
    }
}

// ── Spec impls for operator traits ──────────────────────────────────────

impl<'a, 'b> vstd::std_specs::ops::AddSpecImpl<&'b RuntimeRational> for &'a RuntimeRational {
    open spec fn obeys_add_spec() -> bool { false }

    open spec fn add_req(self, rhs: &'b RuntimeRational) -> bool {
        self.wf_spec() && rhs.wf_spec()
    }

    open spec fn add_spec(self, rhs: &'b RuntimeRational) -> Self::Output {
        arbitrary()
    }
}

impl<'a, 'b> vstd::std_specs::ops::SubSpecImpl<&'b RuntimeRational> for &'a RuntimeRational {
    open spec fn obeys_sub_spec() -> bool { false }

    open spec fn sub_req(self, rhs: &'b RuntimeRational) -> bool {
        self.wf_spec() && rhs.wf_spec()
    }

    open spec fn sub_spec(self, rhs: &'b RuntimeRational) -> Self::Output {
        arbitrary()
    }
}

impl<'a, 'b> vstd::std_specs::ops::MulSpecImpl<&'b RuntimeRational> for &'a RuntimeRational {
    open spec fn obeys_mul_spec() -> bool { false }

    open spec fn mul_req(self, rhs: &'b RuntimeRational) -> bool {
        self.wf_spec() && rhs.wf_spec()
    }

    open spec fn mul_spec(self, rhs: &'b RuntimeRational) -> Self::Output {
        arbitrary()
    }
}

impl<'a, 'b> vstd::std_specs::ops::DivSpecImpl<&'b RuntimeRational> for &'a RuntimeRational {
    open spec fn obeys_div_spec() -> bool { false }

    open spec fn div_req(self, rhs: &'b RuntimeRational) -> bool {
        self.wf_spec() && rhs.wf_spec()
            && !rhs@.eqv_spec(RationalModel::from_int_spec(0))
    }

    open spec fn div_spec(self, rhs: &'b RuntimeRational) -> Self::Output {
        arbitrary()
    }
}

impl<'a> vstd::std_specs::ops::NegSpecImpl for &'a RuntimeRational {
    open spec fn obeys_neg_spec() -> bool { false }

    open spec fn neg_req(self) -> bool {
        self.wf_spec()
    }

    open spec fn neg_spec(self) -> Self::Output {
        arbitrary()
    }
}

// ── core::ops operator trait impls ──────────────────────────────────────

impl<'a, 'b> core::ops::Add<&'b RuntimeRational> for &'a RuntimeRational {
    type Output = RuntimeRational;

    fn add(self, rhs: &'b RuntimeRational) -> (out: Self::Output) {
        RuntimeRational::add(self, rhs)
    }
}

impl<'a, 'b> core::ops::Sub<&'b RuntimeRational> for &'a RuntimeRational {
    type Output = RuntimeRational;

    fn sub(self, rhs: &'b RuntimeRational) -> (out: Self::Output) {
        RuntimeRational::sub(self, rhs)
    }
}

impl<'a, 'b> core::ops::Mul<&'b RuntimeRational> for &'a RuntimeRational {
    type Output = RuntimeRational;

    fn mul(self, rhs: &'b RuntimeRational) -> (out: Self::Output) {
        RuntimeRational::mul(self, rhs)
    }
}

impl<'a, 'b> core::ops::Div<&'b RuntimeRational> for &'a RuntimeRational {
    type Output = RuntimeRational;

    fn div(self, rhs: &'b RuntimeRational) -> (out: Self::Output) {
        RuntimeRational::div(self, rhs)
    }
}

impl<'a> core::ops::Neg for &'a RuntimeRational {
    type Output = RuntimeRational;

    fn neg(self) -> (out: Self::Output) {
        RuntimeRational::neg(self)
    }
}

impl View for RuntimeRational {
    type V = RationalModel;

    open spec fn view(&self) -> RationalModel {
        self.model@
    }
}

} // verus!
