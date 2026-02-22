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

// ── GCD infrastructure ─────────────────────────────────────────────────

/// Spec-level GCD via Euclidean algorithm on naturals.
pub open spec fn gcd_spec(a: nat, b: nat) -> nat
    decreases b
{
    if b == 0 { a } else { gcd_spec(b, (a % b) as nat) }
}

/// GCD divides both inputs when at least one is positive.
///
/// Ensures:
///   - `gcd_spec(a, b) > 0` when `a > 0 || b > 0`
///   - `gcd_spec(a, b)` divides `a`  (i.e. `a % g == 0`)
///   - `gcd_spec(a, b)` divides `b`  (i.e. `b % g == 0`)
proof fn lemma_gcd_properties(a: nat, b: nat)
    requires
        a > 0 || b > 0,
    ensures
        gcd_spec(a, b) > 0,
        a as int % gcd_spec(a, b) as int == 0,
        b as int % gcd_spec(a, b) as int == 0,
    decreases b
{
    if b == 0 {
        // gcd(a, 0) = a.  a > 0 (since at least one > 0 and b == 0).
        // a % a == 0 and 0 % a == 0.
        assert(gcd_spec(a, b) == a);
        assert(a > 0);
        assert(a as int % a as int == 0) by (nonlinear_arith)
            requires a > 0;
        assert(0int % (a as int) == 0) by (nonlinear_arith)
            requires a > 0;
    } else {
        // gcd(a, b) = gcd(b, a % b).
        // b > 0, so b > 0 || (a%b) > 0, enabling the recursive call.
        let r: nat = (a % b) as nat;
        assert(r == (a % b) as nat);
        assert(r < b) by {
            assert(a as int % (b as int) < b as int)
                by (nonlinear_arith) requires b > 0;
        }

        // Recurse: gcd(b, r) divides b and r.
        lemma_gcd_properties(b, r);
        let g = gcd_spec(b, r);
        assert(gcd_spec(a, b) == g);
        assert(g > 0);
        assert(b as int % g as int == 0);
        assert(r as int % g as int == 0);

        // Need to show: a % g == 0.
        // We have: a = (a/b)*b + r  (Euclidean division).
        // g | b and g | r, so g | a.
        let q: nat = (a / b) as nat;
        assert(a == q * b + r) by {
            assert(a as int == (a as int / b as int) * b as int + a as int % b as int)
                by (nonlinear_arith) requires b > 0;
        }

        // Since g | b: b = kb * g for some kb.
        let kb: int = b as int / g as int;
        assert(b as int == kb * g as int) by {
            assert(b as int == (b as int / g as int) * g as int + b as int % g as int)
                by (nonlinear_arith) requires g > 0;
        }

        // Since g | r: r = kr * g for some kr.
        let kr: int = r as int / g as int;
        assert(r as int == kr * g as int) by {
            assert(r as int == (r as int / g as int) * g as int + r as int % g as int)
                by (nonlinear_arith) requires g > 0;
        }

        // a = q*b + r = q*kb*g + kr*g = (q*kb + kr)*g
        assert(a as int == (q as int * kb + kr) * g as int) by (nonlinear_arith)
            requires
                a == q * b + r,
                b as int == kb * g as int,
                r as int == kr * g as int;

        // Therefore a % g == 0.
        assert(a as int % g as int == 0) by (nonlinear_arith)
            requires
                a as int == (q as int * kb + kr) * g as int,
                g > 0;
    }
}

/// Exec-level GCD on BigNat witnesses using the Euclidean algorithm.
fn gcd_bignat(a: RuntimeBigNatWitness, b: RuntimeBigNatWitness) -> (out: RuntimeBigNatWitness)
    requires
        a.wf_spec(),
        b.wf_spec(),
        a.model@ > 0 || b.model@ > 0,
    ensures
        out.wf_spec(),
        out.model@ == gcd_spec(a.model@, b.model@),
        out.model@ > 0,
    decreases b.model@
{
    let b_is_zero = b.is_zero();
    if b_is_zero {
        proof {
            assert(gcd_spec(a.model@, 0) == a.model@);
        }
        a
    } else {
        let (_, r) = a.div_rem(&b);
        proof {
            // r.model@ == a.model@ % b.model@ and r.model@ < b.model@
            assert(r.model@ == a.model@ % b.model@);
            assert(r.model@ < b.model@);
            // gcd(a, b) = gcd(b, a%b) = gcd(b, r)
            assert(gcd_spec(a.model@, b.model@)
                == gcd_spec(b.model@, (a.model@ % b.model@) as nat));
            assert((a.model@ % b.model@) as nat == r.model@);
        }
        gcd_bignat(b, r)
    }
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

    /// Construct a rational from a numerator/denominator pair.
    /// The sign of the denominator is normalized so the effective
    /// denominator is always positive.
    pub fn from_frac(num: i64, den: i64) -> (out: Self)
        requires
            den != 0i64,
        ensures
            out@ == RationalModel::from_frac_spec(num as int, den as int),
            out.wf_spec(),
    {
        let big_num = RuntimeBigIntWitness::from_i64(num);
        let big_den = RuntimeBigIntWitness::from_i64(den);
        let abs_den = big_den.abs();

        if den > 0 {
            let out = RuntimeRational {
                numerator: big_num,
                denominator: abs_den,
                model: Ghost(RationalModel::from_frac_spec(num as int, den as int)),
            };
            proof {
                // from_frac_spec(num, den) when den > 0:
                //   Rational { num: num, den: (den - 1) as nat }
                // So model.num = num, model.denom() = den
                assert(out@.num == num as int);
                assert(out@.denom() == den as int);

                // Witnesses: numerator.model@ = num, denominator.model@ = |den| = den
                assert(out.numerator.model@ == num as int);
                assert(out.denominator.model@ == RuntimeBigIntWitness::abs_model_spec(den as int));
                assert(den > 0);
                assert(RuntimeBigIntWitness::abs_model_spec(den as int) == (den as int) as nat);
                assert(out.denominator.model@ == den as nat);
                assert(out.denominator.model@ > 0);

                // Cross-multiplication: num * den == num * den
                assert(out.numerator.model@ * out@.denom()
                    == out@.num * (out.denominator.model@ as int));
            }
            out
        } else {
            // den < 0: negate numerator, use |den| as denominator
            let neg_num = big_num.neg();
            let out = RuntimeRational {
                numerator: neg_num,
                denominator: abs_den,
                model: Ghost(RationalModel::from_frac_spec(num as int, den as int)),
            };
            proof {
                // from_frac_spec(num, den) when den < 0:
                //   Rational { num: -num, den: (-den - 1) as nat }
                // So model.num = -num, model.denom() = -den
                assert(den < 0);
                assert(out@.num == -(num as int));
                assert(out@.denom() == -(den as int));

                // Witnesses: numerator.model@ = -num, denominator.model@ = |den| = -den
                assert(out.numerator.model@ == -(num as int));
                assert(RuntimeBigIntWitness::abs_model_spec(den as int) == (-(den as int)) as nat);
                assert(out.denominator.model@ == (-(den as int)) as nat);
                assert((den < 0) ==> (-(den as int)) > 0) by (nonlinear_arith);
                assert(out.denominator.model@ > 0);

                // Cross-multiplication: (-num) * (-den) == (-num) * (-den)
                assert(
                    out.numerator.model@ * out@.denom()
                        == out@.num * (out.denominator.model@ as int)
                ) by (nonlinear_arith)
                    requires
                        out.numerator.model@ == -(num as int),
                        out@.denom() == -(den as int),
                        out@.num == -(num as int),
                        out.denominator.model@ == (-(den as int)) as nat;
            }
            out
        }
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
                    &&& r@ == self@.reciprocal_spec()
                    &&& r.wf_spec()
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
                assert(out@ == self@.reciprocal_spec());
                assert(self@.mul_spec(inv).eqv_spec(RationalModel::from_int_spec(1)));
                assert(inv.mul_spec(self@).eqv_spec(RationalModel::from_int_spec(1)));

                // Prove wf_spec of out.
                RationalModel::lemma_denom_positive(self@);
                RationalModel::lemma_denom_positive(inv);
                let ghost sn = self.numerator.model@;
                let ghost sd = self.denominator.model@;
                let ghost rn = self@.num;
                let ghost rd = self@.denom();
                // sn != 0 (same sign as rn, from cross-mult with positive factors)
                assert(sn != 0) by (nonlinear_arith)
                    requires sn * rd == rn * (sd as int), rn != 0, rd > 0, sd > 0;
                // denominator witness > 0 (abs of nonzero)
                assert(out.denominator.model@ > 0);
                // Determine witness values explicitly.
                // new_num = from_sign_and_magnitude(sn < 0, sd_copy):
                //   model@ = if sn < 0 then -(sd as int) else sd as int
                let ghost nn = out.numerator.model@;
                let ghost nd: nat = out.denominator.model@;
                // new_den = abs(sn): model@ = |sn|
                assert(nd == RuntimeBigIntWitness::abs_model_spec(sn));
                // sn and rn have the same sign (from cross-mult with positive factors).
                // sn and rn have the same sign (cross-mult with positive factors)
                assert(sn > 0 ==> rn > 0) by (nonlinear_arith)
                    requires sn * rd == rn * (sd as int), rd > 0, sd > 0;
                assert(sn < 0 ==> rn < 0) by (nonlinear_arith)
                    requires sn * rd == rn * (sd as int), rd > 0, sd > 0;
                assert(rn > 0 ==> sn > 0) by (nonlinear_arith)
                    requires sn * rd == rn * (sd as int), rd > 0, sd > 0;
                assert(rn < 0 ==> sn < 0) by (nonlinear_arith)
                    requires sn * rd == rn * (sd as int), rd > 0, sd > 0;
                if rn > 0 {
                    // reciprocal_spec positive branch
                    assert(sn > 0);
                    assert(nn == sd as int);
                    assert(nd == sn as nat);
                    let ghost nd_int: int = nd as int;
                    assert(nd_int == sn);  // sn > 0 so (sn as nat) as int == sn
                    assert(inv.num == rd);
                    assert(inv.denom() == rn) by (nonlinear_arith)
                        requires rn > 0, inv.den == (rn as nat - 1) as nat;
                    // nn * inv.denom() = sd * rn
                    // inv.num * nd_int = rd * sn
                    // These are equal because sn * rd == rn * sd
                    assert(nn * inv.denom() == inv.num * nd_int) by (nonlinear_arith)
                        requires sn * rd == rn * (sd as int),
                            nn == sd as int, nd_int == sn,
                            inv.num == rd, inv.denom() == rn;
                } else {
                    assert(rn < 0);
                    assert(sn < 0);
                    // reciprocal_spec negative branch
                    assert(nn == -(sd as int));
                    assert(nd == (-sn) as nat);
                    let ghost nd_int: int = nd as int;
                    assert(nd_int == -sn);  // sn < 0 so ((-sn) as nat) as int == -sn
                    assert(inv.num == -rd);
                    assert(inv.denom() == -rn) by (nonlinear_arith)
                        requires rn < 0, inv.den == ((-rn) as nat - 1) as nat;
                    // nn * inv.denom() = (-sd) * (-rn) = sd * rn
                    // inv.num * nd_int = (-rd) * (-sn) = rd * sn
                    // These are equal because sn * rd == rn * sd
                    assert(nn * inv.denom() == inv.num * nd_int) by (nonlinear_arith)
                        requires sn * rd == rn * (sd as int),
                            nn == -(sd as int), nd_int == -sn,
                            inv.num == -rd, inv.denom() == -rn;
                }
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
    pub fn div(&self, rhs: &Self) -> (out: Self)
        requires
            self.wf_spec(),
            rhs.wf_spec(),
            !rhs@.eqv_spec(RationalModel::from_int_spec(0)),
        ensures
            out@ == self@.div_spec(rhs@),
            out.wf_spec(),
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
            // ── Part A: out@ == self@.div_spec(rhs@) ──
            assert(inv == rhs@.reciprocal_spec());
            assert(out@ == self@.mul_spec(inv));
            assert(out@ == self@.div_spec(rhs@));

            // ── Part B: rhs@ * out@ ≡ self@ ──
            let ghost one = RationalModel::from_int_spec(1);
            assert(rhs@.mul_spec(inv).eqv_spec(one));

            RationalModel::lemma_mul_commutative(rhs@, self@.mul_spec(inv));
            let ghost lhs = rhs@.mul_spec(self@.mul_spec(inv));
            let ghost mid1 = self@.mul_spec(inv).mul_spec(rhs@);
            assert(lhs == mid1);

            RationalModel::lemma_mul_associative(self@, inv, rhs@);
            let ghost mid2 = self@.mul_spec(inv.mul_spec(rhs@));
            assert(mid1.eqv_spec(mid2));

            RationalModel::lemma_mul_commutative(inv, rhs@);
            assert(inv.mul_spec(rhs@) == rhs@.mul_spec(inv));
            assert(mid2 == self@.mul_spec(rhs@.mul_spec(inv)));

            RationalModel::lemma_eqv_mul_congruence_right(
                self@,
                rhs@.mul_spec(inv),
                one,
            );
            let ghost mid3 = self@.mul_spec(one);
            assert(self@.mul_spec(rhs@.mul_spec(inv)).eqv_spec(mid3));

            RationalModel::lemma_mul_one_identity(self@);
            assert(mid3.eqv_spec(self@));

            RationalModel::lemma_eqv_reflexive(lhs);
            RationalModel::lemma_eqv_transitive(lhs, mid1, mid2);
            assert(mid2 == self@.mul_spec(rhs@.mul_spec(inv)));
            assert(mid2.eqv_spec(mid3));
            RationalModel::lemma_eqv_transitive(lhs, mid2, mid3);
            RationalModel::lemma_eqv_transitive(lhs, mid3, self@);
            assert(rhs@.mul_spec(out@).eqv_spec(self@));

            // ── Part C: out.wf_spec() ──
            assert(out.numerator.wf_spec());
            assert(out.denominator.wf_spec());

            let ghost sn = self.numerator.model@;
            let ghost sd = self.denominator.model@;
            let ghost sa = self@.denom();
            let ghost n1 = self@.num;
            let ghost rn_i = rhs.numerator.model@;
            let ghost rd = rhs.denominator.model@;
            let ghost ra = rhs@.denom();
            let ghost n2 = rhs@.num;

            RationalModel::lemma_denom_positive(self@);
            RationalModel::lemma_denom_positive(rhs@);

            // rhs.numerator.model@ != 0 (from !rhs@.eqv_spec(0) and wf)
            RationalModel::lemma_eqv_zero_iff_num_zero(rhs@);
            assert(n2 != 0);
            if rn_i == 0 {
                assert((rn_i == 0) ==> rn_i * ra == 0) by (nonlinear_arith);
                assert(n2 * (rd as int) == 0);
                assert(((rd as int) > 0 && n2 * (rd as int) == 0) ==> n2 == 0)
                    by (nonlinear_arith);
                assert(false);
            }
            assert(rn_i != 0);

            // Denominator > 0: self.den * |rhs.num| > 0
            let ghost abs_rn = RuntimeBigIntWitness::abs_model_spec(rn_i);
            assert(recip_den.model@ == abs_rn);
            // abs_model_spec has a conditional that nonlinear_arith can't unfold.
            // Case split to establish abs_rn > 0.
            if rn_i > 0 {
                assert(abs_rn == rn_i as nat);
            } else {
                assert(rn_i < 0);
                assert(abs_rn == (-rn_i) as nat);
            }
            assert(abs_rn > 0);
            Self::lemma_nat_product_positive(sd, abs_rn);
            assert(out.denominator.model@ == sd * abs_rn);
            assert(out.denominator.model@ > 0);

            // Model denom product for self@ * inv
            RationalModel::lemma_mul_denom_product_int(self@, inv);
            assert(out@.denom() == sa * inv.denom());
            assert(out@.num == n1 * inv.num);

            // Witness values
            let ghost rn_w = recip_num.model@;
            let ghost rd_w = recip_den.model@;

            assert(out.numerator.model@ == sn * rn_w);
            assert((sd * rd_w) as int == (sd as int) * (rd_w as int)) by (nonlinear_arith);

            // Prove: rn_w * inv.denom() == inv.num * (rd_w as int)
            // from rhs.wf: rn_i * ra == n2 * (rd as int), by sign case analysis
            if rn_i > 0 {
                assert(!rhs_is_neg);
                assert(rn_w == rd as int);
                assert(rd_w == rn_i as nat);
                assert((rn_i > 0 && ra > 0) ==> rn_i * ra > 0) by (nonlinear_arith);
                assert(n2 * (rd as int) > 0);
                assert(((rd as int) > 0 && n2 * (rd as int) > 0) ==> n2 > 0)
                    by (nonlinear_arith);
                assert(n2 > 0);
                assert(inv.num == ra);
                assert(inv.denom() == n2);
                assert(rn_w * inv.denom() == inv.num * (rd_w as int)) by (nonlinear_arith)
                    requires rn_i * ra == n2 * (rd as int),
                        rn_w == rd as int,
                        rd_w == rn_i as nat,
                        inv.num == ra,
                        inv.denom() == n2,
                        rn_i > 0;
            } else {
                assert(rn_i < 0);
                assert(rhs_is_neg);
                assert(rn_w == -(rd as int));
                assert(rd_w == (-rn_i) as nat);
                assert((rn_i < 0 && ra > 0) ==> rn_i * ra < 0) by (nonlinear_arith);
                assert(n2 * (rd as int) < 0);
                assert(((rd as int) > 0 && n2 * (rd as int) < 0) ==> n2 < 0)
                    by (nonlinear_arith);
                assert(n2 < 0);
                assert(inv.num == -ra);
                assert(inv.denom() == -n2);
                assert(rn_w * inv.denom() == inv.num * (rd_w as int)) by (nonlinear_arith)
                    requires rn_i * ra == n2 * (rd as int),
                        rn_w == -(rd as int),
                        rd_w == (-rn_i) as nat,
                        inv.num == -ra,
                        inv.denom() == -n2,
                        rn_i < 0;
            }

            // Combine via: sn*sa == n1*(sd as int) and rn_w*inv.denom() == inv.num*(rd_w as int)
            assert(
                (sn * rn_w) * (sa * inv.denom())
                    == (n1 * inv.num) * ((sd as int) * (rd_w as int))
            ) by (nonlinear_arith)
                requires
                    sn * sa == n1 * (sd as int),
                    rn_w * inv.denom() == inv.num * (rd_w as int);

            assert(out.numerator.model@ * out@.denom()
                == out@.num * (out.denominator.model@ as int));
            assert(out.wf_spec());
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

    /// Optional GCD normalization: returns an equivalent rational with
    /// smaller numerator/denominator witnesses.
    ///
    /// This divides both the numerator and denominator witnesses by their
    /// GCD.  Callers can invoke this periodically to keep witness sizes
    /// manageable across chains of arithmetic operations.
    pub fn normalize(&self) -> (out: Self)
        requires
            self.wf_spec(),
        ensures
            out.wf_spec(),
            out@.eqv_spec(self@),
    {
        let abs_num = self.numerator.abs();
        let abs_num_copy = abs_num.copy_small_total();
        let den_copy = self.denominator.copy_small_total();

        // Handle zero numerator: already normalized (den witness = 1 would
        // be ideal, but the current form is valid; skip GCD).
        let num_is_zero = abs_num.is_zero();
        if num_is_zero {
            let out = RuntimeRational {
                numerator: self.numerator.copy_small_total(),
                denominator: self.denominator.copy_small_total(),
                model: Ghost(self@),
            };
            proof {
                RationalModel::lemma_eqv_reflexive(self@);
            }
            return out;
        }

        proof {
            // abs_num_copy > 0  (numerator is nonzero)
            assert(abs_num_copy.model@ > 0) by {
                assert(abs_num.model@
                    == RuntimeBigIntWitness::abs_model_spec(self.numerator.model@));
                assert(abs_num_copy.model@ == abs_num.model@);
                // numerator.model@ != 0 (since is_zero returned false)
                if self.numerator.model@ > 0 {
                    assert(abs_num.model@ == self.numerator.model@ as nat);
                } else {
                    assert(self.numerator.model@ < 0);
                    assert(abs_num.model@ == (-self.numerator.model@) as nat);
                }
            }
        }

        let g = gcd_bignat(abs_num_copy, den_copy);

        // Divide witnesses by GCD.
        let new_abs_num = abs_num.div(&g);
        let new_den = self.denominator.div(&g);

        // Rebuild signed numerator.
        let is_neg = self.numerator.is_negative();
        let new_num = if is_neg {
            RuntimeBigIntWitness::from_unsigned(new_abs_num).neg()
        } else {
            RuntimeBigIntWitness::from_unsigned(new_abs_num)
        };

        // Ghost model: set model to match the new witnesses exactly.
        let ghost g_val = g.model@;
        let ghost new_sn: int = new_num.model@;
        let ghost new_sd: nat = new_den.model@;

        proof {
            // ── Establish g divides |sn| and sd ──
            let abs_sn: nat = RuntimeBigIntWitness::abs_model_spec(self.numerator.model@);
            let sd: nat = self.denominator.model@;
            assert(g_val == gcd_spec(abs_sn, sd)) by {
                assert(abs_num_copy.model@ == abs_sn);
                assert(den_copy.model@ == sd);
            }

            lemma_gcd_properties(abs_sn, sd);
            assert(g_val > 0);
            assert(abs_sn as int % g_val as int == 0);
            assert(sd as int % g_val as int == 0);

            // new_den > 0 (since sd > 0 and g divides sd, sd/g >= 1)
            assert(new_sd == sd / g_val);
            assert(new_sd > 0) by (nonlinear_arith)
                requires sd > 0, g_val > 0, sd as int % g_val as int == 0,
                         new_sd == sd / g_val;
        }

        let ghost new_model = RationalModel {
            num: new_sn,
            den: (new_sd - 1) as nat,
        };

        let out = RuntimeRational {
            numerator: new_num,
            denominator: new_den,
            model: Ghost(new_model),
        };

        proof {
            // ── wf_spec: new_sn * new_model.denom() == new_model.num * (new_sd as int) ──
            // Both sides are new_sn * new_sd since model matches witnesses.
            assert(new_model.denom() == new_sd as int);
            assert(new_model.num == new_sn);
            assert(new_sn * (new_sd as int) == new_sn * (new_sd as int));
            assert(out.wf_spec());

            // ── eqv_spec: self@.num * new_model.denom() == new_model.num * self@.denom() ──
            // From old wf_spec: sn * d == n * sd  (where sn = self.numerator.model@,
            //   sd = self.denominator.model@, n = self@.num, d = self@.denom())
            // We have: sn = new_sn * g  (with sign), sd = new_sd * g
            // So: (new_sn * g) * d == n * (new_sd * g)
            // Cancel g: new_sn * d == n * new_sd
            // Which is: new_model.num * self@.denom() == self@.num * new_model.denom()

            let sn = self.numerator.model@;
            let sd = self.denominator.model@ as int;
            let n = self@.num;
            let d = self@.denom();
            let abs_sn: nat = RuntimeBigIntWitness::abs_model_spec(sn);

            // Show: sn == new_sn * g  and  sd == new_sd * g
            // new_abs_num = |sn| / g, new_den = sd / g
            assert(new_abs_num.model@ == abs_sn / g_val);
            assert(new_den.model@ == self.denominator.model@ / g_val);

            // Sign analysis to establish sn == new_sn * (g_val as int)
            if is_neg {
                assert(sn < 0);
                assert(abs_sn == (-sn) as nat);
                assert(new_num.model@ == -(abs_sn / g_val) as int);
                assert(new_sn == -(abs_sn / g_val) as int);
                // sn == -(abs_sn as int) == -((abs_sn/g)*g + abs_sn%g)
                // Since g | abs_sn: abs_sn%g == 0, so abs_sn == (abs_sn/g)*g
                assert(abs_sn as int == (abs_sn / g_val) as int * g_val as int)
                    by (nonlinear_arith)
                    requires abs_sn as int % g_val as int == 0, g_val > 0;
                assert(sn == new_sn * g_val as int) by (nonlinear_arith)
                    requires
                        sn < 0,
                        abs_sn == (-sn) as nat,
                        abs_sn as int == (abs_sn / g_val) as int * g_val as int,
                        new_sn == -(abs_sn / g_val) as int;
            } else {
                assert(sn >= 0);
                assert(abs_sn == sn as nat);
                assert(new_num.model@ == (abs_sn / g_val) as int);
                assert(new_sn == (abs_sn / g_val) as int);
                assert(abs_sn as int == (abs_sn / g_val) as int * g_val as int)
                    by (nonlinear_arith)
                    requires abs_sn as int % g_val as int == 0, g_val > 0;
                assert(sn == new_sn * g_val as int) by (nonlinear_arith)
                    requires
                        sn >= 0,
                        abs_sn == sn as nat,
                        abs_sn as int == (abs_sn / g_val) as int * g_val as int,
                        new_sn == (abs_sn / g_val) as int;
            }
            assert(sn == new_sn * g_val as int);

            // sd == new_sd * g
            let sd_nat: nat = self.denominator.model@;
            assert(sd_nat as int == (sd_nat / g_val) as int * g_val as int)
                by (nonlinear_arith)
                requires sd_nat as int % g_val as int == 0, g_val > 0;
            assert(new_sd == sd_nat / g_val);
            assert(sd == sd_nat as int);
            assert(sd == (new_sd as int) * g_val as int);

            // Cancel g from the wf cross-multiplication: sn * d == n * sd
            // (new_sn * g) * d == n * (new_sd * g)
            // new_sn * d == n * new_sd  (cancel g > 0)
            RationalModel::lemma_denom_positive(self@);
            assert(new_sn * d == n * (new_sd as int)) by (nonlinear_arith)
                requires
                    sn * d == n * sd,
                    sn == new_sn * g_val as int,
                    sd == (new_sd as int) * g_val as int,
                    g_val > 0;

            assert(n * new_model.denom() == new_model.num * d);
            assert(out@.eqv_spec(self@));
        }
        out
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
