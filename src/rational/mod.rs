use vstd::prelude::*;
use vstd::calc;
use vstd::arithmetic::mul::{
    lemma_mul_basics,
    lemma_mul_by_zero_is_zero,
    lemma_mul_is_associative,
    lemma_mul_is_commutative,
    lemma_mul_strict_inequality,
};

pub mod foundation;
pub mod ring_algebra;
pub mod equivalence;
pub mod signum;
pub mod ordering;
pub mod division;
pub mod applications;

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

    /// Spec-level construction from numerator and denominator.
    /// The sign of the denominator is moved to the numerator so the
    /// effective denominator is always positive.
    pub open spec fn from_frac_spec(num: int, den: int) -> Self
        recommends den != 0,
    {
        if den > 0 {
            Rational { num: num, den: (den - 1) as nat }
        } else {
            Rational { num: -num, den: (-den - 1) as nat }
        }
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

}

/// Alias for backward compatibility with code that used the RationalModel name.
pub type RationalModel = Rational;

} // verus!
