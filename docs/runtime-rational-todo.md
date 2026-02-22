# Runtime rational TODO

Improvements to the exec-level `RuntimeRational` and supporting proof
infrastructure in verus-rational.

## 1. Exec-level `from_frac(num, den)`

- [ ] `RuntimeRational::from_frac(num: i64, den: i64)` — construct a rational
  from an explicit numerator/denominator pair at runtime.
- Precondition: `den != 0`.
- Postcondition: `out@ == Rational { num: num as int, den: (den.unsigned_abs() - 1) as nat }` (or equivalent normalised form), `out.wf_spec()`.
- Currently only `from_int(i64)` exists, so there is no way to construct
  e.g. `1/3` at runtime without manual struct assembly.

## 2. Exec-level GCD normalization

- [ ] `RuntimeRational::normalize(&self) -> Self` — return an equivalent
  rational in lowest terms (GCD-reduced).
- Postcondition: `out@.eqv_spec(self@)`, `out.wf_spec()`,
  `out@.normalized_spec()`.
- Ghost-level `normalize_constructive` already exists; this needs an exec
  implementation using `verus-bigint` GCD.
- Without this, denominators grow exponentially across chains of `+`/`*`/`-`
  operations. A CAD kernel doing hundreds of intersection calculations would
  become unusably slow.

## 3. Fix `div` postcondition to guarantee `wf_spec()`

- [ ] `RuntimeRational::div` currently ensures `rhs@ * out@ ≡ self@` but
  does **not** guarantee `out.wf_spec()`.
- Every caller that needs a well-formed result must add a manual proof step.
- Fix: strengthen the `div` postcondition to also ensure `out.wf_spec()`.

## 4. Generalized polynomial evaluation (Horner's method)

- [ ] `horner_spec(coeffs: Seq<Rational>, x: Rational) -> Rational` — evaluate
  a polynomial `c₀ + c₁x + c₂x² + ... + cₙxⁿ` using Horner's method.
- [ ] `lemma_horner_correct(coeffs, x)` — Horner evaluation equals the
  naive sum of `cᵢ * x^i`.
- [ ] Exec-level `RuntimeRational::horner_eval(coeffs, x)` function.
- Useful for: Bezier curves (cubics), NURBS evaluation, curve-surface
  intersection (higher-degree polynomials).
- Generalizes the existing quadratic-specific `discriminant_spec` /
  `lemma_quadratic_at_rational_root`.

## 5. More power / reciprocal lemmas

- [ ] `lemma_pow_reciprocal(a, n)` — `a ≢ 0 → (a⁻¹)ⁿ ≡ (aⁿ)⁻¹`.
- [ ] `lemma_pow_positive(a, n)` — `a > 0 → aⁿ > 0`.
- [ ] `lemma_pow_nonneg(a, n)` — `a ≥ 0 → aⁿ ≥ 0`.
- [ ] `lemma_pow_monotone(a, b, n)` — `0 ≤ a ≤ b → aⁿ ≤ bⁿ`.
- [ ] `lemma_pow_strict_monotone(a, b, n)` — `0 ≤ a < b ∧ n > 0 → aⁿ < bⁿ`.
- Useful for: polynomial bound proofs, growth estimates, convergence.
