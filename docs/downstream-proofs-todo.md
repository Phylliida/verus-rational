# Downstream proof TODO for verus-rational

Proofs useful for a formally verified 3D CAD program built on exact rational
arithmetic.  Items marked **(vcad-math)** have partial or full precedent in
`VerusCAD/crates/vcad-math/src/scalar.rs` and can be ported/adapted.

## 1. Absolute value  ✅

- `abs_spec(a)` — spec function returning a non-negative rational with the
  same magnitude.
- `lemma_abs_nonneg(a)` — `abs(a).signum() >= 0`.
- `lemma_abs_zero_iff(a)` — `abs(a) ≡ 0 ↔ a ≡ 0`.
- `lemma_abs_neg(a)` — `abs(-a) ≡ abs(a)`.
- `lemma_abs_mul(a, b)` — `abs(a*b) ≡ abs(a)*abs(b)`.
- `lemma_triangle_inequality(a, b)` — `abs(a+b) ≤ abs(a) + abs(b)`.
- Runtime `abs()` exec function.

## 2. Min / max  ✅

- `min_spec(a, b)`, `max_spec(a, b)` — spec functions.
- `lemma_min_le_left/right(a, b)` — `min(a,b) ≤ a` and `min(a,b) ≤ b`.
- `lemma_max_ge_left/right(a, b)` — `max(a,b) ≥ a` and `max(a,b) ≥ b`.
- `lemma_min_max_sum(a, b)` — `min(a,b) + max(a,b) ≡ a + b`.
- `lemma_min_commutative`, `lemma_max_commutative`.
- Runtime `min()`, `max()` exec functions.

Useful for: bounding boxes, clipping, interval arithmetic.

## 3. Sign-preserving multiplication monotonicity  ✅

- `lemma_le_mul_nonneg(a, b, c)` — `a ≤ b ∧ 0 ≤ c → a*c ≤ b*c`.
- `lemma_le_mul_nonneg_both(a, b, c, d)` —
  `0 ≤ a ≤ b ∧ 0 ≤ c ≤ d → a*c ≤ b*d`.
- **(vcad-math)** `lemma_le_mul_monotone_nonnegative` and
  `lemma_le_mul_monotone_nonnegative_strong` are partial precedents.

Useful for: area/volume bound proofs, bounding-box containment.

## 4. Squared operations / non-negativity  ✅

- `lemma_square_nonneg(a)` — `a * a ≥ 0` (i.e. signum ≥ 0).
- `lemma_square_le_nonneg(a)` — `from_int(0) ≤ a*a`.
- `lemma_sum_of_squares_nonneg(a, b)` — `a*a + b*b ≥ 0`.
- `lemma_sum_of_squares_zero_iff(a, b)` — `a*a + b*b ≡ 0 ↔ a ≡ 0 ∧ b ≡ 0`.
- Three-component variant for 3D: `a*a + b*b + c*c ≥ 0`, zero-iff.

Useful for: dot-product sign, distance-squared comparisons (avoids square
roots), proving vectors are nonzero.

## 5. Trichotomy  ✅

- `lemma_trichotomy(a, b)` — exactly one of `a < b`, `a ≡ b`, `b < a` holds.
- `lemma_lt_irreflexive(a)` — `¬(a < a)`.
- `lemma_lt_asymmetric(a, b)` — `a < b → ¬(b < a)`.
- `lemma_lt_transitive(a, b, c)` — `a < b ∧ b < c → a < c`.
- `lemma_le_iff_lt_or_eqv`, `lemma_lt_implies_le`, `lemma_eqv_implies_le`.
- `lemma_le_antisymmetric`, `lemma_le_transitive`.

Useful for: orientation predicates, total ordering in sweep-line algorithms,
geometric sorting.

## 6. Cross-multiplication ordering preservation  ✅

- `lemma_cross_mul_le(a, b)` — `a ≤ b ↔ a.num * b.denom() ≤ b.num * a.denom()`.
- `lemma_cross_mul_lt(a, b)` — strict variant.

## 7. Density / midpoint  ✅

- `midpoint_spec(a, b)` — `(a + b) * (1/2)`.
- `lemma_midpoint_between_left/right(a, b)` — `a < b → a < midpoint(a,b) < b`.
- `lemma_midpoint_eqv_self(a)` — `midpoint(a, a) ≡ a`.
- Runtime `midpoint()` exec function.

Useful for: subdivision algorithms, bisection, adaptive refinement.

## 8. Integer embedding preserves order  ✅

- `lemma_from_int_preserves_lt(m, n)` — `m < n → from_int(m) < from_int(n)`.
- `lemma_from_int_preserves_le(m, n)` — `m ≤ n → from_int(m) ≤ from_int(n)`.
- `lemma_from_int_injective(m, n)` — `from_int(m) ≡ from_int(n) → m == n`.
- `lemma_from_int_add(m, n)` — `from_int(m) + from_int(n) ≡ from_int(m+n)`.
- `lemma_from_int_mul(m, n)` — `from_int(m) * from_int(n) ≡ from_int(m*n)`.
- `lemma_from_int_neg(m)`, `lemma_from_int_sub(m, n)`.

---

## 9. Sign of products (orientation predicates)  ✅

Core of determinant-sign reasoning for orient2d / orient3d.

- `lemma_pos_mul_pos(a, b)` — `a > 0 ∧ b > 0 → a*b > 0`
  (i.e. `from_int(0).lt_spec(a) ∧ from_int(0).lt_spec(b) →
  from_int(0).lt_spec(a.mul_spec(b))`).
- `lemma_neg_mul_neg(a, b)` — `a < 0 ∧ b < 0 → a*b > 0`.
- `lemma_pos_mul_neg(a, b)` — `a > 0 ∧ b < 0 → a*b < 0`.
- `lemma_neg_mul_pos(a, b)` — `a < 0 ∧ b > 0 → a*b < 0`.
- `lemma_zero_mul_sign(a, b)` — `a ≡ 0 ∨ b ≡ 0 → a*b ≡ 0`.
- `lemma_product_sign(a, b)` — comprehensive: classifies sign of `a*b`
  from signs of `a` and `b`.

Useful for: orientation predicates, determinant sign, winding number.

## 10. Strict ordering + arithmetic  ✅

The `≤` versions exist (#3, #5); these are the strict `<` counterparts
needed for orientation-predicate strictness.

- `lemma_lt_add_monotone(a, b, c)` — `a < b → a + c < b + c`.
- `lemma_lt_mul_positive(a, b, c)` — `a < b ∧ c > 0 → a*c < b*c`.
- `lemma_lt_mul_negative(a, b, c)` — `a < b ∧ c < 0 → b*c < a*c`
  (order reversal).
- `lemma_lt_sub_equiv(a, b)` — `a < b ↔ from_int(0) < b - a`.

Useful for: proving strict orientation (CW vs CCW, not just collinear),
strict containment, open half-plane tests.

## 11. Negation reverses ordering  ✅

- `lemma_neg_reverses_le(a, b)` — `a ≤ b → -b ≤ -a`.
- `lemma_neg_reverses_lt(a, b)` — `a < b → -b < -a`.
- `lemma_sub_le_monotone_left(a, b, c)` — `a ≤ b → a - c ≤ b - c`.
- `lemma_sub_le_monotone_right(a, b, c)` — `a ≤ b → c - b ≤ c - a`
  (note reversal in second arg).

Useful for: bounding-box reflection/negation, symmetric containment.

## 12. Bilateral addition monotonicity  ✅

- `lemma_le_add_both(a, b, c, d)` — `a ≤ b ∧ c ≤ d → a + c ≤ b + d`.
- `lemma_lt_add_both(a, b, c, d)` — `a < b ∧ c < d → a + c < b + d`.
- `lemma_le_lt_add(a, b, c, d)` — `a ≤ b ∧ c < d → a + c < b + d`.

Useful for: bounding-box proofs (sum of interval bounds), componentwise
vector inequality.

## 13. Multiplicative cancellation  ✅

For intersection computations: solve `t = num / den`, substitute back,
simplify.

- `lemma_mul_cancel_right(a, b, c)` — `a*c ≡ b*c ∧ c ≢ 0 → a ≡ b`.
- `lemma_mul_cancel_left(a, b, c)` — `c*a ≡ c*b ∧ c ≢ 0 → a ≡ b`.

Useful for: parametric intersection (line-line, ray-plane), simplification
of rational expressions in geometric computations.

## 14. Division properties  ✅

For solving linear systems and parametric coordinates.

- `lemma_div_add_numerator(a, b, c)` — `c ≢ 0 → (a + b) / c ≡ a/c + b/c`.
- `lemma_div_cancel(a, b)` — `a ≢ 0 → a * (b / a) ≡ b`.
- `lemma_div_self(a)` — `a ≢ 0 → a / a ≡ 1`.
- `lemma_div_mul_cancel(a, b)` — `b ≢ 0 → (a * b) / b ≡ a`.
- `lemma_div_le_monotone(a, b, c)` — `a ≤ b ∧ c > 0 → a/c ≤ b/c`.
- `lemma_div_neg_denominator(a, b, c)` — `a ≤ b ∧ c < 0 → b/c ≤ a/c`
  (order reversal).

Useful for: intersection parameter computation, barycentric coordinates,
rational Bezier evaluation.

## 15. Convex combination / interpolation  ✅

For parametric line segments, Bezier curves, barycentric coordinates.

- `lemma_convex_between(a, b, t)` —
  `a ≤ b ∧ 0 ≤ t ≤ 1 → a ≤ a*(1-t) + b*t ≤ b`.
- `lemma_convex_endpoints(a, b)` —
  `a*(1-0) + b*0 ≡ a` and `a*(1-1) + b*1 ≡ b`.
- `lemma_convex_midpoint(a, b)` —
  `a*(1 - 1/2) + b*(1/2) ≡ midpoint(a, b)`.

Useful for: proving parametric points lie within segments, subdivision
correctness, de Casteljau algorithm.

## 16. Four-component sum of squares (quaternion norm)  ✅

For quaternion rotation proofs: `|q|² = w² + x² + y² + z²`.

- `lemma_sum_of_four_squares_nonneg(a, b, c, d)` —
  `a² + b² + c² + d² ≥ 0`.
- `lemma_sum_of_four_squares_zero_iff(a, b, c, d)` —
  `a² + b² + c² + d² ≡ 0 ↔ a ≡ 0 ∧ b ≡ 0 ∧ c ≡ 0 ∧ d ≡ 0`.

Useful for: quaternion unit-norm proofs, rotation composition correctness,
SLERP verification.

---

## Notes

- All spec lemmas go in `rational.rs` (ghost model).
- Runtime exec functions go in `runtime_rational.rs` with `wf_spec` contracts.
- When a vcad-math precedent exists, port the proof structure but adapt naming
  (`Scalar` → `Rational`, `pub(crate)` → `pub`, etc.).
