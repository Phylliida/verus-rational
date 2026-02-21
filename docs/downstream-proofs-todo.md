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

## 17. Algebraic identities (constraint equation manipulation)

Expanding/factoring distance constraints, e.g. `|p-q|² = (px-qx)² + (py-qy)²`.

- `lemma_square_of_sum(a, b)` — `(a+b)² ≡ a² + 2ab + b²`.
- `lemma_square_of_difference(a, b)` — `(a-b)² ≡ a² - 2ab + b²`.
- `lemma_difference_of_squares(a, b)` — `a² - b² ≡ (a+b)(a-b)`.

Useful for: distance constraints, circle equations, polynomial manipulation.

## 18. Double negation & subtraction algebra

Bookkeeping lemmas that appear in every nontrivial constraint proof.

- `lemma_neg_neg(a)` — `-(-a) ≡ a`.
- `lemma_sub_self(a)` — `a - a ≡ 0`.
- `lemma_sub_neg(a, b)` — `a - (-b) ≡ a + b`.
- `lemma_neg_add(a, b)` — `-(a+b) ≡ -a + -b`.
- `lemma_neg_sub(a, b)` — `-(a-b) ≡ b - a`.

Useful for: every nontrivial constraint manipulation proof.

## 19. Extended division / reciprocal

Needed for Cramer's rule and parametric computation.

- `lemma_reciprocal_of_product(a, b)` —
  `a ≢ 0 ∧ b ≢ 0 → (a*b)⁻¹ ≡ a⁻¹ * b⁻¹`.
- `lemma_div_mul_assoc(a, b, c)` —
  `b ≢ 0 → (a/b)*c ≡ (a*c)/b`.
- `lemma_div_neg_denominator(a, b, c)` —
  `a ≤ b ∧ c < 0 → b/c ≤ a/c` (order reversal).

Useful for: Cramer's rule, compound fraction simplification, parametric
computation.

## 20. 2×2 determinant & Cramer's rule

Core of line-line intersection and orient2d predicates.

- `det2_spec(a, b, c, d)` — spec function `a*d - b*c`.
- `lemma_cramer2_satisfies(a, b, c, d, e, f)` —
  when `det ≢ 0`, the Cramer solution
  `x = (d*e - b*f)/det, y = (a*f - c*e)/det`
  satisfies `a*x + b*y ≡ e ∧ c*x + d*y ≡ f`.
- `lemma_det2_antisymmetric(a, b, c, d)` —
  `det2(c, d, a, b) ≡ -det2(a, b, c, d)`.
- `lemma_det2_zero_iff_proportional(a, b, c, d)` —
  `det2 ≡ 0 ↔ a*d ≡ b*c` (collinearity test).

Useful for: line-line intersection, orientation predicates, collinearity.

## 21. Quadratic discriminant

For circle-line, circle-circle intersection count.

- `discriminant_spec(a, b, c)` — spec function `b² - 4ac`.
- `lemma_quadratic_at_rational_root(a, b, c, t)` —
  `a*t*t + b*t + c ≡ 0` verification (check a candidate root).
- `lemma_quadratic_double_root(a, b, c)` —
  `disc ≡ 0 ∧ a ≢ 0 → a * (-b/(2a))² + b*(-b/(2a)) + c ≡ 0`.
- `lemma_discriminant_nonneg_square(a, b, c, t)` —
  `a*t² + b*t + c ≡ 0 ∧ a ≢ 0 → disc ≥ 0`.

Useful for: circle-line intersection, tangency detection, constraint
feasibility.

## 22. Integer power / polynomial evaluation

For constraint polynomial evaluation.

- `pow_spec(a, n: nat)` — spec function `a^n`.
- `lemma_pow_zero(a)` — `a^0 ≡ 1`.
- `lemma_pow_one(a)` — `a^1 ≡ a`.
- `lemma_pow_two(a)` — `a^2 ≡ a*a`.
- `lemma_pow_succ(a, n)` — `a^(n+1) ≡ a^n * a`.
- `lemma_pow_mul(a, b, n)` — `(a*b)^n ≡ a^n * b^n`.
- `lemma_pow_add(a, m, n)` — `a^(m+n) ≡ a^m * a^n`.
- `lemma_pow_even_nonneg(a, n)` — `0 ≤ a^(2n)`.

Useful for: polynomial evaluation, Horner's method, constraint degree
analysis.

## 23. Interval containment

For robust geometry and bounding-box proofs.

- `lemma_add_interval(a, lo_a, hi_a, b, lo_b, hi_b)` —
  `a ∈ [lo_a, hi_a] ∧ b ∈ [lo_b, hi_b] → a+b ∈ [lo_a+lo_b, hi_a+hi_b]`.
- `lemma_mul_interval_nonneg(a, lo_a, hi_a, b, lo_b, hi_b)` —
  both non-negative: `a*b ∈ [lo_a*lo_b, hi_a*hi_b]`.
- `lemma_interval_contains_midpoint(lo, hi)` —
  `lo ≤ hi → lo ≤ midpoint(lo,hi) ≤ hi`.

Useful for: bounding-box containment, interval subdivision, robust
geometry.

## 24. Cauchy–Schwarz (squared form)

For angle bounds and distance estimates, provable without square roots.

- `lemma_cauchy_schwarz_2d(a, b, c, d)` —
  `(a*c + b*d)² ≤ (a² + b²)(c² + d²)`.
- `lemma_cauchy_schwarz_3d(a, b, c, d, e, f)` —
  `(a*d + b*e + c*f)² ≤ (a² + b² + c²)(d² + e² + f²)`.

Useful for: dot-product bounds, angle constraints, projection length
bounds.

---

## Notes

- All spec lemmas go in `rational.rs` (ghost model).
- Runtime exec functions go in `runtime_rational.rs` with `wf_spec` contracts.
- When a vcad-math precedent exists, port the proof structure but adapt naming
  (`Scalar` → `Rational`, `pub(crate)` → `pub`, etc.).
