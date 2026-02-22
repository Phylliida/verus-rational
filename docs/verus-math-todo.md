# verus-math TODO

A future `verus-math` crate for multi-dimensional verified mathematics,
building on `verus-rational` for scalar arithmetic. Intended for use in a
formally verified CAD kernel.

## 1. 3x3 determinant + Cramer's rule

- [ ] `det3_spec(a, b, c, d, e, f, g, h, i)` — spec function for 3x3
  determinant via cofactor expansion.
- [ ] `lemma_det3_antisymmetric_rows` — row swap negates determinant.
- [ ] `lemma_det3_zero_iff_coplanar` — `det3 ≡ 0 ↔` rows are linearly
  dependent.
- [ ] `lemma_cramer3_satisfies(...)` — Cramer's rule solution satisfies all
  three equations of a 3x3 system.
- Useful for: plane-line intersection, 3D orientation tests, volume computation,
  barycentric coordinates in 3D.

## 2. Dot product (2D and 3D)

- [ ] `dot2_spec(a1, a2, b1, b2)` — `a1*b1 + a2*b2`.
- [ ] `dot3_spec(a1, a2, a3, b1, b2, b3)` — `a1*b1 + a2*b2 + a3*b3`.
- [ ] `lemma_dot_symmetric(a, b)` — `dot(a,b) ≡ dot(b,a)`.
- [ ] `lemma_dot_bilinear_left(a, b, c)` — `dot(a+b, c) ≡ dot(a,c) + dot(b,c)`.
- [ ] `lemma_dot_bilinear_right(a, b, c)` — `dot(a, b+c) ≡ dot(a,b) + dot(a,c)`.
- [ ] `lemma_dot_scalar_left(k, a, b)` — `dot(k*a, b) ≡ k*dot(a,b)`.
- [ ] `lemma_dot_nonneg_self(a)` — `dot(a,a) ≥ 0`.
- [ ] `lemma_dot_zero_iff(a)` — `dot(a,a) ≡ 0 ↔ a ≡ 0` (all components zero).
- [ ] `lemma_cauchy_schwarz_dot(a, b)` — `dot(a,b)² ≤ dot(a,a)*dot(b,b)`.
  (Reframes existing Cauchy-Schwarz from verus-rational in dot product terms.)
- Useful for: projection, distance, angle computation, normal vectors, half-plane
  tests.

## 3. 3D cross product

- [ ] `cross_spec(a1, a2, a3, b1, b2, b3) -> (Rational, Rational, Rational)` —
  `(a2*b3 - a3*b2, a3*b1 - a1*b3, a1*b2 - a2*b1)`.
- [ ] `lemma_cross_perpendicular_left(a, b)` — `dot(cross(a,b), a) ≡ 0`.
- [ ] `lemma_cross_perpendicular_right(a, b)` — `dot(cross(a,b), b) ≡ 0`.
- [ ] `lemma_cross_anticommutative(a, b)` — `cross(a,b) == -cross(b,a)`.
- [ ] `lemma_cross_self_zero(a)` — `cross(a,a) ≡ 0`.
- [ ] `lemma_scalar_triple_product(a, b, c)` — `dot(a, cross(b,c)) == det3(...)`.
- [ ] `lemma_cross_magnitude_squared(a, b)` —
  `dot(cross(a,b), cross(a,b)) ≡ dot(a,a)*dot(b,b) - dot(a,b)²`.
  (Lagrange identity.)
- Useful for: surface normals, orientation in 3D, triangle area, torque/moment.

## 4. Orientation predicates

- [ ] `orient2d_spec(a, b, c)` — `det2(b-a, c-a)`, returns sign as orientation.
- [ ] `orient3d_spec(a, b, c, d)` — `det3(b-a, c-a, d-a)`.
- [ ] `lemma_orient2d_antisymmetric` — swap reverses sign.
- [ ] `lemma_orient2d_collinear_iff_zero` — `orient2d ≡ 0 ↔ collinear`.
- [ ] `lemma_orient3d_coplanar_iff_zero` — `orient3d ≡ 0 ↔ coplanar`.
- Useful for: point-in-polygon, convex hull, sweep-line predicates, mesh
  validity.

## 5. Vector / point types (2D and 3D)

- [ ] `Vec2 { x: Rational, y: Rational }` — ghost 2D vector type.
- [ ] `Vec3 { x: Rational, y: Rational, z: Rational }` — ghost 3D vector type.
- [ ] Basic operations: add, sub, neg, scale, dot, cross (3D), norm_squared.
- [ ] `RuntimeVec2`, `RuntimeVec3` — exec-level counterparts using
  `RuntimeRational`.
- [ ] `lemma_vec_add_commutative`, `lemma_vec_add_associative`, etc.
- Useful for: every geometric computation. Having dedicated types avoids
  passing 2-3 separate rationals everywhere.

## 6. Linear interpolation / barycentric coordinates

- [ ] `lerp_spec(a, b, t)` — componentwise `a*(1-t) + b*t` for Vec2/Vec3.
- [ ] `barycentric2d_spec(p, a, b, c)` — barycentric coordinates of point p
  in triangle abc.
- [ ] `lemma_barycentric_partition_of_unity(u, v, w)` — `u + v + w ≡ 1`.
- [ ] `lemma_barycentric_inside_iff(u, v, w)` — all ≥ 0 ↔ point inside triangle.
- [ ] `lemma_lerp_endpoints(a, b)` — `lerp(a,b,0) ≡ a`, `lerp(a,b,1) ≡ b`.
- [ ] `lemma_lerp_between(a, b, t)` — componentwise containment for `0 ≤ t ≤ 1`.
- Useful for: triangle containment, mesh interpolation, parametric curves,
  de Casteljau subdivision.

## 7. Matrix types (2x2, 3x3)

- [ ] `Mat2 { a, b, c, d: Rational }` — ghost 2x2 matrix.
- [ ] `Mat3` — ghost 3x3 matrix (9 entries).
- [ ] `det(m)`, `mul(m1, m2)`, `transpose(m)`, `inverse(m)` spec functions.
- [ ] `lemma_det_mul(m1, m2)` — `det(m1*m2) == det(m1)*det(m2)`.
- [ ] `lemma_inverse_correct(m)` — `det(m) ≢ 0 → m * m⁻¹ ≡ I`.
- [ ] `lemma_transpose_det(m)` — `det(mᵀ) == det(m)`.
- Useful for: affine transformations, coordinate changes, projection matrices,
  solving linear systems.

## 8. Affine transformations

- [ ] `affine2d_spec(m: Mat2, t: Vec2, p: Vec2) -> Vec2` — `m*p + t`.
- [ ] `affine3d_spec(m: Mat3, t: Vec3, p: Vec3) -> Vec3` — `m*p + t`.
- [ ] `lemma_affine_compose(m1, t1, m2, t2)` — composition is affine.
- [ ] `lemma_affine_preserves_collinearity(m, t, a, b, c)`.
- [ ] `lemma_affine_invertible(m, t)` — `det(m) ≢ 0 → inverse exists`.
- Useful for: coordinate transforms, symmetry operations, workplane mappings.

## Notes

- This crate would depend on `verus-rational` for scalar arithmetic and
  `verus-bigint` transitively for runtime witnesses.
- Ghost types (`Vec2`, `Mat2`, etc.) and their proof lemmas are the primary
  deliverable. Exec-level runtime types can follow.
- The existing `det2_spec`, `cramer2`, `cauchy_schwarz_2d/3d`, and
  `sum_of_squares_*` lemmas in verus-rational/applications.rs are candidates
  for migration into this crate once it exists.
