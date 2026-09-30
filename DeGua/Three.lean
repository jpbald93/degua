import Mathlib

/-!
# De Gua's theorem, three-dimensional case

For a tetrahedron `OABC` in `EuclideanSpace ℝ (Fin 3)` whose edges `OA`, `OB`, `OC` are pairwise
orthogonal, `area(ABC)² = area(OAB)² + area(OBC)² + area(OCA)²`.
Areas are defined via the cross product: `area(XYZ) = ‖(Y - X) × (Z - X)‖ / 2`.
-/

open Matrix

namespace DeGua

/-- Squared area of the triangle `XYZ` in `ℝ³`, via the cross product:
`area² = ((Y - X) × (Z - X)) ⬝ ((Y - X) × (Z - X)) / 4`. -/
noncomputable def triAreaSq (X Y Z : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  let w := crossProduct (Y - X).ofLp (Z - X).ofLp
  w ⬝ᵥ w / 4

/-- The algebraic core: for pairwise orthogonal `u v w : ℝ³`,
`|(v - u) × (w - u)|² = |u × v|² + |v × w|² + |w × u|²`. -/
theorem cross_sub_sq (u v w : Fin 3 → ℝ) (huv : u ⬝ᵥ v = 0) (hvw : v ⬝ᵥ w = 0)
    (hwu : w ⬝ᵥ u = 0) :
    (crossProduct (v - u) (w - u)) ⬝ᵥ (crossProduct (v - u) (w - u)) =
      (crossProduct u v) ⬝ᵥ (crossProduct u v) + (crossProduct v w) ⬝ᵥ (crossProduct v w) +
        (crossProduct w u) ⬝ᵥ (crossProduct w u) := by
  simp only [dotProduct, Fin.sum_univ_three, cross_apply, Pi.sub_apply] at huv hvw hwu ⊢
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at *
  linear_combination
    (2 * (w 0 * v 0 + w 1 * v 1 + w 2 * v 2) + 2 * (u 0 * w 0 + u 1 * w 1 + u 2 * w 2) - 2 * (w 0 * w 0 + w 1 * w 1 + w 2 * w 2)) * huv
      + (-2 * (v 0 * v 0 + v 1 * v 1 + v 2 * v 2)) * hwu
      + (-2 * (u 0 * u 0 + u 1 * u 1 + u 2 * u 2) + 2 * (u 0 * w 0 + u 1 * w 1 + u 2 * w 2)) * hvw

theorem inner_eq_dot (x y : EuclideanSpace ℝ (Fin 3)) : inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- **De Gua's theorem** (three-dimensional, cross-product form). If the edges `OA`, `OB`, `OC`
of the tetrahedron `OABC` are pairwise orthogonal then
`area(ABC)² = area(OAB)² + area(OBC)² + area(OCA)²`. -/
theorem de_gua_three (O A B C : EuclideanSpace ℝ (Fin 3))
    (hAB : inner ℝ (A - O) (B - O) = 0) (hBC : inner ℝ (B - O) (C - O) = 0)
    (hCA : inner ℝ (C - O) (A - O) = 0) :
    triAreaSq A B C = triAreaSq O A B + triAreaSq O B C + triAreaSq O C A := by
  rw [inner_eq_dot] at hAB hBC hCA
  have h1 : (B - A).ofLp = (B - O).ofLp - (A - O).ofLp := by
    simp only [WithLp.ofLp_sub]; abel
  have h2 : (C - A).ofLp = (C - O).ofLp - (A - O).ofLp := by
    simp only [WithLp.ofLp_sub]; abel
  have key := cross_sub_sq _ _ _ hAB hBC hCA
  unfold triAreaSq
  simp only
  rw [h1, h2, key]
  ring

end DeGua
