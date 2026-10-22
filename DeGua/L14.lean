import DeGua.Bridge
import DeGua.CauchyBinet

/-!
# Layer 14: Mathlib-only restatements and witnesses for De Gua's theorem and Cauchy–Binet

The statements `l14_*` mention only Mathlib notions: the squared area of a triangle in `ℝ³` is
written out as `((B - A) × (C - A)) ⬝ᵥ ((B - A) × (C - A)) / 4` with Mathlib's `crossProduct`, and
the squared `k`-volume of a simplex `x 0, …, x k` is written out as the Gram determinant
`det (gram ℝ (fun j => x j.succ - x 0)) / (k!)²` with Mathlib's `Matrix.gram`. The Cauchy–Binet and
projection statements of the repository already have Mathlib-only types; `l14_*` re-export them.

Witnesses: the corner tetrahedron `O = 0`, `A = (1,0,0)`, `B = (0,2,0)`, `C = (0,0,3)` (squared
face areas `1`, `9`, `9/4`, `49/4`, pairwise distinct and positive), in both the cross-product and
the Gram form; and a `2 × 3` / `3 × 2` integer pair with `det (A * B) = 7 ≠ 0`. The determinant
lemma and the projection form have no hypotheses, so no separate witness is needed for them.
-/

open Matrix Finset

namespace DeGua

/-- **De Gua (three-dimensional, Mathlib-only).** -/
theorem l14_de_gua_three (O A B C : EuclideanSpace ℝ (Fin 3))
    (hAB : inner ℝ (A - O) (B - O) = 0) (hBC : inner ℝ (B - O) (C - O) = 0)
    (hCA : inner ℝ (C - O) (A - O) = 0) :
    crossProduct (B - A).ofLp (C - A).ofLp ⬝ᵥ crossProduct (B - A).ofLp (C - A).ofLp / 4 =
      crossProduct (A - O).ofLp (B - O).ofLp ⬝ᵥ crossProduct (A - O).ofLp (B - O).ofLp / 4 +
        crossProduct (B - O).ofLp (C - O).ofLp ⬝ᵥ crossProduct (B - O).ofLp (C - O).ofLp / 4 +
        crossProduct (C - O).ofLp (A - O).ofLp ⬝ᵥ crossProduct (C - O).ofLp (A - O).ofLp / 4 :=
  de_gua_three O A B C hAB hBC hCA

/-- **De Gua (general form, Mathlib-only).** Squared volumes are Gram determinants of the edge
vectors divided by `(m!)²`. -/
theorem l14_de_gua {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (O : E) {m : ℕ}
    (P : Fin (m + 1) → E) (h : Pairwise fun i j => inner ℝ (P i - O) (P j - O) = 0) :
    (gram ℝ fun j : Fin m => P j.succ - P 0).det / ((m.factorial : ℝ) ^ 2) =
      ∑ i : Fin (m + 1),
        (gram ℝ fun j : Fin m => (Fin.cons O (P ∘ i.succAbove) : Fin (m + 1) → E) j.succ -
          (Fin.cons O (P ∘ i.succAbove) : Fin (m + 1) → E) 0).det / ((m.factorial : ℝ) ^ 2) :=
  de_gua O P h

/-- **Matrix determinant lemma, `diag + const` form (Mathlib-only).** -/
theorem l14_det_diagonal_add_const {ι : Type*} [Fintype ι] [DecidableEq ι] (b : ι → ℝ) (c : ℝ) :
    (diagonal b + of fun _ _ => c).det = ∏ i, b i + c * ∑ i, ∏ j ∈ univ.erase i, b j :=
  det_diagonal_add_const b c

/-- **Cauchy–Binet (Mathlib-only).** -/
theorem l14_cauchy_binet {R : Type*} [CommRing R] {k n : ℕ} (A : Matrix (Fin k) (Fin n) R)
    (B : Matrix (Fin n) (Fin k) R) :
    det (A * B) = ∑ s ∈ univ.filter (fun s : Fin k → Fin n => StrictMono s),
      det (A.submatrix id s) * det (B.submatrix s id) :=
  det_mul_eq_sum_strictMono A B

open Classical in
/-- **Pythagorean theorem for `k`-volumes (Mathlib-only).** -/
theorem l14_det_gram_eq_sum_sq_minors {k n : ℕ} (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    (gram ℝ v).det = ∑ s ∈ univ.filter (fun s : Fin k → Fin n => StrictMono s),
      (det (of fun i j => (v i).ofLp (s j))) ^ 2 :=
  det_gram_eq_sum_sq_minors v

/-! ### Witnesses -/

/-- The four squared face areas of the corner tetrahedron `0, e₀, 2e₁, 3e₂`. -/
theorem l14b_corner_areas :
    let O : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 0]
    let A : EuclideanSpace ℝ (Fin 3) := !₂[1, 0, 0]
    let B : EuclideanSpace ℝ (Fin 3) := !₂[0, 2, 0]
    let C : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 3]
    triAreaSq A B C = 49 / 4 ∧ triAreaSq O A B = 1 ∧ triAreaSq O B C = 9 ∧
      triAreaSq O C A = 9 / 4 := by
  simp only [triAreaSq, cross_apply, dotProduct, Fin.sum_univ_three]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp <;> norm_num

theorem l14b_corner_orth :
    let O : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 0]
    let A : EuclideanSpace ℝ (Fin 3) := !₂[1, 0, 0]
    let B : EuclideanSpace ℝ (Fin 3) := !₂[0, 2, 0]
    let C : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 3]
    inner ℝ (A - O) (B - O) = 0 ∧ inner ℝ (B - O) (C - O) = 0 ∧ inner ℝ (C - O) (A - O) = 0 := by
  simp only [inner_eq_dot, dotProduct, Fin.sum_univ_three]
  refine ⟨?_, ?_, ?_⟩ <;> simp

/-- **Witness (three-dimensional).** The corner tetrahedron `O = 0`, `A = e₀`, `B = 2e₁`, `C = 3e₂`
satisfies the orthogonality hypotheses; its four squared face areas are `49/4`, `1`, `9`, `9/4`,
pairwise distinct and positive. -/
theorem l14w_de_gua_three :
    let O : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 0]
    let A : EuclideanSpace ℝ (Fin 3) := !₂[1, 0, 0]
    let B : EuclideanSpace ℝ (Fin 3) := !₂[0, 2, 0]
    let C : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 3]
    (inner ℝ (A - O) (B - O) = 0 ∧ inner ℝ (B - O) (C - O) = 0 ∧ inner ℝ (C - O) (A - O) = 0) ∧
    crossProduct (B - A).ofLp (C - A).ofLp ⬝ᵥ crossProduct (B - A).ofLp (C - A).ofLp / 4 = 49 / 4 ∧
    crossProduct (A - O).ofLp (B - O).ofLp ⬝ᵥ crossProduct (A - O).ofLp (B - O).ofLp / 4 = 1 ∧
    crossProduct (B - O).ofLp (C - O).ofLp ⬝ᵥ crossProduct (B - O).ofLp (C - O).ofLp / 4 = 9 ∧
    crossProduct (C - O).ofLp (A - O).ofLp ⬝ᵥ crossProduct (C - O).ofLp (A - O).ofLp / 4 = 9 / 4 :=
  ⟨l14b_corner_orth, l14b_corner_areas⟩

/-- **Witness (general form, `m = 2`).** The same tetrahedron, with Gram-determinant areas: the
facet opposite `O` has squared area `49/4` and the three facets through `O` have `9`, `9/4`, `1`
(pairwise distinct, positive). -/
theorem l14w_de_gua :
    let O : EuclideanSpace ℝ (Fin 3) := !₂[0, 0, 0]
    let P : Fin 3 → EuclideanSpace ℝ (Fin 3) := ![!₂[1, 0, 0], !₂[0, 2, 0], !₂[0, 0, 3]]
    (Pairwise fun i j => inner ℝ (P i - O) (P j - O) = 0) ∧
    (gram ℝ fun j : Fin 2 => P j.succ - P 0).det / ((Nat.factorial 2 : ℝ) ^ 2) = 49 / 4 ∧
    (gram ℝ fun j : Fin 2 => ![O, P 1, P 2] j.succ - ![O, P 1, P 2] 0).det /
      ((Nat.factorial 2 : ℝ) ^ 2) = 9 ∧
    (gram ℝ fun j : Fin 2 => ![O, P 0, P 2] j.succ - ![O, P 0, P 2] 0).det /
      ((Nat.factorial 2 : ℝ) ^ 2) = 9 / 4 ∧
    (gram ℝ fun j : Fin 2 => ![O, P 0, P 1] j.succ - ![O, P 0, P 1] 0).det /
      ((Nat.factorial 2 : ℝ) ^ 2) = 1 := by
  intro O P
  obtain ⟨h1, h2, h3, h4⟩ := l14b_corner_areas
  obtain ⟨o1, o2, o3⟩ := l14b_corner_orth
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [P, O, real_inner_comm]
  · exact (triAreaSq_eq_simplexVolSq (P 0) (P 1) (P 2)).symm.trans h1
  · exact (triAreaSq_eq_simplexVolSq O (P 1) (P 2)).symm.trans h3
  · simp only [gram, det_fin_two, of_apply, O, P, inner_eq_dot, dotProduct, Fin.sum_univ_three]
    simp
    norm_num
  · exact (triAreaSq_eq_simplexVolSq O (P 0) (P 1)).symm.trans h2

/-- **Witness (Cauchy–Binet).** A `2 × 3` and a `3 × 2` integer matrix with `det (A * B) = 7`;
the Cauchy–Binet sum over the three column pairs therefore equals `7 ≠ 0`. -/
theorem l14w_cauchy_binet :
    let A : Matrix (Fin 2) (Fin 3) ℤ := !![1, 2, 0; 0, 1, 1]
    let B : Matrix (Fin 3) (Fin 2) ℤ := !![1, 0; 1, 1; 0, 2]
    det (A * B) = 7 ∧ det (A * B) ≠ 0 ∧
      ∑ s ∈ univ.filter (fun s : Fin 2 → Fin 3 => StrictMono s),
        det (A.submatrix id s) * det (B.submatrix s id) = det (A * B) := by
  intro A B
  have h : det (A * B) = 7 := by
    simp only [A, B, det_fin_two, mul_apply, Fin.sum_univ_three]
    simp
  refine ⟨h, by rw [h]; norm_num, (l14_cauchy_binet A B).symm⟩

end DeGua
