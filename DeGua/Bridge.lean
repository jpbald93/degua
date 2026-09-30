import DeGua.Three
import DeGua.General

/-!
# Consistency between the two notions of area in `ℝ³`

The cross-product area of `DeGua.Three` agrees with the Gram-determinant `2`-volume of
`DeGua.General`, and the three-dimensional theorem is the case `m = 2` of `DeGua.de_gua`.
-/

open Matrix

namespace DeGua

/-- Cross-product squared area = Gram-determinant squared area (Lagrange's identity). -/
theorem triAreaSq_eq_simplexVolSq (X Y Z : EuclideanSpace ℝ (Fin 3)) :
    triAreaSq X Y Z = simplexVolSq ![X, Y, Z] := by
  unfold triAreaSq simplexVolSq
  simp only
  rw [cross_dot_cross, det_fin_two]
  simp only [gram_apply, inner_eq_dot, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Nat.factorial]
  norm_num

/-- The three-dimensional theorem recovered as the `m = 2` case of the general `DeGua.de_gua`
(stated with Gram-determinant areas). -/
theorem de_gua_three_of_general (O A B C : EuclideanSpace ℝ (Fin 3))
    (h : Pairwise fun i j => inner ℝ (![A, B, C] i - O) (![A, B, C] j - O) = 0) :
    simplexVolSq ![A, B, C] =
      simplexVolSq ![O, B, C] + simplexVolSq ![O, A, C] + simplexVolSq ![O, A, B] := by
  have e0 : (Fin.cons O (![A, B, C] ∘ Fin.succAbove 0) : Fin 3 → EuclideanSpace ℝ (Fin 3)) =
      ![O, B, C] := by
    funext i; fin_cases i <;> rfl
  have e1 : (Fin.cons O (![A, B, C] ∘ Fin.succAbove 1) : Fin 3 → EuclideanSpace ℝ (Fin 3)) =
      ![O, A, C] := by
    funext i; fin_cases i <;> rfl
  have e2 : (Fin.cons O (![A, B, C] ∘ Fin.succAbove 2) : Fin 3 → EuclideanSpace ℝ (Fin 3)) =
      ![O, A, B] := by
    funext i; fin_cases i <;> rfl
  rw [de_gua O ![A, B, C] h, Fin.sum_univ_three, e0, e1, e2]

end DeGua
