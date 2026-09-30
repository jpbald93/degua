import Mathlib

/-!
# Cauchy–Binet and the "Pythagorean theorem for `k`-volumes"

* `DeGua.det_mul_eq_sum_strictMono` — the **Cauchy–Binet formula** for
  `A : Matrix (Fin k) (Fin n) R`, `B : Matrix (Fin n) (Fin k) R`:
  `det (A * B) = ∑_{s : Fin k → Fin n strictly monotone} det (A_{·,s}) * det (B_{s,·})`.
* `DeGua.det_gram_eq_sum_sq_minors` — for any family `v : Fin k → ℝⁿ`, the Gram determinant
  (the squared `k`-volume of the parallelotope spanned by `v`) equals the sum over all coordinate
  `k`-planes of the squared `k`-volumes of the orthogonal projections of the parallelotope onto
  them (the squares of the `k × k` minors). This is the general form of De Gua's theorem.
-/

open Matrix Finset Equiv

namespace DeGua

variable {R : Type*} [CommRing R] {k n : ℕ}

/-- Expansion of `det (A * B)` for rectangular `A`, `B` as a sum over all maps `Fin k → Fin n`. -/
theorem det_mul_eq_sum_fun (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    det (A * B) = ∑ p : Fin k → Fin n, (∏ i, B (p i) i) * det (A.submatrix id p) := by
  simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  refine Finset.sum_congr rfl fun σ _ => ?_
  simp only [submatrix_apply, id, Finset.prod_mul_distrib]
  ring

open Classical in
/-- The **Cauchy–Binet formula**. -/
theorem det_mul_eq_sum_strictMono (A : Matrix (Fin k) (Fin n) R)
    (B : Matrix (Fin n) (Fin k) R) :
    det (A * B) = ∑ s ∈ univ.filter (fun s : Fin k → Fin n => StrictMono s),
      det (A.submatrix id s) * det (B.submatrix s id) := by
  rw [det_mul_eq_sum_fun]
  rw [← Finset.sum_filter_of_ne (p := fun p : Fin k → Fin n => Function.Injective p)]
  swap
  · intro p _ hp
    by_contra hinj
    apply hp
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
      simp only [Function.Injective, not_forall] at hinj
      obtain ⟨i, j, h, hne⟩ := hinj
      exact ⟨i, j, h, hne⟩
    rw [det_zero_of_column_eq hne (fun r => by simp [hij]), mul_zero]
  simp_rw [det_apply' (B.submatrix _ id), Finset.mul_sum]
  rw [← Finset.sum_product']
  symm
  refine Finset.sum_nbij' (fun x => x.1 ∘ x.2) (fun p => (p ∘ Tuple.sort p, (Tuple.sort p)⁻¹))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨s, τ⟩ h
    simp only [mem_filter, mem_product, mem_univ, true_and, and_true] at h ⊢
    exact h.injective.comp τ.injective
  · intro p hp
    simp only [mem_filter, mem_product, mem_univ, true_and, and_true] at hp ⊢
    exact (Tuple.monotone_sort p).strictMono_of_injective (hp.comp (Tuple.sort p).injective)
  · rintro ⟨s, τ⟩ h
    simp only [mem_filter, mem_product, mem_univ, true_and, and_true] at h
    have hmono : Monotone ((s ∘ τ) ∘ ⇑(τ⁻¹ : Perm (Fin k))) := by
      have : (s ∘ τ) ∘ ⇑(τ⁻¹ : Perm (Fin k)) = s := by funext i; simp
      rw [this]; exact h.monotone
    have heq : (s ∘ τ) ∘ Tuple.sort (s ∘ τ) = (s ∘ τ) ∘ ⇑(τ⁻¹ : Perm (Fin k)) :=
      Tuple.unique_monotone (Tuple.monotone_sort _) hmono
    have hinj : Function.Injective (s ∘ τ) := h.injective.comp τ.injective
    have hsort : Tuple.sort (s ∘ τ) = τ⁻¹ := by
      ext i
      exact congrArg Fin.val (hinj (congrFun heq i))
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [heq]; funext i; simp
    · rw [hsort, inv_inv]
  · intro p _
    funext i
    simp
  · rintro ⟨s, τ⟩ _
    simp only [Function.comp_apply]
    have hsub : A.submatrix id (s ∘ τ) = (A.submatrix id s).submatrix id τ := by
      rw [submatrix_submatrix]; rfl
    rw [hsub, det_permute']
    simp only [submatrix_apply, id]
    ring

open Classical in
/-- **De Gua's theorem, projection form** (the "Pythagorean theorem for `k`-volumes").
For vectors `v 0, …, v (k-1)` in `ℝⁿ`, the Gram determinant — i.e. the squared `k`-volume of the
parallelotope they span — equals the sum, over all coordinate `k`-planes `s`, of the squared
`k`-volume of the projection of the parallelotope onto that plane (the square of the `k × k`
minor on the columns `s`). -/
theorem det_gram_eq_sum_sq_minors (v : Fin k → EuclideanSpace ℝ (Fin n)) :
    (gram ℝ v).det = ∑ s ∈ univ.filter (fun s : Fin k → Fin n => StrictMono s),
      (det (of fun i j => (v i).ofLp (s j))) ^ 2 := by
  let A : Matrix (Fin k) (Fin n) ℝ := of fun i l => (v i).ofLp l
  have hG : gram ℝ v = A * Aᵀ := by
    ext i j
    simp only [gram_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct,
      mul_apply, transpose_apply, A, of_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [hG, det_mul_eq_sum_strictMono]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← transpose_submatrix, det_transpose, sq]
  rfl

end DeGua
