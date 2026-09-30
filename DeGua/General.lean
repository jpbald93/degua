import Mathlib

/-!
# De Gua's theorem in arbitrary dimension

Let `E` be a real inner product space. Take an `n`-simplex (`n = m + 1`) with vertices
`O, P 0, …, P m`, and suppose the edges `P i - O` are pairwise orthogonal. Then the squared
`m`-volume of the facet opposite `O` equals the sum of the squared `m`-volumes of the `n` facets
through `O`.

The squared `k`-volume of a `k`-simplex with vertices `x 0, …, x k` is defined through the
Gram determinant of its edge vectors: `vol² = det (gram (x (j+1) - x 0)) / (k!)²`.
-/

open Matrix Finset

namespace DeGua

section Algebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Matrix determinant lemma for `diagonal b + c • J`, invertible case. -/
theorem det_diagonal_add_const_of_ne_zero (b : ι → ℝ) (c : ℝ) (hb : ∀ i, b i ≠ 0) :
    (diagonal b + of fun _ _ => c).det = ∏ i, b i + c * ∑ i, ∏ j ∈ univ.erase i, b j := by
  have key : (diagonal b + of fun _ _ => c : Matrix ι ι ℝ) =
      diagonal b * (1 + replicateCol Unit (fun j => (b j)⁻¹ * c) *
        replicateRow Unit (fun _ => (1 : ℝ))) := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.add_apply, Matrix.add_apply, Matrix.one_apply,
      diagonal_apply, of_apply]
    simp only [Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Fintype.sum_unique,
      mul_one]
    split_ifs <;> (field_simp [hb i]; try ring)
  rw [key, det_mul, det_diagonal, det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, one_mul]
  rw [mul_add, mul_one, Finset.mul_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.mul_prod_erase univ b (Finset.mem_univ j)]
  field_simp [hb j]

/-- The **matrix determinant lemma** for `diagonal b + c • J` (`J` the all-ones matrix), with no
invertibility hypothesis: `det = ∏ bᵢ + c · ∑ᵢ ∏_{j ≠ i} bⱼ`. -/
theorem det_diagonal_add_const (b : ι → ℝ) (c : ℝ) :
    (diagonal b + of fun _ _ => c).det = ∏ i, b i + c * ∑ i, ∏ j ∈ univ.erase i, b j := by
  let f : ℝ → ℝ := fun t => (diagonal (fun i => b i + t) + of fun _ _ => c).det
  let g : ℝ → ℝ := fun t =>
    ∏ i, (b i + t) + c * ∑ i, ∏ j ∈ univ.erase i, (b j + t)
  have hf : Continuous f := by
    refine Continuous.matrix_det (Continuous.add ?_ continuous_const)
    exact Continuous.matrix_diagonal (continuous_pi fun i => continuous_const.add continuous_id)
  have hg : Continuous g := by fun_prop
  have hS : Dense (Set.range fun i => -b i)ᶜ :=
    (Set.finite_range _).countable.dense_compl ℝ
  have hfg : Set.EqOn f g (Set.range fun i => -b i)ᶜ := by
    intro t ht
    apply det_diagonal_add_const_of_ne_zero
    intro i hi
    exact ht ⟨i, by simp only; linarith⟩
  have := congrFun (Continuous.ext_on hS hf hg hfg) 0
  simpa [f, g] using this

/-- `∏_{k ≠ i} f k` written as a product over all of `univ`. -/
theorem prod_erase_eq_prod_ite (f : ι → ℝ) (i : ι) :
    ∏ k ∈ univ.erase i, f k = ∏ k, if k = i then 1 else f k := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), if_pos rfl, mul_one]
  exact Finset.prod_congr rfl fun k hk => by rw [if_neg (Finset.ne_of_mem_erase hk)]

theorem prod_succAbove_eq_prod_erase {m : ℕ} (f : Fin (m + 1) → ℝ) (i : Fin (m + 1)) :
    ∏ j, f (i.succAbove j) = ∏ k ∈ univ.erase i, f k := by
  rw [prod_erase_eq_prod_ite, Fin.prod_univ_succAbove _ i, if_pos rfl, one_mul]
  exact Finset.prod_congr rfl fun j _ => by rw [if_neg (Fin.succAbove_ne i j)]

/-- The algebraic heart of De Gua's theorem: the Gram determinant of the edge family
`(v (j+1) - v 0)_j` for orthogonal `v` with `‖v i‖² = a i` expands as `∑ᵢ ∏_{k ≠ i} a k`. -/
theorem det_diag_add_const_succ {m : ℕ} (a : Fin (m + 1) → ℝ) :
    (diagonal (fun j : Fin m => a j.succ) + of fun _ _ => a 0).det =
      ∑ i, ∏ k ∈ univ.erase i, a k := by
  rw [det_diagonal_add_const, Fin.sum_univ_succ, Finset.mul_sum]
  congr 1
  · rw [← prod_succAbove_eq_prod_erase]
    simp
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [prod_erase_eq_prod_ite, prod_erase_eq_prod_ite, Fin.prod_univ_succ,
      if_neg (Fin.succ_ne_zero j).symm]
    simp only [Fin.succ_inj]

end Algebra

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The **squared `k`-dimensional volume** of the `k`-simplex with vertices `x 0, …, x k`,
defined as the Gram determinant of the edge vectors `x (j+1) - x 0` divided by `(k!)²`. -/
noncomputable def simplexVolSq {k : ℕ} (x : Fin (k + 1) → E) : ℝ :=
  (gram ℝ fun j : Fin k => x j.succ - x 0).det / ((k.factorial : ℝ) ^ 2)

/-- Gram matrix of an orthogonal family is diagonal. -/
theorem gram_eq_diagonal_of_orthogonal {ι : Type*} [DecidableEq ι] (v : ι → E)
    (h : Pairwise fun i j => inner ℝ (v i) (v j) = 0) :
    gram ℝ v = diagonal fun i => inner ℝ (v i) (v i) := by
  ext i j
  rw [gram_apply, diagonal_apply]
  split_ifs with hij
  · subst hij; rfl
  · exact h hij

/-- The Gram determinant of `(v (j+1) - v 0)_j` for a pairwise orthogonal family `v`. -/
theorem det_gram_sub_of_orthogonal {m : ℕ} (v : Fin (m + 1) → E)
    (h : Pairwise fun i j => inner ℝ (v i) (v j) = 0) :
    (gram ℝ fun j : Fin m => v j.succ - v 0).det =
      ∑ i, ∏ k ∈ univ.erase i, inner ℝ (v k) (v k) := by
  rw [← det_diag_add_const_succ]
  congr 1
  ext j l
  rw [gram_apply, Matrix.add_apply, diagonal_apply, of_apply]
  have h0 : ∀ j : Fin m, inner ℝ (v j.succ) (v 0) = 0 := fun j => h (Fin.succ_ne_zero j)
  have h0' : ∀ j : Fin m, inner ℝ (v 0) (v j.succ) = 0 := fun j => h (Fin.succ_ne_zero j).symm
  simp only [inner_sub_left, inner_sub_right, h0, h0', sub_zero, zero_sub, sub_neg_eq_add]
  split_ifs with hjl
  · subst hjl; ring
  · linear_combination h ((Fin.succ_injective m).ne hjl)

/-- **De Gua's theorem** (general dimension). For an `(m+1)`-simplex with vertices
`O, P 0, …, P m` in a real inner product space whose edges `P i - O` at `O` are pairwise
orthogonal, the squared `m`-volume of the facet `P 0 … P m` opposite `O` equals the sum over `i`
of the squared `m`-volumes of the facets `O, P 0, …, P (i-1), P (i+1), …, P m`. -/
theorem de_gua (O : E) {m : ℕ} (P : Fin (m + 1) → E)
    (h : Pairwise fun i j => inner ℝ (P i - O) (P j - O) = 0) :
    simplexVolSq P =
      ∑ i : Fin (m + 1), simplexVolSq (Fin.cons O (P ∘ i.succAbove) : Fin (m + 1) → E) := by
  unfold simplexVolSq
  rw [← Finset.sum_div]
  congr 1
  have hP : (fun j : Fin m => P j.succ - P 0) =
      fun j => (fun k => P k - O) j.succ - (fun k => P k - O) 0 := by
    funext j; simp
  rw [hP, det_gram_sub_of_orthogonal _ h]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hF : (fun j : Fin m => (Fin.cons O (P ∘ i.succAbove) : Fin (m + 1) → E) j.succ -
      (Fin.cons O (P ∘ i.succAbove) : Fin (m + 1) → E) 0) =
      fun j => P (i.succAbove j) - O := by
    funext j; simp
  rw [hF, gram_eq_diagonal_of_orthogonal, det_diagonal,
    prod_succAbove_eq_prod_erase (fun k => inner ℝ (P k - O) (P k - O))]
  intro j l hjl
  exact h ((Fin.succAbove_right_injective).ne hjl)

end Geometry

end DeGua
