import DeGua.Three
import DeGua.General
import DeGua.Bridge
import DeGua.CauchyBinet

/-!
# Layer 15: classical statements

Layer 15. These definitions and statements were written independently, from textbook statements, by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves (or proves part of) one of them from this development.
-/

open EuclideanGeometry

noncomputable section

open scoped Classical

namespace DeGua.Classical

/-! ## Writer definitions and statements, verbatim (packaged as `Prop`s). -/

def hullVol {n : ℕ} (p : EuclideanSpace ℝ (Fin n)) (s : Set (EuclideanSpace ℝ (Fin n))) : ℝ :=
  (MeasureTheory.volume {v : vectorSpan ℝ s | (v : EuclideanSpace ℝ (Fin n)) + p ∈
    convexHull ℝ s}).toReal

def classical_TriSimplex2_a : Prop := ∀ (O A B C : EuclideanSpace ℝ (Fin 3))
    (h : AffineIndependent ℝ ![O, A, B, C])
    (hAB : inner ℝ (A -ᵥ O) (B -ᵥ O) = 0) (hBC : inner ℝ (B -ᵥ O) (C -ᵥ O) = 0)
    (hCA : inner ℝ (C -ᵥ O) (A -ᵥ O) = 0),
    hullVol A {A, B, C} ^ 2 =
      hullVol O {O, A, B} ^ 2 + hullVol O {O, B, C} ^ 2 + hullVol O {O, C, A} ^ 2

def classical_TriSimplex2_a_coord : Prop := ∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c),
    hullVol (EuclideanSpace.single (0 : Fin 3) a)
      {EuclideanSpace.single (0 : Fin 3) a, EuclideanSpace.single (1 : Fin 3) b,
        EuclideanSpace.single (2 : Fin 3) c} ^ 2 =
      (a * b / 2) ^ 2 + (b * c / 2) ^ 2 + (c * a / 2) ^ 2

def classical_TriSimplex2_b : Prop := ∀ (n : ℕ) (hn : 2 ≤ n)
    (s : Affine.Simplex ℝ (EuclideanSpace ℝ (Fin n)) n)
    (horth : ∀ i j : Fin (n + 1), i ≠ 0 → j ≠ 0 → i ≠ j →
      inner ℝ (s.points i -ᵥ s.points 0) (s.points j -ᵥ s.points 0) = 0),
    hullVol (s.points 1) (s.points '' {0}ᶜ) ^ 2 =
      ∑ j ∈ Finset.univ.erase (0 : Fin (n + 1)), hullVol (s.points 0) (s.points '' {j}ᶜ) ^ 2

def classical_TriSimplex2_b_coord : Prop := ∀ (n : ℕ) (hn : 2 ≤ n) (a : Fin n → ℝ)
    (ha : ∀ i, 0 < a i),
    hullVol (EuclideanSpace.single ⟨0, by omega⟩ (a ⟨0, by omega⟩))
        (Set.range fun i => EuclideanSpace.single i (a i)) ^ 2 =
      ∑ i : Fin n, hullVol 0
        (insert 0 ((fun j => EuclideanSpace.single j (a j)) '' {i}ᶜ)) ^ 2

/-! ## Strongest parts: the same configurations with the repository's Gram-determinant
squared volume `DeGua.simplexVolSq` in place of the measure-theoretic `hullVol ^ 2`. -/

/-- 2a, part: identical hypotheses (affine independence not needed). -/
theorem cov_TriSimplex2_a_part (O A B C : EuclideanSpace ℝ (Fin 3))
    (hAB : inner ℝ (A -ᵥ O) (B -ᵥ O) = 0) (hBC : inner ℝ (B -ᵥ O) (C -ᵥ O) = 0)
    (hCA : inner ℝ (C -ᵥ O) (A -ᵥ O) = 0) :
    DeGua.simplexVolSq ![A, B, C] =
      DeGua.simplexVolSq ![O, A, B] + DeGua.simplexVolSq ![O, B, C] +
        DeGua.simplexVolSq ![O, C, A] := by
  rw [← DeGua.triAreaSq_eq_simplexVolSq, ← DeGua.triAreaSq_eq_simplexVolSq,
    ← DeGua.triAreaSq_eq_simplexVolSq, ← DeGua.triAreaSq_eq_simplexVolSq]
  exact DeGua.de_gua_three O A B C hAB hBC hCA

/-- 2a coordinate form, part (NEW PROOF of the coordinate evaluation). -/
theorem cov_TriSimplex2_a_coord_part (a b c : ℝ) :
    DeGua.simplexVolSq ![EuclideanSpace.single (0 : Fin 3) a, EuclideanSpace.single (1 : Fin 3) b,
        EuclideanSpace.single (2 : Fin 3) c] =
      (a * b / 2) ^ 2 + (b * c / 2) ^ 2 + (c * a / 2) ^ 2 := by
  rw [← DeGua.triAreaSq_eq_simplexVolSq]
  unfold DeGua.triAreaSq
  simp only [dotProduct, Fin.sum_univ_three, cross_apply, WithLp.ofLp_sub,
    Pi.sub_apply, EuclideanSpace.ofLp_single, Pi.single_apply]
  simp
  ring

/-- 2b, part: the writer's `n`-simplex configuration (orthogonal edges at vertex `0`), with
facets listed as vertex tuples: `F_0` is `s.points ∘ Fin.succ`, `F_{i+1}` is `O` followed by the
other `P`s. Holds in every real inner product space and for all `n ≥ 1`. -/
theorem cov_TriSimplex2_b_part {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (n : ℕ) (x : Fin (n + 1 + 1) → E)
    (horth : ∀ i j : Fin (n + 1 + 1), i ≠ 0 → j ≠ 0 → i ≠ j →
      inner ℝ (x i - x 0) (x j - x 0) = 0) :
    DeGua.simplexVolSq (x ∘ Fin.succ) =
      ∑ i : Fin (n + 1),
        DeGua.simplexVolSq (Fin.cons (x 0) ((x ∘ Fin.succ) ∘ i.succAbove) : Fin (n + 1) → E) :=
  DeGua.de_gua (x 0) (x ∘ Fin.succ) fun i j hij =>
    horth i.succ j.succ (Fin.succ_ne_zero _) (Fin.succ_ne_zero _) (Fin.succ_injective _ |>.ne hij)

end DeGua.Classical
