module

public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
public import Mathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace ReciprocityTheory.MultiplicativeHeights

open Finset InnerProductSpace

theorem det_gram_eq_prod_gramSchmidt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : Fin n → E) :
    (Matrix.gram ℂ v).det = ∏ k, (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) := by
  classical
  let c := fun j i => inner ℂ (gramSchmidt ℂ v i) (v j) / (‖gramSchmidt ℂ v i‖ : ℂ) ^ 2
  let A : Matrix (Fin n) (Fin n) ℂ := fun i j => if i = j then 1 else if i < j then c j i else 0
  have hA : ∀ j, v j = ∑ i, A i j • gramSchmidt ℂ v i := by
    intro j
    have h1 : ∀ i, A i j • gramSchmidt ℂ v i =
        (if i = j then gramSchmidt ℂ v i else 0) +
          (if i < j then c j i • gramSchmidt ℂ v i else 0) := by
      intro i
      by_cases h : i = j
      · subst h; simp [A]
      · by_cases h' : i < j
        · simp [A, h, h']
        · simp [A, h, h']
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.sum_filter, gramSchmidt_def'' (𝕜 := ℂ) v j]
    congr 1
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext i
    simp
  have horth : ∀ k l, ⟪gramSchmidt ℂ v k, gramSchmidt ℂ v l⟫_ℂ =
      if k = l then (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ) else 0 := by
    intro k l
    by_cases h : k = l
    · subst h
      rw [ite_eq_left rfl, inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    · rw [ite_eq_right h, gramSchmidt_orthogonal (𝕜 := ℂ) v h]
  have hG : Matrix.gram ℂ v =
      Matrix.conjTranspose A * Matrix.diagonal (fun k => (((‖gramSchmidt ℂ v k‖ ^ 2 : ℝ)) : ℂ)) * A := by
    ext i j
    show ⟪v i, v j⟫_ℂ = _
    rw [hA i, hA j]
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, horth, mul_ite, mul_zero,
      Finset.mem_univ, ite_true, Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_ite_eq',
      Matrix.conjTranspose_apply, starRingEnd_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hAtri : A.BlockTriangular id := by
    intro i j h
    simp only [id] at h
    simp [A, h.ne', not_lt.mpr h.le]
  have hdetA : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hAtri]
    simp [A]
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hdetA, Matrix.det_diagonal]
  simp

theorem prod_le_re_det_gram {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (n : ℕ) (v : Fin n → E) (δ : Fin n → ℝ) (hδ : ∀ k, 0 ≤ δ k)
    (h : ∀ k, ∀ x ∈ Submodule.span ℂ (v '' Set.Iio k), δ k ≤ ‖v k - x‖ ^ 2) :
    ∏ k, δ k ≤ (Matrix.gram ℂ v).det.re := by
  classical
  rw [det_gram_eq_prod_gramSchmidt, ← Complex.ofReal_prod, Complex.ofReal_re]
  refine Finset.prod_le_prod₀ (fun k _ => hδ k) (fun k _ => ?_)
  have hc := gramSchmidt_def'' (𝕜 := ℂ) v k
  have hmem : v k - gramSchmidt ℂ v k ∈ Submodule.span ℂ (v '' Set.Iio k) := by
    rw [hc, add_sub_cancel_left, ← span_gramSchmidt_Iio (𝕜 := ℂ) v k]
    exact Submodule.sum_mem _ fun i hi => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨i, Finset.mem_Iio.mp hi, rfl⟩)
  simpa only [sub_sub_cancel] using h k _ hmem

end ReciprocityTheory.MultiplicativeHeights
