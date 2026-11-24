module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSecPointSeparable
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsGenericFormsKer
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsDerivSpanTrdeg
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFreeParAlgIndep
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace SecPointSeparable

theorem isSeparable_of_derivation_eq_zero {K L : Type} [Field K] [Field L] [Algebra K L]
    [Module.Finite K L] (h : ∀ D : Derivation K L L, D = 0) : Algebra.IsSeparable K L := by
  rw [← Algebra.FormallyUnramified.iff_isSeparable]
  refine ⟨⟨fun a b => ?_⟩⟩
  have key : ∀ ω : Ω[L⁄K], ω = 0 := by
    intro ω
    refine (Module.forall_dual_apply_eq_zero_iff L ω).1 fun φ => ?_
    have : φ = 0 := by
      apply (KaehlerDifferential.linearMapEquivDerivation K L).injective
      rw [map_zero]
      exact h _
    rw [this, LinearMap.zero_apply]
  rw [key a, key b]

end SecPointSeparable

open SecPointSeparable in
theorem SecPointSeparable.proof (h₁ : GenericFormsKer.Statement) (h₂ : DerivSpanTrdeg.Statement)
    (h₃ : FreeParAlgIndep.Statement) : SecPointSeparable.Statement := by
  intro k _ _ n e L _ _ _ _ _ x hx hU hT htr
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, x j₀ ≠ 0 := by
    by_contra! h
    simp [h] at hT
  set z : Fin n → L := fun m => x m * (x j₀)⁻¹ with hz
  obtain ⟨r, hre, b, hb⟩ := h₂ k L (Fin n) z e (htr j₀ hj₀)
  have hind := h₃ k n e L x hx hU hT j₀ hj₀ (htr j₀ hj₀)
  refine isSeparable_of_derivation_eq_zero fun D => ?_
  obtain ⟨c, hc'⟩ : ∃ c : _ → L, ∀ j, D (z j) = ∑ m, c m * (b m j : L) := hb (D.restrictScalars k)
  have hlin : ∀ (a : GenParField k e n) (y : L),
      D (algebraMap (GenParField k e n) L a * y) = algebraMap (GenParField k e n) L a * D y := by
    intro a y
    rw [D.leibniz, D.map_algebraMap, smul_zero, add_zero, smul_eq_mul]
  have hDz₀ : D (z j₀) = 0 := by simp only [z, mul_inv_cancel₀ hj₀, Derivation.map_one_eq_zero]
  have hUDz : ∀ i : Fin e,
      ∑ j, algebraMap _ L (genPar k e n (.inl (i, j))) * D (z j) = 0 := fun i => by
    have h0 : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inl (i, j))) * z j = 0 := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hU i, zero_mul]
    have := congrArg D h0
    rw [map_sum, map_zero] at this
    exact (Finset.sum_congr rfl fun j _ => (hlin _ _).symm).trans this
  have hDz : ∀ j, D (z j) = 0 := by
    have key := h₁ (IntermediateField.adjoin k (Set.range z)) L {j : Fin n // j ≠ j₀} e r hre
      (fun p => algebraMap (GenParField k e n) L (genPar k e n (.inl (p.1, p.2.1)))) hind
      (fun m j => b m j.1) c (fun i => ?_)
    · exact fun j => if hj : j = j₀ then hj ▸ hDz₀ else (hc' j).trans (key ⟨j, hj⟩)
    · have := hUDz i
      rw [Fintype.sum_eq_add_sum_subtype_ne _ j₀, hDz₀, mul_zero, zero_add] at this
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hc' j.1]
      rfl
  have hx₀ : D (x j₀) = 0 := by
    have hs : ∑ j, algebraMap (GenParField k e n) L (genPar k e n (.inr j)) * z j = (x j₀)⁻¹ := by
      simp only [z, ← mul_assoc, ← Finset.sum_mul, hT, one_mul]
    have h1 := congrArg D hs

    rw [map_sum, Finset.sum_eq_zero fun j _ => by rw [hlin, hDz, mul_zero], Derivation.leibniz_inv,
    eq_comm, smul_eq_mul, neg_mul, neg_eq_zero, mul_eq_zero] at h1
    exact h1.resolve_left (pow_ne_zero _ (inv_ne_zero hj₀))
  have hxj : ∀ j, D (x j) = 0 := fun j => by
    rw [show x j = z j * x j₀ by simp only [z, mul_assoc, inv_mul_cancel₀ hj₀, mul_one],
      D.leibniz, hx₀, hDz, smul_zero, smul_zero, add_zero]
  exact Derivation.ext_of_adjoin_eq_top (Set.range x) hx (by rintro _ ⟨j, rfl⟩; simpa using hxj j)

end

end GroundTheory.Heights₂.Heights.Vertical
