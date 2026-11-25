module

public import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesParameterUnique

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace Gp91

namespace GlobalTheory.DSInequiv

private lemma dsParamUniq_conj_mem {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {P : Mx k r}
    (hu : IsUnit P) (hP : Pᴴ * PI.UpqRep.Jm ε * P = PI.UpqRep.Hpk k r) {g : Mx k r} (hg : g ∈ PI.UpqRep.UJset ε) :
    P⁻¹ * g * P ∈ GG k r := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).mp hu
  have hPi : (P⁻¹)ᴴ * PI.UpqRep.Hpk k r * P⁻¹ = PI.UpqRep.Jm ε := by
    rw [← hP, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd, ← Matrix.mul_assoc, ← conjTranspose_mul,
      Matrix.mul_nonsing_inv _ hd, conjTranspose_one, Matrix.one_mul]
  change (P⁻¹ * g * P)ᴴ * PI.UpqRep.Hpk k r * (P⁻¹ * g * P) = PI.UpqRep.Hpk k r
  calc _ = Pᴴ * (gᴴ * ((P⁻¹)ᴴ * PI.UpqRep.Hpk k r * P⁻¹) * g) * P := by
        simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = Pᴴ * (gᴴ * PI.UpqRep.Jm ε * g) * P := by rw [hPi]
    _ = Pᴴ * PI.UpqRep.Jm ε * P := by rw [hg]
    _ = _ := hP

theorem param_eq_of_equiv : HypsG → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (mu' : Fin (2 * r + k + 1) → ℝ) (R R' : Rep k r), R.IsDG ε mu → R'.IsDG ε mu' → ∀ U : R.H ≃ₗᵢ[ℂ] R'.H, (∀ g ∈ GG k r, ∀ x, U (R.σ g x) = R'.σ g (U x)) → mu = mu' := by
  intro hy k r ε mu mu' R R' hR hR' U hU
  obtain ⟨hm, ⟨P, hP, h⟩, hgp⟩ := hR
  obtain ⟨hm', ⟨Q, hQ, h'⟩, hgp'⟩ := hR'
  obtain ⟨v, hv, hv0⟩ := _root_.GlobalTheory.DSInequiv.exists_kfin R hP h
  have hs := hy.1.2.2.1 k r ε mu R.H R.σ hm ⟨P, hP, h⟩ v hv
  have hs' := _root_.GlobalTheory.DSInequiv.smooth_conj (A := Formalism.REAL.Jm ε) hP.1.1 hP.1.2 hs
  have hdP := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  have hdQ := (Matrix.isUnit_iff_isUnit_det Q).mp hQ.1.1
  have p1 := Matrix.mul_nonsing_inv _ hdP
  have q1 := Matrix.mul_nonsing_inv _ hdQ
  have q2 := Matrix.nonsing_inv_mul _ hdQ
  have p3 := fun B : Mx k r => Matrix.nonsing_inv_mul_cancel_left P B hdP
  have q3 := fun B : Mx k r => Matrix.nonsing_inv_mul_cancel_left Q B hdQ
  have p4 := fun B : Mx k r => Matrix.mul_nonsing_inv_cancel_left P B hdP
  have ha := _root_.GlobalTheory.DSInequiv.cayley_quot hQ.1.1 hP.1.2 hQ.1.2
  have hb := _root_.GlobalTheory.DSInequiv.cayley_quot hP.1.1 hQ.1.2 hP.1.2
  obtain ⟨⟨hone, hmul⟩, -⟩ := h'.2.2.1
  set τ' : Mx k r → (R'.H →L[ℂ] R'.H) := fun g => R'.σ (Q⁻¹ * g * Q) with hτ'
  have hmul' : ∀ a ∈ PI.UpqRep.UJset ε, ∀ b ∈ PI.UpqRep.UJset ε, ∀ x, τ' a (τ' b x) = τ' (a * b) x :=
    fun a ha b hb x => (DFunLike.congr_fun (hmul a ha b hb) x).symm
  have hab : (P * Q⁻¹) * (Q * P⁻¹) = 1 := by simp only [Matrix.mul_assoc, q3, p1]
  have hba : (Q * P⁻¹) * (P * Q⁻¹) = 1 := by simp only [Matrix.mul_assoc, p3, q1]
  let A : R'.H ≃L[ℂ] R'.H := ContinuousLinearEquiv.ofContinuousLinearMap (τ' (P * Q⁻¹)) (τ' (Q * P⁻¹))
    (by ext x; exact (hmul' _ ha _ hb x).trans (by rw [hab, hone]; rfl))
    (by ext x; exact (hmul' _ hb _ ha x).trans (by rw [hba, hone]; rfl))
  have hVA : ∀ g, Formalism.REAL.inUJ ε g → ∀ x, (U.toContinuousLinearEquiv.trans A) (R.σ (P⁻¹ * g * P) x) = τ' g ((U.toContinuousLinearEquiv.trans A) x) := by
    intro g hg x
    have hg' : g ∈ PI.UpqRep.UJset ε := hg
    have hG : P⁻¹ * g * P ∈ GG k r := dsParamUniq_conj_mem hP.1.1 hP.1.2 hg
    show τ' (P * Q⁻¹) (U (R.σ (P⁻¹ * g * P) x)) = τ' g (τ' (P * Q⁻¹) (U x))
    have e : R'.σ (P⁻¹ * g * P) = τ' (Q * P⁻¹ * g * (P * Q⁻¹)) := by
      simp only [hτ', Matrix.mul_assoc, q3, q2, Matrix.mul_one]
    rw [hU _ hG, e, hmul' _ ha _ (_root_.GlobalTheory.DSInequiv.inUJ_mul (_root_.GlobalTheory.DSInequiv.inUJ_mul hb hg') ha), hmul' _ hg' _ ha]
    simp only [Matrix.mul_assoc, q3, p4]
  refine _root_.GlobalTheory.DSInequiv.eq_of_capP mu mu' hm.1 hm'.1 fun Y => ?_
  have e1 := hy.2.2.1 k r ε mu _ _ ⟨P, hP⟩ hgp hm h v hs' Y
  have e2 := hy.2.2.1 k r ε mu' _ _ ⟨P, hP⟩ hgp' hm' h' _ (_root_.GlobalTheory.DSInequiv.smooth_equiv (U.toContinuousLinearEquiv.trans A) hVA hs') Y
  rw [← _root_.GlobalTheory.DSInequiv.actU_equiv (U.toContinuousLinearEquiv.trans A) hVA, e1, map_smul] at e2
  exact smul_left_injective ℂ (by simpa using hv0) e2

end GlobalTheory.DSInequiv

end Gp91
