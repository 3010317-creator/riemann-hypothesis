module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.DirichletPrimeToLPartMulLPowerPart
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.DvrIntClosure
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.SoDefs

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.X


theorem UpperTheory.V.X.So.coefOf :
    ∀ (l : ℕ) [Fact l.Prime] (E : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E], ∃ c : HV.Coef l, ∀ x : PadicAlgCl l, x ∈ c.O ↔ x ∈ E ∧ ‖x‖ ≤ 1 := by
  intro l _ K _
  obtain ⟨h1, h2, -⟩ := UpperTheory.V.abelian₂.dvr_intClosure l K
  let f : K →ₐ[ℤ_[l]] PadicAlgCl l := K.val.restrictScalars ℤ_[l]
  have hf : Function.Injective f := Subtype.val_injective
  let e := (integralClosure ℤ_[l] K).equivMapOfInjective f hf
  refine ⟨⟨(integralClosure ℤ_[l] K).map f, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    Module.Finite.equiv e.toLinearEquiv⟩, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, (_root_.UpperTheory.V.abelian₂.isIntegral_iff_norm_le_one_bis K.val y).1 hy⟩
  · rintro ⟨hx, hn⟩
    exact ⟨⟨x, hx⟩, (_root_.UpperTheory.V.abelian₂.isIntegral_iff_norm_le_one_bis K.val ⟨x, hx⟩).2 hn, rfl⟩
