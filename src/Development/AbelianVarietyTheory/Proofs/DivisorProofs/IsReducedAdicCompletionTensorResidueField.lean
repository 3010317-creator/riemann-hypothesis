module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataOfPrime
public import Mathlib.RingTheory.Derivation.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingQuotientOfDetDerivationUnit
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalFibreIsRegularRingEssFiniteTypeInt
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Lemma
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Mathlib.Tactic.Polynomial.Basic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdicCompletion

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEtaleOfIsEtaleCompletion, Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdicCompletionTensorResidueField

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEtaleOfIsEtaleCompletion =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEtaleOfIsEtaleCompletion", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqBotOfFlatQuotientOfMapMaximalIdeal\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure\npublic import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionUnramifiedNormal\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.AdicCompletion.LocalRing\nimport Mathlib.RingTheory.AdicCompletion.Noetherian\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt\n\n"}
section -- clump:auto
@[expose] public section

open IsLocalRing GlobalTheory.Toroidal GlobalTheory.TorRef TensorProduct

namespace GlobalTheory.NormalBaseChange

theorem exists_etale_of_isEtaleCompletion (A R : Type) [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    [Algebra A R] [IsNoetherianRing A] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R]
    (het : IsEtaleCompletion (algebraMap A R)) (hfu : ((residue R).comp (algebraMap A R)).FormallyUnramified) :
    ∃ g : AdicCompletion (maximalIdeal A) A →+* R, g.comp (algebraMap A _) = algebraMap A R ∧
      @Algebra.Etale _ R _ _ g.toAlgebra := by
  obtain ⟨hflat, hmap, hfin⟩ := het
  set h := algebraMap A R with hh
  let D := AdicCompletion (maximalIdeal A) A
  haveI : IsNoetherianRing D := AdicNoeth.isNoetherianRing_adicCompletion A _
  haveI : IsAdicComplete ((maximalIdeal A).map h) R := by rw [hmap]; infer_instance
  obtain ⟨g, hg⟩ := _root_.GlobalTheory.PowerExtensionEvaluation.exists_extension (maximalIdeal A) h
  letI : Algebra D R := g.toAlgebra
  have hgA : ∀ a, g (algebraMap A D a) = h a := fun a => RingHom.congr_fun hg a
  have hmA : (maximalIdeal D).map (algebraMap D R) = maximalIdeal R := by
    rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
    change (maximalIdeal A).map (g.comp _) = _
    rw [hg, hmap]
  haveI : IsLocalHom (algebraMap D R) := ((local_hom_tfae _).out 1 3).mpr hmA.le
  have hres : ((residue R).comp g).Finite :=
    RingHom.Finite.of_comp_finite (f := algebraMap A D) (by rw [RingHom.comp_assoc, hg]; exact hfin)
  haveI : Module.Finite D (R ⧸ (maximalIdeal D).map (algebraMap D R)) := by
    rw [← RingHom.finite_algebraMap]
    show ((Ideal.Quotient.mk _).comp (algebraMap D R)).Finite
    rwa [hmA]
  haveI : IsHausdorff ((maximalIdeal D).map (algebraMap D R)) R := by rw [hmA]; infer_instance
  haveI : Module.Finite D R := FormalIsogeny.finite_of_finite_quotient_map (maximalIdeal D)
  haveI : Module.Flat D R := by
    refine LocalFlat.flat_of_relationsLift R (I := maximalIdeal D)
      (hmA.le.trans (maximalIdeal_le_jacobson _)) fun n => ?_
    haveI : Module.Flat A R := RingHom.flat_algebraMap_iff.mp hflat
    have fg := (maximalIdeal A).fg_of_isNoetherianRing
    have hkerA : ∀ x : D, AdicCompletion.evalₐ (maximalIdeal A) n x = 0 ↔ x ∈ maximalIdeal D ^ n := by
      intro x
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem A,
        ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval fg, LinearMap.mem_ker]
      constructor
      · intro h0
        rw [← AdicCompletion.factor_evalₐ_eq_eval _ x (by simp), h0, map_zero]
      · intro h0
        rw [← AdicCompletion.factor_eval_eq_evalₐ _ x (by simp), h0, map_zero]
    have hmapn : (maximalIdeal D ^ n).map (algebraMap D R) = (maximalIdeal A ^ n).map (algebraMap A R) := by
      rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, Ideal.map_map]
      change (maximalIdeal A ^ n).map (g.comp _) = _
      rw [hg]
    refine LocalFlat.relationsLift_of_square
      (AdicCompletion.evalₐ (maximalIdeal A) n).toRingHom
      (Ideal.Quotient.mk ((maximalIdeal A ^ n).map (algebraMap A R)))
      (algebraMap _ _) (AdicCompletion.surjective_evalₐ _ n) Ideal.Quotient.mk_surjective ?_ ?_ ?_ ?_
    · ext x
      exact (hkerA x)
    · rw [Ideal.mk_ker, hmapn]
    · ext x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (maximalIdeal A) n x)
      have hx : x - algebraMap A D a ∈ maximalIdeal D ^ n := by
        rw [← hkerA, map_sub, ← ha, AlgHom.commutes, sub_eq_zero]
        rfl
      have hx' : algebraMap D R x - h a ∈ (maximalIdeal A ^ n).map (algebraMap A R) := by
        rw [← hmapn, ← hgA]
        rw [show algebraMap D R x - g (algebraMap A D a) = algebraMap D R (x - algebraMap A D a) from
          (map_sub g _ _).symm]
        exact Ideal.mem_map_of_mem _ hx
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ← ha]
      rwa [Ideal.Quotient.algebraMap_quotient_map_quotient, eq_comm, Ideal.Quotient.eq]
    · rw [RingHom.flat_algebraMap_iff]
      exact Module.Flat.of_linearEquiv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor R (maximalIdeal A ^ n)).toLinearEquiv
  haveI : Algebra.FormallyUnramified D (ResidueField R) := by
    rw [← RingHom.formallyUnramified_algebraMap]
    have e : (algebraMap D (ResidueField R)).comp (algebraMap A D) = (residue R).comp h := by
      rw [← hg]; rfl
    exact RingHom.FormallyUnramified.of_comp (f := algebraMap A D) (by rw [e]; exact hfu)
  haveI : Algebra.FormallyUnramified D R :=
    GlobalTheory.EtaleCompletionNormal.formallyUnramified_of_map_maximalIdeal hmA
  haveI : Algebra.FinitePresentation D R :=
    (Algebra.FinitePresentation.of_finiteType (R := D) (A := R)).1 inferInstance
  exact ⟨g, hg, Algebra.Etale.of_formallyUnramified_of_flat⟩

end GlobalTheory.NormalBaseChange
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEtaleOfIsEtaleCompletion =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdicCompletionTensorResidueField =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdicCompletionTensorResidueField", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedEquationPullbackEtaleOverAffineSpace\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEtaleOfIsEtaleCompletion\nimport Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RegularLocalRegularSequence.RingKrullDimQuotientSpanSingletonAddOne\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory.EtaleCompletionRadical

theorem isRadical_map_of_flat {A B : Type} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    [Module.Flat A B] (I : Ideal A) (hI : I.IsRadical)
    (hfib : ∀ (P : Ideal A) [P.IsPrime], _root_.IsReduced (B ⊗[A] P.ResidueField)) :
    (I.map (algebraMap A B)).IsRadical := by
  classical
  haveI : Finite I.minimalPrimes := (Ideal.finite_minimalPrimes_of_isNoetherianRing A I).to_subtype
  haveI : Fintype I.minimalPrimes := Fintype.ofFinite _
  haveI hpr : ∀ P : I.minimalPrimes, P.1.IsPrime := fun P => P.2.1.1
  have hle : ∀ P : I.minimalPrimes, I ≤ P.1 := fun P => P.2.1.2
  let g : ∀ P : I.minimalPrimes, (A ⧸ I) →ₐ[A] P.1.ResidueField := fun P =>
    Ideal.Quotient.liftₐ I (IsScalarTower.toAlgHom A A P.1.ResidueField) (fun a ha => by
      change algebraMap A P.1.ResidueField a = 0
      exact Ideal.algebraMap_residueField_eq_zero.2 (hle P ha))
  let f : (A ⧸ I) →ₗ[A] ∀ P : I.minimalPrimes, P.1.ResidueField := LinearMap.pi fun P => (g P).toLinearMap
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Ideal.Quotient.eq_zero_iff_mem]
    refine hI (Ideal.sInf_minimalPrimes (I := I) ▸ ?_)
    refine Ideal.mem_sInf.2 fun P hP => ?_
    have h0 := congrFun hy ⟨P, hP⟩
    haveI : P.IsPrime := hP.1.1
    exact Ideal.algebraMap_residueField_eq_zero.1 h0
  have hfB := Module.Flat.lTensor_preserves_injective_linearMap (M := B) f hf
  intro x ⟨n, hn⟩

  have hz : (x ⊗ₜ[A] (1 : A ⧸ I) : B ⊗[A] (A ⧸ I)) = 0 := by
    apply hfB
    rw [map_zero]
    apply (TensorProduct.piRight A A B fun P : I.minimalPrimes => P.1.ResidueField).injective
    rw [map_zero]
    funext P
    simp only [LinearMap.lTensor_tmul, TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, Pi.zero_apply]
    change x ⊗ₜ[A] (g P 1) = 0
    rw [map_one]
    have hnil : IsNilpotent (x ⊗ₜ[A] (1 : P.1.ResidueField) : B ⊗[A] P.1.ResidueField) := by
      refine ⟨n, ?_⟩
      rw [Algebra.TensorProduct.tmul_pow, one_pow]
      change Algebra.TensorProduct.includeLeft (S := A) (x ^ n) = 0
      have hk : I.map (algebraMap A B) ≤ RingHom.ker
          (Algebra.TensorProduct.includeLeft (R := A) (S := A) (A := B) (B := P.1.ResidueField)).toRingHom := by
        rw [Ideal.map_le_iff_le_comap]
        intro a ha
        simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeLeft_apply]
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
          Ideal.algebraMap_residueField_eq_zero.2 (hle P ha), TensorProduct.tmul_zero]
      exact hk hn
    exact hnil.eq_zero
  have := congrArg (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).symm hz
  rw [← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk, AlgEquiv.symm_apply_apply, map_zero,
    Ideal.Quotient.eq_zero_iff_mem] at this
  exact this

end GlobalTheory.EtaleCompletionRadical

namespace GlobalTheory.EtaleCompletionRadical


set_option synthInstance.maxHeartbeats 400000 in
theorem isReduced_adicCompletion_tensor_residueField (A : Type) [CommRing A] [IsLocalRing A]
    [Algebra.EssFiniteType ℤ A] (P : Ideal A) [P.IsPrime] :
    _root_.IsReduced (AdicCompletion (maximalIdeal A) A ⊗[A] P.ResidueField) :=
  by apply GlobalTheory.formalFibre_isReduced_of_field

theorem isRadical_map_of_isEtaleCompletion : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (φ : A →+* R), IsAdicComplete (maximalIdeal R) R →
    IsEtaleCompletion φ → ((residue R).comp φ).FormallyUnramified → ∀ I : Ideal A, I.IsRadical →
    (I.map φ).IsRadical := by
  intro A R _ _ _ _ _ _ φ hc het hfu I hI
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing ℤ A
  haveI := hc
  letI : Algebra A R := φ.toAlgebra
  obtain ⟨g, hg, het'⟩ := GlobalTheory.NormalBaseChange.exists_etale_of_isEtaleCompletion A R het hfu
  letI : Algebra (AdicCompletion (maximalIdeal A) A) R := g.toAlgebra
  have h1 : (I.map (algebraMap A (AdicCompletion (maximalIdeal A) A))).IsRadical :=
    isRadical_map_of_flat I hI fun P _ => isReduced_adicCompletion_tensor_residueField A P
  have h2 := GlobalTheory.EtaleReducedEq.isRadical_map_of_etale (C := R) _ h1
  rw [Ideal.map_map] at h2
  change (I.map (g.comp _)).IsRadical at h2
  rwa [hg] at h2

end GlobalTheory.EtaleCompletionRadical
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedAdicCompletionTensorResidueField =====
