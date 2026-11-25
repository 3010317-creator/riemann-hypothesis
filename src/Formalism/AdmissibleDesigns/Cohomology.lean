module

public import Formalism.AdmissibleDesigns.Base
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SecondClosedOfFirstClosed
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.CupKillAdm
import Formalism.CharacterColumnKernels.IdempotentNormalForms.GenFin
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalConcreteOf
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SingleEqSmul
import Formalism.CharacterColumnKernels.Statement
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DistinctEigenvalueCornerPerturbationOfBlocks
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Formalism.SharpRestriction.LevelLetterCocycles.GoodCongruenceDataOf
public import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.RingDataOfIdempotents
public import Formalism.SharpRestriction.LevelLetterCocycles.SecondPropositionEveryLocalisation
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.FirstSummandRepresentation
import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
public import Formalism.WachLatticeTwists.RamifiedBlockRings.ChainFromPrimitiveData
public import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation
public import Formalism.WachLatticeTwists.RamifiedBlockRings.LemmaFiveThreeAnyResidueField
public import Formalism.WachLatticeTwists.RamifiedBlockRings.LocalToDisplayFree
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.AbsIrrOfSpan
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.FinrankRangeEq
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.IdempotentImageSurjective
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.RingObjectsExist
public import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.TopLengthBoundViaSplitting
public import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.IdempotentRankOneAtPoint
public import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.SurjectionOfRankOneIdempotent
import Formalism.WachLatticeTwists.SplitClassesAll.Statement
import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Module.Torsion.Prod
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG

theorem exists_ramification (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    (hinj : Function.Injective (algebraMap O O')) [IsLocalHom (algebraMap O O')] :
    ∃ e : ℕ, ∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
      e * IsDiscreteValuationRing.addVal O y := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible O'
  have hφϖ0 : algebraMap O O' ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by rw [h, map_zero]))
  have hφϖnu : ¬ IsUnit (algebraMap O O' ϖ) := fun h => hϖ.not_isUnit (isUnit_of_map_unit _ _ h)
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hφϖ0 hϖ'
  have he0 : e ≠ 0 := by
    rintro rfl
    apply hφϖnu
    rw [hv, pow_zero, mul_one]
    exact v.isUnit
  refine ⟨e, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    simp [he0, ENat.mul_top]
  · obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    have hu : IsDiscreteValuationRing.addVal O' (algebraMap O O' (u : O)) = 0 :=
      IsDiscreteValuationRing.addVal_eq_zero_iff.2 (u.isUnit.map _)
    simp only [map_mul, map_pow, hv, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hu,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, IsDiscreteValuationRing.addVal_uniformizer hϖ,
      IsDiscreteValuationRing.addVal_uniformizer hϖ']
    simp only [zero_add, nsmul_eq_mul, mul_one]
    ring

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical Polynomial

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG

theorem exists_irreducible_big (k : Type) [Field k] [Finite k] (N : ℕ) :
    ∃ f : k[X], f.Monic ∧ Irreducible f ∧ (N : Cardinal) < Cardinal.mk (AdjoinRoot f) := by
  classical
  haveI hKinf : Infinite (AlgebraicClosure k) := by
    first
    | exact inferInstance
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq (AlgebraicClosure k) (N + 1)
  haveI hfd : FiniteDimensional k (IntermediateField.adjoin k (S : Set (AlgebraicClosure k))) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  haveI : Finite (IntermediateField.adjoin k (S : Set (AlgebraicClosure k))) :=
    Module.finite_of_finite k
  obtain ⟨α, hα⟩ : ∃ α : IntermediateField.adjoin k (S : Set (AlgebraicClosure k)),
      IntermediateField.adjoin k {α} = ⊤ := by
    first
    | exact Field.exists_primitive_element_of_finite_top k _
  have hint : IsIntegral k α := Algebra.IsIntegral.isIntegral α
  refine ⟨minpoly k α, minpoly.monic hint, minpoly.irreducible hint, ?_⟩
  have e1 : Cardinal.mk (AdjoinRoot (minpoly k α)) =
      Cardinal.mk (IntermediateField.adjoin k {α}) :=
    Cardinal.mk_congr (IntermediateField.adjoinRootEquivAdjoin k hint).toEquiv
  rw [e1, hα]
  rw [Cardinal.mk_congr IntermediateField.topEquiv.toEquiv]
  have hSF : ∀ x ∈ S, x ∈ IntermediateField.adjoin k (S : Set (AlgebraicClosure k)) :=
    fun x hx => IntermediateField.subset_adjoin k _ hx
  have hle : (S.card : Cardinal) ≤
      Cardinal.mk (IntermediateField.adjoin k (S : Set (AlgebraicClosure k))) := by
    have hinj : Function.Injective
        (fun x : S => (⟨x, hSF x x.2⟩ : IntermediateField.adjoin k (S : Set (AlgebraicClosure k)))) :=
      fun a b h => Subtype.ext (by have h' := congrArg Subtype.val h; exact h')
    simpa using Cardinal.mk_le_of_injective hinj
  rw [hS] at hle
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self N) hle

theorem unram_ext (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (f : O[X])
    (hf : f.Monic) (hirr : Irreducible (f.map (IsLocalRing.residue O))) :
    ∃ (_ : IsDomain (AdjoinRoot f)) (_ : IsDiscreteValuationRing (AdjoinRoot f)),
      Module.Free O (AdjoinRoot f) ∧ Module.Finite O (AdjoinRoot f) ∧
      (∀ y : O, IsDiscreteValuationRing.addVal (AdjoinRoot f) (algebraMap O (AdjoinRoot f) y) =
        IsDiscreteValuationRing.addVal O y) ∧
      Cardinal.mk (IsLocalRing.ResidueField (AdjoinRoot f)) =
        Cardinal.mk (AdjoinRoot (f.map (IsLocalRing.residue O))) := by
  let A := AdjoinRoot f
  let res := IsLocalRing.residue O
  let fb := f.map res
  have : Fact (Irreducible fb) := ⟨hirr⟩
  let F := AdjoinRoot fb
  have hfirr : Irreducible f := hf.irreducible_of_irreducible_map res f hirr
  have hdom : IsDomain A := AdjoinRoot.isDomain_of_prime hfirr.prime
  let pb := AdjoinRoot.powerBasis' hf
  have hfree : Module.Free O A := Module.Free.of_basis pb.basis
  have hfin : Module.Finite O A := pb.finite
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let ψ : A →+* F := AdjoinRoot.lift ((AdjoinRoot.of fb).comp res) (AdjoinRoot.root fb) (by
    rw [← Polynomial.eval₂_map, AdjoinRoot.eval₂_root])
  have hψmk : ∀ p : O[X], ψ (AdjoinRoot.mk f p) = AdjoinRoot.mk fb (p.map res) := by
    intro p
    rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.aeval_eq]
    rfl
  have hres : Function.Surjective res := IsLocalRing.residue_surjective
  have hψs : Function.Surjective ψ := by
    intro z
    obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
    obtain ⟨q, rfl⟩ := Polynomial.map_surjective res hres p
    exact ⟨AdjoinRoot.mk f q, hψmk q⟩
  let ϖ' : A := algebraMap O A ϖ
  have hker : RingHom.ker ψ = Ideal.span {ϖ'} := by
    apply le_antisymm
    · intro a ha
      obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective a
      rw [RingHom.mem_ker, hψmk, AdjoinRoot.mk_eq_zero] at ha
      obtain ⟨qb, hqb⟩ := ha
      obtain ⟨q, rfl⟩ := Polynomial.map_surjective res hres qb
      have h1 : (p - f * q).map res = 0 := by
        rw [Polynomial.map_sub, Polynomial.map_mul, hqb, sub_self]
      have h2 : C ϖ ∣ p - f * q := by
        rw [Polynomial.C_dvd_iff_dvd_coeff]
        intro i
        have h3 : res ((p - f * q).coeff i) = 0 := by
          rw [← Polynomial.coeff_map, h1, Polynomial.coeff_zero]
        rw [IsLocalRing.residue_eq_zero_iff, hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at h3
        exact h3
      obtain ⟨h, hh⟩ := h2
      rw [Ideal.mem_span_singleton]
      refine ⟨AdjoinRoot.mk f h, ?_⟩
      have h4 : AdjoinRoot.mk f p = AdjoinRoot.mk f (p - f * q) := by
        rw [map_sub, map_mul, AdjoinRoot.mk_self, zero_mul, sub_zero]
      rw [h4, hh, map_mul, AdjoinRoot.mk_C]
      rfl
    · rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
      show ψ (AdjoinRoot.of f ϖ) = 0
      rw [AdjoinRoot.lift_of]
      show AdjoinRoot.of fb (res ϖ) = 0
      rw [(IsLocalRing.residue_eq_zero_iff ϖ).mpr hϖ.not_isUnit, map_zero]
  have hmaxk : (RingHom.ker ψ).IsMaximal := RingHom.ker_isMaximal_of_surjective ψ hψs
  have hloc : IsLocalRing A := by
    refine IsLocalRing.of_unique_max_ideal ⟨RingHom.ker ψ, hmaxk, fun M hM => ?_⟩
    letI : Module.Finite O A := hfin
    have h1 : (M.comap (algebraMap O A)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap O A)
        (RingHom.Finite.to_isIntegral (RingHom.finite_algebraMap.mpr inferInstance)) M
    have h2 : ϖ ∈ M.comap (algebraMap O A) := by
      rw [IsLocalRing.eq_maximalIdeal h1]
      exact hϖ.not_isUnit
    have h3 : RingHom.ker ψ ≤ M := by
      rw [hker, Ideal.span_singleton_le_iff_mem]
      exact h2
    exact (hmaxk.eq_of_le hM.ne_top h3).symm
  have hmA : IsLocalRing.maximalIdeal A = Ideal.span {ϖ'} := by
    rw [← hker]
    exact (IsLocalRing.eq_maximalIdeal hmaxk).symm
  have hinj : Function.Injective (algebraMap O A) := FaithfulSMul.algebraMap_injective O A
  have hnf : ¬ IsField A := fun h =>
    IsDiscreteValuationRing.not_isField O (isField_of_isIntegral_of_isField hinj h)
  have hpr : (IsLocalRing.maximalIdeal A).IsPrincipal := ⟨⟨ϖ', hmA⟩⟩
  have hdvr : IsDiscreteValuationRing A := ((IsDiscreteValuationRing.TFAE A hnf).out 1 5).mpr hpr
  have hϖ' : Irreducible ϖ' := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ').mpr hmA
  refine ⟨hdom, hdvr, hfree, hfin, ?_, ?_⟩
  · obtain ⟨e, he⟩ := exists_ramification O A hinj
    have h1 := he ϖ
    rw [IsDiscreteValuationRing.addVal_uniformizer hϖ, mul_one] at h1
    have h2 : IsDiscreteValuationRing.addVal A ϖ' = 1 := IsDiscreteValuationRing.addVal_uniformizer hϖ'
    have h3 : (e : ℕ∞) = 1 := h1.symm.trans h2
    intro y
    rw [he y, h3, one_mul]
  · have e1 : (A ⧸ IsLocalRing.maximalIdeal A) ≃+* (A ⧸ RingHom.ker ψ) :=
      Ideal.quotEquivOfEq (by rw [hmA, hker])
    exact (e1.trans (RingHom.quotientKerEquivOfSurjective hψs)).toEquiv.cardinal_eq

theorem bigResidueExt : StatBigResidueExt := by
  intro O _ _ _ N
  by_cases hk : Finite (IsLocalRing.ResidueField O)
  · obtain ⟨g, hgm, hgi, hgN⟩ := exists_irreducible_big (IsLocalRing.ResidueField O) N
    have hlift : g ∈ Polynomial.lifts (IsLocalRing.residue O) :=
      (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ IsLocalRing.residue_surjective g)
    obtain ⟨f, hfmap, -, hfm⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hgm
    rw [← hfmap] at hgi hgN
    obtain ⟨h1, h2, hfree, hfin, hval, hcard⟩ := unram_ext O f hfm hgi
    exact ⟨AdjoinRoot f, inferInstance, h1, h2, inferInstance, hfree, hfin, hval,
      lt_of_lt_of_eq hgN hcard.symm⟩
  · have hinf : Infinite (IsLocalRing.ResidueField O) := not_finite_iff_infinite.mp hk
    refine ⟨O, inferInstance, inferInstance, inferInstance, Algebra.id O, inferInstance,
      inferInstance, fun y => rfl, ?_⟩
    exact lt_of_lt_of_le (Cardinal.natCast_lt_aleph0 (n := N)) (Cardinal.aleph0_le_mk _)

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

section

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] [Algebra O O'] {X d G : Type} [Fintype d] [DecidableEq d] [Group G] {t : ℕ}
  {bl : d → Fin (t + 1)} {T : Subalgebra O (X → O)} {r : G →* (X → Matrix d d O)} {π : X}
  {χ₁ ε : G →* Oˣ} {g₀ : G} {eB e₁ s : X → Matrix d d O} {D : RingData O X d G t bl}
  {D' : RingData O' X d G t bl}

private theorem blockPoly_map_lemma {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {d : Type*}
    [Fintype d] [DecidableEq d] (e a : Matrix d d A) :
    blockPoly (e.map f) (a.map f) = (blockPoly e a).map f := by
  unfold blockPoly
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

theorem blockPoly_bc (x : X) :
    blockPoly ((bcM O' eB x).map (algebraMap O' (FractionRing O')))
      ((bcM O' eB x * bcR O' r g₀ x * bcM O' eB x + bcM O' s x).map (algebraMap O' (FractionRing O'))) =
    ((blockPoly (eB x) (eB x * r g₀ x * eB x + s x)).map (algebraMap O O')).map
      (algebraMap O' (FractionRing O')) := by
  have h1 : bcM O' eB x = (eB x).map (algebraMap O O') := rfl
  have h3 : bcR O' r g₀ x = (r g₀ x).map (algebraMap O O') := rfl
  have hs : bcM O' s x = (s x).map (algebraMap O O') := rfl
  have h2 : bcM O' eB x * bcR O' r g₀ x * bcM O' eB x + bcM O' s x =
      (eB x * r g₀ x * eB x + s x).map (algebraMap O O') := by
    rw [h1, h3, hs]
    ext i j

    simp [Matrix.mul_apply, Matrix.add_apply, map_sum, map_mul, map_add (f := _)]
  rw [h2, h1, blockPoly_map_lemma, blockPoly_map_lemma]

theorem exists_sigma (hj : Function.Injective (algebraMap O O')) (hX : DistinctEigenvalueCornerPerturbation O T r π t g₀ eB s)
    (hD : RingDef O T r π χ₁ ε g₀ eB e₁ s D)
    (hD' : RingDef O' (bcT O' T) (bcR O' r) π (bcChar O' χ₁) (bcChar O' ε) g₀ (bcM O' eB) (bcM O' e₁)
      (bcM O' s) D') :
    ∃ σ : D'.X' → D.X', (∀ y', D.p (σ y') = D'.p y') ∧
      (∀ y' i, i < t → algebraMap O O' ((D.rr i : D.X' → O) (σ y')) = (D'.rr i : D'.X' → O') y') ∧
      σ D'.π' = D.π' := by
  classical
  have hι'inj : Function.Injective (algebraMap O' (FractionRing O')) :=
    IsFractionRing.injective O' (FractionRing O')
  have hD0 := hD
  have hD'0 := hD'
  dsimp only [RingDef] at hD0 hD'0
  obtain ⟨-, huniq, -, -, hpπ, hrrπ, -⟩ := hD0
  obtain ⟨hfac', -, -, -, hpπ', hrrπ', -⟩ := hD'0
  unfold DistinctEigenvalueCornerPerturbation at hX
  obtain ⟨-, -, -, -, hαX⟩ := hX
  have key : ∀ y' : D'.X', ∃! x' : D.X', D.p x' = D'.p y' ∧
      ∀ i, i < t → algebraMap O O' ((D.rr i : D.X' → O) x') = (D'.rr i : D'.X' → O') y' := by
    intro y'
    have h1 : ((blockPoly (eB (D'.p y')) (eB (D'.p y') * r g₀ (D'.p y') * eB (D'.p y') + s (D'.p y'))).map
        (algebraMap O O')).map (algebraMap O' (FractionRing O')) =
        ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C
          (algebraMap O' (FractionRing O') ((D'.rr i : D'.X' → O') y'))) := by
      rw [← blockPoly_bc]
      exact hfac' y'
    obtain ⟨α, -, hα⟩ := hαX (D'.p y')
    rw [blockPoly_map_lemma] at hα
    obtain ⟨β, -, hβ⟩ := rootsInt O _ t α hα
    have hroot : ∀ i, i < t → ∃ b : O, algebraMap O O' b = (D'.rr i : D'.X' → O') y' := by
      intro i hi
      have h2 := congrArg (Polynomial.eval
        (algebraMap O' (FractionRing O') ((D'.rr i : D'.X' → O') y'))) h1
      rw [hβ] at h2
      simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h2
      have h3 : ∏ k ∈ Finset.range t, (algebraMap O' (FractionRing O') ((D'.rr i : D'.X' → O') y') -
          algebraMap O' (FractionRing O') ((D'.rr k : D'.X' → O') y')) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.2 hi) (sub_self _)
      rw [h3, Finset.prod_eq_zero_iff] at h2
      obtain ⟨j, -, hj0⟩ := h2
      exact ⟨β j, hι'inj (sub_eq_zero.1 hj0).symm⟩
    choose b hb using hroot
    let α' : ℕ → O := fun i => if h : i < t then b i h else 0
    have hα' : ∀ i, i < t → algebraMap O O' (α' i) = (D'.rr i : D'.X' → O') y' := by
      intro i hi
      simp only [α', dite_eq_left hi]
      exact hb i hi
    have hPinj : Function.Injective
        (Polynomial.map ((algebraMap O' (FractionRing O')).comp (algebraMap O O'))) :=
      Polynomial.map_injective _ (hι'inj.comp hj)
    have hP2 : blockPoly (eB (D'.p y')) (eB (D'.p y') * r g₀ (D'.p y') * eB (D'.p y') + s (D'.p y')) =
        ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (α' i)) := by
      apply hPinj
      rw [← Polynomial.map_map, h1]
      simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
        RingHom.comp_apply]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [hα' i (Finset.mem_range.1 hi)]
    have hfacO : blockPoly ((eB (D'.p y')).map (algebraMap O (FractionRing O)))
        ((eB (D'.p y') * r g₀ (D'.p y') * eB (D'.p y') + s (D'.p y')).map (algebraMap O (FractionRing O))) =
        ∏ i ∈ Finset.range t, (Polynomial.X - Polynomial.C (algebraMap O (FractionRing O) (α' i))) := by
      rw [blockPoly_map_lemma, hP2]
      simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
    obtain ⟨x', ⟨hx'1, hx'2⟩, hx'u⟩ := huniq (D'.p y') α' hfacO
    refine ⟨x', ⟨hx'1, fun i hi => by rw [hx'2 i hi, hα' i hi]⟩, ?_⟩
    rintro z ⟨hz1, hz2⟩
    refine hx'u z ⟨hz1, fun i hi => hj ?_⟩
    rw [hz2 i hi, hα' i hi]
  choose σ hσ using fun y' => (key y').exists
  refine ⟨σ, fun y' => (hσ y').1, fun y' i hi => (hσ y').2 i hi, ?_⟩
  refine (key D'.π').unique (hσ D'.π') ⟨by rw [hpπ, hpπ'], fun i hi => ?_⟩
  rw [hrrπ i hi, hrrπ' i hi]
  simp [bcChar]

theorem bcT'_mem (hD : RingDef O T r π χ₁ ε g₀ eB e₁ s D)
    (hD' : RingDef O' (bcT O' T) (bcR O' r) π (bcChar O' χ₁) (bcChar O' ε) g₀ (bcM O' eB) (bcM O' e₁)
      (bcM O' s) D') (σ : D'.X' → D.X') (hσ1 : ∀ y', D.p (σ y') = D'.p y')
    (hσ2 : ∀ y' i, i < t →
      algebraMap O O' ((D.rr i : D.X' → O) (σ y')) = (D'.rr i : D'.X' → O') y')
    {f : D.X' → O} (hf : f ∈ D.T') : (fun y' => algebraMap O O' (f (σ y'))) ∈ D'.T' := by
  dsimp only [RingDef] at hD hD'
  obtain ⟨-, -, hT, -⟩ := hD
  obtain ⟨-, -, hT', -⟩ := hD'
  rw [hT] at hf
  rw [hT']
  induction hf using Algebra.adjoin_induction with
  | mem x hx =>
    apply Algebra.subset_adjoin
    rcases hx with ⟨g, hg, rfl⟩ | ⟨i, hi, rfl⟩
    · refine Or.inl ⟨algebraMap O O' ∘ g, Algebra.subset_adjoin ⟨g, hg, rfl⟩, ?_⟩
      funext y'
      simp [hσ1 y']
    · exact Or.inr ⟨i, hi, funext fun y' => hσ2 y' i hi⟩
  | algebraMap c =>
    convert Subalgebra.algebraMap_mem (Algebra.adjoin O' _) (algebraMap O O' c) using 1
    funext y'
    simp
  | add x y _ _ ihx ihy =>
    convert Subalgebra.add_mem _ ihx ihy using 1
    funext y'
    simp
  | mul x y _ _ ihx ihy =>
    convert Subalgebra.mul_mem _ ihx ihy using 1
    funext y'
    simp

theorem bcR'_mem (hD : RingDef O T r π χ₁ ε g₀ eB e₁ s D)
    (hD' : RingDef O' (bcT O' T) (bcR O' r) π (bcChar O' χ₁) (bcChar O' ε) g₀ (bcM O' eB) (bcM O' e₁)
      (bcM O' s) D') (σ : D'.X' → D.X') (hσ1 : ∀ y', D.p (σ y') = D'.p y')
    (hσ2 : ∀ y' i, i < t →
      algebraMap O O' ((D.rr i : D.X' → O) (σ y')) = (D'.rr i : D'.X' → O') y')
    (κ : FractionRing O →+* FractionRing O')
    (hκ : ∀ y, κ (algebraMap O (FractionRing O) y) = algebraMap O' (FractionRing O') (algebraMap O O' y))
    {a : D.X' → Matrix d d (FractionRing O)} (ha : a ∈ D.R') :
    (fun y' => (a (σ y')).map κ) ∈ D'.R' := by
  have hmem : ∀ f ∈ D.T', (fun y' => algebraMap O O' (f (σ y'))) ∈ D'.T' :=
    fun f hf => bcT'_mem hD hD' σ hσ1 hσ2 hf
  dsimp only [RingDef] at hD hD'
  obtain ⟨-, -, -, -, -, -, hr, hR, -⟩ := hD
  obtain ⟨-, -, -, -, -, -, hr', hR', -⟩ := hD'
  have ha2 := (hR a).1 ha
  refine (hR' _).2 ?_
  simp only [tSpan, Set.mem_setOf_eq] at ha2 ⊢
  obtain ⟨s0, c, hc, rfl⟩ := ha2
  refine ⟨s0, fun g y' => algebraMap O O' (c g (σ y')),
    fun g => hmem _ (hc g), ?_⟩
  funext y'
  ext i j

  simp [Finset.sum_apply, Matrix.sum_apply, map_sum, hr, hr', hσ1, bcR, bcM]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, hκ, hκ, ← IsScalarTower.algebraMap_apply O O' (FractionRing O')]

end

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem relMap_mul {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] {l m n : Type*} [Fintype l]
    [Fintype m] [Fintype n] (C : Matrix l m O) (B : Matrix m n O) (v : n → M) :
    relMap O M (C * B) v = relMap O M C (relMap O M B v) := by
  ext i
  simp only [relMap, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_apply, Finset.sum_smul,
    Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem ker_eq_of_factor {O M : Type*} [CommRing O] [AddCommGroup M] [Module O M] {m n : Type*}
    [Fintype m] [Fintype n] (A : Matrix m n O) (B : Matrix n n O) (C : Matrix m n O)
    (C' : Matrix n m O) (h1 : A = C * B) (h2 : B = C' * A) :
    LinearMap.ker (relMap O M A) = LinearMap.ker (relMap O M B) := by
  ext v
  simp only [LinearMap.mem_ker]
  constructor
  · intro hv
    rw [h2, relMap_mul, hv, map_zero]
  · intro hv
    rw [h1, relMap_mul, hv, map_zero]

private theorem sum_extend_embedding_zero_eq_sum {α β M : Type*} [Fintype α] [Fintype β] [AddCommMonoid M]
    (f : α ↪ β) (φ : α → M) : ∑ l, Function.extend f φ 0 l = ∑ j, φ j := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map f)), Finset.sum_map]
  · simp only [f.injective.extend_apply]
  · intro l _ hl
    rw [Function.extend_apply']
    · rfl
    · rintro ⟨j, rfl⟩
      exact hl (Finset.mem_map_of_mem _ (Finset.mem_univ j))

theorem exists_square {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq n] (A : Matrix m n O) :
    ∃ (B : Matrix n n O) (C : Matrix m n O) (C' : Matrix n m O), A = C * B ∧ B = C' * A := by
  classical
  obtain ⟨k, b⟩ := Submodule.basisOfPid (Pi.basisFun O n) (Submodule.span O (Set.range A))
  have hk : Fintype.card (Fin k) ≤ Fintype.card n := by
    have h := Submodule.finrank_le (Submodule.span O (Set.range A))
    rw [Module.finrank_eq_card_basis b, Module.finrank_fintype_fun_eq_card] at h
    exact h
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le hk
  have hA : ∀ i, A i ∈ Submodule.span O (Set.range A) := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hb : ∀ j, ∃ w : m → O, ∑ i, w i • A i = (b j : n → O) := fun j =>
    (Submodule.mem_span_range_iff_exists_fun O).1 (b j).2
  choose w hw using hb
  refine ⟨Function.extend f (fun j => (b j : n → O)) 0,
    fun i => Function.extend f (fun j => b.repr ⟨A i, hA i⟩ j) 0,
    Function.extend f w 0, ?_, ?_⟩
  · ext i c
    erw [Matrix.mul_apply]
    have hterm : ∀ l, Function.extend f (fun j => b.repr ⟨A i, hA i⟩ j) 0 l *
        Function.extend f (fun j => (b j : n → O)) 0 l c =
        Function.extend f (fun j => b.repr ⟨A i, hA i⟩ j * (b j : n → O) c) 0 l := by
      intro l
      by_cases hl : ∃ j, f j = l
      · obtain ⟨j, rfl⟩ := hl
        simp only [f.injective.extend_apply]
      · simp only [Function.extend_apply' _ _ _ hl, Pi.zero_apply, zero_mul]
    simp_rw [hterm]
    rw [sum_extend_embedding_zero_eq_sum]
    have h := congrArg (fun x : Submodule.span O (Set.range A) => (x : n → O) c)
      (b.sum_repr ⟨A i, hA i⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    exact h.symm
  · ext l c
    erw [Matrix.mul_apply]
    by_cases hl : ∃ j, f j = l
    · obtain ⟨j, rfl⟩ := hl
      simp only [f.injective.extend_apply]
      have h := congrFun (hw j) c
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
      exact h.symm
    · simp [Function.extend_apply' _ _ _ hl]

theorem kerBc : StatKerBc := by
  intro O O' _ _ _ _ _ _ _ e he m n _ _ _ A
  obtain ⟨B, C, C', h1, h2⟩ := exists_square A
  let j : O →+* O' := algebraMap O O'
  have h1' : A.map j = C.map j * B.map j := by rw [← Matrix.map_mul, ← h1]
  have h2' : B.map j = C'.map j * A.map j := by rw [← Matrix.map_mul, ← h2]
  rw [ker_eq_of_factor A B C C' h1 h2, ker_eq_of_factor (A.map j) (B.map j) (C.map j) (C'.map j) h1' h2']
  have e1 := lenKer O n B
  have e2 := lenKer O' n (B.map j)
  unfold matQ at e1 e2
  rw [e1, e2, ← he]
  congr 1
  exact (RingHom.map_det j B).symm

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

theorem exists_kappa {O : Type} [CommRing O] [IsDomain O] {F : Type} [Field F] (f : O →+* F)
    (hf : Function.Injective f) :
    ∃ κ : FractionRing O →+* F, ∀ y, κ (algebraMap O (FractionRing O) y) = f y :=
  ⟨IsFractionRing.lift hf, IsFractionRing.lift_algebraMap hf⟩

section

variable {O O' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing O'] [IsDomain O']
  [IsDiscreteValuationRing O'] {X d G : Type} [Fintype d] [DecidableEq d] [Group G] {t : ℕ}
  {bl : d → Fin (t + 1)}

def bcHom (D : RingData O X d G t bl) (D' : RingData O' X d G t bl) (σ : D'.X' → D.X')
    (κ : FractionRing O →+* FractionRing O')
    (h : ∀ a ∈ D.R', (fun y' => (a (σ y')).map κ) ∈ D'.R') : D.R' →+* D'.R' :=
  RingHom.codRestrict ((RingHom.pi fun y' => κ.mapMatrix.comp
    (Pi.evalRingHom (fun _ : D.X' => Matrix d d (FractionRing O)) (σ y'))).comp D.R'.val.toRingHom) D'.R'
    (fun a => h a.1 a.2)

end

theorem relMap_ev {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' d : Type} [Fintype d]
    [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) (x' : X') {m g : Type}
    [Fintype m] [Fintype g] (P : Matrix m g R') (v : g → EvalSp O d R' x') (i : m) (a : d) :
    relMap (FractionRing O) (EvalSp O d R' x') P v i a =
      ∑ q, ∑ b, (P i q).1 x' a b * (v q b : FractionRing O) := by
  let evA : EvalSp O d R' x' →+ FractionRing O :=
    { toFun := fun w => w a, map_zero' := rfl, map_add' := fun _ _ => rfl }
  show evA (∑ q, P i q • v q) = _

  rw [map_sum]
  rfl

theorem span_single {R : Type*} [Ring R] {m g : Type} [Fintype m] [Fintype g] [DecidableEq g]
    (Θ : Matrix m g R) :
    Submodule.span R (Set.range fun j : g => (relSpan Θ).mkQ (Pi.single j (1 : R))) = ⊤ := by
  refine eq_top_iff.mpr fun z _ => ?_
  obtain ⟨w, rfl⟩ := (relSpan Θ).mkQ_surjective z
  have h : w = ∑ j, w j • (Pi.single j (1 : R) : g → R) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]

  rw [h, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem moduleBc : StatModuleBc := by
  intro O O' _ _ _ _ _ _ _ _ _ e he X _ d G _ _ _ t bl T r π χ₁ ε g₀ eB e₁ s hX D D' hD hD' _ _ _
    NN _ _ g n hn
  have hj : Function.Injective (algebraMap O O') := FaithfulSMul.algebraMap_injective O O'
  have hι' : Function.Injective (algebraMap O' (FractionRing O')) :=
    IsFractionRing.injective O' (FractionRing O')
  obtain ⟨κ, hκ⟩ := exists_kappa ((algebraMap O' (FractionRing O')).comp (algebraMap O O')) (hι'.comp hj)
  have hκ' : ∀ y, κ (algebraMap O (FractionRing O) y) =
      algebraMap O' (FractionRing O') (algebraMap O O' y) := hκ
  obtain ⟨σ, hσ1, hσ2, hσπ⟩ := exists_sigma hj hX hD hD'
  have hmem : ∀ a ∈ D.R', (fun y' => (a (σ y')).map κ) ∈ D'.R' :=
    fun a ha => bcR'_mem hD hD' σ hσ1 hσ2 κ hκ' ha
  let bc : D.R' →+* D'.R' := bcHom D D' σ κ hmem
  have hbc : ∀ (a : D.R') y', (bc a).1 y' = (a.1 (σ y')).map κ := fun a y' => rfl

  have hblk : ∀ (a : D.R') k, D'.ρk k (bc a) = (D.ρk k a).map (algebraMap O O') := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17, h18, -⟩ := hD
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h17', h18', -⟩ := hD'
    intro a k
    have h1 : D'.ρπ (bc a) = (D.ρπ a).map (algebraMap O O') := by
      ext u v
      apply hι'
      have e1 := congrFun (congrFun (h17' (bc a)) u) v
      have e2 := congrFun (congrFun (h17 a) u) v
      simp only [Matrix.map_apply] at e1 e2
      rw [e1, hbc, hσπ, Matrix.map_apply, ← e2, hκ']
      rfl
    rw [← h18', h1, ← h18]
    rfl
  obtain ⟨m, P, ⟨eq⟩⟩ := finPres D.R' NN g n hn
  let P' : Matrix (Fin m) (Fin g) D'.R' := P.map bc
  refine ⟨Coker P', inferInstance, inferInstance,
    fun j => (relSpan P').mkQ (Pi.single j (1 : D'.R')), span_single P', ?_, ?_⟩
  · intro Z hφ y' hy'
    obtain ⟨φ, hφ0⟩ := hφ (σ y') (by rw [hσ1]; exact hy')
    let ψ : Coker P →ₗ[D.R'] EvalSp O d D.R' (σ y') := φ ∘ₗ eq.symm.toLinearMap
    have hψ : ψ ≠ 0 := by
      intro h
      apply hφ0
      ext z
      have hz := LinearMap.congr_fun h (eq z)
      simpa [ψ] using hz
    let v := homEquiv (O := FractionRing O) P ψ
    have hv0 : v ≠ 0 := fun h => hψ ((LinearEquiv.map_eq_zero_iff _).mp h)
    let v' : Fin g → EvalSp O' d D'.R' y' := fun i a => κ ((v : Fin g → EvalSp O d D.R' (σ y')) i a)
    have hv' : v' ∈ LinearMap.ker (relMap (FractionRing O') (EvalSp O' d D'.R' y') P') := by
      rw [LinearMap.mem_ker]
      funext i
      funext a
      have h1 := congrFun (congrFun (LinearMap.mem_ker.mp v.2) i) a
      have h2 : ∑ q, ∑ b, (P i q).1 (σ y') a b *
          ((v : Fin g → EvalSp O d D.R' (σ y')) q b : FractionRing O) = 0 := by
        rw [← relMap_ev]
        exact h1
      rw [relMap_ev]
      show _ = (0 : FractionRing O')
      have h3 := congrArg κ h2

      rw [map_zero, map_sum] at h3
      rw [← h3]
      refine Finset.sum_congr rfl fun q _ => ?_

      rw [map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul]
      rfl
    refine ⟨(homEquiv (O := FractionRing O') P').symm ⟨v', hv'⟩, fun h => hv0 ?_⟩
    have h4 : (⟨v', hv'⟩ : LinearMap.ker (relMap (FractionRing O') (EvalSp O' d D'.R' y') P')) = 0 :=
      (LinearEquiv.map_eq_zero_iff _).mp h
    have h5 : v' = 0 := congrArg Subtype.val h4
    apply Subtype.ext
    funext i a
    have h6 : κ ((v : Fin g → EvalSp O d D.R' (σ y')) i a) = 0 := congrFun (congrFun h5 i) a
    exact (map_eq_zero κ).mp h6
  · intro k
    have a1 := kerHomRect D.R' O (Fin m) (Fin g) {a // bl a = k} (D.ρk k).toRingHom P
    have a2 := (LinearEquiv.congrLeft (LatQ O {a // bl a = k} (D.ρk k).toRingHom) O eq).length_eq
    have a3 := kerHomRect D'.R' O' (Fin m) (Fin g) {a // bl a = k} (D'.ρk k).toRingHom P'
    have a4 := kerBc O O' e he (Fin m × {a // bl a = k}) (Fin g × {a // bl a = k})
      (fun p q => (D.ρk k).toRingHom (P p.1 q.1) p.2 q.2)
    have a5 : (Matrix.map (fun (p : Fin m × {a // bl a = k}) (q : Fin g × {a // bl a = k}) =>
        (D.ρk k).toRingHom (P p.1 q.1) p.2 q.2) (algebraMap O O')) =
        fun p q => (D'.ρk k).toRingHom (P' p.1 q.1) p.2 q.2 := by
      funext p q
      show algebraMap O O' (D.ρk k (P p.1 q.1) p.2 q.2) = D'.ρk k (bc (P p.1 q.1)) p.2 q.2
      rw [hblk]
      rfl
    rw [a5] at a4
    exact a3.symm.trans (a4.trans (by rw [a1, a2]))

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

theorem split_ext {O : Type} [CommRing O] [IsDomain O] {F : Type} [Field F] (f : O →+* F)
    (hf : Function.Injective f) (P : Polynomial O)
    (h : (P.map (algebraMap O (FractionRing O))).Splits) : (P.map f).Splits := by
  have hg : (IsFractionRing.lift hf : FractionRing O →+* F).comp (algebraMap O (FractionRing O)) = f := by
    ext y
    exact IsFractionRing.lift_algebraMap hf y
  rw [← hg, ← Polynomial.map_map]
  exact h.map _

theorem blockPoly_separable_splits {O : Type} (O' : Type) [CommRing O] [IsDomain O] [CommRing O'] [IsDomain O']
    [Algebra O O'] [FaithfulSMul O O'] {X : Type} {T : Subalgebra O (X → O)} {d : Type} [Fintype d]
    [DecidableEq d] {G : Type} [Group G] {r : G →* (X → Matrix d d O)} {π : X} {t : ℕ} {g₀ : G}
    {eB s : X → Matrix d d O} (h : DistinctEigenvalueCornerPerturbation O T r π t g₀ eB s) :
    (∀ x, (blockPoly ((eB x).map (algebraMap O (FractionRing O)))
      ((eB x * r g₀ x * eB x + s x).map (algebraMap O (FractionRing O)))).Separable) ∧
    (∀ x, ((blockPoly (eB x) (eB x * r g₀ x * eB x + s x)).map
      ((algebraMap O' (FractionRing O')).comp (algebraMap O O'))).Splits) := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · obtain ⟨α, hα, he⟩ := h.2.2.2.2 x
    rw [he]
    exact Polynomial.separable_prod_X_sub_C_iff.2 hα
  · obtain ⟨α, hα, he⟩ := h.2.2.2.2 x
    have hinj : Function.Injective ((algebraMap O' (FractionRing O')).comp (algebraMap O O')) := by
      rw [RingHom.coe_comp]
      exact (IsFractionRing.injective O' (FractionRing O')).comp
        (FaithfulSMul.algebraMap_injective O O')
    apply split_ext ((algebraMap O' (FractionRing O')).comp (algebraMap O O')) hinj
    rw [blockPoly_map, he]
    first
      | exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _

theorem lemma_five_three_extension_of_module (hM : StatModuleBc) : LemmaFiveThreeOverExtension := by
  intro O _ _ _ X _ d G _ _ _ t ht bl T r π χ₁ ε g₀ eB e₁ s hP hA hI hX D hD _ _ Z NN _ _ g n hn hφ
    O' _ _ _ _ _ _ e he hk
  obtain ⟨hsep, hspl⟩ := blockPoly_separable_splits O' hX
  obtain ⟨cP, cA, cI, cX, cv⟩ := stageC O O' e he X T d G r π t bl χ₁ ε hP hA eB e₁ hI g₀ s hX.1 hX.2.1
    hX.2.2.1 hX.2.2.2.1 hsep hspl
  obtain ⟨D', hD', ⟨i1, i2, i3, i4, i5⟩, i3', hT⟩ := ring_objects_exist O' X (bcT O' T) d G (bcR O' r) π t ht bl _ _
    cP cA _ _ cI g₀ _ cX
  obtain ⟨NN', _, _, n', hn', hφ', hlen⟩ := hM O O' e he X d G t bl T r π χ₁ ε g₀ eB e₁ s hX D D'
    hD hD' NN g n hn
  have hpπ : D'.p D'.π' = π := by
    obtain ⟨-, -, -, -, h, -⟩ := hD'
    exact h
  have h1 := lemma_five_three_holds O' X d G t ht bl (bcT O' T) D' hT Z NN' g n' hn' (hφ' Z hφ) hk
  rw [hpπ, cv Z] at h1
  simp only [hlen] at h1
  rw [← Finset.mul_sum] at h1
  have he0 : (e : ℕ∞) ≠ 0 := by
    intro h0
    have h2 := he 0
    rw [map_zero, h0, zero_mul] at h2
    simp at h2
  exact (ENat.mul_le_mul_left_iff he0 (ENat.natCast_ne_top e)).mp h1

theorem any_residue_field_of_module_baseChange_of_big_residue_ext (hM : StatModuleBc) (hE : StatBigResidueExt) : LemmaFiveThreeAnyResidueField := by
  intro O _ _ _ X _ d G _ _ _ t ht bl T r π χ₁ ε g₀ eB e₁ s hP hA hI hX D hD _ _ Z NN _ _ g n hn hφ
  obtain ⟨O', _, _, _, _, _, _, he, hk⟩ := hE O (g * Fintype.card d)
  exact lemma_five_three_extension_of_module hM O X d G t ht bl T r π χ₁ ε g₀ eB e₁ s hP hA hI hX D hD Z NN g n hn hφ O' 1
    (fun y => by rw [he y, Nat.cast_one, one_mul]) hk

theorem lemma_five_three_any_residue_field : LemmaFiveThreeAnyResidueField := any_residue_field_of_module_baseChange_of_big_residue_ext moduleBc bigResidueExt

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.RepresentationBoundsCohomology.BR

theorem free_of_bound (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X X' : Type)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (Z : Set X) (p : X' → X) (q : ℕ)
    (b : Fin q → (X' → O)) (d : Type) [Fintype d] [DecidableEq d]
    (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsNoetherian R' R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (G : Type) [Group G] (r : G →* R') (χ : G →* Tcˣ) (E e₁ : R') (δ : Tc)
    (π' : X') (ρπ : R' →ₐ[O] Matrix d d O) (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (sE : Finset G) (tE : G → Tc) (δO : O)
    (hR : RingTop O X X' T T' p q b d R' Tc G r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hB : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j : ℕ → ℕ)
      (Kc : ∀ l, Fin (j (colIdx l)) → G → R') (k0 : ι → G → R'),
      (∀ x', p x' ∉ Z → ∃ φ : ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[R']
        EvalSp O d R' x', φ ≠ 0) →
      vcc T Z (p π') ≤ ∑ k : Fin (t + 1), Module.length O
        (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[R'] blockRestrictedRepresentationType bl ρk k)) :
    LocalToDisplayFree O X X' T Z p d R' Tc G r χ E e₁ δ π' t ht bl ρk δO := by
  obtain ⟨ha, hb, hc, hEE, hee, hpts, hρπ, hbl, hsurj, hblk, hcard1, hEsum, hE0, hδ0, hτ0, hne, hC,
    hOne⟩ := hR
  intro ι _ _ colIdx hinj D j e' Kc k0 hoff ℓ cB what₂ qs deg s vhE H0 Sha hk0
    cols eO vδ N h0 L _ _ _ tens v₁ κ HcG Hc F Vo VS Io IS ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ lam Cs _ _
    cls pr Fs Im cT I γQ ζ ζO nQ u hIn0 hInC hIn1
  refine top_length_bound_via_splitting O X X' T T' Z p q b ha (fun x _ => hb x) d R' hc Tc G r χ E e₁ δ ι colIdx hinj
    D j e' Kc k0 hEE hee ?_ π' ρπ hρπ t ht bl hbl ρk hsurj hblk ?_ hcard1
    sE tE δO ℓ cB what₂ qs deg s vhE H0 Sha hEsum hk0
    L tens v₁ κ HcG Hc F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂ inc π γ lam Cs cls pr Fs Im
    cT I γQ ζ ζO nQ u hE0 hδ0 hτ0 hne hIn0 ?_ ?_
  · intro x' hx'
    obtain ⟨δx, h1, h2, h3, h4⟩ := hpts x'
    exact ⟨δx, h1, h2, h3, h4, (hoff x' hx').1, (hoff x' hx').2⟩
  · refine hB ι colIdx D j Kc k0 fun x' hx' => ?_
    obtain ⟨δx, h1, h2, h3, h4⟩ := hpts x'
    exact columnJ R' Tc (FractionRing O) (EvalSp O d R' x') G r χ E e₁ δ ι (fun l => D (colIdx l))
      (fun l => j (colIdx l)) Kc k0 hEE hee δx h1 h2 h3 h4 (hoff x' hx').1 (hoff x' hx').2
  · intro c hc2
    obtain ⟨h1, h2, h3, h4⟩ := hC c hc2
    exact ⟨h1, h2, h3, h4, (hInC c hc2).1, (hInC c hc2).2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hOne
    exact ⟨h1, h2, h3, h4, hIn1⟩

theorem displayFree (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X : Type) [Fintype X]
    (T : Subalgebra O (X → O)) (d : Type) [Fintype d] [DecidableEq d] (G : Type) [Group G]
    (r₀ : G →* (X → Matrix d d O)) (π : X) (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1)) (χ₁ ε : G →* Oˣ)
    (hP : PrimHyp O T r₀ π bl χ₁ ε)
    (hA : AbsIrr (fun g => ((r₀ g π).toSquareBlock bl 0).map (IsLocalRing.residue O)))
    (eB e₁ : X → Matrix d d O) (hI : IdemHyp O T r₀ π bl eB e₁) (g₀ : G) (s : X → Matrix d d O)
    (hX : DistinctEigenvalueCornerPerturbation O T r₀ π t g₀ eB s) (D : RingData O X d G t bl)
    (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s D) [IsNoetherian D.R' D.R']
    [∀ x', IsScalarTower D.T' D.R' (EvalSp O d D.R' x')] [∀ k, SMulCommClass D.R' O (blockRestrictedRepresentationType bl D.ρk k)]
    [∀ k, IsScalarTower D.T' D.R' (blockRestrictedRepresentationType bl D.ρk k)] [∀ k, IsScalarTower O D.R' (blockRestrictedRepresentationType bl D.ρk k)]
    (hT : D.Top T ht) (Z : Set X) :
    LocalToDisplayFree O X D.X' T Z D.p d D.R' D.T' G D.r D.χ D.E D.e₁ D.δ D.π' t ht bl D.ρk D.δO := by
  have hpπ : D.p D.π' = π := by
    obtain ⟨-, -, -, -, h, -⟩ := hD
    exact h
  refine free_of_bound O X D.X' T D.T' Z D.p D.q D.b d D.R' D.T' G D.r D.χ D.E D.e₁ D.δ D.π' D.ρπ t ht bl
    D.ρk D.sE D.tE D.δO hT fun ι _ _ colIdx Dd j Kc k0 hφ => ?_
  set_option synthInstance.maxHeartbeats 400000 in
   obtain ⟨g, n, hn⟩ := Module.Finite.exists_fin (R := D.R')
    (M := ColNNJ D.r D.χ D.E D.e₁ D.δ (fun l => Dd (colIdx l)) (fun l => j (colIdx l)) Kc k0)
  rw [hpπ]
  exact lemma_five_three_any_residue_field O X d G t ht bl T r₀ π χ₁ ε g₀ eB e₁ s hP hA hI hX D hD Z _ g n hn hφ

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Matrix Formalism.RepresentationBoundsCohomology.ringDataObjects Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities Formalism.NG Formalism.MainNotions.N.RepresentationBoundsCohomology

variable {D : D7} (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem normalized_ring_data (hN : NormAt D.nd r ρ π)
    (hG1 : ∀ (γ : GE D.nd) (k : ℕ), (fun x : D.nd.X i => ((rO D.nd i r x γ).charpolyRev).coeff k) ∈ D.nd.T i)
    (hres : Submodule.span (kk D.nd i)
      (Set.range (mapM (IsLocalRing.residue (D.nd.O i)) (rhoO D.nd i ρ π))) = ⊤)
    (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hI : IdemHyp (D.nd.O i) (D.nd.T i) (repX D.nd r) π (blk D.R) eB e₁)
    (hX : DistinctEigenvalueCornerPerturbation (D.nd.O i) (D.nd.T i) (repX D.nd r) π D.R.t g0 eB s) :
    ∃ Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (blk D.R),
      RingDef (D.nd.O i) (D.nd.T i) (repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd ∧
      vcc (D.nd.T i) (D.nd.Z i : Set (D.nd.X i)) (Dd.p Dd.π') =
        Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ∧
      ∃ (_ : IsNoetherian Dd.R' Dd.R')
        (_ : ∀ x', IsScalarTower Dd.T' Dd.R' (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'))
        (_ : ∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (blk D.R) Dd.ρk k))
        (_ : ∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (blk D.R) Dd.ρk k))
        (_ : ∀ k, IsScalarTower (D.nd.O i) Dd.R' (blockRestrictedRepresentationType (blk D.R) Dd.ρk k)),
        Dd.Top (D.nd.T i) (one_le_letterBlockLength D.R) ∧
        ∀ [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
          [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [TopologicalSpace Dd.R']
          [IsTopologicalAddGroup Dd.R'] [ContinuousConstSMul (D.nd.O i) Dd.R'] [ContinuousMul Dd.R'],
          RealDisplayAllK (D.nd.l i) (D.nd.O i) (D.nd.X i) Dd.X' (D.nd.Z i : Set (D.nd.X i)) Dd.p (Fin D.R.nV)
            Dd.R' Dd.T' D.host.E D.nd.Om Dd.r Dd.χ Dd.E Dd.e₁ D.R.t (one_le_letterBlockLength D.R) (blk D.R) Dd.ρk Dd.δO
            (epsU D.nd i) g0 (Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)) := by
  obtain ⟨Dd, hD, ⟨i1, i2, -, i4, i5⟩, i3, hT⟩ := ring_objects_exist (D.nd.O i) (D.nd.X i) (D.nd.T i) (Fin D.R.nV) (GE D.nd)
    (repX D.nd r) π D.R.t (one_le_letterBlockLength D.R) (blk D.R) (chiU D.nd i 1) (epsU D.nd i) (primHyp_of D.nd r ρ π hN hG1)
    (absIrr_of_res D.nd r ρ π hN hres) eB e₁ hI g0 s hX
  have hFree := fun Z => displayFree (D.nd.O i) (D.nd.X i) (D.nd.T i) (Fin D.R.nV) (GE D.nd) (repX D.nd r) π D.R.t
    (one_le_letterBlockLength D.R) (blk D.R) (chiU D.nd i 1) (epsU D.nd i) (primHyp_of D.nd r ρ π hN hG1)
    (absIrr_of_res D.nd r ρ π hN hres) eB e₁ hI g0 s hX Dd hD hT Z
  have hp : Dd.p Dd.π' = π := by
    obtain ⟨-, -, -, -, h, -⟩ := hD
    exact h
  have hv : vcc (D.nd.T i) (D.nd.Z i : Set (D.nd.X i)) (Dd.p Dd.π') =
      Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) := by
    rw [hp, Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.length_ccAt]
  refine ⟨Dd, hD, hv, i1, i2, i3, i4, i5, hT, ?_⟩
  intro _ _ _ _ _ _ _
  exact realDisplayAllK_of (D.nd.l i) (D.nd.O i) (D.nd.X i) Dd.X' (D.nd.Z i : Set (D.nd.X i)) Dd.p (Fin D.R.nV)
    Dd.R' Dd.T' D.host.E D.nd.Om Dd.r Dd.χ Dd.E Dd.e₁ Dd.δ D.R.t (one_le_letterBlockLength D.R) (blk D.R) Dd.ρk Dd.δO
    (epsU D.nd i) g0 _ (D.nd.T i) Dd.T' Dd.q Dd.b Dd.π' Dd.ρπ Dd.sE Dd.tE (chiU D.nd i 1 g0) hT
    (hFree (D.nd.Z i : Set (D.nd.X i))) (Formalism.RepresentationBoundsCohomology.SF.deltaO_eq hD) hv.symm

end Formalism.MainNotions.N.K

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

namespace Formalism.MainNotions.N.KDim

open Formalism.MainNotions.N.KHf

section Trans

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  (ρ : Representation O Γ V)

def cobK : V →ₗ[FractionRing O] (Γ → V) where
  toFun v γ := ρ γ v - v
  map_add' u v := by
    funext γ
    simp only [map_add (f := _), Pi.add_apply]
    abel
  map_smul' k v := by
    funext γ
    simp only [Pi.smul_apply, RingHom.id_apply, smul_sub]
    rw [smulK (ρ γ) k v]

def fwd : ↥(finZ e PD ρ ι) →ₛₗ[(e : FractionRing O →+* LL)] ↥(finiteCocycles PD (repL e ρ ι)) where
  toFun c := ⟨fun g => (c.1 (ι g) : TrV e V), c.2⟩
  map_add' _ _ := rfl
  map_smul' k c := by
    apply Subtype.ext
    funext g
    show k • c.1 (ι g) = e.symm (e k) • c.1 (ι g)
    rw [RingEquiv.symm_apply_apply]

variable {ι} (hι : Function.Bijective ι)
include hι

def bwd : ↥(finiteCocycles PD (repL e ρ ι)) →ₛₗ[(e.symm : LL →+* FractionRing O)] ↥(finZ e PD ρ ι) where
  toFun c := ⟨fun γ => (c.1 ((Equiv.ofBijective ι hι).symm γ) : V), by
    show (fun g => (c.1 ((Equiv.ofBijective ι hι).symm (ι g)) : TrV e V)) ∈ finiteCocycles PD (repL e ρ ι)
    have h : (fun g => (c.1 ((Equiv.ofBijective ι hι).symm (ι g)) : TrV e V)) = c.1 := by
      funext g
      have : (Equiv.ofBijective ι hι).symm (ι g) = g := (Equiv.ofBijective ι hι).symm_apply_apply g
      rw [this]
    rw [h]
    exact c.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem bwd_fwd (c : ↥(finZ e PD ρ ι)) : bwd e PD ρ hι (fwd e PD ι ρ c) = c := by
  apply Subtype.ext
  funext γ
  exact congrArg c.1 ((Equiv.ofBijective ι hι).apply_symm_apply γ)

theorem fwd_bwd (c : ↥(finiteCocycles PD (repL e ρ ι))) : fwd e PD ι ρ (bwd e PD ρ hι c) = c := by
  apply Subtype.ext
  funext g
  exact congrArg c.1 ((Equiv.ofBijective ι hι).symm_apply_apply g)

theorem mem_cob_iff (c : ↥(finZ e PD ρ ι)) :
    c.1 ∈ LinearMap.range (cobK ρ) ↔ (fwd e PD ι ρ c).1 ∈ B1 (repL e ρ ι) := by
  rw [B1, LinearMap.mem_range, LinearMap.mem_range]
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(show TrV e V from v), ?_⟩
    funext g
    exact congrFun hv (ι g)
  · rintro ⟨w, hw⟩
    refine ⟨(show V from w), ?_⟩
    funext γ
    obtain ⟨g, rfl⟩ := hι.2 γ
    exact congrFun hw g

def fwdQ : (↥(finZ e PD ρ ι) ⧸ (LinearMap.range (cobK ρ)).comap (finZ e PD ρ ι).subtype) →ₛₗ[(e : FractionRing O →+* LL)]
    FiniteCohomology PD (repL e ρ ι) :=
  Submodule.mapQ ((LinearMap.range (cobK ρ)).comap (finZ e PD ρ ι).subtype)
    ((B1 (repL e ρ ι)).comap (finiteCocycles PD (repL e ρ ι)).subtype) (fwd e PD ι ρ)
    (by intro c hc; exact (mem_cob_iff e PD ρ hι c).1 hc)

def quotEquiv : (↥(finZ e PD ρ ι) ⧸ (LinearMap.range (cobK ρ)).comap (finZ e PD ρ ι).subtype) ≃+
    FiniteCohomology PD (repL e ρ ι) where
  toFun := fwdQ e PD ρ hι
  invFun := Submodule.mapQ ((B1 (repL e ρ ι)).comap (finiteCocycles PD (repL e ρ ι)).subtype)
    ((LinearMap.range (cobK ρ)).comap (finZ e PD ρ ι).subtype) (bwd e PD ρ hι) (by
    intro c hc
    have h : (fwd e PD ι ρ (bwd e PD ρ hι c)).1 ∈ B1 (repL e ρ ι) := by
      rw [fwd_bwd]
      exact hc
    exact (mem_cob_iff e PD ρ hι _).2 h)
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H c => exact congrArg Submodule.Quotient.mk (bwd_fwd e PD ρ hι c)
  right_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H c => exact congrArg Submodule.Quotient.mk (fwd_bwd e PD ρ hι c)
  map_add' x y := map_add (fwdQ e PD ρ hι) x y

theorem rank_finQuot :
    Module.rank (FractionRing O)
        (↥(finZ e PD ρ ι) ⧸ (LinearMap.range (cobK ρ)).comap (finZ e PD ρ ι).subtype) =
      Module.rank LL (FiniteCohomology PD (repL e ρ ι)) :=
  rank_eq_of_equiv_equiv e (quotEquiv e PD ρ hι) e.bijective
    (fun k x => (fwdQ e PD ρ hι).map_smulₛₗ k x)

omit hι in
theorem mem_H0V' {W : Type} [AddCommGroup W] [Module LL W] (σ : Representation LL G W) (v : W) :
    v ∈ H0V σ ↔ ∀ g, σ g v = v := by
  simp only [H0V, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]

def cohomZeroEquivContinuous : ↥(LinearMap.ker (cobK ρ)) ≃+ ↥(H0V (repL e ρ ι)) where
  toFun v := ⟨(v.1 : TrV e V), by
    refine (mem_H0V' (repL e ρ ι) _).2 (fun g => ?_)
    have h := congrFun (LinearMap.mem_ker.mp v.2) (ι g)
    exact sub_eq_zero.mp h⟩
  invFun v := ⟨(show V from v.1), by
    show (show V from v.1) ∈ LinearMap.ker (cobK ρ)
    rw [LinearMap.mem_ker]
    funext γ
    obtain ⟨g, rfl⟩ := hι.2 γ
    have h2 := (mem_H0V' (repL e ρ ι) _).1 v.2 g
    exact sub_eq_zero.mpr h2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

theorem rank_invariants_eq :
    Module.rank (FractionRing O) ↥(LinearMap.ker (cobK ρ)) = Module.rank LL ↥(H0V (repL e ρ ι)) :=
  rank_eq_of_equiv_equiv e (cohomZeroEquivContinuous e ρ hι) e.bijective (fun k v => by
    apply Subtype.ext
    show k • (v.1 : V) = e.symm (e k) • (v.1 : V)
    rw [RingEquiv.symm_apply_apply])

theorem finrank_invariants_eq :
    Module.finrank (FractionRing O) ↥(LinearMap.ker (cobK ρ)) = Module.finrank LL ↥(H0V (repL e ρ ι)) := by
  exact congrArg Cardinal.toNat (rank_invariants_eq e ρ hι)

omit hι [TopologicalSpace LL] in
theorem finDim_TrV [FiniteDimensional (FractionRing O) V] : FiniteDimensional LL (TrV e V) := by
  have h : Module.rank (FractionRing O) V = Module.rank LL (TrV e V) :=
    rank_eq_of_equiv_equiv e (AddEquiv.refl V) e.bijective (fun k v => by
      show k • v = e.symm (e k) • v
      rw [RingEquiv.symm_apply_apply])
  have h1 : Module.rank (FractionRing O) V < Cardinal.aleph0 := Module.rank_lt_aleph0_iff.mpr inferInstance
  rw [h] at h1
  exact Module.rank_lt_aleph0_iff.mp h1

end Trans

section Count

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [Fintype (K →ₐ[Qp] LL)]

def FilLow {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) : Prop :=
  ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL ↥(DdRE PD ρ τ) ∧
    ∃ lo : ℤ, lo ≤ 0 ∧ ∀ a, a ≤ lo → FildR PD ρ τ a = DdRE PD ρ τ

private theorem sum_Ico_sub_succ_eq_telescope (f : ℤ → ℤ) : ∀ (n : ℕ) (lo : ℤ), lo + n = 0 →
    ∑ a ∈ Finset.Ico lo 0, (f a - f (a + 1)) = f lo - f 0 := by
  intro n
  induction n with
  | zero =>
    intro lo h
    have h0 : lo = 0 := by omega
    subst h0
    simp
  | succ k ih =>
    intro lo h
    have hs : Finset.Ico lo 0 = insert lo (Finset.Ico (lo + 1) 0) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert]
      omega
    have hn : lo ∉ Finset.Ico (lo + 1) 0 := by
      simp only [Finset.mem_Ico]
      omega
    rw [hs, Finset.sum_insert hn, ih (lo + 1) (by omega)]
    ring

theorem negdim_eq {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (hfin : FiniteDimensional LL ↥(DdRE PD ρ τ))
    (lo : ℤ) (hlo : lo ≤ 0) (hF : FildR PD ρ τ lo = DdRE PD ρ τ) :
    (finrank LL ↥(DdRE PD ρ τ) : ℤ) - finrank LL ↥(FildR PD ρ τ 0) =
      ∑ a ∈ Finset.Ico lo 0, multV PD ρ τ a := by
  have hn : lo + (((-lo).toNat : ℕ) : ℤ) = 0 := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  have h := sum_Ico_sub_succ_eq_telescope (fun a => (finrank LL ↥(FildR PD ρ τ a) : ℤ)) (-lo).toNat lo hn
  rw [← hF]
  exact h.symm

theorem count_eq (hBK : BlochKatoDim PD LL) (hS : Splits LL (K := K) (Qp := Qp))
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] [TopologicalSpace V] [IsModuleTopology LL V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul LL V] (ρ : Representation LL G V)
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    [FiniteDimensional LL W] [TopologicalSpace W] [IsModuleTopology LL W] [IsTopologicalAddGroup W]
    [ContinuousConstSMul LL W] (ρW : Representation LL G W)
    (hcV : ∀ x, Continuous fun g => ρ g x) (hcW : ∀ x, Continuous fun g => ρW g x)
    (hcrV : IsCrys PD ρ) (hcrW : IsCrys PD ρW) (hlowV : FilLow PD ρ) (hlowW : FilLow PD ρW)
    (hneg : ∀ τ a, a < 0 → multV PD ρ τ a = multV PD ρW τ a) (h0W : H0V ρW = ⊥) :
    (finrank LL (FiniteCohomology PD ρ) : ℤ) = finrank LL ↥(H0V ρ) + finrank LL (FiniteCohomology PD ρW) := by
  have hV := hBK hS V ρ hcV hcrV
  have hW := hBK hS W ρW hcW hcrW
  have hsum : ∀ τ : K →ₐ[Qp] LL, ((finrank LL ↥(DdRE PD ρ τ) : ℤ) - finrank LL ↥(FildR PD ρ τ 0)) =
      ((finrank LL ↥(DdRE PD ρW τ) : ℤ) - finrank LL ↥(FildR PD ρW τ 0)) := by
    intro τ
    obtain ⟨hfV, loV, hloV, hFV⟩ := hlowV τ
    obtain ⟨hfW, loW, hloW, hFW⟩ := hlowW τ
    rw [negdim_eq PD ρ τ hfV (min loV loW) (le_trans (min_le_left _ _) hloV) (hFV _ (min_le_left _ _)),
      negdim_eq PD ρW τ hfW (min loV loW) (le_trans (min_le_left _ _) hloV) (hFW _ (min_le_right _ _))]
    apply Finset.sum_congr rfl
    intro a ha
    exact hneg τ a (Finset.mem_Ico.mp ha).2
  rw [hV, hW, Finset.sum_congr rfl (fun τ _ => hsum τ), h0W]
  simp

theorem rank_le_count (hBK : BlochKatoDim PD LL) (hS : Splits LL (K := K) (Qp := Qp))
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [FiniteDimensional LL V] [TopologicalSpace V] [IsModuleTopology LL V] [IsTopologicalAddGroup V]
    [ContinuousConstSMul LL V] (ρ : Representation LL G V)
    {W : Type} [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    [FiniteDimensional LL W] [TopologicalSpace W] [IsModuleTopology LL W] [IsTopologicalAddGroup W]
    [ContinuousConstSMul LL W] (ρW : Representation LL G W)
    (hcV : ∀ x, Continuous fun g => ρ g x) (hcW : ∀ x, Continuous fun g => ρW g x)
    (hcrV : IsCrys PD ρ) (hcrW : IsCrys PD ρW) (hlowV : FilLow PD ρ) (hlowW : FilLow PD ρW)
    (hneg : ∀ τ a, a < 0 → multV PD ρ τ a = multV PD ρW τ a) (h0W : H0V ρW = ⊥)
    (hfin : FiniteDimensional LL (FiniteCohomology PD ρ)) :
    Module.rank LL (FiniteCohomology PD ρ) ≤ ((finrank LL (FiniteCohomology PD ρW) + finrank LL ↥(H0V ρ) : ℕ) : Cardinal) := by
  have h := count_eq PD hBK hS ρ ρW hcV hcW hcrV hcrW hlowV hlowW hneg h0W
  have h' : finrank LL (FiniteCohomology PD ρ) = finrank LL (FiniteCohomology PD ρW) + finrank LL ↥(H0V ρ) := by omega
  rw [← h']
  have hlt : Module.rank LL (FiniteCohomology PD ρ) < Cardinal.aleph0 := Module.rank_lt_aleph0_iff.mpr hfin
  first
    | exact le_of_eq (Module.finrank_eq_rank (R := LL) (M := FiniteCohomology PD ρ)).symm

end Count

section Low

open Classical

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem fil_anti : Antitone PD.Fil := by
  exact antitone_int_of_succ_le PD.Fil_anti

theorem filV_mono {a b : ℤ} (h : a ≤ b) : FilV PD (LL := LL) (V := V) b ≤ FilV PD a := by
  have hle : (PD.Fil b).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := fun x hx => fil_anti PD h hx
  intro x hx
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  clear hx
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul v f => exact LinearMap.mem_range.mpr ⟨v ⊗ₜ[Qp] Submodule.inclusion hle f, rfl⟩
  | add y z hy hz => rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz

theorem exists_filV (x : TensorProduct Qp V BdR) : ∃ a, x ∈ FilV PD (LL := LL) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v f =>
    obtain ⟨a, ha⟩ := PD.Fil_exh f
    exact ⟨a, LinearMap.mem_range.mpr ⟨v ⊗ₜ[Qp] (⟨f, ha⟩ : ↥((PD.Fil a).restrictScalars Qp)), rfl⟩⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (filV_mono PD (min_le_left a b) ha)
      (filV_mono PD (min_le_right a b) hb)⟩

theorem exists_low_finset (s : Finset (TensorProduct Qp V BdR)) :
    ∃ a : ℤ, a ≤ 0 ∧ ∀ x ∈ s, x ∈ FilV PD (LL := LL) a := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, le_refl 0, fun x hx => by simp at hx⟩
  | @insert x s hxs ih =>
    obtain ⟨a, ha0, ha⟩ := ih
    obtain ⟨b, hb⟩ := exists_filV PD (LL := LL) x
    refine ⟨min a b, le_trans (min_le_left a b) ha0, fun y hy => ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy'
    · exact filV_mono PD (min_le_right a b) hb
    · exact filV_mono PD (min_le_left a b) (ha y hy')

variable (ρ : Representation LL G V)

theorem low_of_fin (τ : K →ₐ[Qp] LL) (hfin : FiniteDimensional LL ↥(DdRE PD ρ τ)) :
    ∃ lo : ℤ, lo ≤ 0 ∧ ∀ a, a ≤ lo → FildR PD ρ τ a = DdRE PD ρ τ := by
  let b := Module.finBasis LL ↥(DdRE PD ρ τ)
  obtain ⟨lo, hlo, hs⟩ := exists_low_finset PD (LL := LL)
    (Finset.univ.image (fun j => ((b j : ↥(DdRE PD ρ τ)) : TensorProduct Qp V BdR)))
  refine ⟨lo, hlo, fun a ha => ?_⟩
  have hb : ∀ j, ((b j : ↥(DdRE PD ρ τ)) : TensorProduct Qp V BdR) ∈ FilV PD (LL := LL) a := fun j =>
    filV_mono PD ha (hs _ (Finset.mem_image_of_mem _ (Finset.mem_univ j)))
  unfold FildR
  apply inf_eq_left.mpr
  intro y hy
  have hspan : Submodule.span LL (Set.range b) ≤ (FilV PD (LL := LL) a).comap (DdRE PD ρ τ).subtype := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact hb j
  rw [b.span_eq] at hspan
  exact hspan (Submodule.mem_top (x := (⟨y, hy⟩ : ↥(DdRE PD ρ τ))))

theorem filLow_of_dR [FiniteDimensional LL V] (hV : 0 < finrank LL V)
    (hDR : finrank LL ↥(DdR PD ρ) = finrank Qp K * finrank LL V) : FilLow PD ρ := by
  intro τ
  haveI := PD.finK
  have hK : 0 < Module.finrank Qp K := Module.finrank_pos
  have hpos : 0 < finrank LL ↥(DdR PD ρ) := by
    rw [hDR]
    exact Nat.mul_pos hK hV
  haveI : FiniteDimensional LL ↥(DdR PD ρ) := Module.finite_of_finrank_pos hpos
  have hle : DdRE PD ρ τ ≤ DdR PD ρ := inf_le_left
  haveI hfin : FiniteDimensional LL ↥(DdRE PD ρ τ) := Submodule.finiteDimensional_of_le hle
  exact ⟨hfin, low_of_fin PD ρ τ hfin⟩

end Low

section Rec

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG Classical

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem col_over (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ placesOver D.host.E (D.nd.l i) := by
  have hmem : l.1 ∈ K.plSet i dc := by
    unfold K.plSet
    simp only [Finset.mem_union]
    exact Or.inl (Or.inr l.2)
  have hidx : K.plOf i dc (K.colIdx i dc l) = l.1 := by
    unfold K.plOf K.colIdx K.idx
    rw [dite_eq_left hmem, dite_eq_left ((K.plSet i dc).equivFin ⟨l.1, hmem⟩).isLt]
    simp
  rw [hidx]
  exact (dc.cover l.1).mp (Or.inr l.2)

theorem colD_eq (x' : X') (n : ℕ) :
    letI := evalModO i (R' := R') x'
    haveI := evalTower i (R' := R') x'
    colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ (Γn i dc n) =
      cobK (repE i dc r χ x' n) := by
  first
    | rfl

abbrev repX (x' : X') (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    letI := evalModO i (R' := R') x'
    Representation (Br.LL D.nbr i _ hn) (Br.G D.nbr i _ hn)
      (TrV (eK (D.nbr i _ hn)) (EvalSp (D.nd.O i) d R' x')) :=
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  repL (eK (D.nbr i _ hn)) (repE i dc r χ x' n) (Br.iota D.nbr i _ hn)

abbrev repW (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    Representation (Br.LL D.nbr i _ hn) (Br.G D.nbr i _ hn) (Fin D.R.r → Br.LL D.nbr i _ hn) :=
  matRep (Br.loc D.nbr i _ hn (WpO D.nd i ρ π))

def ContX (x' : X') (l : K.Col i dc) : Prop :=
  letI := evalModO i (R' := R') x'
  ∀ v, Continuous fun g => repX i dc r χ x' (K.colIdx i dc l) (col_over i dc l) g v

theorem contX_of_orbC (x' : X') (l : K.Col i dc) :
    letI := evalModO i (R' := R') x'
    haveI := evalTower i (R' := R') x'
    OrbC i dc (repE i dc r χ x' (K.colIdx i dc l)) → ContX i dc r χ x' l := by
  intro h
  exact h (col_over i dc l)

def CrysX (x' : X') (l : K.Col i dc) : Prop :=
  letI := evalModO i (R' := R') x'
  IsCrys (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repX i dc r χ x' (K.colIdx i dc l) (col_over i dc l))

def NegX (x' : X') (l : K.Col i dc) : Prop :=
  letI := evalModO i (R' := R') x'
  ∀ τ a, a < 0 →
    multV (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repX i dc r χ x' (K.colIdx i dc l) (col_over i dc l)) τ a =
      multV (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repW i dc ρ π (K.colIdx i dc l) (col_over i dc l)) τ a

def FilLowX (x' : X') (l : K.Col i dc) : Prop :=
  letI := evalModO i (R' := R') x'
  FilLow (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repX i dc r χ x' (K.colIdx i dc l) (col_over i dc l))

def FinX (x' : X') (l : K.Col i dc) : Prop :=
  letI := evalModO i (R' := R') x'
  FiniteDimensional (Br.LL D.nbr i _ (col_over i dc l))
    (FiniteCohomology (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repX i dc r χ x' (K.colIdx i dc l) (col_over i dc l)))

def GoodW (l : K.Col i dc) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repW i dc ρ π (K.colIdx i dc l) (col_over i dc l)) ∧
    (∀ v, Continuous fun g => repW i dc ρ π (K.colIdx i dc l) (col_over i dc l) g v) ∧
    FilLow (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repW i dc ρ π (K.colIdx i dc l) (col_over i dc l))

omit [DecidableEq d] in
theorem invariants_twist_eq_bot (rX : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hG2 : TruncatedSeriesCountingIdentities.admG2 i rX ρ π)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    H0V (repW i dc ρ π n hn) = ⊥ := by
  have h := (hG2 (K.plOf i dc n) hn (TruncatedSeriesCountingIdentities.CoefExt.self (D := D) (i := i) (hw := hn))).1
  exact h.2.2.2.2.2.1

end Rec

section Main

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG Classical

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

private theorem lx_col_eq (x' : X') (l : K.Col i dc) :
    letI := evalModO i (R' := R') x'
    haveI := evalTower i (R' := R') x'
    Lx i dc r χ x' l = finZ (eK (D.nbr i _ (col_over i dc l))) (Br.PD D.loc D.nbr i _ (col_over i dc l))
      (repE i dc r χ x' (K.colIdx i dc l)) (Br.iota D.nbr i _ (col_over i dc l)) := by
  unfold Lx fZ
  rw [dite_eq_left (col_over i dc l)]

set_option synthInstance.maxHeartbeats 80000 in
private theorem jK_colIdx_eq_finrank_cohomology (l : K.Col i dc) :
    jK i dc ρ π (K.colIdx i dc l) = Module.finrank (Br.LL D.nbr i _ (col_over i dc l))
      (FiniteCohomology (Br.PD D.loc D.nbr i _ (col_over i dc l))
        (repW i dc ρ π (K.colIdx i dc l) (col_over i dc l))) := by
  unfold jK
  rw [dite_eq_left (col_over i dc l)]
  rfl

private theorem iota_bijective_col (l : K.Col i dc) :
    Function.Bijective (Br.iota D.nbr i _ (col_over i dc l)) :=
  (D.nbr i _ (col_over i dc l)).e.symm.bijective

theorem dimLx_of (rX : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x' : X') (l : K.Col i dc)
    (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i rX ρ π)
    (hc : ContX i dc r χ x' l) (hcr : CrysX i dc r χ x' l) (hneg : NegX i dc r χ ρ π x' l)
    (hlow : FilLowX i dc r χ x' l) (hfin : FinX i dc r χ x' l) (hW : GoodW i dc ρ π l) :
    DimLx i dc r χ (jK i dc ρ π) x' l := by
  have hw := col_over i dc l
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  have hι := iota_bijective_col i dc l
  unfold DimLx
  rw [lx_col_eq i dc r χ x' l, colD_eq i dc r χ x' (K.colIdx i dc l), jK_colIdx_eq_finrank_cohomology i dc ρ π l,
    rank_finQuot (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (repE i dc r χ x' (K.colIdx i dc l)) hι,
    finrank_invariants_eq (eK (D.nbr i _ hw)) (repE i dc r χ x' (K.colIdx i dc l)) hι]
  haveI := finDim_TrV (V := EvalSp (D.nd.O i) d R' x') (eK (D.nbr i _ hw))
  have hBK' : BlochKatoDim (Br.PD D.loc D.nbr i _ hw) (Br.LL D.nbr i _ hw) := (hBK (K.plOf i dc (K.colIdx i dc l)) hw (TruncatedSeriesCountingIdentities.CoefExt.self (D := D) (i := i) (hw := hw))).2.1
  have hS : Splits (Br.LL D.nbr i _ hw) (K := Br.Kw D.nbr i _ hw) (Qp := ℚ_[D.nd.l i]) :=
    LargeLevelLemmas.splits_coef (TruncatedSeriesCountingIdentities.CoefExt.self (D := D) (i := i) (hw := hw))
  exact rank_le_count (Br.PD D.loc D.nbr i _ hw) hBK' hS
    (repX i dc r χ x' (K.colIdx i dc l) hw) (repW i dc ρ π (K.colIdx i dc l) hw)
    hc hW.2.1 hcr hW.1 hlow hW.2.2 hneg (invariants_twist_eq_bot i dc ρ π rX hG2 (K.colIdx i dc l) hw) hfin

end Main

section Dr

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG Classical

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem finrank_TrV (x' : X') {LL : Type} [Field LL] (e : FractionRing (D.nd.O i) ≃+* LL) :
    Module.finrank LL (TrV e (EvalSp (D.nd.O i) d R' x')) = Fintype.card d := by
  have h : Module.rank (FractionRing (D.nd.O i)) (d → FractionRing (D.nd.O i)) =
      Module.rank LL (TrV e (EvalSp (D.nd.O i) d R' x')) :=
    rank_eq_of_equiv_equiv e (AddEquiv.refl _) e.bijective (fun k v => by
      show k • v = e.symm (e k) • v
      rw [RingEquiv.symm_apply_apply])
  have h2 : Module.finrank (FractionRing (D.nd.O i)) (d → FractionRing (D.nd.O i)) =
      Module.finrank LL (TrV e (EvalSp (D.nd.O i) d R' x')) := congrArg Cardinal.toNat h
  rw [← h2]
  first
    | simp

def grepX (x' : X') (l : K.Col i dc) (hc : ContX i dc r χ x' l) :
    GRep (Br.G D.nbr i _ (col_over i dc l)) ℚ_[D.nd.l i] (Br.LL D.nbr i _ (col_over i dc l))
      (Br.OLL D.nbr i _ (col_over i dc l)) :=
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  letI mO : Module (Br.OLL D.nbr i _ (col_over i dc l))
      (TrV (eK (D.nbr i _ (col_over i dc l))) (EvalSp (D.nd.O i) d R' x')) :=
    Module.compHom _ (algebraMap (Br.OLL D.nbr i _ (col_over i dc l)) (Br.LL D.nbr i _ (col_over i dc l)))
  haveI tO : IsScalarTower (Br.OLL D.nbr i _ (col_over i dc l)) (Br.LL D.nbr i _ (col_over i dc l))
      (TrV (eK (D.nbr i _ (col_over i dc l))) (EvalSp (D.nd.O i) d R' x')) :=
    ⟨fun a b v => by
      show (a • b) • v = (algebraMap _ (Br.LL D.nbr i _ (col_over i dc l)) a) • (b • v)
      rw [Algebra.smul_def, mul_smul]⟩
  haveI := finDim_TrV (V := EvalSp (D.nd.O i) d R' x') (eK (D.nbr i _ (col_over i dc l)))
  { V := TrV (eK (D.nbr i _ (col_over i dc l))) (EvalSp (D.nd.O i) d R' x')
    modO := mO
    towO := tO
    ρ := repX i dc r χ x' (K.colIdx i dc l) (col_over i dc l)
    cont := hc }

theorem filLowX_of (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hd : 0 < Fintype.card d) (x' : X') (l : K.Col i dc)
    (hc : ContX i dc r χ x' l) (hcr : CrysX i dc r χ x' l) : FilLowX i dc r χ x' l := by
  have hw := col_over i dc l
  have hF := (hFont (K.plOf i dc (K.colIdx i dc l)) hw (TruncatedSeriesCountingIdentities.CoefExt.self (D := D) (i := i) (hw := hw))).2.2.2
  have hDR := hF (grepX i dc r χ x' l hc) hcr
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  haveI := finDim_TrV (V := EvalSp (D.nd.O i) d R' x') (eK (D.nbr i _ hw))
  exact filLow_of_dR (Br.PD D.loc D.nbr i _ hw) (repX i dc r χ x' (K.colIdx i dc l) hw)
    (by rw [finrank_TrV]; exact hd) hDR

def grepW (l : K.Col i dc)
    (hc : ∀ v, Continuous fun g => repW i dc ρ π (K.colIdx i dc l) (col_over i dc l) g v) :
    GRep (Br.G D.nbr i _ (col_over i dc l)) ℚ_[D.nd.l i] (Br.LL D.nbr i _ (col_over i dc l))
      (Br.OLL D.nbr i _ (col_over i dc l)) where
  V := Fin D.R.r → Br.LL D.nbr i _ (col_over i dc l)
  ρ := repW i dc ρ π (K.colIdx i dc l) (col_over i dc l)
  cont := hc

theorem goodW_of (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hr : 0 < D.R.r) (l : K.Col i dc)
    (hcr : IsCrys (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repW i dc ρ π (K.colIdx i dc l) (col_over i dc l)))
    (hc : ∀ v, Continuous fun g => repW i dc ρ π (K.colIdx i dc l) (col_over i dc l) g v) :
    GoodW i dc ρ π l := by
  refine ⟨hcr, hc, ?_⟩
  have hw := col_over i dc l
  have hF := (hFont (K.plOf i dc (K.colIdx i dc l)) hw (TruncatedSeriesCountingIdentities.CoefExt.self (D := D) (i := i) (hw := hw))).2.2.2
  have hDR := hF (grepW i dc ρ π l hc) hcr
  have hpos : 0 < Module.finrank (Br.LL D.nbr i _ hw) (Fin D.R.r → Br.LL D.nbr i _ hw) := by
    first
      | (rw [Module.finrank_fin_fun]; exact hr)
  exact filLow_of_dR (Br.PD D.loc D.nbr i _ hw) (repW i dc ρ π (K.colIdx i dc l) hw) hpos hDR

end Dr

section Main2

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG Classical

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def CrysW (l : K.Col i dc) : Prop :=
  IsCrys (Br.PD D.loc D.nbr i _ (col_over i dc l)) (repW i dc ρ π (K.colIdx i dc l) (col_over i dc l))

def ContW (l : K.Col i dc) : Prop :=
  ∀ v, Continuous fun g => repW i dc ρ π (K.colIdx i dc l) (col_over i dc l) g v

theorem dimLx_of_font (rX : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (x' : X') (l : K.Col i dc)
    (hd : 0 < Fintype.card d) (hr : 0 < D.R.r)
    (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i rX ρ π) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i)
    (hc : ContX i dc r χ x' l) (hcr : CrysX i dc r χ x' l) (hneg : NegX i dc r χ ρ π x' l)
    (hfin : FinX i dc r χ x' l) (hcrW : CrysW i dc ρ π l) (hcW : ContW i dc ρ π l) :
    DimLx i dc r χ (jK i dc ρ π) x' l :=
  dimLx_of i dc r χ ρ π rX x' l hBK hG2 hc hcr hneg (filLowX_of i dc r χ hFont hd x' l hc hcr) hfin
    (goodW_of i dc ρ π hFont hr l hcrW hcW)

end Main2

section EvalU

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type}
  [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)}
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData O X d G t bl) {T : Subalgebra O (X → O)} {r₀ : G →* (X → Matrix d d O)}
  {π₀ : X} {χ₁ ε : G →* Oˣ} {g₀ : G} {eB e₁ s : X → Matrix d d O}

end EvalU

section Ident

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG Classical

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) {bl : Fin D.R.nV → Fin (D.R.t + 1)}
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t bl)

def phiX (x' : Dd.X') {LL : Type} [Field LL] (e : FractionRing (D.nd.O i) ≃+* LL) :
    TrV e (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') ≃ₗ[LL] (Fin D.R.nV → LL) where
  toFun v j := e ((show Fin D.R.nV → FractionRing (D.nd.O i) from v) j)
  invFun w := (show EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x' from fun j => e.symm (w j))
  map_add' u v := by
    funext j
    exact map_add e _ _
  map_smul' c v := by
    funext j
    show e (e.symm c * (show Fin D.R.nV → FractionRing (D.nd.O i) from v) j) = c * e _
    rw [map_mul, RingEquiv.apply_symm_apply]
  left_inv v := by
    funext j
    exact e.symm_apply_apply _
  right_inv w := by
    funext j
    exact e.apply_symm_apply _

end Ident

end Formalism.MainNotions.N.KDim
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.QS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Eval
variable {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {π : D.nd.X i} {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
  {Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)}

structure Ev (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)) : Prop where
  r_eval : ∀ (g : GE D.nd) (x' : Dd.X'),
    ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))
  chi_eval : ∀ (g : GE D.nd) (x' : Dd.X'),
    (((Dd.χ g : Dd.T'ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i)
  smul_eval : ∀ (f : Dd.T') (a : Dd.R') (x' : Dd.X'),
    ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x'
  blk_smul : ∀ (f : Dd.T') k (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k), f • m = ((f : Dd.X' → D.nd.O i) Dd.π') • m
  ρπ_eval : ∀ a : Dd.R', (Dd.ρπ a).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) =
    (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) Dd.π'
  ρk_eval : ∀ (a : Dd.R') k, (Dd.ρπ a).toSquareBlock (RepresentationBoundsCohomology.blk D.R) k = Dd.ρk k a
  pπ : Dd.p Dd.π' = π
  comp_mem : ∀ f ∈ D.nd.T i, (f ∘ Dd.p) ∈ Dd.T'

theorem ev_of (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    Ev r π Dd := by
  obtain ⟨-, -, h3, -, h5, -, h7, -, h9, -, h11, h12, -, -, -, -, h17, h18, -⟩ := hD
  refine ⟨h7, h12, h9, h11, h17, h18, h5, fun f hf => ?_⟩
  rw [h3]
  exact Algebra.subset_adjoin (Or.inl ⟨f, hf, rfl⟩)

theorem act_eval (a : Dd.R') (x' : Dd.X') (η : EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') :
    ((a • η : EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') : Fin D.R.nV → FractionRing (D.nd.O i)) =
      ((a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x').mulVec
        (η : Fin D.R.nV → FractionRing (D.nd.O i)) := by
  funext k
  simp only [Matrix.mulVec, dotProduct]
  rfl

theorem character_trivial_where_lattice {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (g : GE D.nd) (hg : rO D.nd i r π g = 1) : D.nd.chi i 1 g = 1 := by
  obtain ⟨e, he⟩ := hdec
  have h := he g (e.symm (0, fun _ => 1))
  have h1 : (mapM (toK D.nd i) (rO D.nd i r π)) g = 1 := by
    simp only [mapM, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, hg, map_one]
  rw [h1, Matrix.one_mulVec, LinearEquiv.apply_symm_apply] at h
  have h2 := congrFun (congrArg Prod.snd h) ⟨0, RepresentationBoundsCohomology.one_le_letterBlockLength D.R⟩
  simp only [mul_one] at h2
  apply Units.ext
  apply IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))
  simpa using h2.symm

end Eval

section G4
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem rO_one_of_Io (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (v : Vo i) (g : GE D.nd) (hg : g ∈ Io i v) (x : D.nd.X i) :
    rO D.nd i r x g = 1 := by
  have h := hG4 x v.1 v.2.1 v.2.2.1 v.2.2.2 g hg
  simp [rO, h]

theorem inertia_triviality_clause (hE : Ev r π Dd) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) : InertiaActsTrivially i Dd := by
  intro v g hg
  refine ⟨?_, ?_⟩
  · apply Subtype.ext
    funext x'
    rw [hE.r_eval, rO_one_of_Io i r hG4 v g hg]
    simp
  · have hc := character_trivial_where_lattice hdec g (rO_one_of_Io i r hG4 v g hg π)
    apply Units.ext
    apply Subtype.ext
    funext x'
    rw [hE.chi_eval, hc]
    simp

theorem no_fixed_vector_off_z (hE : Ev r π Dd) (hG6 : TruncatedSeriesCountingIdentities.admG6 i r) : NoFixedVectorOffZ i Dd := by
  intro x' hx η _ hη
  obtain ⟨g, hg⟩ := Inst.exists_nonfixed_twisted_vector (N := D.nd) (r := r) hG6 (Dd.p x') hx η hη
  refine ⟨g, fun h => hg ?_⟩
  have h2 : ((((((Dd.χ g)⁻¹ : Dd.T'ˣ) : Dd.T') • Dd.r g) • η : EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') :
      Fin D.R.nV → FractionRing (D.nd.O i)) = (η : Fin D.R.nV → FractionRing (D.nd.O i)) := h
  rw [act_eval, hE.smul_eval, hE.r_eval] at h2
  have hi : ((((Dd.χ g)⁻¹ : Dd.T'ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' =
      (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
    rw [← map_inv, hE.chi_eval, map_inv]
  rw [hi] at h2
  have e : ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) •
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).mulVec
        (η : Fin D.R.nV → FractionRing (D.nd.O i)) =
      (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) •
      ((rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).mulVec
        (η : Fin D.R.nV → FractionRing (D.nd.O i)) := by
    first
    | exact Matrix.smul_mulVec _ _ _
  exact e.symm.trans h2
end G4

section Cover
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem first_character_unramified (w : ℕ) : Fpos i dc Dd (c1 (D := D)) w ≤ unrH1 (resU i dc Dd (c1 (D := D)) w) (I i dc w) := by
  unfold Fpos
  split_ifs
  · exact le_rfl
  · exact inf_le_right
  · exact bot_le
  · exact le_rfl
  · exact bot_le

theorem ine_le_I {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ plSet i dc) :
    Ine (F := D.host.E) (Av v) ≤ (I i dc (idx i dc v)).map (decs D.host.E (Aw i dc) (idx i dc v)).subtype := by
  have hA : Aw i dc (idx i dc v) = Av v := by
    unfold Aw Av
    rw [plOf_idx i dc hv]
  intro g hg
  have hg' : g ∈ Ine (F := D.host.E) (Aw i dc (idx i dc v)) := hA ▸ hg
  refine Subgroup.mem_map.2 ⟨⟨g, Ine_le_Dec _ hg'⟩, ?_, rfl⟩
  exact Subgroup.mem_subgroupOf.2 hg'

theorem coverClause : CoverClause i dc Dd := by
  intro v
  by_cases hl : v ∈ placesOver D.host.E (D.nd.l i)
  · right; right
    have hrc := (dc.cover v).2 hl
    have hv : v ∈ plSet i dc := by
      unfold plSet
      rcases hrc with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    refine ⟨idx i dc v, ?_, I i dc (idx i dc v), first_character_unramified i dc Dd _, ine_le_I i dc hv⟩
    rcases hrc with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h))
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨v, h⟩, Finset.mem_univ _, rfl⟩)
  by_cases hS : v ∈ D.nd.S i
  · exact Or.inr (Or.inl ⟨⟨v, hS⟩, le_rfl⟩)
  by_cases hQ : v ∈ D.nd.Q i
  · right; right
    have hv : v ∈ plSet i dc := Finset.mem_union_right _ hQ
    exact ⟨idx i dc v, Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hQ)),
      I i dc (idx i dc v), first_character_unramified i dc Dd _, ine_le_I i dc hv⟩
  · exact Or.inl ⟨⟨v, hl, hS, hQ⟩, le_rfl⟩

end Cover

section GlobalTheory
variable {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} {π : D.nd.X i}
  {Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)}

theorem blk_eq {c' : Fin D.R.t} (a : Fin D.R.nV) (h : RepresentationBoundsCohomology.blk D.R a = c'.succ) :
    a = (Fin.natAdd D.R.r c' : Fin (D.R.r + D.R.t)) := by
  have h' := h
  simp only [RepresentationBoundsCohomology.blk, RepresentationBoundsCohomology.blkG] at h'
  split_ifs at h' with h1
  · exact absurd h'.symm (Fin.succ_ne_zero c')
  · apply Fin.ext
    have h2 := congrArg Fin.val h'
    simp only [Fin.val_succ] at h2
    simp only [Fin.val_natAdd]
    omega

theorem blk_act (c' : Fin D.R.t) (a : Dd.R') (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ) (hE : Ev r π Dd) :
    a • m = (Dd.ρπ a (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c')) • m := by
  funext k
  have hk : ∀ j : {a // RepresentationBoundsCohomology.blk D.R a = c'.succ}, j = k := by
    intro j
    apply Subtype.ext
    rw [blk_eq j.1 j.2, blk_eq k.1 k.2]
  show ∑ j, (Dd.ρk c'.succ a) k j • m j = _
  rw [Finset.sum_eq_single k (fun j _ hj => absurd (hk j) hj) (fun h => absurd (Finset.mem_univ k) h)]
  rw [← hE.ρk_eval]
  show Dd.ρπ a k.1 k.1 • m k = Dd.ρπ a (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c') • m k
  rw [blk_eq k.1 k.2]

end GlobalTheory

section LocQ
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

variable {i r ρ π Dd} in
theorem rblk (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c' : Fin D.R.t) (g : GE D.nd) :
    Dd.ρπ (Dd.r g) (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c') =
      ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  apply IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))
  have h1 : algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (Dd.ρπ (Dd.r g) (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c')) =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (rO D.nd i r π g (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c')) := by
    have h := congrFun (congrFun (hE.ρπ_eval (Dd.r g)) (Fin.natAdd D.R.r c')) (Fin.natAdd D.R.r c')
    rw [hE.r_eval, hE.pπ] at h
    exact h
  rw [h1]
  exact congrArg _ (hN.2.1 g c')

variable {i r ρ π Dd} in
theorem r_act (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c' : Fin D.R.t) (g : GE D.nd)
    (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ) :
    Dd.r g • m = ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) • m := by
  rw [blk_act c' _ m hE, rblk hE hN c' g]

theorem chi_c_eq (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∈ D.nd.S i ∨ v ∈ D.nd.Q i)
    (c' : Fin D.R.t) (g : GE D.nd) (hg : g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v)) :
    D.nd.chi i ((c' : ℕ) + 1) g = D.nd.chi i 1 g :=
  (h5x v hv).2.1 ((c' : ℕ) + 1) (Finset.mem_Icc.2 ⟨by omega, by have := c'.2; omega⟩) g hg

theorem conj_eq {M : Type*} [Monoid M] (u : Mˣ) (b c : M) (h : ↑u⁻¹ * b * ↑u = c) : b = ↑u * c * ↑u⁻¹ := by
  subst h
  simp [mul_assoc]

theorem plOf_mem_Q {w : ℕ} (hw : w ∈ qsN i dc) : plOf i dc w ∈ D.nd.Q i := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
  rw [plOf_idx i dc (Finset.mem_union_right _ hv)]
  exact hv

theorem locQ (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (hQP : QPow i) (c' : Fin D.R.t) :
    ∀ w ∈ qsN i dc, Fpos i dc Dd c'.succ w = unrH1 (resU i dc Dd c'.succ w) (I i dc w) ∧ γQ i dc w ∈ I i dc w ∧
      (Dd.r (γQ i dc w : GE D.nd) - 1) * (Dd.r (γQ i dc w : GE D.nd) - algebraMap Dd.T' Dd.R' (ζ i dc Dd w)) = 0 ∧
      ((Dd.χ (γQ i dc w : GE D.nd) : Dd.T'ˣ) : Dd.T') = ζ i dc Dd w ∧
      (∀ g ∈ I i dc w, Dd.r (g : GE D.nd) = Dd.r (γQ i dc w : GE D.nd) ^ nQ i dc w g ∧
        Dd.χ (g : GE D.nd) = Dd.χ (γQ i dc w : GE D.nd) ^ nQ i dc w g) ∧
      (∀ g ∈ I i dc w, ∀ m : Mc i Dd c'.succ, uElt Dd.r Dd.χ (g : GE D.nd) • m = m) ∧
      (∀ m : Mc i Dd c'.succ, Dd.r (γQ i dc w : GE D.nd) • m = ζO i dc w • m) := by
  intro w hw
  have hq := plOf_mem_Q i dc hw
  have hγ : D.nd.gam0 i (plOf i dc w) ∈ Ine (F := D.host.E) (D.nd.plOm.1 (plOf i dc w)) := D.nd.locNd_chebotarevPlace_mem i _
  have hdiag := fun x => ((hG5 (plOf i dc w) (Or.inr hq)).1 (Or.inl hq) x)
  refine ⟨?_, Subgroup.mem_subgroupOf.2 hγ, ?_, rfl, ?_, ?_, ?_⟩
  · unfold Fpos
    rw [ite_eq_left hw]
  · apply Subtype.ext
    funext x'
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one, ZeroMemClass.coe_zero,
      Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.zero_apply]
    rw [Algebra.algebraMap_eq_smul_one, hE.smul_eval, hE.r_eval]
    try simp only [OneMemClass.coe_one, Pi.one_apply]
    have hz : ((ζ i dc Dd w : Dd.T') : Dd.X' → D.nd.O i) x' =
        ((D.nd.chi i 1 (D.nd.gam0 i (plOf i dc w)) : (D.nd.O i)ˣ) : D.nd.O i) := hE.chi_eval _ x'
    rw [hz]
    have h0 := congrArg (fun X => X.map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
      ((hdiag (Dd.p x')).1 _ hγ)
    try dsimp only at h0
    rw [Matrix.map_zero _ (map_zero _)] at h0
    have hs : (chi1 D.nd i (D.nd.gam0 i (plOf i dc w)) • (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i))).map
        (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) =
        algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (chi1 D.nd i (D.nd.gam0 i (plOf i dc w))) • 1 := by
      ext a b
      by_cases h : a = b <;> simp [h]
    rw [← h0, Matrix.map_mul, Matrix.map_sub, Matrix.map_sub, Matrix.map_one, hs]
    · rfl
    all_goals simp
  · intro g hg
    have hg' : (g : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 (plOf i dc w)) := Subgroup.mem_subgroupOf.1 hg
    have hex : ∃ n : ℕ, D.nd.chi i 1 (g : GE D.nd) = D.nd.chi i 1 (γQ i dc w : GE D.nd) ^ n :=
      hQP _ hq _ hg'
    have hn : D.nd.chi i 1 (g : GE D.nd) = D.nd.chi i 1 (γQ i dc w : GE D.nd) ^ nQ i dc w g := by
      unfold nQ
      rw [dite_eq_left hex]
      exact Nat.find_spec hex
    refine ⟨?_, ?_⟩
    · apply Subtype.ext
      funext x'
      simp only [SubmonoidClass.coe_pow, Pi.pow_apply]
      rw [hE.r_eval, hE.r_eval]
      obtain ⟨Pm, hPm⟩ := (hdiag (Dd.p x')).2
      have h1 := hPm _ hg'
      have h2 := hPm _ hγ
      rw [Units.val_mul, Units.val_mul] at h1 h2
      have e1 := conj_eq Pm _ _ h1
      have e2 := conj_eq Pm _ _ h2
      have m1 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r (Dd.p x')) (g : GE D.nd) : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
          (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) := rfl
      have m2 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r (Dd.p x')) (D.nd.gam0 i (plOf i dc w)) : GL _ _) :
          Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
          (rO D.nd i r (Dd.p x') (γQ i dc w : GE D.nd)).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) := rfl
      rw [m1] at e1
      rw [m2] at e2
      rw [e1, e2, Units.conj_pow, Matrix.diagonal_pow]
      congr 2
      congr 1
      funext k
      try simp only [Pi.pow_apply]
      split_ifs
      · simp
      · rw [← map_pow]
        congr 1
        have := congrArg (fun u : (D.nd.O i)ˣ => (u : D.nd.O i)) hn
        simp only [Units.val_pow_eq_pow_val] at this
        exact this
    · apply Units.ext
      apply Subtype.ext
      funext x'
      simp only [Units.val_pow_eq_pow_val, SubmonoidClass.coe_pow, Pi.pow_apply]
      rw [hE.chi_eval, hE.chi_eval, hn, Units.val_pow_eq_pow_val]
  · intro g hg m
    have hg' : (g : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 (plOf i dc w)) := Subgroup.mem_subgroupOf.1 hg
    unfold uElt
    rw [smul_assoc, r_act hE hN c', hE.blk_smul, chi_c_eq i h5x _ (Or.inr hq) c' _ hg']
    have hi : ((((Dd.χ (g : GE D.nd))⁻¹ : Dd.T'ˣ) : Dd.T') : Dd.X' → D.nd.O i) Dd.π' =
        (((D.nd.chi i 1 (g : GE D.nd))⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      rw [← map_inv, hE.chi_eval, map_inv]
    rw [hi, smul_smul, Units.inv_mul, one_smul]
  · intro m
    rw [r_act hE hN c', chi_c_eq i h5x _ (Or.inr hq) c' (γQ i dc w : GE D.nd) hγ]
    rfl

end LocQ

section Assemble
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def LocS (c : Fin (D.R.t + 1)) : Prop :=
  ∀ v, ∀ g ∈ IS i v, ∃ a : Dd.R', a * ((Dd.r g - algebraMap Dd.T' Dd.R' ((Dd.χ g : Dd.T'ˣ) : Dd.T')) * Dd.E) = 0 ∧
    ∀ m : Mc i Dd c, a • m = 0 → m = 0

theorem locClause (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r)
    (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (hQP : QPow i) (c' : Fin D.R.t)
    (hS : LocS i Dd c'.succ) : LocClause i dc Dd c'.succ :=
  ⟨locQ i dc r ρ π Dd hE hN hG5 h5x hQP c', inertia_triviality_clause i r ρ π Dd hE hG4 hdec, hS⟩

end Assemble

section LocSpde
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem conj_prod {M : Type*} [Ring M] (u : Mˣ) (a b x y : M) :
    (↑u * a * ↑u⁻¹ - x) * (↑u * b * ↑u⁻¹ - y) =
      ↑u * ((a - ↑u⁻¹ * x * ↑u) * (b - ↑u⁻¹ * y * ↑u)) * ↑u⁻¹ := by
  simp only [mul_sub, sub_mul, mul_assoc, Units.mul_inv_cancel_left, Units.inv_mul_cancel_left,
    Units.mul_inv, mul_one]

theorem S_pde {v : HeightOneSpectrum (𝓞 D.host.E)} (hS : v ∈ D.nd.S i)
    (hv : ¬ ∃ k, v ∈ placesOver D.host.E (D.host.g k)) :
    v ∈ placesOver D.host.E D.host.pde ∨ (D.nd.l i = D.host.pde ∧ v ∈ placesOver D.host.E D.host.pde') := by
  obtain ⟨h1, -⟩ := (D.nd.S_def i v).1 hS
  rcases h1 with h | h | h
  · exact absurd ⟨0, h⟩ hv
  · exact absurd ⟨1, h⟩ hv
  · split_ifs at h with hl
    · exact Or.inr ⟨hl, h⟩
    · exact Or.inl h

theorem locS_pde (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (c' : Fin D.R.t) (v : VS i) (hv : ¬ ∃ k, v.1 ∈ placesOver D.host.E (D.host.g k)) (g : GE D.nd)
    (hg : g ∈ IS i v) :
    ∃ a : Dd.R', a * ((Dd.r g - algebraMap Dd.T' Dd.R' ((Dd.χ g : Dd.T'ˣ) : Dd.T')) * Dd.E) = 0 ∧
      ∀ m : Mc i Dd c'.succ, a • m = 0 → m = 0 := by
  have hS := v.2
  have hcase := S_pde i hS hv
  have hA := (hG5 v.1 (Or.inl hS)).1 (by
    rcases hcase with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h))
  have hu : IsUnit (D.nd.zeta i v.1 - 1) := (h5x v.1 (Or.inl hS)).2.2.2 hS hcase
  have hγ := D.nd.locNd_chebotarevPlace_mem i v.1
  refine ⟨Dd.r (D.nd.gam0 i v.1) - 1, ?_, ?_⟩
  · apply Subtype.ext
    funext x'
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one, ZeroMemClass.coe_zero,
      Pi.mul_apply, Pi.sub_apply, Pi.one_apply, Pi.zero_apply]
    rw [Algebra.algebraMap_eq_smul_one, hE.smul_eval, hE.r_eval, hE.r_eval, hE.chi_eval]
    try simp only [OneMemClass.coe_one, Pi.one_apply]
    rw [← mul_assoc]
    refine (congrArg (· * _) ?_).trans (zero_mul _)
    obtain ⟨Pm, hPm⟩ := (hA (Dd.p x')).2
    have h1 := hPm _ hγ
    have h2 := hPm _ hg
    rw [Units.val_mul, Units.val_mul] at h1 h2
    have e1 := conj_eq Pm _ _ h1
    have e2 := conj_eq Pm _ _ h2
    have m1 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r (Dd.p x')) (D.nd.gam0 i v.1) : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
        (rO D.nd i r (Dd.p x') (D.nd.gam0 i v.1)).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) := rfl
    have m2 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r (Dd.p x')) g : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
        (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) := rfl
    rw [m1] at e1
    rw [m2] at e2
    rw [e1, e2, conj_prod]
    have hc1 : ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = 1 := by simp
    have hc2 : ∀ c : KK D.nd i, ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * (c • (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i))) * ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
        c • 1 := by intro c; simp
    rw [hc1, hc2]
    have hz : ∀ (d : Fin D.R.nV → KK D.nd i) (c : KK D.nd i),
        (Matrix.diagonal d - c • 1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = Matrix.diagonal (fun k => d k - c) := by
      intro d c
      ext a b
      by_cases h : a = b <;> simp [h]
    have hz1 : ∀ (d : Fin D.R.nV → KK D.nd i),
        (Matrix.diagonal d - 1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = Matrix.diagonal (fun k => d k - 1) := by
      intro d
      ext a b
      by_cases h : a = b <;> simp [h]
    rw [hz1, hz, Matrix.diagonal_mul_diagonal]
    have hd : ∀ f : Fin D.R.nV → KK D.nd i, f = 0 →
        ((Pm : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * Matrix.diagonal f * ((Pm⁻¹ : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = 0 := by
      intro f hf
      subst hf
      simp
    apply hd
    funext k
    simp only [Pi.zero_apply]
    split_ifs <;> simp [chi1]
  · intro m hm
    rw [sub_smul, r_act hE hN c', one_smul, chi_c_eq i h5x _ (Or.inl hS) c' _ hγ] at hm
    have h1 : (D.nd.zeta i v.1 - 1) • m = 0 := by
      rw [sub_smul, one_smul]
      exact hm
    obtain ⟨u, hu'⟩ := hu
    calc m = ((u⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • ((u : D.nd.O i) • m) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = 0 := by rw [hu', h1, smul_zero]
end LocSpde

section LocSg
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem locS_g (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (c' : Fin D.R.t) (v : VS i) (hv : ∃ k, v.1 ∈ placesOver D.host.E (D.host.g k)) (g : GE D.nd)
    (hg : g ∈ IS i v) :
    ∃ a : Dd.R', a * ((Dd.r g - algebraMap Dd.T' Dd.R' ((Dd.χ g : Dd.T'ˣ) : Dd.T')) * Dd.E) = 0 ∧
      ∀ m : Mc i Dd c'.succ, a • m = 0 → m = 0 := by
  have hS := v.2
  have hT : TameGen D.nd (D.nd.plOm.1 v.1) (D.nd.gam0 i v.1) := (D.nd.restN_tameGenerator_generates i v.1 (Or.inl hS)).2
  obtain ⟨Pp, hPu, hPx⟩ := (hG5 v.1 (Or.inl hS)).2 hv hS hT
  have hγ := D.nd.locNd_chebotarevPlace_mem i v.1
  let φ : D.nd.T i → Dd.T' := fun f => ⟨(f : D.nd.X i → D.nd.O i) ∘ Dd.p, hE.comp_mem _ f.2⟩
  refine ⟨∑ k ∈ Finset.range (Pp.natDegree + 1), φ (Pp.coeff k) • Dd.r (D.nd.gam0 i v.1) ^ k, ?_, ?_⟩
  · apply Subtype.ext
    funext x'
    have hdeg : (Pp.map ((Pi.evalRingHom (fun _ : D.nd.X i => D.nd.O i) (Dd.p x')).comp
        (D.nd.T i).val.toRingHom)).natDegree < Pp.natDegree + 1 :=
      Nat.lt_succ_of_le (Polynomial.natDegree_map_le)
    have h0 := congrArg (fun X => X.map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) (hPx (Dd.p x') g hg)
    try dsimp only at h0
    rw [Matrix.map_zero _ (map_zero _), Polynomial.aeval_eq_sum_range' hdeg] at h0
    have hF : ∀ A : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i),
        A.map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) =
          (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).mapMatrix A := fun _ => rfl
    have hsm : ∀ (c : D.nd.O i) (B : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)),
        (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).mapMatrix (c • B) =
          algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c •
            (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).mapMatrix B := by
      intro c B
      ext a b
      simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
    simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, ZeroMemClass.coe_zero,
      Pi.mul_apply, Pi.sub_apply, Pi.zero_apply]
    rw [← mul_assoc]
    refine (congrArg (· * _) ?_).trans (zero_mul _)
    rw [← h0, Matrix.map_mul]
    congr 1
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply, hF, map_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hE.smul_eval, SubmonoidClass.coe_pow, Pi.pow_apply, hE.r_eval, Polynomial.coeff_map, hsm, hF, ← map_pow]
      rfl
    · rw [Algebra.algebraMap_eq_smul_one, hE.smul_eval, hE.r_eval, hE.chi_eval]
      simp only [OneMemClass.coe_one, Pi.one_apply]
      rw [hF (((r (Dd.p x') g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) - chi1 D.nd i g • 1),
        map_sub, hsm, map_one]
      rfl
  · intro m hm
    have hterm : ∀ k, (φ (Pp.coeff k) • Dd.r (D.nd.gam0 i v.1) ^ k) • m =
        (((Pp.coeff k : D.nd.T i) : D.nd.X i → D.nd.O i) π *
          ((D.nd.chi i 1 (D.nd.gam0 i v.1) : (D.nd.O i)ˣ) : D.nd.O i) ^ k) • m := by
      intro k
      rw [smul_assoc, hE.blk_smul, ← map_pow, r_act hE hN c', chi_c_eq i h5x _ (Or.inl hS) c' _ (pow_mem hγ k),
        map_pow, Units.val_pow_eq_pow_val, smul_smul]
      show (((Pp.coeff k : D.nd.T i) : D.nd.X i → D.nd.O i) (Dd.p Dd.π') * _) • m = _
      rw [hE.pπ]
    rw [Finset.sum_smul, Finset.sum_congr rfl (fun k _ => hterm k), ← Finset.sum_smul] at hm
    have hu : IsUnit (∑ k ∈ Finset.range (Pp.natDegree + 1), ((Pp.coeff k : D.nd.T i) : D.nd.X i → D.nd.O i) π *
        ((D.nd.chi i 1 (D.nd.gam0 i v.1) : (D.nd.O i)ˣ) : D.nd.O i) ^ k) := by
      have h := hPu.map (evT D.nd i π)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Polynomial.eval_eq_sum_range, map_sum] at h
      simpa [evT, chi1] using h
    obtain ⟨u, hu'⟩ := hu
    calc m = ((u⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • ((u : D.nd.O i) • m) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = 0 := by rw [hu', hm, smul_zero]

end LocSg

section Final
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem locS (hE : Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i)
    (c' : Fin D.R.t) : LocS i Dd c'.succ := by
  intro v g hg
  by_cases hv : ∃ k, v.1 ∈ placesOver D.host.E (D.host.g k)
  · exact locS_g i r ρ π Dd hE hN hG5 h5x c' v hv g hg
  · exact locS_pde i r ρ π Dd hE hN hG5 h5x c' v hv g hg

end Final

section Shape
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem idx_not_qs {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ plSet i dc)
    (hl : v ∈ placesOver D.host.E (D.nd.l i)) : idx i dc v ∉ qsN i dc := by
  intro h
  obtain ⟨u, hu, he⟩ := Finset.mem_image.1 h
  have huv := idx_inj i dc (Finset.mem_union_right _ hu) hv he
  exact D.nd.SQ_l i u (Or.inr hu) (huv ▸ hl)

theorem row_mem_pl {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ dc.row) : v ∈ plSet i dc :=
  Finset.mem_union_left _ (Finset.mem_union_left _ hv)

theorem Fpos_row (c : Fin (D.R.t + 1)) {w : ℕ} (hw : w ∈ rowsN i dc) :
    Fpos i dc Dd c w = if (c : ℕ) = 1 then lcH1 (resU i dc Dd c w) ⊓
        unrH1 (resU i dc Dd c w) ((Ine (F := D.host.E) (Aw i dc w)).subgroupOf (decs D.host.E (Aw i dc) w))
      else ⊥ := by
  have hq : w ∉ qsN i dc := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    exact idx_not_qs i dc (row_mem_pl i dc hv) ((dc.cover v).1 (Or.inl hv))
  unfold Fpos
  simp only [ite_eq_right hq, ite_eq_left hw]

end Shape

end Formalism.MainNotions.N.K.QS

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KBKa

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N.KHf ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {VT VT' : Type}
  [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
  [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  (Dat : LatData O Γ VT VT')
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)
  {Qp : Type} [Field Qp] [Algebra Qp LL]
  {OL : Type} [CommRing OL] [Algebra OL LL]
  {G : Type} [Group G] [TopologicalSpace G] (ι : G →* Γ)
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)

instance instModOL (V : Type) [AddCommGroup V] [Module (FractionRing O) V] : Module OL (TrV e V) :=
  Module.compHom V (e.symm.toRingHom.comp (algebraMap OL LL))

instance instTowOL (V : Type) [AddCommGroup V] [Module (FractionRing O) V] :
    IsScalarTower OL LL (TrV e V) :=
  ⟨fun c a v => by
    show (e.symm (c • a)) • (show V from v) = (e.symm (algebraMap OL LL c)) • ((e.symm a) • (show V from v))
    rw [Algebra.smul_def, map_mul, mul_smul]⟩

def IotaHomeo : Prop := ∃ h : G ≃ₜ Γ, ∀ g, h g = ι g

def HomeoK : Prop := Continuous e ∧ Continuous e.symm

def TopMatch (V : Type) [AddCommGroup V] [Module (FractionRing O) V] [t : TopologicalSpace V] : Prop :=
  (instTop (V := V) e : TopologicalSpace (TrV e V)) = t

def CycMatch : Prop :=
  ∀ g, e (algebraMap O (FractionRing O) ((Dat.ε (ι g) : Oˣ) : O)) = ((cycLL PD LL g : LLˣ) : LL)

def toV {V : Type} (x : TrV e V) : V := x

theorem toV_add {V : Type} [AddCommGroup V] [Module (FractionRing O) V] (x y : TrV e V) :
    toV e (x + y) = toV e x + toV e y := rfl

theorem toV_smul {V : Type} [AddCommGroup V] [Module (FractionRing O) V] (c : LL) (x : TrV e V) :
    toV e (c • x) = e.symm c • toV e x := rfl

theorem bT_smulK_left (k : FractionRing O) (v : VT) (w : VT') : Dat.bT (k • v) w = k • Dat.bT v w :=
  smulK (Dat.bT.flip w) k v

theorem bT_smulK_right (k : FractionRing O) (v : VT) (w : VT') : Dat.bT v (k • w) = k • Dat.bT v w :=
  smulK (Dat.bT v) k w

def pairLL : TrV e VT →ₗ[LL] TrV e VT' →ₗ[LL] LL :=
  LinearMap.mk₂ LL (fun x y => e (Dat.bT (toV e x) (toV e y)))
    (fun x x' y => by rw [toV_add, map_add (f := _), LinearMap.add_apply, map_add (f := _)])
    (fun c x y => by
      rw [toV_smul, bT_smulK_left, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply, smul_eq_mul])
    (fun x y y' => by rw [toV_add, map_add (f := _), map_add (f := _)])
    (fun c x y => by
      rw [toV_smul, bT_smulK_right, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply, smul_eq_mul])

theorem pairLL_apply (x : TrV e VT) (y : TrV e VT') :
    pairLL Dat e x y = e (Dat.bT (toV e x) (toV e y)) := rfl

def repA (hfin : FiniteDimensional LL (TrV e VT))
    (hc : ∀ x, Continuous fun g => repL e Dat.ρT ι g x) : Formalism.MainNotions.N.GRep G Qp LL OL where
  V := TrV e VT
  fd := hfin
  ρ := repL e Dat.ρT ι
  cont := hc

def repA' (hfin : FiniteDimensional LL (TrV e VT'))
    (hc : ∀ x, Continuous fun g => repL e Dat.ρT' ι g x) : Formalism.MainNotions.N.GRep G Qp LL OL where
  V := TrV e VT'
  fd := hfin
  ρ := repL e Dat.ρT' ι
  cont := hc

end Gen

section GenP

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)

theorem cont_iff {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [t : TopologicalSpace V]
    (h : TopMatch e V) {X : Type} [TopologicalSpace X] (f : X → V) :
    @Continuous X (TrV e V) _ (instTop e) f ↔ Continuous f := by
  unfold TopMatch at h
  rw [h]
  exact Iff.rfl

def ofV {V : Type} (x : V) : TrV e V := x

theorem ofV_smulK {V : Type} [AddCommGroup V] [Module (FractionRing O) V] (k : FractionRing O) (x : V) :
    ofV e (V := V) (k • x) = e k • ofV e x := by
  show k • x = e.symm (e k) • x
  rw [RingEquiv.symm_apply_apply]

theorem fd_of_finK {V : Type} [AddCommGroup V] [Module (FractionRing O) V]
    [hV : Module.Finite (FractionRing O) V] : FiniteDimensional LL (TrV e V) := by
  obtain ⟨S, hS⟩ := hV.fg_top
  refine ⟨⟨S.image (ofV e), ?_⟩⟩
  rw [Finset.coe_image, eq_top_iff]
  intro v _
  have hv : toV e v ∈ Submodule.span (FractionRing O) (S : Set V) := by rw [hS]; exact Submodule.mem_top
  have key : ∀ x ∈ Submodule.span (FractionRing O) (S : Set V),
      ofV e x ∈ Submodule.span LL (ofV e '' (S : Set V)) := by
    intro x hx
    refine Submodule.span_induction (p := fun x _ => ofV e x ∈ Submodule.span LL (ofV e '' (S : Set V)))
      (fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩) (Submodule.zero_mem _)
      (fun y z _ _ hy hz => Submodule.add_mem _ hy hz) (fun k y _ hy => ?_) hx
    rw [ofV_smulK]
    exact Submodule.smul_mem _ _ hy
  exact key _ hv

theorem finK_of_lat {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] {T : Submodule O V} (h : IsLatticeIn T) :
    Module.Finite (FractionRing O) V := by
  obtain ⟨S, hS⟩ := h.1
  refine ⟨⟨S, ?_⟩⟩
  apply top_unique
  rw [← h.2]
  apply Submodule.span_le.mpr
  have hsub : Submodule.span O (S : Set V) ≤
      (Submodule.span (FractionRing O) (S : Set V)).restrictScalars O := by
    apply Submodule.span_le.mpr
    exact fun x hx => Submodule.subset_span hx
  rw [hS] at hsub
  exact hsub
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {V : Type} [AddCommGroup V] [Module O V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]

theorem sub_mem_of_mk_eq (ρ : Representation O Γ V) (Z : Submodule (FractionRing O) (Γ → V))
    (hB : ∀ x, d0 ρ x ∈ Z) (c c' : Z1 ρ)
    (h : Submodule.mkQ ((B1 ρ).comap (Z1 ρ).subtype) c = Submodule.mkQ _ c') :
    (c : Γ → V) - c' ∈ Z := by
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨m, hm⟩ := h
  have : (c : Γ → V) - c' = d0 ρ m := by rw [hm]; rfl
  rw [this]
  exact hB m

theorem mk_smul (ρ : Representation O Γ V) [ContinuousConstSMul (FractionRing O) V]
    [Module (FractionRing O) (H1 ρ)] [IsScalarTower O (FractionRing O) (H1 ρ)]
    (k : FractionRing O) (c : Z1 ρ) :
    ∃ kc : Z1 ρ, (kc : Γ → V) = k • (c : Γ → V) ∧
      Submodule.mkQ ((B1 ρ).comap (Z1 ρ).subtype) kc = k • Submodule.mkQ _ c := by
  have hc : Continuous (c : Γ → V) ∧ ∀ g h, c.1 (g * h) = c.1 g + ρ g (c.1 h) := c.2
  refine ⟨⟨k • (c : Γ → V), hc.1.const_smul k, fun g h => ?_⟩, rfl, ?_⟩
  · show k • c.1 (g * h) = k • c.1 g + ρ g (k • c.1 h)
    rw [hc.2 g h, smul_add, smulK (ρ g) k]
  · obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors O) k
    have hs : algebraMap O (FractionRing O) (s : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    dsimp only at hxs
    apply smul_right_injective (H1 ρ) hs
    dsimp only
    rw [smul_smul, mul_comm, hxs, algebraMap_smul, algebraMap_smul, ← map_smul, ← map_smul]
    congr 1
    apply Subtype.ext
    funext g
    show (s : O) • (k • c.1 g) = x • c.1 g
    rw [← algebraMap_smul (FractionRing O) (s : O) (k • c.1 g), smul_smul, mul_comm, hxs, algebraMap_smul]

def clsSet (ρ : Representation O Γ V) (Z : Submodule (FractionRing O) (Γ → V)) : Submodule O (H1 ρ) :=
  (((Z.restrictScalars O).comap (LinearMap.compLeft LinearMap.id Γ)).comap (Z1 ρ).subtype).map
    (Submodule.mkQ _)

theorem mem_span_iff (ρ : Representation O Γ V) [ContinuousConstSMul (FractionRing O) V]
    [Module (FractionRing O) (H1 ρ)] [IsScalarTower O (FractionRing O) (H1 ρ)]
    (Z : Submodule (FractionRing O) (Γ → V)) (hB : ∀ x, d0 ρ x ∈ Z) (c : Z1 ρ) :
    Submodule.mkQ ((B1 ρ).comap (Z1 ρ).subtype) c ∈
      Submodule.span (FractionRing O) (clsSet ρ Z : Set (H1 ρ)) ↔ (c : Γ → V) ∈ Z := by
  let S : Submodule (FractionRing O) (H1 ρ) :=
    { carrier := {a | ∀ c : Z1 ρ, Submodule.mkQ ((B1 ρ).comap (Z1 ρ).subtype) c = a → (c : Γ → V) ∈ Z}
      zero_mem' := fun c hc => by
        have h := sub_mem_of_mk_eq ρ Z hB c 0 (by rw [hc, map_zero])
        simpa using h
      add_mem' := fun {a b} ha hb c hc => by
        obtain ⟨ca, rfl⟩ := Submodule.mkQ_surjective _ a
        obtain ⟨cb, rfl⟩ := Submodule.mkQ_surjective _ b
        have h := sub_mem_of_mk_eq ρ Z hB c (ca + cb) (by rw [hc, map_add (f := _)])
        have e1 : (c : Γ → V) = ((c : Γ → V) - ((ca + cb : Z1 ρ) : Γ → V)) + ((ca : Γ → V) + cb) := by
          simp
        rw [e1]
        exact Z.add_mem h (Z.add_mem (ha ca rfl) (hb cb rfl))
      smul_mem' := fun k a ha c hc => by
        obtain ⟨ca, rfl⟩ := Submodule.mkQ_surjective _ a
        obtain ⟨kc, hkc, hmk⟩ := mk_smul ρ k ca
        have h := sub_mem_of_mk_eq ρ Z hB c kc (by rw [hc, hmk])
        have e1 : (c : Γ → V) = ((c : Γ → V) - kc) + k • (ca : Γ → V) := by rw [← hkc]; abel
        rw [e1]
        exact Z.add_mem h (Z.smul_mem k (ha ca rfl)) }
  constructor
  · intro h
    have hle : Submodule.span (FractionRing O) (clsSet ρ Z : Set (H1 ρ)) ≤ S := by
      rw [Submodule.span_le]
      rintro _ ⟨c0, hc0, rfl⟩ c hc
      have h1 := sub_mem_of_mk_eq ρ Z hB c c0 hc
      have e1 : (c : Γ → V) = ((c : Γ → V) - c0) + c0 := by abel
      rw [e1]
      exact Z.add_mem h1 hc0
    exact hle h c rfl
  · intro h
    exact Submodule.subset_span ⟨c, h, rfl⟩

end GenP

section GenQ

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {VT VT' : Type}
  [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
  [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  (Dat : LatData O Γ VT VT')
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)
  {Qp : Type} [Field Qp] [Algebra Qp LL]
  {OL : Type} [CommRing OL] [Algebra OL LL]
  {G : Type} [Group G] [TopologicalSpace G] (ι : G →* Γ)
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)

def dualMap : VT' →ₗ[FractionRing O] (VT →ₗ[FractionRing O] FractionRing O) where
  toFun f :=
    { toFun := fun x => Dat.bT x f
      map_add' := fun x y => by rw [map_add (f := _), LinearMap.add_apply]
      map_smul' := fun k x => bT_smulK_left Dat k x f }
  map_add' f f' := LinearMap.ext fun x => map_add (Dat.bT x) f f'
  map_smul' k f := LinearMap.ext fun x => bT_smulK_right Dat k x f

theorem dualMap_bij (hP : PerfectRight Dat.bT) : Function.Bijective (dualMap Dat) := by
  constructor
  · intro f f' h
    obtain ⟨g, _, hg⟩ := hP (dualMap Dat f)
    have h1 := hg f (fun x => rfl)
    have h2 := hg f' (fun x => by rw [h]; rfl)
    rw [h1, h2]
  · intro ψ
    obtain ⟨f, hf, _⟩ := hP ψ
    exact ⟨f, LinearMap.ext hf⟩

theorem finK' [Module.Finite (FractionRing O) VT] (hP : PerfectRight Dat.bT) :
    Module.Finite (FractionRing O) VT' :=
  Module.Finite.equiv (LinearEquiv.ofBijective (dualMap Dat) (dualMap_bij Dat hP)).symm

theorem nondeg_left (hP : PerfectRight Dat.bT) (x : VT) (hx : ∀ y, Dat.bT x y = 0) : x = 0 := by
  by_contra hne
  obtain ⟨ψ, hψ⟩ : ∃ ψ : VT →ₗ[FractionRing O] FractionRing O, ψ x ≠ 0 := by
    by_contra! hall
    exact hne ((Module.forall_dual_apply_eq_zero_iff (FractionRing O) x).1 hall)
  obtain ⟨f, hf, _⟩ := hP ψ
  exact hψ ((hf x).symm.trans (hx f))

theorem nondeg_right (hP : PerfectRight Dat.bT) (y : VT') (hy : ∀ x, Dat.bT x y = 0) : y = 0 := by
  obtain ⟨f, _, hu⟩ := hP 0
  rw [hu y (fun x => hy x), hu 0 (fun x => by simp)]

theorem isDual1 (hreal : Formalism.RepresentationBoundsCohomology.FIN.RealLat Dat) (hcyc : CycMatch Dat e ι PD) :
    IsDual1 PD (repL e Dat.ρT ι) (repL e Dat.ρT' ι) (pairLL Dat e) := by
  haveI : Module.Finite (FractionRing O) VT := finK_of_lat hreal.lat
  haveI : Module.Finite (FractionRing O) VT' := finK' Dat hreal.perf
  haveI := fd_of_finK e (V := VT)
  haveI := fd_of_finK e (V := VT')
  have hl : ∀ x : TrV e VT, (∀ y, pairLL Dat e x y = 0) → x = 0 := fun x hx =>
    nondeg_left Dat hreal.perf (toV e x) fun y => (map_eq_zero_iff e e.injective).1 (hx y)
  have hr : ∀ y : TrV e VT', (∀ x, pairLL Dat e x y = 0) → y = 0 := fun y hy =>
    nondeg_right Dat hreal.perf (toV e y) fun x => (map_eq_zero_iff e e.injective).1 (hy x)
  refine ⟨fun g x y => ?_, hl, hr, ?_⟩
  · rw [pairLL_apply, pairLL_apply]
    show e (Dat.bT (Dat.ρT (ι g) (toV e x)) (Dat.ρT' (ι g) (toV e y))) = _
    rw [Dat.eqT, Algebra.smul_def, map_mul, hcyc g]
  · apply le_antisymm
    · have hinj : Function.Injective (pairLL Dat e) := fun x x' h => by
        have := hl (x - x') (fun y => by rw [map_sub, LinearMap.sub_apply, h, sub_self])
        exact sub_eq_zero.1 this
      exact (LinearMap.finrank_le_finrank_of_injective hinj).trans (Subspace.dual_finrank_eq).le
    · have hinj : Function.Injective (pairLL Dat e).flip := fun y y' h => by
        have := hr (y - y') (fun x => by
          have h' := congrArg (fun F => F x) h
          simp only [LinearMap.flip_apply] at h'
          rw [map_sub, h', sub_self])
        exact sub_eq_zero.1 this
      exact (LinearMap.finrank_le_finrank_of_injective hinj).trans (Subspace.dual_finrank_eq).le

theorem coboundary_mem_finite_classes {V : Type} [AddCommGroup V] [Module O V] [t : TopologicalSpace V] [IsTopologicalAddGroup V]
    [ContinuousSMul O V]
    [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    (ρ : Representation O Γ V) (htop : TopMatch e V) (hι : Continuous ι) (hc : ContAction ρ) (x : V) :
    d0 ρ x ∈ finZ e PD ρ ι := by
  rw [mem_finZ]
  refine ⟨⟨?_, fun g h => ?_⟩, (ofV e x : TrV e V) ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  · exact (cont_iff e htop _).2 ((hc.comp ((hι).prodMk continuous_const)).sub continuous_const)
  · show ρ (ι (g * h)) x - x = (ρ (ι g) x - x) + ρ (ι g) (ρ (ι h) x - x)
    rw [map_mul, map_mul, Module.End.mul_apply, map_sub]
    abel
  · show (ofV e (ρ (ι g) x - x) : TrV e V) ⊗ₜ[Qp] (1 : B) = actVB PD (repL e ρ ι) g (ofV e x ⊗ₜ[Qp] (1 : B)) - ofV e x ⊗ₜ[Qp] (1 : B)
    rw [actVB, TensorProduct.AlgebraTensorModule.map_tmul]
    simp only [LinearMap.restrictScalars_apply, AlgHom.toLinearMap_apply, map_one]
    rw [← TensorProduct.sub_tmul]
    rfl

end GenQ

section GenR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)
  {G : Type} [Group G] [TopologicalSpace G] (ι : G →* Γ)
  {V : Type} [AddCommGroup V] [Module O V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [ContinuousSMul O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]

theorem continuous_cocycle_transport (ρ : Representation O Γ V) (htop : TopMatch e V) (hι : Continuous ι) (c : Z1 ρ) :
    (fun g => ofV e (c.1 (ι g))) ∈ continuousCocycles (repL e ρ ι) := by
  have hc : Continuous (c : Γ → V) ∧ ∀ g h, c.1 (g * h) = c.1 g + ρ g (c.1 h) := c.2
  refine ⟨(cont_iff e htop _).2 (hc.1.comp hι), fun g h => ?_⟩
  show c.1 (ι (g * h)) = c.1 (ι g) + ρ (ι g) (c.1 (ι h))
  rw [map_mul, hc.2]

theorem symm_iota (h : G ≃ₜ Γ) (hh : ∀ g, h g = ι g) (γ : Γ) : ι (h.symm γ) = γ := by
  rw [← hh, h.apply_symm_apply]

theorem symm_iota' (h : G ≃ₜ Γ) (hh : ∀ g, h g = ι g) (g : G) : h.symm (ι g) = g := by
  rw [← hh, h.symm_apply_apply]

theorem exists_cocycle_of_continuous (ρ : Representation O Γ V) (htop : TopMatch e V) (h : G ≃ₜ Γ)
    (hh : ∀ g, h g = ι g) (b : G → TrV e V) (hb : b ∈ continuousCocycles (repL e ρ ι)) :
    ∃ d : Z1 ρ, ∀ g, ofV e (d.1 (ι g)) = b g := by
  have hb' : Continuous b ∧ ∀ g g', b (g * g') = b g + repL e ρ ι g (b g') := hb
  refine ⟨⟨fun γ => toV e (b (h.symm γ)), (cont_iff e htop _).1 (hb'.1.comp h.symm.continuous),
    fun γ δ => ?_⟩, fun g => ?_⟩
  · have hm : h.symm (γ * δ) = h.symm γ * h.symm δ := by
      apply h.injective
      rw [h.apply_symm_apply, hh, map_mul, symm_iota ι h hh, symm_iota ι h hh]
    show toV e (b (h.symm (γ * δ))) = toV e (b (h.symm γ)) + ρ γ (toV e (b (h.symm δ)))
    rw [hm, hb'.2]
    show toV e (b (h.symm γ)) + ρ (ι (h.symm γ)) (toV e (b (h.symm δ))) = _
    rw [symm_iota ι h hh]
  · show b (h.symm (ι g)) = b g
    rw [symm_iota' ι h hh]

end GenR

section GenS

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)]
  [ContinuousSMul O (FractionRing O)]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {VT VT' : Type}
  [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [Module (FractionRing O) VT] [IsScalarTower O (FractionRing O) VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
  [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  (Dat : LatData O Γ VT VT')
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)
  {Qp : Type} [Field Qp] [Algebra Qp LL]
  {OL : Type} [CommRing OL] [Algebra OL LL]
  {G : Type} [Group G] [TopologicalSpace G] (ι : G →* Γ)
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)

theorem cup_iff (hι : Continuous ι) (hK : HomeoK e) (hcyc : CycMatch Dat e ι PD) (h : G ≃ₜ Γ)
    (hh : ∀ g, h g = ι g) (c : Z1 Dat.ρT) (d : Z1 Dat.ρT') :
    ReciprocityTheory.ChartRestriction.T2.cupFG Dat (Submodule.mkQ _ c) (Submodule.mkQ _ d) = 0 ↔
      CobL PD (cupL (repL e Dat.ρT' ι) (pairLL Dat e) (fun g => ofV e (c.1 (ι g)))
        (fun g => ofV e (d.1 (ι g)))) := by
  show Submodule.mkQ _ (cupCocycleZ1Z1 Dat.ρT Dat.ρT' (twist Dat.ε (FractionRing O)) Dat.bT Dat.contbT Dat.eqT
    Dat.contT' c d) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    separated_dvr_second_cohomology_mem]
  constructor
  · rintro ⟨f, hf, hfe⟩
    refine ⟨fun g => e (f (ι g)), hK.1.comp (hf.comp hι), ?_⟩
    funext ⟨g, g'⟩
    have h1 := congrFun hfe (ι g, ι g')
    simp only [d1_apply, twist_apply, Algebra.smul_def] at h1
    show ((cycLL PD LL g : LLˣ) : LL) * e (f (ι g')) - e (f (ι (g * g'))) + e (f (ι g)) =
      e (Dat.bT (c.1 (ι g)) (Dat.ρT' (ι g) (d.1 (ι g'))))
    rw [← hcyc g, ← map_mul, ← map_sub, ← map_add (f := _), map_mul ι]
    exact congrArg e h1
  · rintro ⟨f', hf', hfe'⟩
    refine ⟨fun γ => e.symm (f' (h.symm γ)), hK.2.comp (hf'.comp h.symm.continuous), ?_⟩
    funext ⟨γ, δ⟩
    obtain ⟨g1, rfl⟩ : ∃ g1, ι g1 = γ := ⟨h.symm γ, symm_iota ι h hh γ⟩
    obtain ⟨g2, rfl⟩ : ∃ g2, ι g2 = δ := ⟨h.symm δ, symm_iota ι h hh δ⟩
    have h1 := congrFun hfe' (g1, g2)
    change ((cycLL PD LL g1 : LLˣ) : LL) * f' g2 - f' (g1 * g2) + f' g1 =
      e (Dat.bT (c.1 (ι g1)) (Dat.ρT' (ι g1) (d.1 (ι g2)))) at h1
    show ((Dat.ε (ι g1) : Oˣ) : O) • e.symm (f' (h.symm (ι g2))) - e.symm (f' (h.symm (ι g1 * ι g2))) +
      e.symm (f' (h.symm (ι g1))) = Dat.bT (c.1 (ι g1)) (Dat.ρT' (ι g1) (d.1 (ι g2)))
    rw [← map_mul ι, symm_iota' ι h hh, symm_iota' ι h hh, symm_iota' ι h hh]
    apply e.injective
    rw [map_add (f := _), map_sub, Algebra.smul_def, map_mul, hcyc g1, e.apply_symm_apply, e.apply_symm_apply,
      e.apply_symm_apply]
    exact h1

theorem bka_gen [Module (FractionRing O) (H1 Dat.ρT)] [IsScalarTower O (FractionRing O) (H1 Dat.ρT)]
    [Module (FractionRing O) (H1 Dat.ρT')] [IsScalarTower O (FractionRing O) (H1 Dat.ρT')]
    (hbk : Formalism.MainNotions.LargeLevelLemmas.bkAAt PD LL OL) (hreal : Formalism.RepresentationBoundsCohomology.FIN.RealLat Dat) (hι : IotaHomeo ι)
    (hK : HomeoK e) (ht : TopMatch e VT) (ht' : TopMatch e VT') (hcyc : CycMatch Dat e ι PD)
    (hdr : IsDR PD (repL e Dat.ρT ι))
    (Z : Submodule (FractionRing O) (Γ → VT)) (Z' : Submodule (FractionRing O) (Γ → VT'))
    (hZ : Z = finZ e PD Dat.ρT ι) (hZ' : Z' = finZ e PD Dat.ρT' ι) (a : H1 Dat.ρT) :
    a ∈ Submodule.span (FractionRing O) (clsSet Dat.ρT Z : Set (H1 Dat.ρT)) ↔
      ∀ b ∈ Submodule.span (FractionRing O) (clsSet Dat.ρT' Z' : Set (H1 Dat.ρT')),
        ReciprocityTheory.ChartRestriction.T2.cupFG Dat a b = 0 := by
  subst hZ hZ'
  obtain ⟨h, hh⟩ := hι
  have hιc : Continuous ι := by
    rw [show (ι : G → Γ) = h from funext fun g => (hh g).symm]
    exact h.continuous
  haveI : Module.Finite (FractionRing O) VT := finK_of_lat hreal.lat
  haveI : Module.Finite (FractionRing O) VT' := finK' Dat hreal.perf
  haveI : ContinuousConstSMul (FractionRing O) VT := hreal.cs
  haveI : ContinuousConstSMul (FractionRing O) VT' := hreal.cs'
  have fdV := fd_of_finK e (V := VT)
  have fdV' := fd_of_finK e (V := VT')
  have hcA : ∀ x, Continuous fun g => repL e Dat.ρT ι g x := fun x =>
    (cont_iff e ht _).2 (hreal.contT.comp (hιc.prodMk continuous_const))
  have hcA' : ∀ x, Continuous fun g => repL e Dat.ρT' ι g x := fun x =>
    (cont_iff e ht' _).2 (Dat.contT'.comp (hιc.prodMk continuous_const))
  let A := repA (Qp := Qp) (OL := OL) Dat e ι fdV hcA
  let A' := repA' (Qp := Qp) (OL := OL) Dat e ι fdV' hcA'
  have hB : ∀ x, d0 Dat.ρT x ∈ finZ e PD Dat.ρT ι := coboundary_mem_finite_classes e ι PD Dat.ρT ht hιc hreal.contT
  have hB' : ∀ x, d0 Dat.ρT' x ∈ finZ e PD Dat.ρT' ι := coboundary_mem_finite_classes e ι PD Dat.ρT' ht' hιc Dat.contT'
  obtain ⟨c, rfl⟩ := Submodule.mkQ_surjective _ a
  rw [mem_span_iff Dat.ρT _ hB c, mem_finZ]
  have hcZ := continuous_cocycle_transport e ι Dat.ρT ht hιc c
  have hdual := isDual1 Dat e ι PD hreal hcyc
  refine ((hbk A A' (pairLL Dat e) hdr hdual).1 _ hcZ).trans ?_
  constructor
  · intro H b hb
    obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ b
    have hd := (mem_span_iff Dat.ρT' _ hB' d).1 hb
    exact (cup_iff Dat e ι PD hιc hK hcyc h hh c d).2 (H _ hd)
  · intro H b hb
    obtain ⟨d, hd⟩ := exists_cocycle_of_continuous e ι Dat.ρT' ht' h hh b hb.1
    have hbd : b = fun g => ofV e (d.1 (ι g)) := funext fun g => (hd g).symm
    subst hbd
    have hdZ : d.1 ∈ finZ e PD Dat.ρT' ι := hb
    exact (cup_iff Dat e ι PD hιc hK hcyc h hh c d).1 (H _ ((mem_span_iff Dat.ρT' _ hB' d).2 hdZ))

end GenS

section Rec

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem over_of_row {w : ℕ} (hw : w ∈ K.rowsN i dc) : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i) := by
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
  have hp : v ∈ K.plSet i dc := Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  rw [K.plOf_idx i dc hp]
  exact (dc.cover v).1 (Or.inl hv)

theorem iotaHomeo_rec {w : ℕ} (hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i)) :
    IotaHomeo (Br.iota D.nbr i _ hn) :=
  ⟨Br.ιHomeo (D.nbr i _ hn), fun _ => rfl⟩

variable [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

def RowIn (w : ℕ) : Prop :=
  ∀ hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
    HomeoK (eK (D.nbr i _ hn)) ∧
    TopMatch (eK (D.nbr i _ hn)) (VT w) ∧ TopMatch (eK (D.nbr i _ hn)) (VT' w) ∧
    CycMatch (Dat w) (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) (Br.PD D.loc D.nbr i _ hn) ∧
    IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn)) (Dat w).ρT (Br.iota D.nbr i _ hn))

theorem bk_a_of_admitted_bk_a (hBK : LargeLevelLemmas.BlochKatoAnnihilators i) (hG : K.SelfGood i) {w : ℕ} (hw : w ∈ K.rowsN i dc)
    (hreal : Formalism.RepresentationBoundsCohomology.FIN.RealLat (Dat w)) (hin : RowIn i dc VT VT' Dat w) :
    Formalism.MainNotions.N.KHf.BKa i dc VT VT' Dat w := by
  have hn := over_of_row i dc hw
  obtain ⟨hK, ht, ht', hcyc, hdr⟩ := hin hn
  have hbk : LargeLevelLemmas.bkAAt (Br.PD D.loc D.nbr i _ hn) (Br.LLw (D.nbr i _ hn)) ↥(OL (D.nbr i _ hn).LL) :=
    hBK _ hn (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (hG _ hn)
  intro a
  exact bka_gen (Dat w) (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) (Br.PD D.loc D.nbr i _ hn) hbk hreal (iotaHomeo_rec i dc hn) hK
    ht ht' hcyc hdr (fZ i dc w (Dat w).ρT) (fZ i dc w (Dat w).ρT') (fZ_pos i dc (Dat w).ρT hn)
    (fZ_pos i dc (Dat w).ρT' hn) a

end Rec

end Formalism.MainNotions.N.KBKa
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf

theorem baer_of_div {R Q : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [AddCommGroup Q] [Module R Q]
    (hdiv : ∀ a : R, a ≠ 0 → ∀ y : Q, ∃ q : Q, a • q = y) : Module.Baer R Q := by
  intro I g
  have ha : Submodule.IsPrincipal.generator I ∈ I := Submodule.IsPrincipal.generator_mem I
  by_cases h0 : Submodule.IsPrincipal.generator I = 0
  · refine ⟨0, fun x hx => ?_⟩
    obtain ⟨s, rfl⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).1 hx
    have : (⟨s • Submodule.IsPrincipal.generator I, hx⟩ : I) = 0 := Subtype.ext (by simp [h0])
    rw [this, map_zero, LinearMap.zero_apply]
  · obtain ⟨q, hq⟩ := hdiv _ h0 (g ⟨_, ha⟩)
    refine ⟨LinearMap.toSpanSingleton R Q q, fun x hx => ?_⟩
    obtain ⟨s, rfl⟩ := (Submodule.IsPrincipal.mem_iff_eq_smul_generator I).1 hx
    rw [LinearMap.toSpanSingleton_apply, smul_assoc, hq, ← map_smul]
    rfl

section Gen

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {Ow : Type} [CommRing Ow] [Algebra Ow LL] (eO : O ≃+* Ow)

scoped instance (priority := low) modOwY (V : Type) [AddCommGroup V] [Module (FractionRing O) V] :
    Module Ow (TrV e V) :=
  Module.compHom (TrV e V) (algebraMap Ow LL)

variable {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]

instance towOwY : IsScalarTower Ow LL (TrV e V) :=
  ⟨fun a b v => by
    show (a • b) • v = (algebraMap Ow LL a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩

def trY (v : V) : TrV e V := v

variable {e eO}

theorem smul_OwY (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (c : Ow) (v : V) : (c • trY e v : TrV e V) = trY e (eO.symm c • v) := by
  show (e.symm (algebraMap Ow LL c)) • v = eO.symm c • v
  conv_lhs => rw [← RingEquiv.apply_symm_apply eO c]
  rw [heO, RingEquiv.symm_apply_apply, algebraMap_smul]

variable {M : Type} [AddCommGroup M] [Module O M]

variable (e eO) in
def latTY (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a)) :
    Submodule Ow (TrV e (MK (O := O) M)) where
  carrier := Set.range fun m : M => trY e (mkK (O := O) m)
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add (mkK (O := O) (M := M)) a b⟩
  zero_mem' := ⟨0, map_zero (mkK (O := O) (M := M))⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    refine ⟨eO.symm c • a, ?_⟩
    show trY e (mkK (O := O) (eO.symm c • a)) = c • trY e (mkK (O := O) a)
    rw [smul_OwY heO, map_smul]

def MOY (_eO : O ≃+* Ow) (M : Type) : Type := M

instance : AddCommGroup (MOY eO M) := ‹AddCommGroup M›
instance : Module O (MOY eO M) := ‹Module O M›
instance instModMOY : Module Ow (MOY eO M) := Module.compHom M eO.symm.toRingHom

variable (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))

def latMapY : MOY eO M →ₗ[Ow] ↥(latTY e eO (M := M) heO) where
  toFun m := ⟨trY e (mkK (O := O) (show M from m)), m, rfl⟩
  map_add' a b := Subtype.ext (map_add (mkK (O := O) (M := M)) a b)
  map_smul' c a := Subtype.ext (by
    show trY e (mkK (O := O) (eO.symm c • (show M from a))) = c • trY e (mkK (O := O) (show M from a))
    rw [smul_OwY heO, map_smul])

theorem latMapY_bij (hinj : Function.Injective (mkK (O := O) (M := M))) :
    Function.Bijective (latMapY (eO := eO) (M := M) heO) :=
  ⟨fun a b h => hinj (congrArg Subtype.val h : trY e (mkK (O := O) (show M from a)) = trY e (mkK (show M from b))),
    fun ⟨_, m, hm⟩ => ⟨m, Subtype.ext hm⟩⟩

def latEquivY (hinj : Function.Injective (mkK (O := O) (M := M))) : MOY eO M ≃ₗ[Ow] ↥(latTY e eO (M := M) heO) :=
  LinearEquiv.ofBijective (latMapY heO) (latMapY_bij heO hinj)

def basMOY [Module.Free O M] : Basis (Module.Free.ChooseBasisIndex O M) O (MOY eO M) := Module.Free.chooseBasis O M

theorem free_MOY [Module.Free O M] : Module.Free Ow (MOY eO M) :=
  Module.Free.of_basis ((basMOY (eO := eO)).mapCoeffs eO
    (fun c (x : MOY eO M) => by
      show eO.symm (eO c) • (show M from x) = c • (show M from x)
      rw [RingEquiv.symm_apply_apply]))

theorem finite_MOY [Module.Finite O M] [Module.Free O M] : Module.Finite Ow (MOY eO M) :=
  Module.Finite.of_basis ((basMOY (eO := eO)).mapCoeffs eO
    (fun c (x : MOY eO M) => by
      show eO.symm (eO c) • (show M from x) = c • (show M from x)
      rw [RingEquiv.symm_apply_apply]))

theorem mkK_spanY (v : MK (O := O) M) : ∃ c : O, c ≠ 0 ∧ ∃ m, mkK m = c • v := by
  induction v using LocalizedModule.induction_on with
  | h m s =>
    refine ⟨(s : O), nonZeroDivisors.coe_ne_zero s, m, ?_⟩
    rw [LocalizedModule.smul'_mk]
    show LocalizedModule.mk m 1 = _
    rw [LocalizedModule.mk_eq]
    exact ⟨1, by simp [Submonoid.smul_def]⟩

theorem mkK_injY [NoZeroSMulDivisors O M] : Function.Injective (mkK (O := O) (M := M)) := by
  intro a b h
  obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := nonZeroDivisors O) (f := mkK (O := O) (M := M)) h
  rw [Submonoid.smul_def, Submonoid.smul_def] at hc
  exact smul_right_injective M (nonZeroDivisors.coe_ne_zero c) hc

variable {Γ G : Type} [Group Γ] [Group G] (ι : G →* Γ)

def latY [Module.Finite O M] [Module.Free O M] [NoZeroSMulDivisors O M] (ρM : Representation O Γ M) :
    Lattice (O := Ow) (repL e (locRep ρM) ι) where
  T := latTY e eO heO
  stable g := by
    rintro _ ⟨m, rfl⟩
    exact ⟨ρM (ι g) m, (locRep_mkK ρM (ι g) m).symm⟩
  fg := by
    haveI := finite_MOY (eO := eO) (M := M)
    haveI : Module.Finite Ow ↥(latTY e eO (M := M) heO) := Module.Finite.equiv (latEquivY heO mkK_injY)
    exact (Module.Finite.iff_fg).1 inferInstance
  free := by
    haveI := free_MOY (eO := eO) (M := M)
    exact Module.Free.of_equiv (latEquivY heO mkK_injY)
  span := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, hc, m, hm⟩ := mkK_spanY (O := O) (show MK (O := O) M from v)
    have hk : algebraMap O (FractionRing O) c ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
    have hv0 : (show MK (O := O) M from v) = (algebraMap O (FractionRing O) c)⁻¹ • mkK m := by
      rw [hm, ← algebraMap_smul (FractionRing O) c (show MK (O := O) M from v), smul_smul, inv_mul_cancel₀ hk, one_smul]
    have hv : v = e (algebraMap O (FractionRing O) c)⁻¹ • trY e (mkK (O := O) m) := by
      show (show MK (O := O) M from v) = e.symm (e (algebraMap O (FractionRing O) c)⁻¹) • mkK m
      rw [RingEquiv.symm_apply_apply, hv0]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

end Gen

section Gen2

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  {e : FractionRing O ≃+* LL} {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {Γ G : Type} [Group Γ] [Group G] (ι : G →* Γ)
  {N : Type} [AddCommGroup N] [Module O N]

variable (e) in
def eLin : TrV e (FractionRing O) →ₗ[LL] LL where
  toFun x := e (show FractionRing O from x)
  map_add' x y := map_add e _ _
  map_smul' c x := by
    show e (e.symm c * (show FractionRing O from x)) = c * e (show FractionRing O from x)
    rw [map_mul, RingEquiv.apply_symm_apply]

variable (e N) in
def pY : TrV e (MK (O := O) (N × O)) →ₗ[LL] LL :=
  eLin e ∘ₗ trL e (liftK (V := FractionRing O) (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O N O))

theorem pY_mk (m : N × O) : pY e N (trY e (mkK (O := O) m)) = e (algebraMap O (FractionRing O) m.2) := by
  show e (liftK (V := FractionRing O) (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O N O) (mkK m)) = _
  rw [liftK_mkK]
  rfl

theorem pY_inv (ρM : Representation O Γ (N × O)) (h2 : ∀ g m, (ρM g m).2 = m.2) (g : G)
    (v : TrV e (MK (O := O) (N × O))) : pY e N (repL e (locRep ρM) ι g v) = pY e N v := by
  have h := liftK_equiv (Representation.trivial O Γ (FractionRing O)) ρM
    (Algebra.linearMap O (FractionRing O) ∘ₗ LinearMap.snd O N O)
    (fun g m => by
      show algebraMap O (FractionRing O) (ρM g m).2 = algebraMap O (FractionRing O) m.2
      rw [h2]) (ι g) (show MK (O := O) (N × O) from v)
  show e (liftK _ (locRep ρM (ι g) (show MK (O := O) (N × O) from v))) = e (liftK _ (show MK (O := O) (N × O) from v))
  rw [h]
  rfl

include heO in
theorem pY_int (v : TrV e (MK (O := O) (N × O))) (hv : ∃ m : N × O, trY e (mkK (O := O) m) = v) :
    pY e N v ∈ Set.range (algebraMap Ow LL) := by
  obtain ⟨m, rfl⟩ := hv
  rw [pY_mk, ← heO]
  exact ⟨_, rfl⟩

theorem pY_zero (m : N × O) (h : pY e N (trY e (mkK (O := O) m)) = 0) : m.2 = 0 := by
  rw [pY_mk] at h
  have h1 : algebraMap O (FractionRing O) m.2 = 0 := by
    rwa [map_eq_zero_iff e e.injective] at h
  exact (IsFractionRing.injective O (FractionRing O)) (h1.trans (map_zero _).symm)

include heO in
theorem div_quot {V : Type} [AddCommGroup V] [Module LL V] [Module Ow V] [IsScalarTower Ow LL V]
    (T : Submodule Ow V) (a : O) (ha : a ≠ 0) (y : V ⧸ T) : ∃ q : V ⧸ T, eO a • q = y := by
  induction y using Submodule.Quotient.induction_on with
  | H v =>
    have hc : algebraMap Ow LL (eO a) ≠ 0 := by
      rw [heO]
      exact (map_ne_zero e).2 (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha))
    refine ⟨Submodule.Quotient.mk ((algebraMap Ow LL (eO a))⁻¹ • v), ?_⟩
    rw [← Submodule.Quotient.mk_smul, ← algebraMap_smul LL (eO a), smul_smul, mul_inv_cancel₀ hc, one_smul]

theorem nzsd_prod [NoZeroSMulDivisors O N] : NoZeroSMulDivisors O (N × O) :=
  ⟨fun {c x} h => by
    by_cases hc : c = 0
    · exact Or.inl hc
    · right
      have h1 : c • x.1 = 0 := congrArg Prod.fst h
      have h2 : c * x.2 = 0 := congrArg Prod.snd h
      exact Prod.ext ((smul_eq_zero.1 h1).resolve_left hc) ((mul_eq_zero.1 h2).resolve_left hc)⟩

include heO in
theorem ext_of_baer [IsPrincipalIdealRing O] [NoZeroSMulDivisors O N] {Q : Type} [AddCommGroup Q] [Module Ow Q]
    (hdiv : ∀ a : O, a ≠ 0 → ∀ y : Q, ∃ q : Q, eO a • q = y) (g₀ : N →+ Q)
    (hg : ∀ (a : O) (n : N), g₀ (a • n) = eO a • g₀ n) :
    ∃ φ : TrV e (MK (O := O) (N × O)) →ₗ[Ow] Q, ∀ n : N, φ (trY e (mkK (O := O) (n, (0 : O)))) = g₀ n := by
  letI : Module O Q := Module.compHom Q eO.toRingHom
  have hB : Module.Baer O Q := baer_of_div fun a ha y => hdiv a ha y
  let f : N →ₗ[O] MK (O := O) (N × O) := mkK ∘ₗ LinearMap.inl O N O
  haveI := nzsd_prod (O := O) (N := N)
  have hf : Function.Injective f := mkK_injY.comp LinearMap.inl_injective
  let g : N →ₗ[O] Q := { toFun := g₀, map_add' := g₀.map_add, map_smul' := fun a n => hg a n }
  obtain ⟨h, hh⟩ := hB.extension_property f hf g
  refine ⟨⟨⟨fun v => h (show MK (O := O) (N × O) from v), fun x y => h.map_add _ _⟩, fun c v => ?_⟩,
    fun n => LinearMap.congr_fun hh n⟩
  have hs := smul_OwY (V := MK (O := O) (N × O)) heO c (show MK (O := O) (N × O) from v)
  show h (show MK (O := O) (N × O) from (c • v)) = c • h (show MK (O := O) (N × O) from v)
  have hs' : (show MK (O := O) (N × O) from (c • v)) = eO.symm c • (show MK (O := O) (N × O) from v) := hs
  rw [hs', h.map_smul]
  show eO (eO.symm c) • h _ = _
  rw [RingEquiv.apply_symm_apply]

end Gen2

end Formalism.MainNotions.N.K.TBa

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf

section Mk

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL]
  {e : FractionRing O ≃+* LL} {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] (ι : G →* Γ)
  {N : Type} [AddCommGroup N] [Module O N] [Module.Finite O N] [Module.Free O (N × O)] [NoZeroSMulDivisors O (N × O)]
  (Qp : Type) [Field Qp] [Algebra Qp LL]
  (ρM : Representation O Γ (N × O)) (h2 : ∀ g m, (ρM g m).2 = m.2)
  [FiniteDimensional LL (TrV e (MK (O := O) (N × O)))]
  (hcont : ∀ x, Continuous fun g => repL e (locRep ρM) ι g x)

def mkYt : YtLat (G := G) (Qp := Qp) LL Ow where
  V := TrV e (MK (O := O) (N × O))
  ρ := repL e (locRep ρM) ι
  L := latY heO ι ρM
  cont := hcont
  p := pY e N
  p_inv g v := pY_inv ι ρM h2 g v
  p_int v hv := pY_int heO v hv
  e₀ := trY e (mkK (O := O) ((0 : N), (1 : O)))
  e₀_mem := ⟨_, rfl⟩
  p_e₀ := by rw [pY_mk]; simp

end Mk

section GenY

variable {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
  {A T' GG : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group GG]
  (r : GG →* A) (χ : GG →* T'ˣ) (E : A)

theorem nzsdY [NoZeroSMulDivisors O A] : NoZeroSMulDivisors O ↥(Ymod r χ E) :=
  Function.Injective.noZeroSMulDivisors (fun y : ↥(Ymod r χ E) => (y : A)) Subtype.val_injective rfl
    (fun _ _ => rfl)

theorem finY [Module.Finite O A] : Module.Finite O ↥(Ymod r χ E) := by
  haveI : IsNoetherian O A := isNoetherian_of_isNoetherianRing_of_finite O A
  let f : ↥(Ymod r χ E) →ₗ[O] A :=
    { toFun := fun y => (y : A), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective f Subtype.val_injective

theorem freeY [Module.Finite O A] [NoZeroSMulDivisors O A] : Module.Free O (↥(Ymod r χ E) × O) := by
  haveI := finY (O := O) r χ E
  haveI := nzsdY (O := O) r χ E
  haveI := nzsd_prod (O := O) (N := ↥(Ymod r χ E))
  exact Module.free_of_finite_type_torsion_free'

theorem ytRep_zero (g : GG) (y : ↥(Ymod r χ E)) : ytRep O r χ E g (y, 0) = (uElt r χ g • y, 0) :=
  Prod.ext (by
    show uElt r χ g • y + (0 : O) • yY r χ E g = _
    rw [zero_smul, add_zero]) rfl

theorem ytRep_e (g : GG) : ytRep O r χ E g (0, 1) = (yY r χ E g, 1) :=
  Prod.ext (by
    show uElt r χ g • (0 : ↥(Ymod r χ E)) + (1 : O) • yY r χ E g = _
    rw [smul_zero, one_smul, zero_add]) rfl

end GenY

section GenT

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {Ow : Type} [CommRing Ow] [Algebra Ow LL]
    {O : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    {e : FractionRing O ≃+* LL} {eO : O ≃+* Ow}
    (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    {A T' GG : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group GG]
    (r : GG →* A) (χ : GG →* T'ˣ) (E : A) (Dw : Subgroup GG) (eG : ↥Dw ≃* G)

abbrev ytVG : Representation LL G (TrV e (MK (O := O) (↥(Ymod r χ E) × O))) :=
  repL e (locRep (resRep (ytRep O r χ E) Dw)) eG.symm.toMonoidHom

variable (Qp) in
def ytG [Module.Finite O A] [NoZeroSMulDivisors O A] (hfd : FiniteDimensional LL (TrV e (MK (O := O) (↥(Ymod r χ E) × O))))
    (hcont : ∀ x, Continuous fun g => ytVG (e := e) r χ E Dw eG g x) : YtLat (G := G) (Qp := Qp) LL Ow :=
  haveI := finY (O := O) r χ E
  haveI := freeY (O := O) r χ E
  haveI := nzsdY (O := O) r χ E
  haveI := nzsd_prod (O := O) (N := ↥(Ymod r χ E))
  mkYt heO eG.symm.toMonoidHom Qp (resRep (ytRep O r χ E) Dw) (fun _ _ => rfl) hcont

theorem ytG_psi [Module.Finite O A] [NoZeroSMulDivisors O A] (hfd : FiniteDimensional LL (TrV e (MK (O := O) (↥(Ymod r χ E) × O))))
    (hcont : ∀ x, Continuous fun g => ytVG (e := e) r χ E Dw eG g x)
    {M : Type} [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M] {e' : ℕ}
    (Cd : CoefDict PD LL Ow eO M r χ Dw eG e') :
    PsiExt eO r χ E Dw eG (ytG Qp heO r χ E Dw eG hfd hcont) Cd := by
  intro ψ hψe
  haveI := nzsdY (O := O) r χ E
  obtain ⟨φ, hφ⟩ := ext_of_baer (e := e) (eO := eO) heO (N := ↥(Ymod r χ E)) (Q := Cd.Ce.V ⧸ Cd.Ce.L.T)
    (div_quot heO Cd.Ce.L.T) (Cd.u.toAddMonoidHom.comp ψ.toAddMonoidHom)
    (fun a n => by
      show Cd.u (ψ (a • n)) = _
      rw [ψ.map_smul, Cd.u_smul]
      rfl)
  refine ⟨φ, ?_, ?_⟩
  · intro g y hy hp
    obtain ⟨⟨n, c0⟩, rfl⟩ := hy
    have hc0 : c0 = 0 := pY_zero (m := (n, c0)) hp
    subst hc0
    show φ (trY e (locRep (resRep (ytRep O r χ E) Dw) (eG.symm g) (mkK (n, (0 : O))))) =
      actD Cd.Ce.L g (φ (trY e (mkK (n, (0 : O)))))
    rw [locRep_mkK]
    show φ (trY e (mkK (ytRep O r χ E ((eG.symm g : ↥Dw) : GG) (n, (0 : O))))) = _
    rw [ytRep_zero, hφ, hφ]
    show Cd.u (ψ _) = _
    rw [hψe _ (eG.symm g).2 n, Cd.u_act (eG.symm g) (ψ n), MulEquiv.apply_symm_apply]
    rfl
  · intro γ
    show φ (trY e (locRep (resRep (ytRep O r χ E) Dw) (eG.symm (eG γ)) (mkK ((0 : ↥(Ymod r χ E)), (1 : O)))) -
        trY e (mkK ((0 : ↥(Ymod r χ E)), (1 : O)))) = _
    rw [MulEquiv.symm_apply_apply, locRep_mkK]
    show φ (trY e (mkK (ytRep O r χ E (γ : GG) ((0 : ↥(Ymod r χ E)), (1 : O)))) -
        trY e (mkK ((0 : ↥(Ymod r χ E)), (1 : O)))) = _
    rw [ytRep_e]
    have h3 : (mkK (O := O) (yY r χ E (γ : GG), (1 : O)) - mkK (O := O) ((0 : ↥(Ymod r χ E)), (1 : O)) :
          MK (O := O) (↥(Ymod r χ E) × O)) = mkK (O := O) (yY r χ E (γ : GG), (0 : O)) := by
      rw [← map_sub]
      congr 1
      ext <;> simp
    exact (congrArg φ h3).trans (hφ _)

theorem ytG_crys [Module.Finite O A] [NoZeroSMulDivisors O A] (hfd : FiniteDimensional LL (TrV e (MK (O := O) (↥(Ymod r χ E) × O))))
    (hcont : ∀ x, Continuous fun g => ytVG (e := e) r χ E Dw eG g x)
    (hF : TruncatedSeriesCountingIdentities.FontaineAt PD LL Ow) {ιx : Type} {k : ℕ} (Ms : ιx → G →* Matrix (Fin k) (Fin k) LL)
    (hMc : ∀ x, Continuous (Ms x)) (hMs : ∀ x, IsCrys PD (matRep (Ms x))) {m : ℕ} (xs : Fin m → ιx)
    (φ : TrV e (MK (O := O) (↥(Ymod r χ E) × O)) →ₗ[LL] (Fin m → Fin k → LL)) (hφ : Function.Injective φ)
    (heq : ∀ g v, φ (ytVG (e := e) r χ E Dw eG g v) = fun a => (Ms (xs a) g).mulVec (φ v a)) :
    IsCrys PD (ytG Qp heO r χ E Dw eG hfd hcont).ρ ∧
      ∀ τ a, IsJumpV PD (ytG Qp heO r χ E Dw eG hfd hcont).ρ τ a → ∃ x, IsJumpV PD (matRep (Ms x)) τ a := by
  let Ag : GRep G Qp LL Ow :=
    { V := TrV e (MK (O := O) (↥(Ymod r χ E) × O)), ρ := ytVG (e := e) r χ E Dw eG, cont := hcont }
  exact crys_of_inj PD Ms hF hMc hMs Ag xs φ hφ heq

end GenT

end Formalism.MainNotions.N.K.TBa

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KFin

open Formalism.NG

section Gen

variable {O : Type} [CommRing O] [IsDomain O] {Γ : Type} [Group Γ]
  {L : Type} [AddCommGroup L] [Module O L]
  {V : Type} [AddCommGroup V] [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
  {M : Type} [AddCommGroup M] [Module O M]
  (ρL : Representation O Γ L) (ρV : Representation O Γ V) (ρM : Representation O Γ M)
  (iL : L →ₗ[O] V) (qV : V →ₗ[O] M) (Zf : Submodule (FractionRing O) (Γ → V))

def finPreG : Submodule O (Γ → L) := (Zf.restrictScalars O).comap (LinearMap.compLeft iL Γ)

def FfG : Submodule O (H1z ρL) := ((finPreG iL Zf).comap (coZ1s ρL).subtype).map (Submodule.mkQ _)

def ImageOfFiniteCocycles : Submodule O (H1z ρM) :=
  (((Zf.restrictScalars O).map (LinearMap.compLeft qV Γ) ⊔ coB1 ρM).comap (coZ1s ρM).subtype).map (Submodule.mkQ _)

theorem FfG_sat (hB : ∀ v : V, coD0 ρV v ∈ Zf) (hiL : ∀ g m, iL (ρL g m) = ρV g (iL m))
    (c : O) (z : H1z ρL) (hc : c ≠ 0) (hz : c • z ∈ FfG ρL iL Zf) : z ∈ FfG ρL iL Zf := by
  obtain ⟨z₀, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  unfold FfG at hz ⊢
  rw [Submodule.mem_map] at hz
  obtain ⟨w, hw, hwz⟩ := hz
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq] at hwz
  rw [Submodule.mem_comap] at hwz hw
  unfold coB1 at hwz
  rw [LinearMap.mem_range] at hwz
  obtain ⟨m, hm⟩ := hwz
  apply Submodule.mem_map_of_mem
  rw [Submodule.mem_comap]
  unfold finPreG at hw ⊢
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem] at hw ⊢
  have hc' : algebraMap O (FractionRing O) c ≠ 0 := by
    intro h0
    exact hc ((IsFractionRing.injective O (FractionRing O)) (by rw [h0, map_zero]))
  have key : LinearMap.compLeft iL Γ (z₀ : Γ → L) =
      (algebraMap O (FractionRing O) c)⁻¹ • (LinearMap.compLeft iL Γ (w : Γ → L) - coD0 ρV (iL m)) := by
    funext g
    have hmg : ρL g m - m = (w : Γ → L) g - c • (z₀ : Γ → L) g := congrFun hm g
    show iL ((z₀ : Γ → L) g) = (algebraMap O (FractionRing O) c)⁻¹ • (iL ((w : Γ → L) g) - (ρV g (iL m) - iL m))
    rw [← hiL, ← map_sub, ← map_sub, hmg, sub_sub_cancel, map_smul,
      ← algebraMap_smul (FractionRing O) c (iL ((z₀ : Γ → L) g)), smul_smul, inv_mul_cancel₀ hc', one_smul]
  have hfin : LinearMap.compLeft iL Γ (z₀ : Γ → L) ∈ Zf := by
    rw [key]
    exact Zf.smul_mem _ (Zf.sub_mem hw (hB _))
  exact hfin

theorem mem_image_of_tensor_sum (tens : L →ₗ[O] KO O →ₗ[O] M)
    (htens : ∀ v (x : FractionRing O), tens v (Submodule.Quotient.mk x) = qV (x • iL v))
    {ι : Type} [Fintype ι] (κ : ι → Γ → L) (hκ : ∀ a, (fun g => iL (κ a g)) ∈ Zf)
    (z : coZ1s ρM) (x : ι → KO O) (hz : ∀ g, (z : Γ → M) g = ∑ a, tens (κ a g) (x a)) :
    Submodule.mkQ _ z ∈ ImageOfFiniteCocycles ρM qV Zf := by
  choose y hy using fun a => Submodule.Quotient.mk_surjective _ (x a)
  unfold ImageOfFiniteCocycles
  apply Submodule.mem_map_of_mem
  rw [Submodule.mem_comap]
  apply Submodule.mem_sup_left
  rw [Submodule.mem_map]
  refine ⟨∑ a, y a • (fun g => iL (κ a g)), ?_, ?_⟩
  · rw [Submodule.restrictScalars_mem]
    exact Zf.sum_mem (fun a _ => Zf.smul_mem _ (hκ a))
  · funext g
    show qV ((∑ a, y a • (fun g => iL (κ a g))) g) = (z : Γ → M) g

    rw [hz g, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [← hy a, htens]
    rfl

def LatBasisG (j : ℕ) : Prop :=
  ∃ κ' : Fin j → coZ1s ρL, (∀ a, (fun g => iL ((κ' a : Γ → L) g)) ∈ Zf) ∧
    (∀ z ∈ FfG ρL iL Zf, ∃ (b : Fin j → O) (c : O), c ≠ 0 ∧
      c • (z - ∑ a, b a • (Submodule.mkQ _ (κ' a) : H1z ρL)) = 0) ∧
    (∀ (b : Fin j → O) (c : O), c ≠ 0 → c • ∑ a, b a • (Submodule.mkQ _ (κ' a) : H1z ρL) = 0 → b = 0)

def kapG (j : ℕ) : Fin j → coZ1s ρL :=
  if h : LatBasisG ρL iL Zf j then h.choose else fun _ => 0

theorem kapG_fin (j : ℕ) (a : Fin j) : (fun g => iL ((kapG ρL iL Zf j a : Γ → L) g)) ∈ Zf := by
  by_cases h : LatBasisG ρL iL Zf j
  · have e : kapG ρL iL Zf j = h.choose := dite_eq_left h
    rw [e]
    exact h.choose_spec.1 a
  · have e : kapG ρL iL Zf j = fun _ => 0 := dite_eq_right h
    rw [e]
    convert Zf.zero_mem using 1
    ext g
    simp

theorem kapG_eq {j : ℕ} (h : LatBasisG ρL iL Zf j) : kapG ρL iL Zf j = h.choose := dite_eq_left h

theorem kapG_basis {j : ℕ} (h : LatBasisG ρL iL Zf j) :
    (∀ z ∈ FfG ρL iL Zf, ∃ (b : Fin j → O) (c : O), c ≠ 0 ∧
      c • (z - ∑ a, b a • (Submodule.mkQ _ (kapG ρL iL Zf j a) : H1z ρL)) = 0) ∧
    (∀ (b : Fin j → O) (c : O), c ≠ 0 →
      c • ∑ a, b a • (Submodule.mkQ _ (kapG ρL iL Zf j a) : H1z ρL) = 0 → b = 0) := by
  rw [kapG_eq (h := h)]
  exact h.choose_spec.2

theorem kapG_mem' (j : ℕ) (a : Fin j) : Submodule.mkQ _ (kapG ρL iL Zf j a) ∈ FfG ρL iL Zf := by
  unfold FfG
  apply Submodule.mem_map_of_mem
  rw [Submodule.mem_comap]
  unfold finPreG
  rw [Submodule.mem_comap, Submodule.restrictScalars_mem]
  exact kapG_fin ρL iL Zf j a

theorem latBasisG_of [IsPrincipalIdealRing O] (j : ℕ) (hfg : Module.Finite O ↥(FfG ρL iL Zf))
    (hrk : Module.finrank O (↥(FfG ρL iL Zf) ⧸ Submodule.torsion O ↥(FfG ρL iL Zf)) = j) :
    LatBasisG ρL iL Zf j := by
  classical
  haveI := hfg
  haveI hfree : Module.Free O (↥(FfG ρL iL Zf) ⧸ Submodule.torsion O ↥(FfG ρL iL Zf)) := by
    first
      | exact Module.free_of_finite_type_torsion_free'
  let e := Module.finBasisOfFinrankEq _ _ hrk
  choose f hf using fun a => Submodule.Quotient.mk_surjective (Submodule.torsion O ↥(FfG ρL iL Zf)) (e a)
  have hw : ∀ a, ∃ w : ↥(coZ1s ρL), w ∈ (finPreG iL Zf).comap (coZ1s ρL).subtype ∧
      Submodule.mkQ _ w = ((f a : ↥(FfG ρL iL Zf)) : H1z ρL) := by
    intro a
    have h := (f a).2
    unfold FfG at h
    rw [Submodule.mem_map] at h
    exact h
  choose w hwmem hwf using hw
  refine ⟨w, ?_, ?_, ?_⟩
  · intro a
    have h := hwmem a
    rw [Submodule.mem_comap] at h
    unfold finPreG at h
    rw [Submodule.mem_comap, Submodule.restrictScalars_mem] at h
    exact h
  · intro z hz
    let zF : ↥(FfG ρL iL Zf) := ⟨z, hz⟩
    let b := e.repr (Submodule.Quotient.mk zF)
    refine ⟨fun a => b a, ?_⟩
    have hmem : zF - ∑ a, b a • f a ∈ Submodule.torsion O ↥(FfG ρL iL Zf) := by

      rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sub, map_sum]
      simp only [map_smul, Submodule.mkQ_apply, hf]
      rw [sub_eq_zero]
      exact (e.sum_repr _).symm
    obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff _).1 hmem
    refine ⟨(c : O), ?_, ?_⟩
    · first
        | exact nonZeroDivisors.coe_ne_zero c
    · have h2 := congrArg Subtype.val hc
      simpa [zF, Submonoid.smul_def, Submodule.coe_smul, Submodule.coe_sub, Submodule.coe_sum, ← hwf] using h2
  · intro b c hc hsum
    have hF : (c • ∑ a, b a • f a : ↥(FfG ρL iL Zf)) = 0 := by
      apply Subtype.ext
      simpa [Submodule.coe_smul, Submodule.coe_sum, ← hwf] using hsum
    have hT : ∑ a, b a • f a ∈ Submodule.torsion O ↥(FfG ρL iL Zf) :=
      (Submodule.mem_torsion_iff _).2 ⟨⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩, hF⟩
    have h0 : (Submodule.torsion O ↥(FfG ρL iL Zf)).mkQ (∑ a, b a • f a) = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hT

    rw [map_sum] at h0
    simp only [map_smul, Submodule.mkQ_apply, hf] at h0
    exact funext (Fintype.linearIndependent_iff.1 e.linearIndependent b h0)

end Gen

section Lat

open Formalism.RepresentationBoundsCohomology.SF

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type} [Ring A]
  (n : Type) [Fintype n] [DecidableEq n] (ρ : A →+* Matrix n n O)

theorem iLM_smul (a : A) (u : LatM O O n ρ) : iLM O n ρ (a • u) = a • iLM O n ρ u := by
  funext k
  show algebraMap O (FractionRing O) (∑ j, (ρ a) k j • u j) =
    ∑ j, (ρ a) k j • algebraMap O (FractionRing O) (u j)

  rw [map_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [smul_eq_mul, map_mul, Algebra.smul_def]

theorem tensM_mk (u : LatM O O n ρ) (x : FractionRing O) :
    tensM O n ρ u (Submodule.Quotient.mk x) = qVM O n ρ (x • iLM O n ρ u) := by
  funext a
  show u a • (Submodule.Quotient.mk x : KO O) =
    (1 : Submodule O (FractionRing O)).mkQ (x • algebraMap O (FractionRing O) (u a))
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply]
  congr 1
  rw [Algebra.smul_def, smul_eq_mul, mul_comm]

end Lat

section Rec

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev Lr : Type := LatM (D.nd.O i) (D.nd.O i) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

abbrev Vr : Type := LatM (D.nd.O i) (FractionRing (D.nd.O i)) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

abbrev iLr : Lr i Dd →ₗ[D.nd.O i] Vr i Dd := iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom

abbrev qVr : Vr i Dd →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0 := qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom

abbrev tensr : Lr i Dd →ₗ[D.nd.O i] KO (D.nd.O i) →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0 :=
  tensM (D.nd.O i) _ (Dd.ρk 0).toRingHom

abbrev Γc (l : K.Col i dc) := KHf.Γn i dc (K.colIdx i dc l)

abbrev ρL (l : K.Col i dc) : Representation (D.nd.O i) ↥(Γc i dc l) (Lr i Dd) :=
  resRep (uRep (D.nd.O i) (M := Lr i Dd) Dd.r Dd.χ) (Γc i dc l)

abbrev ρV (l : K.Col i dc) : Representation (D.nd.O i) ↥(Γc i dc l) (Vr i Dd) :=
  resRep (uRep (D.nd.O i) (M := Vr i Dd) Dd.r Dd.χ) (Γc i dc l)

abbrev ρM (l : K.Col i dc) : Representation (D.nd.O i) ↥(Γc i dc l) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) :=
  resRep (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ) (Γc i dc l)

abbrev Zf (l : K.Col i dc) : Submodule (FractionRing (D.nd.O i)) (↥(Γc i dc l) → Vr i Dd) :=
  KHf.fZ i dc (K.colIdx i dc l) (ρV i dc Dd l)

abbrev Ffr (l : K.Col i dc) := KHf.Ff i dc Dd.r Dd.χ (iLr i Dd) l

variable (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

abbrev jr : ℕ → ℕ := KHf.jK i dc ρ π

def CobFin (l : K.Col i dc) : Prop := ∀ v : Vr i Dd, coD0 (ρV i dc Dd l) v ∈ Zf i dc Dd l

def LatBasis (l : K.Col i dc) : Prop :=
  LatBasisG (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l) (jr i dc ρ π (K.colIdx i dc l))

def κz (l : K.Col i dc) (a : Fin (jr i dc ρ π (K.colIdx i dc l))) :
    coZ1s (resRep (uRep (D.nd.O i) (M := Lr i Dd) Dd.r Dd.χ) (Γc i dc l)) :=
  kapG (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l) (jr i dc ρ π (K.colIdx i dc l)) a

def κ (l : K.Col i dc) (a : Fin (jr i dc ρ π (K.colIdx i dc l))) (g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om) : Lr i Dd :=
  if h : g ∈ Γc i dc l then (κz i dc Dd ρ π l a : ↥(Γc i dc l) → Lr i Dd) ⟨g, h⟩ else 0

theorem cobFin_of (l : K.Col i dc) (h : KHf.OrbC i dc (ρV i dc Dd l)) : CobFin i dc Dd l := by
  intro v
  show coD0 (ρV i dc Dd l) v ∈ KHf.fZ i dc (K.colIdx i dc l) (ρV i dc Dd l)
  unfold KHf.fZ
  split
  · rename_i hn
    have hO := h hn
    simp only [KHf.finZ, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
    refine ⟨⟨?_, ?_⟩, TensorProduct.tmul _ v 1, ?_⟩
    · exact (hO v).sub continuous_const
    · intro g g'
      show (ρV i dc Dd l) (Br.iota D.nbr i _ hn (g * g')) v - v =
        ((ρV i dc Dd l) (Br.iota D.nbr i _ hn g) v - v) +
          (ρV i dc Dd l) (Br.iota D.nbr i _ hn g) ((ρV i dc Dd l) (Br.iota D.nbr i _ hn g') v - v)
      have hm : ∀ w : Vr i Dd, (ρV i dc Dd l) (Br.iota D.nbr i _ hn (g * g')) w =
          (ρV i dc Dd l) (Br.iota D.nbr i _ hn g) ((ρV i dc Dd l) (Br.iota D.nbr i _ hn g') w) := by
        intro w
        rw [map_mul]
        exact LinearMap.congr_fun ((ρV i dc Dd l).map_mul _ _) w
      rw [hm, map_sub]
      abel
    · intro g
      unfold Formalism.WeaklyAdmissibleFiltrations.actVB
      erw [TensorProduct.AlgebraTensorModule.map_tmul]
      have h1 : ((Br.PD D.loc D.nbr i _ hn).actB g).toAlgHom 1 = 1 := map_one _
      simp only [LinearMap.coe_restrictScalars, AlgHom.toLinearMap_apply, h1]
      erw [← TensorProduct.sub_tmul]
      rfl
  · exact Submodule.mem_top

def FinFf (l : K.Col i dc) : Prop := Module.Finite (D.nd.O i) ↥(FfG (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l))

def RankFf (l : K.Col i dc) : Prop :=
  Module.finrank (D.nd.O i) (↥(FfG (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l)) ⧸
      Submodule.torsion (D.nd.O i) ↥(FfG (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l))) =
    jr i dc ρ π (K.colIdx i dc l)

theorem latBasis_of (l : K.Col i dc) (hf : FinFf i dc Dd l) (hr : RankFf i dc Dd ρ π l) : LatBasis i dc Dd ρ π l := latBasisG_of _ _ _ _ hf hr

theorem κ_mem (l : K.Col i dc) a (g : ↥(Γc i dc l)) :
    κ i dc Dd ρ π l a g = (κz i dc Dd ρ π l a : ↥(Γc i dc l) → Lr i Dd) g := by
  unfold κ
  rw [dite_eq_left g.2]

theorem iL_equiv (l : K.Col i dc) (g : ↥(Γc i dc l)) (m : Lr i Dd) :
    iLr i Dd (ρL i dc Dd l g m) = ρV i dc Dd l g (iLr i Dd m) := iLM_smul (D.nd.O i) _ (Dd.ρk 0).toRingHom (Formalism.NG.uElt Dd.r Dd.χ (g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om)) m

theorem finRhoAt (l : K.Col i dc) (hB : CobFin i dc Dd l) (hL : LatBasis i dc Dd ρ π l) :
    KHf.FinRhoAt i dc Dd.r Dd.χ (Ffr i dc Dd) (jr i dc ρ π) (κ i dc Dd ρ π) (κz i dc Dd ρ π) l := by
  unfold KHf.FinRhoAt
  refine ⟨fun a g => (κ_mem i dc Dd ρ π l a g).symm, ?_, fun a => ?_, ?_, ?_⟩
  · intro c z hc hz
    exact FfG_sat _ _ _ _ hB (iL_equiv i dc Dd l) c z hc hz
  · exact _root_.Formalism.MainNotions.N.KFin.kapG_mem' _ _ _ _ a
  · exact (kapG_basis (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l) hL).1
  · exact (kapG_basis (ρL i dc Dd l) (iLr i Dd) (Zf i dc Dd l) hL).2

theorem clause3 (l : K.Col i dc) (z : coZ1s (ρM i dc Dd l)) (x : Fin (jr i dc ρ π (K.colIdx i dc l)) → KO (D.nd.O i))
    (hz : ∀ g : ↥(Γc i dc l), (z : ↥(Γc i dc l) → blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) g =
      ∑ a, tensr i Dd (κ i dc Dd ρ π l a g) (x a)) :
    Submodule.mkQ _ z ∈ KHf.F0col i dc (K.colIdx i dc l) (ρV i dc Dd l) (ρM i dc Dd l) (qVr i Dd) := by
  have hκ : ∀ a, (fun g : ↥(Γc i dc l) => iLr i Dd (κ i dc Dd ρ π l a g)) ∈ Zf i dc Dd l := by
    intro a
    have e : (fun g : ↥(Γc i dc l) => iLr i Dd (κ i dc Dd ρ π l a g)) =
        fun g => iLr i Dd ((κz i dc Dd ρ π l a : ↥(Γc i dc l) → Lr i Dd) g) := by
      funext g
      rw [κ_mem]
    rw [e]
    exact kapG_fin _ _ _ _ a
  exact mem_image_of_tensor_sum (ρM i dc Dd l) (iLr i Dd) (qVr i Dd) (Zf i dc Dd l) (tensr i Dd)
    (fun v x => tensM_mk _ _ _ v x) (fun a g => κ i dc Dd ρ π l a g) hκ z x hz

theorem finRhoAt_of (l : K.Col i dc) (hO : KHf.OrbC i dc (ρV i dc Dd l)) (hf : FinFf i dc Dd l)
    (hr : RankFf i dc Dd ρ π l) :
    KHf.FinRhoAt i dc Dd.r Dd.χ (Ffr i dc Dd) (jr i dc ρ π) (κ i dc Dd ρ π) (κz i dc Dd ρ π) l := finRhoAt i dc Dd ρ π l (cobFin_of i dc Dd l hO) (latBasis_of i dc Dd ρ π l hf hr)

end Rec

section Unr

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.RepresentationBoundsCohomology.FIN ReciprocityTheory.Gal

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (δO : D.nd.O i)

abbrev Icol (l : K.Col i dc) : Subgroup ↥(Γc i dc l) :=
  (Ine (F := D.host.E) (K.Aw i dc (K.colIdx i dc l))).subgroupOf (decs D.host.E (K.Aw i dc) (K.colIdx i dc l))

def UnrAdm (l : K.Col i dc) (f : ↥(Γc i dc l) → D.nd.O i) : Prop :=
  (∀ g h, f (g * h) = f g + f h) ∧ (∀ g ∈ Icol i dc l, f g = 0) ∧
    ∀ hn : K.plOf i dc (K.colIdx i dc l) ∈ placesOver D.host.E (D.nd.l i),
      Continuous fun g => KHf.eK (D.nbr i _ hn)
        (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (f (Br.iota D.nbr i _ hn g)))

def UnrHom (l : K.Col i dc) : Prop := ∃ f, UnrAdm i dc l f ∧ ∃ g, f g = 1

def uzOf (l : K.Col i dc) (f : ↥(Γc i dc l) → D.nd.O i) (hf : ∀ g h, f (g * h) = f g + f h) :
    Formalism.NG.coZ1s (Representation.trivial (D.nd.O i) ↥(Γc i dc l) ↥(Ideal.span {δO})) :=
  ⟨fun g => ⟨δO * f g, Ideal.mem_span_singleton'.2 ⟨f g, mul_comm _ _⟩⟩, fun g h => by
    apply Subtype.ext
    simp [hf, mul_add]⟩

def UnrFinIn (l : K.Col i dc) : Prop :=
  ∀ f (hf : UnrAdm i dc l f), Submodule.mkQ _ (uzOf i dc δO l f hf.1) ∈ KHf.HfE₂ i dc δO l

def uCol (l : K.Col i dc) : ↥(Γc i dc l) → D.nd.O i :=
  if h : UnrHom i dc l then h.choose else 0

theorem uCol_add (l : K.Col i dc) (g h : ↥(Γc i dc l)) : uCol i dc l (g * h) = uCol i dc l g + uCol i dc l h := by
  by_cases hU : UnrHom i dc l
  · have e : uCol i dc l = hU.choose := dite_eq_left hU
    rw [e]
    obtain ⟨⟨hadd, _, _⟩, _⟩ := hU.choose_spec
    exact hadd g h
  · have e : uCol i dc l = 0 := dite_eq_right hU
    rw [e]
    simp

def u (l : K.Col i dc) (g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om) : D.nd.O i :=
  if h : g ∈ Γc i dc l then uCol i dc l ⟨g, h⟩ else 0

def uz (l : K.Col i dc) : Formalism.NG.coZ1s (Representation.trivial (D.nd.O i) ↥(Γc i dc l) ↥(Ideal.span {δO})) :=
  uzOf i dc δO l (uCol i dc l) (uCol_add i dc l)

theorem u_mem (l : K.Col i dc) (g : ↥(Γc i dc l)) : u i dc l g = uCol i dc l g := by
  unfold u
  rw [dite_eq_left g.2]

theorem uCol_spec (l : K.Col i dc) (hU : UnrHom i dc l) :
    UnrAdm i dc l (uCol i dc l) ∧ ∃ g, uCol i dc l g = 1 := by
  have e : uCol i dc l = hU.choose := dite_eq_left hU
  rw [e]
  exact hU.choose_spec

theorem u_I (l : K.Col i dc) (hU : UnrHom i dc l) : ∀ g ∈ Icol i dc l, u i dc l (g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om) = 0 := by
  intro g hg
  rw [u_mem]
  obtain ⟨⟨_, hI, _⟩, _⟩ := uCol_spec i dc l hU
  exact hI g hg

theorem u_one (l : K.Col i dc) (hU : UnrHom i dc l) : ∃ g ∈ Γc i dc l, u i dc l g = 1 := by
  obtain ⟨_, g, hg⟩ := uCol_spec i dc l hU
  exact ⟨g, g.2, by rw [u_mem]; exact hg⟩

end Unr

end Formalism.MainNotions.N.KFin
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

section Gen

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M W : Type} [AddCommGroup M] [Module O M] [AddCommGroup W] [Module O W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul O W]
  (ρM : Representation O G M) (ρW : Representation O G W) (φ : M ≃ₗ[O] W)
  (hφ : ∀ g m, φ (ρM g m) = ρW g (φ m))

include hφ

theorem symm_equiv (g : G) (w : W) : φ.symm (ρW g w) = ρM g (φ.symm w) := by
  apply φ.injective
  rw [hφ, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

def psiZ : ReciprocityTheory.Gal.Z1 ρW →ₗ[O] coZ1s ρM where
  toFun f := ⟨fun g => φ.symm (f.1 g), fun g h => by
    show φ.symm (f.1 (g * h)) = φ.symm (f.1 g) + ρM g (φ.symm (f.1 h))
    rw [f.2.2 g h, map_add (f := _), symm_equiv ρM ρW φ hφ]⟩
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp

theorem psiZ_apply (f : ReciprocityTheory.Gal.Z1 ρW) (g : G) :
    (psiZ ρM ρW φ hφ f : G → M) g = φ.symm (f.1 g) := rfl

def psi : ReciprocityTheory.Gal.H1 ρW →ₗ[O] H1z ρM :=
  Submodule.mapQ _ _ (psiZ ρM ρW φ hφ) (by
    intro f hf
    obtain ⟨w, hw⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 ρW _).1 hf
    refine ⟨φ.symm w, funext fun g => ?_⟩
    change ρM g (φ.symm w) - φ.symm w = φ.symm (f.1 g)
    rw [show f.1 g = ρW g w - w from hw g, map_sub, symm_equiv ρM ρW φ hφ])

theorem psi_mk (f : ReciprocityTheory.Gal.Z1 ρW) :
    psi ρM ρW φ hφ (Submodule.Quotient.mk f) = Submodule.Quotient.mk (psiZ ρM ρW φ hφ f) := rfl

theorem psi_injective : Function.Injective (psi ρM ρW φ hφ) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker, psi_mk, Submodule.Quotient.mk_eq_zero] at hx
  rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
  obtain ⟨m, hm⟩ := hx
  show f.1 ∈ ReciprocityTheory.Gal.B1 ρW
  rw [ReciprocityTheory.Gal.mem_coboundaries1]
  refine ⟨φ m, fun g => ?_⟩
  have h2 : φ.symm (f.1 g) = ρM g m - m := by
    first
    | exact (congrFun hm g).symm
  rw [← hφ, ← map_sub, ← h2, LinearEquiv.apply_symm_apply]

theorem lc_mem_range {x : H1z ρM} (hx : x ∈ lcH1 ρM) : ∃ y, psi ρM ρW φ hφ y = x := by
  obtain ⟨c, hc, rfl⟩ := hx
  have hc' : IsLocallyConstant (c : G → M) := hc
  have hcont : Continuous (fun g => φ ((c : G → M) g)) := (hc'.comp (⇑φ)).continuous
  have hcoc : ∀ g h, φ ((c : G → M) (g * h)) = φ ((c : G → M) g) + ρW g (φ ((c : G → M) h)) := by
    intro g h
    rw [c.2 g h, map_add (f := _), hφ]
  refine ⟨Submodule.Quotient.mk ⟨fun g => φ ((c : G → M) g), hcont, hcoc⟩, ?_⟩
  rw [psi_mk]
  show Submodule.Quotient.mk _ = Submodule.Quotient.mk c
  congr 1
  apply Subtype.ext
  funext g
  simp only [psiZ_apply, LinearEquiv.symm_apply_apply]

theorem injTie_of {S : Submodule O (H1z ρM)} {S' : Submodule O (ReciprocityTheory.Gal.H1 ρW)}
    (hS : S ≤ lcH1 ρM) (h : ∀ y, psi ρM ρW φ hφ y ∈ S → y ∈ S') : InjTie S S' := by
  let T : Submodule O (ReciprocityTheory.Gal.H1 ρW) := S.comap (psi ρM ρW φ hφ)
  let gT : T →ₗ[O] S := (psi ρM ρW φ hφ).restrict (fun x hx => hx)
  have hg : Function.Bijective gT := by
    constructor
    · intro a b hab
      apply Subtype.ext
      apply psi_injective ρM ρW φ hφ
      exact congrArg Subtype.val hab
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy⟩ := lc_mem_range ρM ρW φ hφ (hS hx)
      refine ⟨⟨y, ?_⟩, ?_⟩
      · show psi ρM ρW φ hφ y ∈ S
        rw [hy]
        exact hx
      · apply Subtype.ext
        exact hy
  let e := LinearEquiv.ofBijective gT hg
  refine ⟨(Submodule.inclusion (fun y hy => h y hy)).comp e.symm.toLinearMap, ?_⟩
  exact (Submodule.inclusion_injective (fun y hy => h y hy)).comp e.symm.injective

end Gen

end Formalism.MainNotions.N.K.Sel

namespace Formalism.MainNotions.N.K.Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N
  Formalism.MainNotions.N.K Formalism.BasicNotions

section Unr

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M W : Type} [AddCommGroup M] [Module O M] [AddCommGroup W] [Module O W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul O W]
  (ρM : Representation O G M) (ρW : Representation O G W) (φ : M ≃ₗ[O] W)
  (hφ : ∀ g m, φ (ρM g m) = ρW g (φ m))

theorem unr_tie {I Dg : Subgroup G} (y : ReciprocityTheory.Gal.H1 ρW)
    (h : Formalism.NG.resH1 ρM I (psi ρM ρW φ hφ y) = 0) :
    ReciprocityTheory.Gal.resH1 (ρW.comp Dg.subtype) (I.subgroupOf Dg).subtype continuous_subtype_val
      (ReciprocityTheory.Gal.resH1 ρW Dg.subtype continuous_subtype_val y) = 0 := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [psi_mk] at h
  change Submodule.Quotient.mk (restrictCocycles1 ρM I (psiZ ρM ρW φ hφ f)) = 0 at h
  rw [Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨m, hm⟩ := h
  show Submodule.Quotient.mk _ = 0
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.mem_coboundaries1]
  refine ⟨φ m, fun g => ?_⟩
  have hg' : φ.symm (f.1 ((g : Dg) : G)) = ρM ((g : Dg) : G) m - m := by
    have h1 := congrFun hm ⟨((g : Dg) : G), g.2⟩
    first
    | exact h1.symm
  show f.1 ((g : Dg) : G) = ρW ((g : Dg) : G) (φ m) - φ m
  rw [← hφ, ← map_sub, ← hg', LinearEquiv.apply_symm_apply]

end Unr

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) {A T' : Type} [Ring A] [Algebra (D.nd.O i) A] [CommRing T'] [Algebra T' A]
  (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
  (r : GE D.nd →* A) (χ : GE D.nd →* T'ˣ)
  (φ : M ≃ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r)
  (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := M) r χ g m) = Br.WKO i ρ π g (φ m))

def BkAt (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) w)))) :
    Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (x : ReciprocityTheory.Gal.H1 (Br.WKO i ρ π)),
    Formalism.NG.resH1 (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) (idx i dc w))
              (psi (uRep (D.nd.O i) (M := M) r χ) (Br.WKO i ρ π) φ hφ x) ∈ F (idx i dc w) →
      ReciprocityTheory.Gal.resH1 (Br.WKO i ρ π) (decS D.nd w) continuous_subtype_val x ∈
        Br.bk D.loc D.nbr i w hw (WpO D.nd i ρ π)

theorem idx_mem_rows_cols {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    idx i dc w ∈ rowsN i dc ∪ Finset.univ.image (colIdx i dc) := by
  rcases (dc.cover w).mpr hw with h | h
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ h)
  · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨⟨w, h⟩, Finset.mem_univ _, rfl⟩)

theorem tieSel1_of
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) w))))
    (hBk : BkAt i dc ρ π M r χ φ hφ F) :
    TieSel1 i ρ π M r χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) F (K.QS.Io i) := by
  refine injTie_of (uRep (D.nd.O i) (M := M) r χ) (Br.WKO i ρ π) φ hφ ?_ ?_
  · intro x hx
    exact (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).1
  · intro y hy
    obtain ⟨hy1, hloc⟩ := Submodule.mem_inf.mp hy
    have hunr := (Submodule.mem_inf.mp hy1).2
    unfold Br.selPi Br.selG Formalism.GaloisCohomology.SelAll
    refine (ReciprocityTheory.Gal.mem_Sel _ _ _ _ _).2 fun v => ?_
    unfold Formalism.GaloisCohomology.bkCond
    split_ifs with h1 h2
    · have hw : v ∈ placesOver D.host.E (D.nd.l i) := h1
      have hm := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hloc (idx i dc v))
        (idx_mem_rows_cols i dc hw)
      have hb := hBk v hw y hm
      unfold Br.LlG
      rw [dite_eq_left hw]
      exact hb
    · exact Submodule.mem_top
    · have hS : v ∉ D.nd.S i := fun h => h2 (Or.inl h)
      have hQ : v ∉ D.nd.Q i := fun h => h2 (Or.inr h)
      let vo : K.QS.Vo i := ⟨v, h1, hS, hQ⟩
      have hu := (Submodule.mem_iInf _).1 hunr vo
      exact unr_tie (uRep (D.nd.O i) (M := M) r χ) (Br.WKO i ρ π) φ hφ y hu

end Rec

end Formalism.MainNotions.N.K.Sel

namespace Formalism.MainNotions.N.K.Sel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

section Row

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def LenOlSelf : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    lenOl (Br.PD D.loc D.nbr i w hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) = eON i

def RowTie (rowLen : ℕ → ℕ∞) : Prop :=
  ∀ n ∈ rowsN i dc, ∀ (hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (b : ℚ),
    RowAt (Br.PD D.loc D.nbr i (plOf i dc n) hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw).LL))
        (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw) (rDuO D.nd i r x)))
        ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw) (T2O D.nd i ρ π)) b →
      rowLen n ≠ ⊤ ∧
        ((rowLen n).toNat : ℚ) ≤
          b * ((lenOl (Br.PD D.loc D.nbr i (plOf i dc n) hw)
            (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i (plOf i dc n) hw).LL))).toNat : ℚ)

end Row

end Formalism.MainNotions.N.K.Sel

namespace Formalism.MainNotions.N.K.Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N
  Formalism.MainNotions.N.K Formalism.BasicNotions

section ResCompat

variable {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
  {M W : Type} [AddCommGroup M] [Module O M] [AddCommGroup W] [Module O W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousConstSMul O W]
  (ρM : Representation O G M) (ρW : Representation O G W) (φ : M ≃ₗ[O] W)
  (hφ : ∀ g m, φ (ρM g m) = ρW g (φ m))

theorem psi_res (Dg : Subgroup G) (x : ReciprocityTheory.Gal.H1 ρW) :
    psi (resRep ρM Dg) (ρW.comp Dg.subtype) φ (fun g m => hφ g m)
        (ReciprocityTheory.Gal.resH1 ρW Dg.subtype continuous_subtype_val x) =
      Formalism.NG.resH1 ρM Dg (psi ρM ρW φ hφ x) := by
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  first
  | rfl

end ResCompat

section RecLoc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) {A T' : Type} [Ring A] [Algebra (D.nd.O i) A] [CommRing T'] [Algebra T' A]
  (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
  (r : GE D.nd →* A) (χ : GE D.nd →* T'ˣ)
  (φ : M ≃ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r)
  (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := M) r χ g m) = Br.WKO i ρ π g (φ m))

def BkLoc (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) w)))) :
    Prop :=
  ∀ n ∈ rowsN i dc ∪ Finset.univ.image (colIdx i dc),
    ∀ (hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
      (y : ReciprocityTheory.Gal.H1 ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n)))),
      psi (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n))
          ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) φ (fun g m => hφ g m) y ∈ F n →
        y ∈ Br.bk D.loc D.nbr i (plOf i dc n) hw (WpO D.nd i ρ π)

theorem bkAt_of_loc
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) w))))
    (h : BkLoc i dc ρ π M r χ φ hφ F) : BkAt i dc ρ π M r χ φ hφ F := by
  intro w hw x hx
  have hmem := idx_mem_rows_cols i dc hw
  have hwp : w ∈ plSet i dc := by
    unfold plSet
    rcases (dc.cover w).mpr hw with h' | h'
    · simp [h']
    · simp [h']
  have e : plOf i dc (idx i dc w) = w := plOf_idx i dc hwp
  generalize hn : idx i dc w = n at *
  subst e
  apply h n hmem hw
  first
  | (erw [psi_res]; exact hx)

end RecLoc

end Formalism.MainNotions.N.K.Sel

namespace Formalism.MainNotions.N.K.Sel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

section LenUnit

theorem length_semilinear {R S N M : Type} [CommRing R] [CommRing S] [AddCommGroup N] [Module R N]
    [AddCommGroup M] [Module S M] (e : R ≃+* S) [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)] (f : N ≃ₛₗ[(e : R →+* S)] M) :
    Module.length R N = Module.length S M := by
  first
  | (unfold Module.length; congr 1; exact Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap f))

def quotSL {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S) [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)]
    [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)] (x : R) :
    (R ⧸ Ideal.span {x}) ≃ₛₗ[(e : R →+* S)] (S ⧸ Ideal.span {e x}) where
  toFun := Ideal.quotientEquiv _ _ e (by rw [Ideal.map_span, Set.image_singleton]; rfl)
  invFun := (Ideal.quotientEquiv _ _ e (by rw [Ideal.map_span, Set.image_singleton]; rfl)).symm
  left_inv := RingEquiv.symm_apply_apply _
  right_inv := RingEquiv.apply_symm_apply _
  map_add' := map_add _
  map_smul' := by
    intro r y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [Algebra.smul_def, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.algebraMap_eq, map_mul]
    rfl

set_option synthInstance.maxHeartbeats 400000 in
theorem lenOlSelf {D : D7} (i : D.nd.Loc) : LenOlSelf i := by
  intro w hw
  unfold lenOl eON
  rw [Br.PD_p]
  have h1 := RingHomInvPair.of_ringEquiv (D.nbr i w hw).eO
  have h2 := RingHomInvPair.symm ((D.nbr i w hw).eO : D.nd.O i →+* ↥(OL (D.nbr i w hw).LL))
    ((D.nbr i w hw).eO.symm : ↥(OL (D.nbr i w hw).LL) →+* D.nd.O i)
  have h := length_semilinear (D.nbr i w hw).eO (quotSL (D.nbr i w hw).eO ((D.nd.l i : ℕ) : D.nd.O i))
  rw [map_natCast] at h
  exact h.symm

end LenUnit

end Formalism.MainNotions.N.K.Sel

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Formalism.NG Module

section Gen

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] (eO : O ≃+* Ow)

scoped instance (priority := low) modOw (V : Type) [AddCommGroup V] [Module (FractionRing O) V] : Module Ow (TrV e V) :=
  Module.compHom (TrV e V) (algebraMap Ow LL)

variable {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]

instance towOw : IsScalarTower Ow LL (TrV e V) :=
  ⟨fun a b v => by
    show (a • b) • v = (algebraMap Ow LL a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩

variable {e eO}

def tr (e : FractionRing O ≃+* LL) (v : V) : TrV e V := v

def untr (e : FractionRing O ≃+* LL) (v : TrV e V) : V := v

theorem smul_eO (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (a : O) (v : V) : (eO a • tr e v : TrV e V) = tr e (a • v) := by
  show (algebraMap Ow LL (eO a)) • tr e v = tr e (a • v)
  rw [smulLL_def, heO, RingEquiv.symm_apply_apply]
  exact algebraMap_smul (FractionRing O) a v

theorem smul_Ow (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (c : Ow) (v : V) : (c • tr e v : TrV e V) = tr e (eO.symm c • v) := by
  have h := smul_eO heO (eO.symm c) v
  rwa [RingEquiv.apply_symm_apply] at h

variable {M : Type} [AddCommGroup M] [Module O M] (j : M →ₗ[O] V)

variable (e eO) in
def latT (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a)) :
    Submodule Ow (TrV e V) where
  carrier := Set.range fun m => tr e (j m)
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, map_add j a b⟩
  zero_mem' := ⟨0, map_zero j⟩
  smul_mem' := by
    rintro c _ ⟨a, rfl⟩
    refine ⟨eO.symm c • a, ?_⟩
    show tr e (j (eO.symm c • a)) = c • tr e (j a)
    rw [smul_Ow heO, map_smul]

theorem mem_latT (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (v : TrV e V) : v ∈ latT e eO j heO ↔ ∃ m, tr e (j m) = v := by
  exact Iff.rfl

def MO (_eO : O ≃+* Ow) (M : Type) : Type := M

instance : AddCommGroup (MO eO M) := ‹AddCommGroup M›
instance : Module O (MO eO M) := ‹Module O M›
instance instModMO : Module Ow (MO eO M) := Module.compHom M eO.symm.toRingHom

def latMap (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a)) :
    MO eO M →ₗ[Ow] ↥(latT e eO j heO) where
  toFun m := ⟨tr e (j m), m, rfl⟩
  map_add' a b := Subtype.ext (map_add j a b)
  map_smul' c a := Subtype.ext (by
    show tr e (j (eO.symm c • (show M from a))) = c • tr e (j a)
    rw [smul_Ow heO, map_smul])

def latEquiv (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (hj : Function.Injective j) : MO eO M ≃ₗ[Ow] ↥(latT e eO j heO) :=
  LinearEquiv.ofBijective (latMap j heO)
    ⟨fun a b h => hj (congrArg Subtype.val h : tr e (j a) = tr e (j b)),
      fun ⟨_, m, hm⟩ => ⟨m, Subtype.ext hm⟩⟩

def basMO [Module.Free O M] : Basis (Module.Free.ChooseBasisIndex O M) O (MO eO M) := Module.Free.chooseBasis O M

theorem free_MO [Module.Free O M] : Module.Free Ow (MO eO M) := by
  exact Module.Free.of_basis ((basMO (eO := eO) (M := M)).mapCoeffs eO (fun c x => by
    show eO.symm (eO c) • x = c • x
    rw [RingEquiv.symm_apply_apply]))

theorem finite_MO [Module.Finite O M] [Module.Free O M] : Module.Finite Ow (MO eO M) := by
  exact Module.Finite.of_basis ((basMO (eO := eO) (M := M)).mapCoeffs eO (fun c x => by
    show eO.symm (eO c) • x = c • x
    rw [RingEquiv.symm_apply_apply]))

variable {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)

variable (e eO) in
def latOf (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
    (ρV : Representation O Γ V) (ρM : Representation O Γ M) (hj : Function.Injective j)
    (hjeq : ∀ γ m, j (ρM γ m) = ρV γ (j m))
    (hsp : ∀ v : V, ∃ c : O, c ≠ 0 ∧ ∃ m, j m = c • v) [Module.Finite O M] [Module.Free O M] :
    Lattice (O := Ow) (repL e ρV ι) where
  T := latT e eO j heO
  stable g := by
    rintro _ ⟨m, rfl⟩
    exact ⟨ρM (ι g) m, hjeq _ _⟩
  fg := by
    haveI := finite_MO (eO := eO) (M := M)
    haveI : Module.Finite Ow ↥(latT e eO j heO) := Module.Finite.equiv (latEquiv j heO hj)
    exact (Module.Finite.iff_fg).1 inferInstance
  free := by
    haveI := free_MO (eO := eO) (M := M)
    exact Module.Free.of_equiv (latEquiv j heO hj)
  span := by
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, hc, m, hm⟩ := hsp (untr e v)
    have hk : algebraMap O (FractionRing O) c ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
    have hv0 : untr e v = (algebraMap O (FractionRing O) c)⁻¹ • j m := by
      rw [hm, ← algebraMap_smul (FractionRing O) c (untr e v), smul_smul, inv_mul_cancel₀ hk, one_smul]
    have hv : v = e (algebraMap O (FractionRing O) c)⁻¹ • tr e (j m) := by
      show untr e v = e.symm (e (algebraMap O (FractionRing O) c)⁻¹) • j m
      rw [RingEquiv.symm_apply_apply, hv0]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, rfl⟩)

end Gen

section Lift

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  {e : FractionRing O ≃+* LL} {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {P Q VP VQ : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
  [AddCommGroup VP] [Module (FractionRing O) VP] [Module O VP] [IsScalarTower O (FractionRing O) VP]
  [AddCommGroup VQ] [Module (FractionRing O) VQ] [Module O VQ] [IsScalarTower O (FractionRing O) VQ]
  [Module.Finite O P] [Module.Free O P] [Module.Finite O Q] [Module.Free O Q]
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {ρP : Representation O Γ P} {ρQ : Representation O Γ Q} {ρVP : Representation O Γ VP}
  {ρVQ : Representation O Γ VQ} {jP : P →ₗ[O] VP} {jQ : Q →ₗ[O] VQ}
  (hjP : Function.Injective jP) (hjQ : Function.Injective jQ)
  (hjeqP : ∀ γ m, jP (ρP γ m) = ρVP γ (jP m)) (hjeqQ : ∀ γ m, jQ (ρQ γ m) = ρVQ γ (jQ m))
  (hspP : ∀ v : VP, ∃ c : O, c ≠ 0 ∧ ∃ m, jP m = c • v) (hspQ : ∀ v : VQ, ∃ c : O, c ≠ 0 ∧ ∃ m, jQ m = c • v)
  {ev : P →ₗ[O] Q} {f0 : VP →ₗ[O] VQ}
  (hf0 : ∀ γ v, f0 (ρVP γ v) = ρVQ γ (f0 v)) (hcomm : ∀ m, f0 (jP m) = jQ (ev m))

def latHom : LatHom (latOf e eO jP ι heO ρVP ρP hjP hjeqP hspP) (latOf e eO jQ ι heO ρVQ ρQ hjQ hjeqQ hspQ) where
  f := trL e f0
  equiv g x := hf0 (ι g) x
  cont := trL_cont e f0
  T_le := by
    rintro _ ⟨m, rfl⟩
    exact ⟨ev m, (hcomm m).symm⟩

theorem latHom_onto (hev : Function.Surjective ev) :
    (latHom ι heO hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm).Onto := by
  intro y hy
  obtain ⟨q, rfl⟩ := (mem_latT jQ heO y).mp hy
  obtain ⟨p, rfl⟩ := hev q
  refine ⟨tr e (jP p), (mem_latT jP heO _).mpr ⟨p, rfl⟩, ?_⟩
  show trL e f0 (tr e (jP p)) = tr e (jQ (ev p))
  rw [trL_apply]
  exact hcomm p

end Lift

section FromAt

theorem finDim_of_lat {LL Ow : Type} [Field LL] [CommRing Ow] [Algebra Ow LL] {G : Type} [Group G]
    {Qp : Type} [Field Qp] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] [Module Ow V]
    [IsScalarTower Ow LL V] {ρ : Representation LL G V} (L : Lattice (O := Ow) ρ) : FiniteDimensional LL V := by
  obtain ⟨s, hs⟩ := L.fg
  have h1 : (L.T : Set V) ⊆ Submodule.span LL (s : Set V) := by
    rw [← hs]
    exact Submodule.span_subset_span Ow LL _
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff, ← L.span]
  exact Submodule.span_le.mpr h1

end FromAt

section Lift2

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL]
  {e : FractionRing O ≃+* LL} {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {P Q VP VQ : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
  [AddCommGroup VP] [Module (FractionRing O) VP] [Module O VP] [IsScalarTower O (FractionRing O) VP]
  [AddCommGroup VQ] [Module (FractionRing O) VQ] [Module O VQ] [IsScalarTower O (FractionRing O) VQ]
  [Module.Finite O P] [Module.Free O P] [Module.Finite O Q] [Module.Free O Q]
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {ρP : Representation O Γ P} {ρQ : Representation O Γ Q} {ρVP : Representation O Γ VP}
  {ρVQ : Representation O Γ VQ} {jP : P →ₗ[O] VP} {jQ : Q →ₗ[O] VQ}
  (hjP : Function.Injective jP) (hjQ : Function.Injective jQ)
  (hjeqP : ∀ γ m, jP (ρP γ m) = ρVP γ (jP m)) (hjeqQ : ∀ γ m, jQ (ρQ γ m) = ρVQ γ (jQ m))
  (hspP : ∀ v : VP, ∃ c : O, c ≠ 0 ∧ ∃ m, jP m = c • v) (hspQ : ∀ v : VQ, ∃ c : O, c ≠ 0 ∧ ∃ m, jQ m = c • v)
  {ev : P →ₗ[O] Q} {f0 : VP →ₗ[O] VQ}
  (hf0 : ∀ γ v, f0 (ρVP γ v) = ρVQ γ (f0 v)) (hcomm : ∀ m, f0 (jP m) = jQ (ev m))

include hspQ hcomm in
theorem trL_onto (hev : Function.Surjective ev) : Function.Surjective (trL e f0) := by
  intro w
  obtain ⟨c, hc, q, hq⟩ := hspQ (untr e w)
  obtain ⟨p, rfl⟩ := hev q
  have hk : algebraMap O (FractionRing O) c ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)
  refine ⟨tr e ((algebraMap O (FractionRing O) c)⁻¹ • jP p), ?_⟩
  rw [trL_apply]
  show f0 ((algebraMap O (FractionRing O) c)⁻¹ • jP p) = untr e w
  rw [smulK, hcomm, hq, ← algebraMap_smul (FractionRing O) c, smul_smul, inv_mul_cancel₀ hk, one_smul]

end Lift2

section Loc

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module O M]

theorem mkK_inj [Module.Free O M] : Function.Injective (mkK (O := O) (M := M)) := by
  intro a b h
  simp only [LocalizedModule.mkLinearMap_apply] at h
  rw [LocalizedModule.mk_eq] at h
  obtain ⟨u, hu⟩ := h
  simp only [one_smul, Submonoid.smul_def] at hu
  exact smul_right_injective M (nonZeroDivisors.coe_ne_zero u) hu

theorem mkK_span (v : MK (O := O) M) : ∃ c : O, c ≠ 0 ∧ ∃ m, mkK m = c • v := by
  refine LocalizedModule.induction_on (fun m s => ?_) v
  refine ⟨s, nonZeroDivisors.coe_ne_zero s, m, ?_⟩
  rw [LocalizedModule.mkLinearMap_apply, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def]⟩

end Loc

end Formalism.MainNotions.N.KRow

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Transport

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {O' : Type} [CommRing O'] {σ : O' ≃+* O}
    {A T' GG : Type} [Ring A] [Algebra O' A] [CommRing T'] [Algebra T' A] [Group GG]
    {M : Type} [AddCommGroup M] [Module A M] [Module O' M] [SMulCommClass A O' M]
    {r : GG →* A} {χ : GG →* T'ˣ} {E : A} {Dw : Subgroup GG} {eG : Dw ≃* G}

theorem back_cob {e cB ℓ : ℕ} (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hp : PD.p = ℓ) (z : Dw → M)
    (x : Cd.Ce.V ⧸ Cd.Ce.L.T) (g : Dw)
    (hg : (((PD.p : O) ^ cB) • trC Cd z) (eG g) = actD Cd.Ce.L (eG g) x - x) :
    ((ℓ : O') ^ cB) • z g = uElt r χ (g : GG) • Cd.u.symm x - Cd.u.symm x := by
  apply Cd.u.injective
  rw [map_sub, Cd.u_act, AddEquiv.apply_symm_apply, Cd.u_smul, map_pow, map_natCast, ← hg, ← hp]
  simp only [trC, MulEquiv.symm_apply_apply, Pi.smul_apply]

theorem tb_pos {e t cB ℓ : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (he : 0 < e) (het : e < t)
    (Y : YtLat (G := G) (Qp := Qp) LL O) (hY : YtCrys (PD := PD) Y J)
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hψ : PsiExt σ r χ E Dw eG Y Cd) [TopologicalSpace Dw]
    (hloc : YLoc (O := O') M r χ E Dw) (heG : Continuous eG.symm) (hp : PD.p = ℓ)
    (ψ : Ymod r χ E →ₗ[O'] M) (hψe : ∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : ∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : GG))) :
    ((ℓ : O') ^ cB) • (z : Dw → M) ∈ coB1 (resRep (uRep O' (M := M) r χ) Dw) := by
  have hzl : IsLocallyConstant (z : Dw → M) := by
    have h := hloc ψ hψe
    have hf : (z : Dw → M) = fun g : Dw => ψ (yY r χ E (g : GG)) := funext hz
    rw [hf]
    exact h
  have h1 := trC_hf hTB het Y hY Cd hψ ψ hψe (z : Dw → M) hz
  have h2 := trC_mem_Z1D Cd heG z hzl ((PD.p : O) ^ cB)
  obtain ⟨x, hx⟩ := (hTB.2 e het Cd.Ce.V Cd.Ce.ρ Cd.Ce.L Cd.Ce.cont Cd.Ce.mat).1 he ⟨h2, h1⟩
  refine ⟨Cd.u.symm x, ?_⟩
  funext g
  show uElt r χ (g : GG) • Cd.u.symm x - Cd.u.symm x = ((ℓ : O') ^ cB) • (z : Dw → M) g
  refine (back_cob Cd hp (z : Dw → M) x g ?_).symm
  have := congrFun hx (eG g)
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at this
  exact this.symm

theorem tb_zero {e t cB ℓ : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (he : e = 0) (het : e < t)
    (Y : YtLat (G := G) (Qp := Qp) LL O) (hY : YtCrys (PD := PD) Y J)
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hψ : PsiExt σ r χ E Dw eG Y Cd) [TopologicalSpace Dw]
    (hloc : YLoc (O := O') M r χ E Dw) (heG : Continuous eG.symm) (hp : PD.p = ℓ)
    (I' : Subgroup Dw) (hI : ∀ g : Dw, g ∈ I' → eG g ∈ I)
    (ψ : Ymod r χ E →ₗ[O'] M) (hψe : ∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y)
    (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw)) (hz : ∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : GG))) :
    IsLocallyConstant (z : Dw → M) ∧
    ∃ m : M, ∀ g : Dw, g ∈ I' → ((ℓ : O') ^ cB) • (z : Dw → M) g = uElt r χ (g : GG) • m - m := by
  have hzl : IsLocallyConstant (z : Dw → M) := by
    have h := hloc ψ hψe
    have hf : (z : Dw → M) = fun g : Dw => ψ (yY r χ E (g : GG)) := funext hz
    rw [hf]
    exact h
  refine ⟨hzl, ?_⟩
  have h1 := trC_hf hTB het Y hY Cd hψ ψ hψe (z : Dw → M) hz
  have h2 := trC_mem_Z1D Cd heG z hzl ((PD.p : O) ^ cB)
  have hmem : ((PD.p : O) ^ cB) • trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L ⊓ HfD PD Cd.Ce.L := ⟨h2, h1⟩
  rw [(hTB.2 e het Cd.Ce.V Cd.Ce.ρ Cd.Ce.L Cd.Ce.cont Cd.Ce.mat).2.1 he] at hmem
  obtain ⟨a, ⟨x, hx⟩, b, ⟨y, hy⟩, hab⟩ := Submodule.mem_sup.1 hmem.2
  refine ⟨Cd.u.symm (x + y), fun g hg => back_cob Cd hp (z : Dw → M) (x + y) g ?_⟩
  have hb := congrFun hy (eG g)
  simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at hb
  rw [← hab, Pi.add_apply, hx (eG g) (hI g hg), ← hb, map_add (f := _)]
  abel

end Transport

section Cls

variable {O Γ M : Type} [CommRing O] [Group Γ] [AddCommGroup M] [Module O M] (ρ : Representation O Γ M)

theorem mkQ_eq_zero_of (z : coZ1s ρ) (h : (z : Γ → M) ∈ coB1 ρ) :
    (Submodule.mkQ _ z : H1z ρ) = 0 := by
  exact (Submodule.Quotient.mk_eq_zero _).mpr h

theorem mem_unramified_of_coboundary (I : Subgroup Γ) (z : coZ1s ρ) (m : M) (hm : ∀ g ∈ I, (z : Γ → M) g = ρ g m - m) :
    (Submodule.mkQ _ z : H1z ρ) ∈ unrH1 ρ I := by
  rw [unrH1, LinearMap.mem_ker, Formalism.NG.resH1, Submodule.mkQ_apply, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero]
  refine ⟨m, ?_⟩
  funext g
  exact (hm g.1 g.2).symm

theorem mem_locally_constant_of [TopologicalSpace Γ] (z : coZ1s ρ) (h : IsLocallyConstant (z : Γ → M)) :
    (Submodule.mkQ _ z : H1z ρ) ∈ Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 ρ :=
  ⟨z, h, rfl⟩

end Cls

end Formalism.MainNotions.N.K.TB

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Record

open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev Qcore (c : Fin (D.R.t + 1)) (n cB : ℕ) : Type :=
  ↥(Hc i dc Dd c n ⊓ divBy (Fc i dc Dd c n) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)) ⧸
    (Fc i dc Dd c n).comap (Hc i dc Dd c n ⊓ divBy (Fc i dc Dd c n) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)).subtype

def TBLenAt (cB : ℕ) (n : ℕ) (c : Fin (D.R.t + 1)) : Prop :=
  Module.length (D.nd.O i) (Qcore i dc Dd c n cB) ≤
    Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)}) * (cB : ℕ∞) *
      ((Formalism.MainNotions.N.locDeg D.host.E (plOf i dc n) : ℕ∞) + 1)

def TBLen (cB : ℕ) : Prop :=
  ∀ n ∈ rowsN i dc, ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) → TBLenAt i dc Dd cB n c

def TrivialBoundAtRows (cB : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    Formalism.MainNotions.N.TBAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (Br.inert D.nbr i w hw)
      (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) D.R.t cB

theorem eW_symm_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Continuous (eW i dc hw).symm := by
  have h1 : Continuous (D.nbr i w hw).e.symm := (D.nbr i w hw).e_symm_cont
  have h2 : Continuous (MulEquiv.subgroupCongr (Dw_idx i dc hw)).symm :=
    continuous_induced_rng.2 continuous_subtype_val
  exact h2.comp h1

theorem eW_inert {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (g : Dw i dc (idx i dc w)) (hg : g ∈ (Ine (F := D.host.E) (Aw i dc (idx i dc w))).subgroupOf (Dw i dc (idx i dc w))) :
    eW i dc hw g ∈ Br.inert D.nbr i w hw := by
  have hmem : w ∈ plSet i dc := by
    simp only [plSet, Finset.mem_union]
    exact Or.inl ((dc.cover w).2 hw)
  have hA : Aw i dc (idx i dc w) = D.nd.plOm.1 w := by
    unfold Aw
    rw [plOf_idx i dc hmem]
  unfold Br.inert
  rw [Subgroup.mem_subgroupOf, hA] at hg
  simp only [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Br.iota]
  have hx : ((Br.ι (D.nbr i w hw) (eW i dc hw g)) : GE D.nd) = (g : GE D.nd) := by
    simp [Br.ι, eW]
  rw [hx]
  exact hg

theorem tbTarget_of (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hd : TBDict i dc r π Dd)
    (hlen : TBLen i dc Dd cB) : TBTarget i dc Dd cB := by
  intro n hn c hc
  have hlen' := hlen n hn c hc
  obtain ⟨w, hwrow, rfl⟩ := Finset.mem_image.1 hn
  have hw : w ∈ placesOver D.host.E (D.nd.l i) := (dc.cover w).1 (Or.inl hwrow)
  obtain ⟨Y, Cd, hY, hψ, hloc⟩ := hd w hw hwrow c hc
  have hT : Formalism.MainNotions.N.TBAt (Br.PD D.loc D.nbr i w hw) (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (Br.inert D.nbr i w hw)
      (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) D.R.t cB := hTB w hw hwrow
  have het : (c : ℕ) - 1 < D.R.t := by
    have := c.2
    omega
  have hp : (Br.PD D.loc D.nbr i w hw).p = D.nd.l i := Br.PD_p D.loc D.nbr i w hw
  refine ⟨?_, le_rfl, ?_, hlen'⟩
  · unfold Fc Hc
    split_ifs
    · exact inf_le_left
    · exact bot_le
  · intro ψ hψe z hz
    unfold Fc
    split_ifs with h1
    · obtain ⟨hzl, m, hm⟩ := tb_zero (σ := selfO i hw) (M := Mc i Dd c) (eG := eW i dc hw) hT (by omega) het Y hY Cd hψ hloc (eW_symm_cont i dc hw) hp
        ((Ine (F := D.host.E) (Aw i dc (idx i dc w))).subgroupOf (Dw i dc (idx i dc w))) (eW_inert i dc hw)
        ψ hψe z hz
      rw [← map_smul]
      exact ⟨mem_locally_constant_of _ _ (hzl.comp (fun m => ((D.nd.l i : D.nd.O i) ^ cB) • m)),
        mem_unramified_of_coboundary _ _ _ m hm⟩
    · have := tb_pos (σ := selfO i hw) (M := Mc i Dd c) (eG := eW i dc hw) hT (by omega) het Y hY Cd hψ hloc (eW_symm_cont i dc hw) hp ψ hψe z hz
      rw [Submodule.mem_bot, ← map_smul]
      exact mkQ_eq_zero_of _ _ this

end Record

end Formalism.MainNotions.N.K.TB

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.ShaT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.MainNotions.N.K.QS Formalism.RepresentationBoundsCohomology.FIN
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Gen

variable {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]

def selRep2 (ρ : Representation R G M) {V VS : Type} (J : V → Subgroup G) (JS : VS → Subgroup G)
    (D : ℕ → Subgroup G) (F : ∀ w, Submodule R (H1z (resRep ρ (D w)))) (P : Finset ℕ) : Submodule R (H1z ρ) :=
  (lcH1 ρ ⊓ (⨅ v, unrH1 ρ (J v)) ⊓ ⨅ v, unrH1 ρ (JS v)) ⊓ ⨅ w ∈ P, (F w).comap (resH1 ρ (D w))

def Fsha (ρ : Representation R G M) (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs : Finset ℕ) (w : ℕ) :
    Submodule R (H1z (resRep ρ (D w))) :=
  if w ∈ qs then unrH1 (resRep ρ (D w)) (Iq w) else ⊥

def RepIso {M' : Type} [AddCommGroup M'] [Module R M'] (ρ : Representation R G M) (ρ' : Representation R G M') :
    Prop :=
  ∃ φ : M ≃ₗ[R] M', ∀ g m, φ (ρ g m) = ρ' g (φ m)

end Gen

def CoefChange (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] (ψ : G →* ℤ_[l]ˣ) {V VS : Type} (J : V → Subgroup G)
    (JS : VS → Subgroup G) (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs P : Finset ℕ),
    let ψO : G →* Oˣ := (Units.map (algebraMap ℤ_[l] O).toMonoidHom).comp ψ
    let ρO := Formalism.GaloisCohomology.scalRep (KO O) ψO
    let ρZ := Formalism.GaloisCohomology.scalRep (Formalism.GaloisCohomology.QZ l) ψ
    Module.length O ↥(selRep2 ρO J JS D (Fsha ρO D Iq qs) P) ≤
      Module.length O (O ⧸ Ideal.span {((l : ℕ) : O)}) * Module.length ℤ_[l] ↥(selRep2 ρZ J JS D (Fsha ρZ D Iq qs) P)

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def Pall : Finset ℕ := rowsN i dc ∪ qsN i dc ∪ univ.image (colIdx i dc)

def cycE : GE D.nd →* ℤ_[D.nd.l i]ˣ := cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i)

def qzE (e : ℕ) : Representation ℤ_[D.nd.l i] (GE D.nd) (Formalism.GaloisCohomology.QZ (D.nd.l i)) :=
  Formalism.GaloisCohomology.scalRep (Formalism.GaloisCohomology.QZ (D.nd.l i)) (cycE i ^ (-(e : ℤ)))

def koE (e : ℕ) : Representation (D.nd.O i) (GE D.nd) (KO (D.nd.O i)) :=
  Formalism.GaloisCohomology.scalRep (KO (D.nd.O i)) ((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp
    (cycE i ^ (-(e : ℤ))))

def selZ (e : ℕ) : Submodule ℤ_[D.nd.l i] (H1z (qzE i e)) :=
  selRep2 (qzE i e) (Io i) (IS i) (decs D.host.E (Aw i dc)) (Fsha (qzE i e) (decs D.host.E (Aw i dc)) (I i dc) (qsN i dc))
    (Pall i dc)

def BlockTwistedCyclotomic (c : Fin (D.R.t + 1)) : Prop :=
  RepIso (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (koE i ((c : ℕ) - 1))

def ZlSha (e : ℕ) : Prop :=
  Module.length ℤ_[D.nd.l i] ↥(selZ i dc e) ≤ Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)

end Rec

end Formalism.MainNotions.N.K.ShaT

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf

section Record

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))

abbrev YtM : Type := ↥(Ymod Dd.r Dd.χ Dd.E) × D.nd.O i

instance instAddCommGroupYtM : AddCommGroup (YtM i Dd) := Prod.instAddCommGroup

abbrev ytRepW (n : ℕ) : Representation (D.nd.O i) ↥(Dw i dc n) (YtM i Dd) :=
  resRep (ytRep (D.nd.O i) Dd.r Dd.χ Dd.E) (Dw i dc n)

abbrev ιW {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Br.G D.nbr i w hw →* ↥(Dw i dc (idx i dc w)) :=
  (eW i dc hw).symm.toMonoidHom

abbrev eS {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    FractionRing (D.nd.O i) ≃+* ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 :=
  eK (D.nbr i w hw)

abbrev ytV {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Representation ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (Br.G D.nbr i w hw) (TrV (eS i hw) (MK (O := D.nd.O i) (YtM i Dd))) :=
  repL (eS i hw) (locRep (ytRepW i dc Dd (idx i dc w))) (ιW i dc hw)

abbrev MsW {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    Br.G D.nbr i w hw →* Matrix (Fin D.R.nV) (Fin D.R.nV) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 :=
  TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (rTwO D.nd i r x)

def MsContW {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Prop :=
  ∀ x, Continuous (MsW i r hw x)

def YtEmbW {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) : Prop :=
  ∃ (m : ℕ) (xs : Fin m → D.nd.X i)
    (φ : TrV (eS i hw) (MK (O := D.nd.O i) (YtM i Dd)) →ₗ[↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1]
      (Fin m → Fin D.R.nV → ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1)),
    Function.Injective φ ∧ ∀ g v, φ (ytV i dc Dd hw g v) = fun a => (MsW i r hw (xs a) g).mulVec (φ v a)

variable [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def YtTarget {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) : Prop :=
  ∀ Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1),
    ∃ Y : YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL),
      YtCrys (PD := Br.PD D.loc D.nbr i w hw) Y (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) ∧
      PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) Y Cd

end Record

end Formalism.MainNotions.N.K.TBa

end
end

section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions.N Topology

namespace Formalism.MainNotions.N.K.Norm

section Rec

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem map_smul_toK' (c : D.nd.O i) (A : MatN D.nd i) :
    (c • A).map (toK D.nd i) = toK D.nd i c • A.map (toK D.nd i) := by
  ext a b
  simp [Matrix.smul_apply]

theorem exists_integral_mul (M : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) :
    ∃ (b : D.nd.O i) (M0 : MatN D.nd i), b ≠ 0 ∧ M0.map (toK D.nd i) = b • M := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (D.nd.O i)) Finset.univ
    (fun ab : Fin D.R.nV × Fin D.R.nV => M ab.1 ab.2)
  choose M0 hM0 using fun ab : Fin D.R.nV × Fin D.R.nV => hb ab (Finset.mem_univ _)
  refine ⟨b, fun a c => M0 (a, c), nonZeroDivisors.coe_ne_zero b, ?_⟩
  ext a c
  simp only [Matrix.smul_apply]
  exact hM0 (a, c)

theorem rhoCont_of (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) : RhoCont i ρ π := by
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ := conjK_self i r ρ π hd
  have hA : ∀ g, (rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = P * (rO D.nd i r π g).map (toK D.nd i) * Q := by
    intro g
    have h := hconj g
    beta_reduce at h
    rw [h, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  obtain ⟨b1, P0, hb1, hP0⟩ := exists_integral_mul i P
  obtain ⟨b2, Q0, hb2, hQ0⟩ := exists_integral_mul i Q
  have hid : ∀ g, (b1 * b2) • rO D.nd i (rN i r ρ π) π g = P0 * rO D.nd i r π g * Q0 := by
    intro g
    apply Matrix.map_injective (toK_inj i)
    show ((b1 * b2) • rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = (P0 * rO D.nd i r π g * Q0).map (toK D.nd i)
    rw [Matrix.map_mul, Matrix.map_mul, hP0, hQ0, map_smul_toK', hA, map_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, smul_smul, mul_comm (toK D.nd i b1), ← map_mul]
    exact algebraMap_smul (KK D.nd i) (b2 * b1) _
  have hcont : Continuous fun g => (b1 * b2) • rO D.nd i (rN i r ρ π) π g := by
    simp only [hid]
    exact (continuous_const.matrix_mul (hc π)).matrix_mul continuous_const
  have hne : b1 * b2 ≠ 0 := mul_ne_zero hb1 hb2
  unfold RhoCont
  refine continuous_pi fun a => continuous_pi fun b => ?_
  refine GlobalTheory.BlockJumpsCompare.continuous_of_mul (D.nd.O_adic i) hne ?_
  have h2 : Continuous fun g => ((b1 * b2) • rO D.nd i (rN i r ρ π) π g) (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) :=
    (continuous_apply_apply _ _).comp hcont
  refine h2.congr (fun g => ?_)
  change (b1 * b2) * rO D.nd i (rN i r ρ π) π g (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) = _
  rw [(normAt_rN i r ρ π).2.2 g a b]

end Rec

end Formalism.MainNotions.N.K.Norm
end
