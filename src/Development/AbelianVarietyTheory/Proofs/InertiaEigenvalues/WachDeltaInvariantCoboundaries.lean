module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordApply
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedRootSubOnePow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedTraceAndLvlDvd
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardTorsionMulFinrank
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfAlgHomEqMul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAddPiSmul
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixFrobenius
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective
public import Mathlib.Algebra.Divisibility.Prod
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.RingTheory.PowerSeries.Inverse

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletedLocalisationInvariants, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordInjectiveRangeMem, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixGamma, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootCoeffRingOfGood, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueAlgHomOfPadicLocalization, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearMatrixComm, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulVecSmul, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootCoeffRingOfGood =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootCoeffRingOfGood", "h": "module\n\npublic import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.RegularLocalRing.Defs\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem exists_primitiveRoot_coeffRing_of_good {l : ℕ} [Fact l.Prime] (K LL : FinExt l)
    (h : Good K 1 LL) : ∃ ζ : ↥(OL LL), IsPrimitiveRoot ζ l := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hdeg : (Polynomial.cyclotomic l (Om l)).degree ≠ 0 :=
    (Polynomial.degree_cyclotomic_pos l (Om l) hl).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
  haveI : NeZero (l : Om l) := ⟨Nat.cast_ne_zero.mpr hl.ne'⟩
  have hζ : IsPrimitiveRoot z l := Polynomial.isRoot_cyclotomic_iff.mp hz
  have hmem : z ∈ Ks K 1 := by
    refine (le_sup_right : _ ≤ Ks K 1) ?_
    apply IntermediateField.subset_adjoin
    change z ^ (l ^ 1) = 1
    rw [pow_one]
    exact hζ.pow_eq_one
  have hLL : z ∈ LL.1 := h.2.2.2 (Ks K 1).val ⟨z, hmem⟩
  have hζ' : IsPrimitiveRoot (⟨z, hLL⟩ : ↥LL.1) l :=
    IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) hζ Subtype.val_injective
  have hint : IsIntegral ℤ_[l] (⟨z, hLL⟩ : ↥LL.1) :=
    IsIntegral.of_pow hl (by rw [hζ'.pow_eq_one]; exact isIntegral_one)
  exact ⟨⟨⟨z, hLL⟩, hint⟩,
    IsPrimitiveRoot.of_map_of_injective (f := (OL LL).val) hζ' Subtype.val_injective⟩

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootCoeffRingOfGood =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBin\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordApply\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedRootSubOnePow\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AssociatedTraceAndLvlDvd\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardTorsionMulFinrank\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletedLocalisationInvariants\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordInjectiveRangeMem\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfAlgHomEqMul\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBasisAddPiSmul\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixFrobenius\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMatrixGamma\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimitiveRootCoeffRingOfGood\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueAlgHomOfPadicLocalization\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemXSmulOfProjective\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearMatrixComm\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumMulVecSmul\npublic import Mathlib.Algebra.Divisibility.Prod\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.PowerSeries.Inverse\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.NB GlobalTheory.CycFr

namespace GlobalTheory.WachTie

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}

theorem mem_DelF_iff (g : W.Gam) : g ∈ W.DelF ↔ IsOfFinOrder g := by
  rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one]

theorem sum_DelF_mul {M : Type} [AddCommMonoid M] (F : W.Gam → M) (d : W.Gam) (hd : d ∈ W.DelF) :
    ∑ δ ∈ W.DelF, F (d * δ) = ∑ δ ∈ W.DelF, F δ := by
  refine Finset.sum_equiv (Equiv.mulLeft d) (fun δ => ?_) fun _ _ => rfl
  rw [mem_DelF_iff] at hd
  rw [mem_DelF_iff, mem_DelF_iff]
  exact ⟨fun h => hd.mul h, fun h => by simpa using hd.inv.mul h⟩

theorem prod_DelF_mul {M : Type} [CommMonoid M] (F : W.Gam → M) (d : W.Gam) (hd : d ∈ W.DelF) :
    ∏ δ ∈ W.DelF, F (d * δ) = ∏ δ ∈ W.DelF, F δ := by
  refine Finset.prod_equiv (Equiv.mulLeft d) (fun δ => ?_) fun _ _ => rfl
  rw [mem_DelF_iff] at hd
  rw [mem_DelF_iff, mem_DelF_iff]
  exact ⟨fun h => hd.mul h, fun h => by simpa using hd.inv.mul h⟩

theorem piNorm_spec : Associated (piNorm W) (X ^ W.DelF.card) ∧
    ∀ δ ∈ W.DelF, W.γ₀ δ (piNorm W) = piNorm W := by
  constructor
  · rw [piNorm, ← Finset.prod_const]
    refine Associated.prod _ _ _ fun δ _ => ?_
    obtain ⟨w, hw⟩ := X_dvd_iff.2 (W.γ₀_X δ).1
    have h1 := (W.γ₀_X δ).2
    rw [hw, coeff_succ_X_mul, coeff_zero_eq_constantCoeff] at h1
    rw [hw]
    exact associated_mul_unit_left _ _ (isUnit_iff_constantCoeff.2 (h1 ▸ (W.χΓ δ).isUnit))
  · intro d hd
    rw [piNorm, map_prod, ← prod_DelF_mul W (fun δ => W.γ₀ δ X) d hd]
    exact Finset.prod_congr rfl fun δ _ => by rw [map_mul]; rfl

variable [Fact l.Prime] [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (hp : PD.p = l)
include hp

omit [CharZero O] in
theorem φ₀_eq : W.φ₀ = act O (l : ℤ_[l]) ∧ W.q₀ = lvl l O 0 := by
  have h1 := W.q₀_def
  rw [hp] at h1
  refine ⟨algHom_ext_X _ _ ⟨_, W.φ₀_X⟩ (by rw [W.φ₀_X, h1, act_nat_X]), ?_⟩
  apply mul_left_cancel₀ (X_ne_zero (R := O))
  rw [h1, ← act_l_X, act_nat_X]

variable (χ : W.Gam →* ℤ_[l]ˣ) (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O))
include hχ

theorem γ₀_eq (g : W.Gam) : W.γ₀ g = act O (χ g : ℤ_[l]) :=
  GlobalTheory.CycFr.eq_act_of_comm W.φ₀ _ _ (by rw [(φ₀_eq W hp).1, act_nat_X]) (W.γ₀_comm g) (W.γ₀_X g).1
    (by rw [(W.γ₀_X g).2, hχ])

theorem exists_frTie [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]
    (hl : l ≠ 2) (hu : ¬ IsUnit (l : O)) (hζ : ∃ ζ : O, IsPrimitiveRoot ζ l)
    (hχ1 : Associated ((χ W.gam : ℤ_[l]) - 1) (l : ℤ_[l])) (ξ : O⟦X⟧)
    (hξ : Associated ξ (X ^ W.DelF.card)) (hinv : ∀ δ ∈ W.DelF, W.γ₀ δ ξ = ξ) :
    ∃ (R : Fr l O) (j : O⟦X⟧ →ₐ[O] O⟦X⟧), j X = ξ ∧ FrTie W R j ∧
      ∀ τ, ∃ ζ : O, IsPrimitiveRoot ζ l ∧ X - C (ζ - 1) ∣ ξ - C (R.ϖ τ) := by
  classical
  obtain ⟨hφ, hq⟩ := φ₀_eq W hp
  have hγ := γ₀_eq W hp χ hχ
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  let Δ : Subgroup ℤ_[l]ˣ := (CommGroup.torsion W.Gam).map χ
  have hΔ : (Δ : Set ℤ_[l]ˣ) = ↑(W.DelF.image χ) := by
    ext x
    simp only [Δ, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, CommGroup.mem_torsion,
      Finset.coe_image, mem_DelF_iff]
  have hfa : ∀ p : ℤ_[l]ˣ → Prop, (∀ δ ∈ Δ, p δ) ↔ ∀ δ ∈ W.DelF, p (χ δ) := by
    intro p
    simp only [← SetLike.mem_coe, hΔ, Finset.coe_image, Set.forall_mem_image]
  haveI : Finite Δ := by
    change Finite (Δ : Set ℤ_[l]ˣ)
    rw [hΔ]; infer_instance
  have hcard : Nat.card Δ = W.DelF.card := by
    change Nat.card (Δ : Set ℤ_[l]ˣ) = _
    rw [hΔ, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hχi]
  obtain ⟨R, j, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := exists_frame Δ (χ W.gam) ξ hl hu
    hζ (hcard ▸ hξ) ((hfa _).2 fun δ hδ => by rw [← hγ]; exact hinv δ hδ) hχ1
  refine ⟨R, j, h1, ⟨h2, fun a => ?_, by rw [hφ]; exact h4, by rw [hγ]; exact h5,
    Units.ext (h6.trans (hχ _)), h7.trans hcard, ?_, hq ▸ h8⟩, h9⟩
  · rw [h3, hfa]; simp only [hγ]
  · rw [h1, h7, hcard]; exact hξ

theorem π₀₁_spec (hl : l ≠ 2) (hc : W.DelF.card = l - 1) :
    Associated W.π₀₁ (X ^ W.DelF.card) ∧
      (∀ δ ∈ W.DelF, W.γ₀ δ W.π₀₁ = W.π₀₁) ∧ lvl l O 0 ∣ W.π₀₁ + (l : O⟦X⟧) := by
  classical
  have hγ := γ₀_eq W hp χ hχ
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  obtain ⟨a1, a2⟩ := GlobalTheory.CycFr.associated_trace_and_lvl_dvd (O := O) (W.DelF.image χ) hl
    (by rw [Finset.card_image_of_injective _ hχi, hc]) (fun δ hδ => by
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.1 hδ
      exact χ.isOfFinOrder ((mem_DelF_iff W g).1 hg))
  rw [Finset.sum_image (fun a _ b _ hab => hχi hab)] at a1 a2
  simp only [← hγ] at a1 a2
  have e : W.π₀₁ = 1 - (l : O⟦X⟧) + ∑ δ ∈ W.DelF, W.γ₀ δ (1 + X) := by
    rw [LocWach.π₀₁, hp]
  refine ⟨by rw [e, hc]; exact a1, fun d hd => ?_, by rw [e]; convert a2 using 1; ring⟩
  have h2 : W.γ₀ d (∑ δ ∈ W.DelF, W.γ₀ δ (1 + X)) = ∑ δ ∈ W.DelF, W.γ₀ δ (1 + X) := by

    rw [map_sum, ← sum_DelF_mul W (fun δ => W.γ₀ δ (1 + X)) d hd]
    exact Finset.sum_congr rfl fun δ _ => by rw [map_mul]; rfl
  rw [e, map_add (f := _), h2, map_sub, map_one, map_natCast]

end Generic

theorem eq_neg_of_root {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (hu : ¬ IsUnit (l : O)) (ξ : O⟦X⟧) (x ζ : O)
    (hζ : IsPrimitiveRoot ζ l) (hd : X - C (ζ - 1) ∣ ξ - C x) (hq : lvl l O 0 ∣ ξ + (l : O⟦X⟧)) :
    x = -(l : O) := by
  have h4 : X - C (ζ - 1) ∣ lvl l O 0 := by
    have h5 : lvl l O 0 = ∑ i ∈ Finset.range l, ((1 + X) ^ i - C ζ ^ i) := by
      rw [Finset.sum_sub_distrib]
      simp only [← map_pow]

      rw [← map_sum, hζ.geom_sum_eq_zero (Fact.out : l.Prime).one_lt]
      simp [lvl]
    rw [h5]
    refine Finset.dvd_sum fun i _ => ?_
    convert sub_dvd_pow_sub_pow (1 + X) (C ζ) i using 1
    rw [map_sub, map_one]; ring
  have h6 := (prime_X_sub_C _ (sub_one_mem_max hu ζ hζ.pow_eq_one)).2 (x + l) (by
    convert (h4.trans hq).sub hd using 1
    rw [map_add (f := _), map_natCast]; ring)
  exact eq_neg_of_add_eq_zero_left h6

def Attached {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} {n : ℕ}
    (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (R : Fr l ↥(OL LL))
    (j : (↥(OL LL))⟦X⟧ →ₐ[↥(OL LL)] (↥(OL LL))⟦X⟧) : Prop :=
  FrTie W R j ∧
    ∀ τ, ∃ ζ : ↥(OL LL), IsPrimitiveRoot ζ l ∧ X - C (ζ - 1) ∣ j X - C (R.ϖ τ)

theorem exists_attached {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) {K LL : FinExt l}
    (h : Good K 1 LL) (hl : l ≠ 2) (ξ : (↥(OL LL))⟦X⟧)
    (hξ : Associated ξ (X ^ (H.W K 1 LL h).DelF.card))
    (hinv : ∀ δ ∈ (H.W K 1 LL h).DelF, (H.W K 1 LL h).γ₀ δ ξ = ξ) :
    ∃ R j, j X = ξ ∧ R.e = Module.finrank ↥(K0 K) ↥K.1 ∧ Attached (H.W K 1 LL h) R j := by
  have hs := H.W_s K 1 LL h
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  have hex : ∀ g, ∃ y : ℤ_[l], algebraMap ℤ_[l] ↥(OL LL) y = ((H.W K 1 LL h).χΓ g : ↥(OL LL)) := by
    intro g
    obtain ⟨a, rfl⟩ := (H.W K 1 LL h).resΓ_onto g
    have hm : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ a : ℚ_[l])) := by
      rw [← (H.W K 1 LL h).χΓ_res a]
      exact ((H.W K 1 LL h).χΓ ((H.W K 1 LL h).resΓ a) : ↥(OL LL)).2
    have hm' : IsIntegral ℤ_[l] ((P.PD K).χ a : ℚ_[l]) :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[l] ℚ_[l] ↥LL.1)
        (algebraMap ℚ_[l] ↥LL.1).injective).mp hm
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hm'
    refine ⟨y, Subtype.ext ?_⟩
    show algebraMap ℤ_[l] ↥LL.1 y = _
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1, hy, ← (H.W K 1 LL h).χΓ_res a]
    rfl
  have hinj : Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
    intro a b hab
    apply IsFractionRing.injective ℤ_[l] ℚ_[l]
    apply (algebraMap ℚ_[l] ↥LL.1).injective
    rw [← IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1, ← IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1]
    exact congrArg Subtype.val hab
  choose y hy using hex
  have hi : ∀ g, y g * y g⁻¹ = 1 := fun g => hinj (by
    rw [map_mul, hy, hy, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one])
  have hi' : ∀ g, y g⁻¹ * y g = 1 := fun g => by simpa using hi g⁻¹
  let u : (H.W K 1 LL h).Gam → ℤ_[l]ˣ := fun g => ⟨y g, y g⁻¹, hi g, hi' g⟩
  let χ : (H.W K 1 LL h).Gam →* ℤ_[l]ˣ :=
    { toFun := u
      map_one' := by apply Units.ext; apply hinj; simp [u, hy]
      map_mul' := by intro a b; apply Units.ext; apply hinj; simp [u, hy] }
  have hχ : ∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = ((H.W K 1 LL h).χΓ g : ↥(OL LL)) := hy
  have hχ1 : Associated ((χ (H.W K 1 LL h).gam : ℤ_[l]) - 1) (l : ℤ_[l]) := by
    have hv : P.v LL (algebraMap ℤ_[l] ↥LL.1 ((χ (H.W K 1 LL h).gam : ℤ_[l]) - 1)) = 1 := by
      rw [map_sub, map_one, IsScalarTower.algebraMap_apply ℤ_[l] ↥(OL LL) ↥LL.1, hχ]
      have hg := (H.W K 1 LL h).gam_gen
      rw [hs, Nat.cast_one] at hg
      exact hg
    have hc0 : ((χ (H.W K 1 LL h).gam : ℤ_[l]) - 1) ≠ 0 := by
      intro hc
      rw [hc, map_zero, AddValuation.map_zero] at hv
      exact WithTop.top_ne_one hv
    have hspec := PadicInt.unitCoeff_spec hc0
    set v := PadicInt.unitCoeff hc0
    have hnn : ∀ w : ℤ_[l], 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 w) := fun w =>
      (P.v_O LL _).mpr (Subalgebra.algebraMap_mem _ w)
    have hv0 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (v : ℤ_[l])) = 0 := by
      have h1 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (v : ℤ_[l])) +
          P.v LL (algebraMap ℤ_[l] ↥LL.1 ((v⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) = 0 := by
        rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
      exact ((add_eq_zero_iff_of_nonneg (hnn _) (hnn _)).mp h1).1
    have hval : ((χ (H.W K 1 LL h).gam : ℤ_[l]) - 1).valuation = 1 := by
      rw [hspec, map_mul, AddValuation.map_mul, hv0, zero_add, map_pow, AddValuation.map_pow,
        map_natCast, P.v_l LL, nsmul_one] at hv
      exact_mod_cast hv
    refine ⟨v⁻¹, ?_⟩
    conv_lhs => rw [hspec]
    rw [hval, pow_one, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
  obtain ⟨R, j, rfl, h2, h5⟩ := exists_frTie (H.W K 1 LL h) (P.PD_p K) χ hχ hl hu
    (GlobalTheory.exists_primitiveRoot_coeffRing_of_good K LL h) hχ1 ξ hξ hinv
  have h3 : R.e = Module.finrank ↥(K0 K) ↥K.1 := by
    have hes := R.es
    have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL (H.W K 1 LL h) hl h.2.2.1
    have h2l := (Fact.out : l.Prime).two_le
    rw [h2.2.2.2.2.2.1] at hes
    have h0 : (H.W K 1 LL h).DelF.card ≠ 0 := fun h0 => by rw [h0] at hes; lia
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0)
    rw [hc, mul_comm, hes]
  exact ⟨R, j, rfl, h3, h2, h5⟩

end GlobalTheory.WachTie
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries =====
