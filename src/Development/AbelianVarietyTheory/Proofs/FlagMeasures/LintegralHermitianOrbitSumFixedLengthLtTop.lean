module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AdelicUnitaryGroupStabilisersUnimodular
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelicUnitaryComplementRangeStabiliser
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsReflection
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabTransitiveOfLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FundamentalDomainUnitaryAdelicExistsMeasureEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WittTheoremAdelicOneVector
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Algebra.Group.OpenMapping
import Mathlib.Topology.Baire.LocallyCompactRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct ENNReal Pointwise

noncomputable section

namespace GlobalTheory.OrbitSumInt

theorem exists_compact_reach {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SigmaCompactSpace G] [MulAction G X] [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [ContinuousSMul G X] (x0 : X) (hcl : IsClosed (MulAction.orbit G x0))
    (K : Set X) (hK : IsCompact K) :
    ∃ C : Set G, IsCompact C ∧ ∀ g : G, g • x0 ∈ K → ∃ c ∈ C, c • x0 = g • x0 := by
  let O := MulAction.orbit G x0
  have : LocallyCompactSpace O := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : ContinuousSMul G O := ⟨continuous_induced_rng.2
    (continuous_smul.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))⟩
  let o0 : O := ⟨x0, MulAction.mem_orbit_self x0⟩
  have hopen : IsOpenMap (fun g : G => g • o0) := isOpenMap_smul_of_sigmaCompact o0
  have hK' : IsCompact (Subtype.val ⁻¹' K : Set O) :=
    hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have key : ∃ C : Set G, IsCompact C ∧ (Subtype.val ⁻¹' K : Set O) ⊆ (fun g : G => g • o0) '' C := by
    refine hK'.induction_on (p := fun s => ∃ C : Set G, IsCompact C ∧ s ⊆ (fun g : G => g • o0) '' C)
      ⟨∅, isCompact_empty, Set.empty_subset _⟩ (fun s t hst ⟨C, hC, h⟩ => ⟨C, hC, hst.trans h⟩) ?_ ?_
    · rintro s t ⟨C, hC, h⟩ ⟨D, hD, h'⟩
      exact ⟨C ∪ D, hC.union hD, by rw [Set.image_union]; exact Set.union_subset_union h h'⟩
    · rintro ⟨_, g, rfl⟩ -
      obtain ⟨C, hC, hg⟩ := exists_compact_mem_nhds g
      exact ⟨_, mem_nhdsWithin_of_mem_nhds (hopen.image_mem_nhds hg), C, hC, subset_rfl⟩
  obtain ⟨C, hC, h⟩ := key
  refine ⟨C, hC, fun g hg => ?_⟩
  obtain ⟨c, hc, e⟩ := h (a := g • o0) hg
  exact ⟨c, hc, congrArg Subtype.val e⟩


end GlobalTheory.OrbitSumInt
