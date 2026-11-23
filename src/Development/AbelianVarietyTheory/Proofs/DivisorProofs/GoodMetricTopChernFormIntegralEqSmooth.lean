module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMulTopChernFormIsTopDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPatchOfComplexPointOpenPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPoincareGoodPatchOutsideOpen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothPartitionOfUnityComplexPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralCongrOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFiniteSumTopForms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionDensitiesPartitionUnityEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopChernFormGoodPatch
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceComplexPointsOfProjVariety
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

@[expose] public section

open AlgebraicGeometry MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.GoodTop

theorem goodTopChernForm : GlobalTheory.Published.GoodTopChernForm := by
  intro F _ σ X m E O H H₀ hH hG hH₀ t ht
  rw [hasChernIntegral_iff] at ht ⊢
  haveI := X.smooth_str
  haveI : SecondCountableTopology (CxPts X.str σ) := inferInstance
  have hp : ∀ y : CxPts X.str σ, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := fun y => by
    by_cases hy : y ∈ ptsIn X.str σ O
    · exact _root_.GlobalTheory.GoodTop.exists_goodPatch_of_mem E O H hH y hy
    · exact _root_.GlobalTheory.GoodTop.exists_goodPatch E O H hG y hy
  choose e S A W c hyW hP using hp
  obtain ⟨s, ρ, hρ, hsupp, hsum⟩ := _root_.GlobalTheory.GoodTop.exists_cInf_partition W fun y => (hP y).isOpen.mem_nhds (hyW y)
  choose a b ha hb hab using fun i : s => _root_.GlobalTheory.GoodTop.hasInt_patch_transgression E O H H₀ hH hH₀ (hP i) (hρ i) (hsupp i)
  have hd : ∀ i j : AlgChart X.str σ X.dim,
      DifferentiableOn ℂ (j.e ∘ i.e.symm) (i.e.target ∩ i.e.symm ⁻¹' j.e.source) := fun i j => i.holo_trans j
  have hcov : ∀ y, ∃ i : AlgChart X.str σ X.dim, y ∈ i.e.source := fun y => AlgChart.exists_mem_source y
  have hm : ∀ U : X.X.Opens, MeasurableSet (ptsIn X.str σ U) := fun U => (isOpen_ptsIn U).measurableSet
  have hc : ∀ i, Continuous (ρ i) := fun i => continuous_iff_continuousAt.2 fun y => (hρ i y).continuousAt
  have h₁ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H) (ptsIn X.str σ O) (∑ i, a i) := by
    refine _root_.GlobalTheory.GoodTop.hasInt_congr_on _ (hm O) (fun i y _ _ => ?_)
      (_root_.GlobalTheory.GoodTop.hasInt_sum _ hd hcov (hm O) (fun i => _root_.GlobalTheory.GoodTop.isTopForm_mul_topDens E O H hH (hc i)) ha)
    rw [← Finset.sum_mul, hsum, one_mul]
  have h₂ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H₀) (ptsIn X.str σ ⊤) (∑ i, b i) := by
    refine _root_.GlobalTheory.GoodTop.hasInt_congr_on _ (hm ⊤) (fun i y _ _ => ?_)
      (_root_.GlobalTheory.GoodTop.hasInt_sum _ hd hcov (hm ⊤) (fun i => _root_.GlobalTheory.GoodTop.isTopForm_mul_topDens E ⊤ H₀ hH₀ (hc i)) hb)
    rw [← Finset.sum_mul, hsum, one_mul]
  have h₃ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun _ _ => 0) (ptsIn X.str σ O) (∑ i, (a i - b i)) :=
    _root_.GlobalTheory.GoodTop.hasInt_congr_on _ (hm O) (fun i y _ hy => _root_.GlobalTheory.GoodTop.sum_corrDens_eq_zero E O H H₀ ρ hρ hsum i y hy)
      (_root_.GlobalTheory.GoodTop.hasInt_sum _ hd hcov (hm O) (fun i => _root_.GlobalTheory.GoodTop.isTopForm_corrDens E O H H₀ hH hH₀ (hρ i)) hab)
  have e₂ : ∑ i, b i = t := h₂.2.symm.trans ht.2
  have e₃ : ∑ i, (a i - b i) = 0 := h₃.2.symm.trans (_root_.GlobalTheory.GoodTop.hasInt_zero _ _).2
  rw [Finset.sum_sub_distrib, sub_eq_zero, e₂] at e₃
  exact e₃ ▸ h₁

end GlobalTheory.GoodTop
