module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtPsiOfNotMemZeroSet
public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLeviNonnegOfChartPlurisubharmonic
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameWeightLevi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobianDetIsFrameOnCanonicalWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothEtaleOfSmoothInCharts
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

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.wt_psi_smooth_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ δ : ℝ, (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), ∀ i y, y ∈ (A.chart i).source → y ∉ A.zeroSet s → ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i (fun x => A.ph E i x + α * psi A L s x) y ξ) → ∀ (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → (∀ y ∈ U, y ∉ A.zeroSet s) → SmoothR n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y) ∧ SmoothR n (fun y : U => z y) (fun y : U => psi A L s y) ∧ ∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n (fun y : U => z y) (fun y : U => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y) := by
  intro n Y _ _ _ _ _ ι La _ A E L s hs δ hlevi U z β hz hβ hU
  have hJ := _root_.GlobalTheory.OTY.jdet_isFrameOn_kap n Y ι La A U z hz
  have hW := _root_.GlobalTheory.frameWeight_levi n Y ι La A E U β (jdet A z) hz.isOpen hβ hJ
  have hP : ∀ x ∈ U, ∀ i, x ∈ (A.chart i).source →
      ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i x) :=
    fun x hx i hi => _root_.GlobalTheory.OTY.contDiffAt_psi_of_notMem_zeroSet n Y ι La A L s hs x (hU x hx) i hi
  have hS := (_root_.GlobalTheory.OTY.smooth_etale_of_smooth_in_charts n Y ι La A U z hz).2
  refine ⟨hS (GlobalTheory.OTY.TwEst.wt A E β z)
      (fun x hx => ⟨A.pick x, A.mem_pick x, (hW x hx _ (A.mem_pick x)).1⟩),
    hS (psi A L s) (fun x hx => ⟨A.pick x, A.mem_pick x, hP x hx _ (A.mem_pick x)⟩), ?_⟩
  intro α hα
  refine _root_.GlobalTheory.OTY.etale_leviNonneg n Y ι La A U z hz (fun y => GlobalTheory.OTY.TwEst.wt A E β z y + α * psi A L s y)
    (fun x hx => ⟨A.pick x, A.mem_pick x, ?_, fun ξ => ?_⟩)
  · exact (hW x hx _ (A.mem_pick x)).1.add (contDiffAt_const.mul (hP x hx _ (A.mem_pick x)))
  · have hc : ContDiffAt ℝ ∞ ((fun y => α * psi A L s y) ∘ (A.chart (A.pick x)).symm)
        (A.chart (A.pick x) x) :=
      contDiffAt_const.mul (hP x hx _ (A.mem_pick x))
    exact le_of_le_of_eq (hlevi α hα (A.pick x) x (A.mem_pick x) (hU x hx) ξ)
      ((hW x hx _ (A.mem_pick x)).2 _ hc ξ).symm
