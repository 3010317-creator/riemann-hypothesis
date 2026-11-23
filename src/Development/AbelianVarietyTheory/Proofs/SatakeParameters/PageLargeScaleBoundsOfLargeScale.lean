module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleLogMulLeSizeRatio
public import Formalism.LocalRingCardinality.DataParams
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThinSizeDominatesAtLargeScale
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopSizeAddLeThreeHalvesScale
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem roomy_of_large : ∀ eps C A : ℝ, 0 < eps → 100 ≤ C → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L), L.sc.eps = eps → P.CLw ≤ A → x0 ≤ L.sc.x → Roomy L C := by
  intro eps C A he hC
  have hC0 : (0 : ℝ) ≤ C := by linarith
  obtain ⟨x1, h1⟩ := _root_.GlobalTheory.HTW.thinSize_dominates eps he
  obtain ⟨x2, h2⟩ := _root_.GlobalTheory.scale_log_mul_b'_le_b eps C (max A 0) he hC0 (le_max_right _ _)
  refine ⟨max (max x1 x2) 4, fun D L P hL hA hx => ?_⟩
  have hx1 : x1 ≤ L.sc.x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : x2 ≤ L.sc.x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx4 : (4 : ℝ) ≤ L.sc.x := le_trans (le_max_right _ _) hx
  obtain ⟨a1, a2, a3⟩ := h1 D L P hL hx1
  refine ⟨hC, a1, a2, a3, _root_.GlobalTheory.Ggeo.bT_add_div_le_three_halves D L P hx4, ?_⟩
  have hb : (0 : ℝ) ≤ L.sc.b' := by linarith
  have hlog : 0 ≤ Real.log L.sc.x := Real.log_nonneg (by linarith)
  have hw : (D.host.Lw : ℝ) ≤ max A 0 * Real.log L.sc.x :=
    P.Lw_le.trans (mul_le_mul_of_nonneg_right (hA.trans (le_max_left _ _)) hlog)
  refine le_trans ?_ (h2 L.sc hL hx2)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) hC0) hb

end GlobalTheory.HTW
