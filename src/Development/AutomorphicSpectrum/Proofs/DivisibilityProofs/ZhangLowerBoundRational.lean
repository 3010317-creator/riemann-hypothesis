module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RationalWeightIntegralCoeffs
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelArithIntersectionFormula
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelCurveDegreeNef
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelLogIntegralFormula
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelPointHeightDegree
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelSemipositiveConj
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

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem zhang_lower_bound_root_model : SuccessiveMinimaLowerBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ), IsRatWt lam →
      M.Semipos t lam s → M.NefFib lam s → (∀ W, M.IsPt W → e ≤ M.ht II t lam s W) →
      ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) ≤
        M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  intro hZ1 II hII Ψ _ N M t lam s e hrat hsemi hnef hpts
  obtain ⟨q, n, hq, hn⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.clear_rat_weight_coef Ψ N M lam s hrat
  have hp := _root_.GlobalTheory.CompanionTheory.Ar.Top.semipositive_integral_multiple Ψ N M t lam s q n hn hsemi
  have hnf := (_root_.GlobalTheory.CompanionTheory.Ar.Top.nefFib_integral_multiple Ψ N M t lam s q n hn).2 hnef
  have hW : ∀ W, IsArithVar W 1 → M.P ≤ W →
      ((q : ℝ) * e) * degC W ≤ II M.K M.ι W 1 ![combLine (M.line t) n] := by
    intro W h1 h2
    have hpt : M.IsPt W := ⟨h1, h2⟩
    obtain ⟨hd, hI⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.ht_combLine_integral_multiple II hII Ψ N M t lam s q n W hn hpt
    rw [hI]
    have hq' : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hd' : (0 : ℝ) ≤ degC W := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpts W hpt) hq') hd'
  have key := hZ1 M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) II hII.1 M.arith le_rfl
    hp.1 hnf hp.2 hW
  have hgeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) =
      (M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N) := by
    have := _root_.GlobalTheory.CompanionTheory.Ar.Top.geoFun_comb_mixed II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n) (fun _ j => hn j)
    simpa [geomDeg, Finset.prod_const] using this
  rw [hgeo, _root_.GlobalTheory.CompanionTheory.Ar.Top.top_comb_eq_arFun II hII Ψ N M t lam s q n hn] at key
  have hδ : (0 : ℝ) < M.δ := by exact_mod_cast M.δ_pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : (0 : ℝ) < (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) := by positivity
  refine le_of_mul_le_mul_left ?_ hc
  calc (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) * (((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N))
      = ((dimFl Ψ N + 1 : ℕ) : ℝ) * ((q : ℝ) * e) *
          ((M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N)) := by
        push_cast; ring
    _ ≤ _ := key

end GlobalTheory.CompanionTheory.Ar.Top
