module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterPC
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.MemConePtsIffChartIdeal
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.MinimalPrimesOfMultihomogSup
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularSystemOfParametersLocalRing
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartMultihomogOrderAtPoint
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartParametersAtConePoint
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularAtConePointStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncChartRegularWithBoundaryChoiceStatement
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerFromAffineChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SymbolicPowerInAffineChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.ChPrime
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.UnitTimesParameterMonomial
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
import Mathlib.Tactic.Linter.Style
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterMinor

@[expose] public section

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp

theorem exists_sncData_of_isSncModel : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomogIdeal J → ¬ J ≤ mCoordIdeal y → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, ∃ d : ReciprocityTheory.AnForm.R.SncData (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.bd (pC (mCoordIdeal y)) (pC J) p) (SncRes.coord (pC (mCoordIdeal y)) p x) e (SncRes.rc (pC (mCoordIdeal y)) (pC J)), (∃ O : Set (SncRes.Pts (pC (mCoordIdeal y))), IsOpen O ∧ x ∈ O ∧ O ⊆ SncRes.src (pC (mCoordIdeal y)) p ∧ ∀ k, SncRes.comp (pC (mCoordIdeal y)) (pC J) k ∩ O = {x' ∈ O | ∃ l, d.σ l = some k ∧ eval (SncRes.coord (pC (mCoordIdeal y)) p x') (d.r l) = 0}) ∧ ∀ (f : MvPolynomial (Σ k, ι k) ℂ) (a : K → ℕ), ReciprocityTheory.AnForm.R.IsMultiHomog f a → f ∉ pC (mCoordIdeal y) → (∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC (mCoordIdeal y)), eval z f = 0 → z ∈ ReciprocityTheory.AnForm.R.conePts (pC J)) → ∃ u : ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x), IsUnit u ∧ algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (bind₁ (SncRes.lift p) f) = u * ∏ l ∈ d.J, algebraMap _ (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) (d.r l) ^ (d.σ l).elim 0 (fun k => SncRes.ordAlong (SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k) (pC (mCoordIdeal y)) f) := by
  intro K _ ι _ Ω _ _ y e J hA hJ hJn hS p x hx
  have hPm : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC (mCoordIdeal y)) := isMultiHomogIdeal_pC hA.2.1.2.1
  have hDm : ReciprocityTheory.AnForm.R.IsMultiHomogIdeal (pC J) := isMultiHomogIdeal_pC hJ
  have hz : ∀ k, SncRes.rep x ⟨k, p k⟩ ≠ 0 := hx
  have hzc := SncRes.rep_mem x
  obtain ⟨r, Jf, hIt, hreg, hdim, hspan, hpr⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exists_params K ι Ω y e J hA hS p (SncRes.rep x) hzc hz
  have hID : SncRes.ideal (pC (mCoordIdeal y)) p ≤ SncRes.ideal (pC (mCoordIdeal y) ⊔ pC J) p :=
    Ideal.map_mono (sup_le_sup_right le_sup_left _)
  obtain ⟨h, hh, hmem, hle⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_prod_params _ e _ _ _ r Jf hID hIt hreg hdim hspan hpr
  obtain ⟨σ, hinj, hnone, hσ, hcov⟩ := GlobalTheory.T.snc_chart_regular_at_cone_point K ι _ (pC J) e p (SncRes.rep x) r Jf hPm hDm hzc hz hIt hreg hdim hspan hpr
  let d : ReciprocityTheory.AnForm.R.SncData (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.bd (pC (mCoordIdeal y)) (pC J) p) (SncRes.coord (pC (mCoordIdeal y)) p x) e (SncRes.rc (pC (mCoordIdeal y)) (pC J)) :=
    { r := r, J := Jf, h := h, σ := σ, σ_injOn := hinj, σ_eq_none := hnone, span_eq := hspan, eval_h := hh,
      mem_bd := hmem, le_span := hle }
  refine ⟨d, GlobalTheory.T.snc_chart_regular_with_boundary_choice K ι _ (pC J) e p x r Jf σ hPm hDm hx hIt hreg hdim hspan hnone (fun l k hl => (hσ l k hl).1) hcov, ?_⟩
  intro f a hf hfP hfz
  obtain ⟨u, mm, hm0, hfac⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Mono.exists_unit_mul_monomial K ι _ (pC J) e p (SncRes.rep x) r Jf f a hPm hDm hzc hz hIt hreg hdim hspan hpr hf hfz
  refine ⟨u.val, u.isUnit, ?_⟩
  refine hfac.trans (congrArg (fun w => u.val * w) (Finset.prod_congr rfl fun l hl => ?_))
  have hlJ : l ∈ Jf := hl
  obtain ⟨k, hk⟩ : ∃ k, σ l = some k := by
    cases hσl : σ l with
    | none => exact absurd hlJ ((hnone l).1 hσl)
    | some k => exact ⟨k, rfl⟩
  have hdσ : d.σ l = some k := hk
  rw [hdσ]
  obtain ⟨hQc, hX⟩ := hσ l k hk
  have hQmin := SncRes.compIdeal_mem (P := pC (mCoordIdeal y)) (pC J) k
  have hQm := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup K ι _ _ hPm hDm _ hQmin
  have hQp : (SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k).IsPrime := hQmin.1.1
  have hord := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.exponent_eq_order_polynomial _ e _ _ r Jf _ u mm hIt hreg hdim hspan hfac l hlJ
  have key : ∀ n : ℕ, (∃ s ∉ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k,
      s * f ∈ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k ^ n ⊔ pC (mCoordIdeal y)) ↔ n ≤ mm l := by
    intro n
    rw [← hord n, ← hQc]
    constructor
    · rintro ⟨s, hs, hsf⟩
      exact _root_.GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Dehom.relation_dehom K ι _ _ p f s a n hPm hQm hQp hX hf hs hsf
    · rintro ⟨s', hs, hsf⟩
      exact _root_.GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Homog.relation_homogenises K ι _ _ p f a n s' hPm hQm hQp hX hf hs hsf
  have hset : {n : ℕ | ∃ s ∉ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k,
      s * f ∈ SncRes.compIdeal (pC (mCoordIdeal y)) (pC J) k ^ n ⊔ pC (mCoordIdeal y)} = Set.Iic (mm l) := by
    ext n
    exact key n
  show _ ^ mm l = _ ^ (SncRes.ordAlong _ _ f)
  rw [SncRes.ordAlong, hset, csSup_Iic]
  rfl

end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
