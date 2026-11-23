module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtHolomorphicComplexChartOfSmoothAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableOnHolomorphicChartTransEtaleChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodPatchChartImageProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramMatrixSmoothIsUnitInHolomorphicChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnChernTransgressionTermPoincareGrowth
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopFormIntegralOfSupportInHolomorphicChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceComplexPointsOfProjVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionDensityHolomorphicChartEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopCoeffComplexEqZeroOfCutoffZero
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

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

set_option autoImplicit false
noncomputable section

theorem GlobalTheory.GoodTop.hasInt_corrDens_of_goodPatch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (corrDens E H₀ H ρ) (ptsIn X.str σ O) ((Real.pi ^ X.dim)⁻¹ * (∫ v in offHyp S (e '' W), corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) v).re) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hP ρ hρ hsupp
  classical
  have := X.smooth_str
  obtain ⟨hUo, hUeq, hK⟩ := _root_.GlobalTheory.GoodTop.goodPatch_image E O H hP
  set g : V X.dim → ℝ := corrTop (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ())
    with hg
  have hKc : IsCompact (e '' tsupport ρ) := hK _ (isClosed_tsupport ρ) hsupp
  have hint : IntegrableOn (corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()))
      (offHyp S (e '' W)) := by
    refine _root_.GlobalTheory.GoodTop.integrableOn_corrC S (e '' W) (e '' tsupport ρ) _ _ _ c hUo hKc (Set.image_mono hsupp) ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩ a ha
      exact hP.small z hz a ha
    · rintro _ ⟨z, hz, rfl⟩
      have htop : z ∈ ptsIn X.str σ (⊤ : X.X.Opens) := by
        simp [ptsIn]
      exact _root_.GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart E ⊤ H₀ hH₀ hP.holo htop (hP.sub hz) (hP.frame z hz)
    · intro v hv
      rw [← hUeq] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact _root_.GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart E O H hH hP.holo hzO (hP.sub hz) (hP.frame z hz)
    · intro v hv a i j
      rw [← hUeq] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.form z hz hzO a i j
    · intro v hv a b i j
      rw [← hUeq] at hv
      obtain ⟨z, ⟨hzO, hz⟩, rfl⟩ := hv
      exact hP.dbar z hz hzO a b i j
    · rintro _ ⟨z, hz, rfl⟩
      exact (_root_.GlobalTheory.GoodTop.contDiffAt_holoChart hP.holo (hP.sub hz) (hρ z)).contDiffWithinAt
    · rintro _ ⟨z, hz, rfl⟩ hK'
      rw [e.left_inv (hP.sub hz)]
      by_contra h0
      exact hK' ⟨z, subset_tsupport ρ h0, rfl⟩
  have hgi : IntegrableOn g (e '' (ptsIn X.str σ O ∩ W)) := by
    rw [hUeq]
    exact (hint.re).const_mul _
  have hval : (∫ v in e '' (ptsIn X.str σ O ∩ W), g v) = (Real.pi ^ X.dim)⁻¹ *
      (∫ v in offHyp S (e '' W), corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) v).re := by
    rw [hUeq, hg]
    simp only [corrTop]
    rw [integral_const_mul]
    congr 1
    exact integral_re hint
  rw [← hval]
  refine _root_.GlobalTheory.GoodTop.hasInt_of_chart (fun c : AlgChart X.str σ X.dim => c.e) (fun i j => i.holo_trans j)
    (fun y => AlgChart.exists_mem_source y) (isOpen_ptsIn O).measurableSet e W g hP.isOpen hP.sub
    (fun j => _root_.GlobalTheory.GoodTop.holoChart_trans_algChart hP.holo j) (_root_.GlobalTheory.GoodTop.isTopForm_corrDens E O H H₀ hH hH₀ hρ) ?_ ?_ hgi
  · intro i y _ hyW hyi
    have hy : y ∉ tsupport ρ := fun h => hyW (hsupp h)
    have h0 : ρ =ᶠ[𝓝 y] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.1 hy
    have h1 : (fun v => ρ (i.e.symm v)) =ᶠ[𝓝 (i.e y)] fun _ => 0 := by
      have ht := (i.e.continuousAt_symm (i.e.map_source hyi)).tendsto
      rw [i.e.left_inv hyi] at ht
      exact ht.eventually h0
    simp only [corrDens, corrTop]
    rw [_root_.GlobalTheory.GoodTop.corrC_eq_zero_of_eventuallyEq_zero _ _ h1]
    simp
  · intro j y hyS hyW hyj
    exact _root_.GlobalTheory.GoodTop.corrTop_holoChart_trans E O H H₀ hH hH₀ hρ hP.holo j hyS (hP.sub hyW) hyj (hP.frame y hyW)
