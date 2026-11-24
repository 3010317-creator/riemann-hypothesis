module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.Analysis.Analytic.Order
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogDerivRiemannZetaLocalZeroSum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory.PrincipalLogDeriv

lemma norm_cpow_neg_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖(p : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [Complex.norm_natCast_cpow_of_pos hp.pos, Complex.neg_re]
  calc (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2

lemma half_le_norm_one_sub {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    1 / 2 ≤ ‖1 - (p : ℂ) ^ (-s)‖ := by
  have h := norm_cpow_neg_le hp hs
  have h' := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-s))
  rw [norm_one] at h'
  linarith

lemma one_sub_ne_zero {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    1 - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h' := half_le_norm_one_sub hp hs
  rw [h, norm_zero] at h'
  norm_num at h'

lemma hasDerivAt_factor {p : ℕ} (hp : p.Prime) (s : ℂ) :
    HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p) s := by
  have hc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z)) ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s :=
    ((hasDerivAt_id' s).neg).const_cpow (Or.inl hc)
  have h2 : HasDerivAt (fun z : ℂ => 1 - (p : ℂ) ^ (-z))
      (-((p : ℂ) ^ (-s) * Complex.log p * (-1))) s := h.const_sub 1
  convert h2 using 1
  ring

lemma norm_logDeriv_factor_le {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ ≤ Real.log p := by
  have h1 := norm_cpow_neg_le hp hs
  have h2 := half_le_norm_one_sub hp hs
  have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hlog : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p), Complex.norm_real,
      Real.norm_of_nonneg hl]
  rw [logDeriv_apply, (hasDerivAt_factor hp s).deriv, norm_div, norm_mul, hlog,
    div_le_iff₀ (by linarith)]
  nlinarith

lemma sum_log_primeFactors_le (q : ℕ) [NeZero q] :
    ∑ p ∈ q.primeFactors, Real.log p ≤ Real.log q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
  apply Real.log_le_log
  · exact Finset.prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  · have h := Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q)
    rw [← Nat.cast_prod]
    exact_mod_cast h

lemma norm_logDeriv_sub_le (q : ℕ) [NeZero q] {s : ℂ} (hs : 1 < s.re) :
    ‖deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
      - deriv riemannZeta s / riemannZeta s‖ ≤ Real.log q := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs
    exact lt_irrefl _ hs
  have hre : 1 ≤ s.re := hs.le
  have hev : LFunction (1 : DirichletCharacter ℂ q) =ᶠ[nhds s]
      fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z := by
    filter_upwards [isOpen_ne.mem_nhds hs1] with z hz
    exact LFunctionTrivChar_eq_mul_riemannZeta hz
  have hfac : ∀ p ∈ q.primeFactors, (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s ≠ 0 :=
    fun p hp => one_sub_ne_zero (Nat.prime_of_mem_primeFactors hp) hre
  have hdfac : ∀ p ∈ q.primeFactors, DifferentiableAt ℂ (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s :=
    fun p hp => (hasDerivAt_factor (Nat.prime_of_mem_primeFactors hp) s).differentiableAt
  have hF0 : (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-s))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfac
  have hFd : DifferentiableAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s :=
    DifferentiableAt.fun_finsetProd hdfac
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hζd : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hL : deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
      LFunction (1 : DirichletCharacter ℂ q) s =
      logDeriv (fun z => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s := by
    rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [hL, logDeriv_fun_mul (f := fun z : ℂ => ∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) s hF0 hζ0
    hFd hζd, ← logDeriv_apply riemannZeta, add_sub_cancel_right,
    logDeriv_fun_prod (f := fun (p : ℕ) (z : ℂ) => 1 - (p : ℂ) ^ (-z)) hfac hdfac]
  calc ‖∑ p ∈ q.primeFactors, logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖
      ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, Real.log p :=
        Finset.sum_le_sum fun p hp => norm_logDeriv_factor_le (Nat.prime_of_mem_primeFactors hp) hre
    _ ≤ Real.log q := sum_log_primeFactors_le q

theorem neg_re_logDeriv_le : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (σ t : ℝ), 1 < σ → σ ≤ 2 → -(deriv (LFunction (1 : DirichletCharacter ℂ q)) (σ + t * I) / LFunction (1 : DirichletCharacter ℂ q) (σ + t * I)).re ≤ (1 / ((σ : ℂ) + t * I - 1)).re + C * Real.log (q * (|t| + 2)) := by
  obtain ⟨C, hC, hZ⟩ := _root_.GlobalTheory.ZetaLocal.logDeriv_riemannZeta_local
  refine ⟨C + 1, by linarith, ?_⟩
  intro q _ σ t hσ1 hσ2
  set s : ℂ := (σ : ℂ) + t * I with hsdef
  have hsre : s.re = σ := by simp [hsdef]
  have hs1 : 1 < s.re := by rw [hsre]; exact hσ1
  have hsne : s ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hs1
    exact lt_irrefl _ hs1
  have hζ0 : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs1
  have hdist : ‖s - (3 / 2 + t * I)‖ ≤ 2 / 3 := by
    have h1 : s - (3 / 2 + t * I) = ((σ - 3 / 2 : ℝ) : ℂ) := by
      rw [hsdef]; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  obtain ⟨hfin, hbound⟩ := hZ t s hdist hsne hζ0
  set Z := {w : ℂ | ‖w - (3 / 2 + t * I)‖ ≤ 5 / 6 ∧ w ≠ 1 ∧ riemannZeta w = 0} with hZdef
  set S := ∑ᶠ w ∈ Z, (analyticOrderNatAt riemannZeta w : ℂ) / (s - w) with hSdef
  have hterm : ∀ w ∈ Z, 0 ≤ ((analyticOrderNatAt riemannZeta w : ℂ) / (s - w)).re := by
    intro w hw
    have hw1 : w.re ≤ 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_lt_re h hw.2.2
    have hpos : 0 ≤ (s - w).re := by rw [Complex.sub_re, hsre]; linarith
    rw [Complex.div_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, zero_div, add_zero]
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) hpos) (Complex.normSq_nonneg _)
  have hS : 0 ≤ S.re := by
    rw [hSdef, finsum_mem_eq_finite_toFinset_sum _ hfin, Complex.re_sum]
    exact Finset.sum_nonneg fun w hw => hterm w (hfin.mem_toFinset.mp hw)
  set E := deriv riemannZeta s / riemannZeta s + 1 / (s - 1) - S with hEdef
  have hζ : deriv riemannZeta s / riemannZeta s = E - 1 / (s - 1) + S := by
    rw [hEdef]; ring
  have hE : -E.re ≤ C * Real.log (|t| + 2) :=
    le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm E) hbound)
  set D := deriv (LFunction (1 : DirichletCharacter ℂ q)) s / LFunction (1 : DirichletCharacter ℂ q) s
    - deriv riemannZeta s / riemannZeta s with hDdef
  have hD : ‖D‖ ≤ Real.log q := norm_logDeriv_sub_le q hs1
  have hDre : -D.re ≤ Real.log q := le_trans (neg_le_abs _) (le_trans (Complex.abs_re_le_norm D) hD)
  have hLsplit : deriv (LFunction (1 : DirichletCharacter ℂ q)) s /
      LFunction (1 : DirichletCharacter ℂ q) s = D + (E - 1 / (s - 1) + S) := by
    rw [hDdef, ← hζ]; ring
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
  have ht2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  have hlt : 0 ≤ Real.log (|t| + 2) := Real.log_nonneg (by linarith)
  have hlog : Real.log (q * (|t| + 2)) = Real.log q + Real.log (|t| + 2) :=
    Real.log_mul (by linarith) (by linarith)
  rw [hLsplit, hlog]
  simp only [Complex.add_re, Complex.sub_re]
  nlinarith

open Filter Topology

private lemma deriv_dslope_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) :
    deriv (dslope f 0) 0 = deriv (deriv f) 0 / 2 := by
  let g := dslope f 0
  have hg : AnalyticAt ℂ g 0 := hf.dslope 0
  have he : f = fun z : ℂ => f 0 + z * g z := by
    funext z
    simpa only [sub_zero, smul_eq_mul, add_comm] using
      (eq_add_of_sub_eq (sub_smul_dslope f 0 z).symm)
  have hd : deriv f =ᶠ[𝓝 (0 : ℂ)] fun z => g z + z * deriv g z := by
    filter_upwards [hg.eventually_analyticAt] with z hz
    have h := ((hasDerivAt_id' z).fun_mul hz.differentiableAt.hasDerivAt).const_add (f 0)
    rw [he]
    simpa only [Pi.mul_apply, one_mul] using h.deriv
  have h2 := (hg.differentiableAt.hasDerivAt.fun_add
    ((hasDerivAt_id' (0 : ℂ)).fun_mul hg.deriv.differentiableAt.hasDerivAt)).deriv
  rw [hd.deriv_eq, h2]
  simp only [one_mul, zero_mul, add_zero]
  change deriv g 0 = (deriv g 0 + deriv g 0) / 2
  ring


private lemma logDeriv_simple_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0) (hd0 : deriv f 0 ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 = deriv (deriv f) 0 / (2 * deriv f 0) ∧
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), f s ≠ 0 ∧ deriv f s / f s = 1 / s + h s := by
  let g := dslope f 0
  have hg : AnalyticAt ℂ g 0 := hf.dslope 0
  have hg0 : g 0 ≠ 0 := by simpa only [g, dslope_same] using hd0
  have he : f = fun z : ℂ => z * g z := by
    funext z
    simpa only [sub_zero, smul_eq_mul, hf0] using (sub_smul_dslope f 0 z).symm
  refine ⟨fun s => deriv g s / g s, hg.deriv.div hg hg0, ?_, ?_⟩
  · simp only [g, dslope_same, deriv_dslope_zero hf, div_div]
  · filter_upwards [hg.continuousAt.eventually_ne hg0 |>.filter_mono nhdsWithin_le_nhds,
      hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hgs hga hs
    have hs0 : s ≠ 0 := hs
    have hd : deriv f s = g s + s * deriv g s := by
      rw [he]
      simpa only [one_mul] using ((hasDerivAt_id' s).fun_mul hga.differentiableAt.hasDerivAt).deriv
    constructor
    · rw [congrFun he s]
      exact mul_ne_zero hs0 hgs
    · rw [hd, congrFun he s]
      field_simp


private lemma logDeriv_factor_origin {p : ℕ} (hp : p.Prime) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 = -(Complex.log p) / 2 ∧
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), 1 - (p : ℂ) ^ (-s) ≠ 0 ∧
        logDeriv (fun z : ℂ => 1 - (p : ℂ) ^ (-z)) s = 1 / s + h s := by
  let f := fun z : ℂ => 1 - (p : ℂ) ^ (-z)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hf : AnalyticAt ℂ f 0 := by
    apply Differentiable.analyticAt
    intro s
    exact (hasDerivAt_factor hp s).differentiableAt
  have hd : deriv f = fun z : ℂ => (p : ℂ) ^ (-z) * Complex.log p :=
    funext fun z => (hasDerivAt_factor hp z).deriv
  have hdz : deriv f 0 = Complex.log p := by simp [hd]
  have hlog : Complex.log (p : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg p)]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.log_pos (by exact_mod_cast hp.one_lt)))
  have hdd : deriv (deriv f) 0 = -(Complex.log p) ^ 2 := by
    rw [hd]
    have h := ((((hasDerivAt_id' (0 : ℂ)).neg).const_cpow (Or.inl hp0)).mul_const (Complex.log p)).deriv
    convert h using 1; simp; ring
  obtain ⟨g, hg, hval, he⟩ := logDeriv_simple_zero hf (by simp [f]) (by rwa [hdz])
  refine ⟨g, hg, ?_, he⟩
  rw [hval, hdd, hdz]
  field_simp


private lemma logDeriv_product_origin (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 = -(∑ p ∈ S, Complex.log p) / 2 ∧
      ∀ᶠ s in 𝓝[≠] (0 : ℂ), (∏ p ∈ S, (1 - (p : ℂ) ^ (-s))) ≠ 0 ∧
        logDeriv (fun z : ℂ => ∏ p ∈ S, (1 - (p : ℂ) ^ (-z))) s =
          (S.card : ℂ) / s + h s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨fun _ => 0, analyticAt_const, by simp, ?_⟩
    exact Filter.Eventually.of_forall (by intro s; simp [logDeriv_apply])
  | @insert p S hp ih =>
    have hp' := hS p (Finset.mem_insert_self p S)
    have hS' : ∀ r ∈ S, r.Prime := fun r hr => hS r (Finset.mem_insert_of_mem hr)
    obtain ⟨g, hg, hgv, hge⟩ := logDeriv_factor_origin hp'
    obtain ⟨h, hh, hhv, hhe⟩ := ih hS'
    refine ⟨fun z => g z + h z, hg.add hh, ?_, ?_⟩
    · dsimp only
      rw [hgv, hhv, Finset.sum_insert hp]
      ring
    · filter_upwards [hge, hhe] with s hs₁ hs₂
      have he : (fun z : ℂ => ∏ r ∈ insert p S, (1 - (r : ℂ) ^ (-z))) =
          fun z => (1 - (p : ℂ) ^ (-z)) * ∏ r ∈ S, (1 - (r : ℂ) ^ (-z)) := by
        funext z
        rw [Finset.prod_insert hp]
      constructor
      · rw [Finset.prod_insert hp]
        exact mul_ne_zero hs₁.1 hs₂.1
      · rw [he, logDeriv_fun_mul s hs₁.1 hs₂.1
          (hasDerivAt_factor hp' s).differentiableAt
          (DifferentiableAt.fun_finsetProd fun r hr =>
            (hasDerivAt_factor (hS' r hr) s).differentiableAt),
          hs₁.2, hs₂.2, Finset.card_insert_of_notMem hp, Nat.cast_add, Nat.cast_one]
        ring


/-- The principal logarithmic derivative has residue equal to the number of distinct
prime divisors at the origin. Its constant term includes one `-log p / 2` contribution
from each removed Euler factor. The expansion holds on a punctured neighborhood. -/
theorem logDeriv_LFunction_one_near_zero (q : ℕ) [NeZero q] :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
      h 0 = Complex.log (2 * (Real.pi : ℂ)) - (∑ p ∈ q.primeFactors, Complex.log p) / 2 ∧
      ∀ᶠ s in 𝓝[≠] (0 : ℂ),
        deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
          DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s =
          (q.primeFactors.card : ℂ) / s + h s := by
  obtain ⟨g, hg, hgv, hge⟩ := logDeriv_product_origin q.primeFactors
    (fun _ hp => Nat.prime_of_mem_primeFactors hp)
  have hz : AnalyticAt ℂ riemannZeta 0 :=
    DifferentiableOn.analyticAt (s := {z | z ≠ 1})
      (fun z hz => (differentiableAt_riemannZeta hz).differentiableWithinAt)
      (isOpen_ne.mem_nhds (by norm_num : (0 : ℂ) ≠ 1))
  have hz0 : riemannZeta 0 ≠ 0 := by norm_num [riemannZeta_zero]
  refine ⟨fun z => deriv riemannZeta z / riemannZeta z + g z,
    (hz.deriv.div hz hz0).add hg, ?_, ?_⟩
  · dsimp only
    rw [hgv, deriv_riemannZeta_zero, riemannZeta_zero]
    ring
  · filter_upwards [hge, hz.continuousAt.eventually_ne hz0 |>.filter_mono nhdsWithin_le_nhds,
      hz.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      eventually_ne_nhds (by norm_num : (0 : ℂ) ≠ 1) |>.filter_mono nhdsWithin_le_nhds]
      with s hs hzs hza hs1
    have he : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) =ᶠ[𝓝 s]
        fun z : ℂ => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z := by
      filter_upwards [eventually_ne_nhds hs1] with z hz
      exact DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz
    have hds : DifferentiableAt ℂ (fun z : ℂ => ∏ p ∈ q.primeFactors,
        (1 - (p : ℂ) ^ (-z))) s := DifferentiableAt.fun_finsetProd fun p hp =>
      (hasDerivAt_factor (Nat.prime_of_mem_primeFactors hp) s).differentiableAt
    have hl : deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s /
        DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s =
        logDeriv (fun z : ℂ => (∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-z))) * riemannZeta z) s := by
      rw [logDeriv_apply, he.deriv_eq, he.eq_of_nhds]
    rw [hl, logDeriv_fun_mul s hs.1 hzs hds hza.differentiableAt, hs.2, logDeriv_apply]
    ring


end GlobalTheory.PrincipalLogDeriv
