module
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.RingTheory.SimpleRing.Principal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLFewZerosSmallDiscStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLargeVonMangoldtLogPowerSeriesNearZeroStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LargeMeanOfLargeDerivativeStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimeMeanValueCharactersTwistIntegralLeStatement
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ZeroFreePrincipal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogFactorialEqSumVonMangoldtMulDiv
import Mathlib.MeasureTheory.Function.Floor

@[expose] public section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin.LogFree
theorem principal_height : ∃ η : ℝ, 0 < η ∧ ∀ (q : ℕ) [NeZero q] (s : ℂ), 1 - η ≤ s.re → s.re < 1 →
    LFunction (1 : DirichletCharacter ℂ q) s = 0 → 3 ≤ |s.im| := by
  obtain ⟨c, hc, H⟩ := GlobalTheory.ZeroFreePrincipal.zero_free
  refine ⟨min (1 / 2) (c / Real.log 5), lt_min (by norm_num) (div_pos hc (Real.log_pos (by norm_num))),
    fun q _ s h1 h2 h0 => le_of_not_gt fun hlt => ?_⟩
  have hs : s ≠ 1 := by rintro rfl; simp at h2
  have := H 1 s hs <| (congrFun LFunction_modOne_eq s).trans <|
    (mul_eq_zero.1 ((LFunctionTrivChar_eq_mul_riemannZeta (N := q) hs).symm.trans h0)).resolve_left fun hp => by
      obtain ⟨p, hpm, hp0⟩ := Finset.prod_eq_zero_iff.1 hp
      have h3 : ‖(p : ℂ) ^ (-s)‖ < 1 := (Complex.norm_natCast_cpow_of_pos (Nat.prime_of_mem_primeFactors hpm).pos (-s)) ▸
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hpm).one_lt)
          (by simp; linarith [min_le_left (1 / 2 : ℝ) (c / Real.log 5)])
      simp [← sub_eq_zero.1 hp0] at h3
  linarith [min_le_right (1 / 2 : ℝ) (c / Real.log 5), div_le_div_of_nonneg_left hc.le
    (Real.log_pos (by push_cast; linarith [abs_nonneg s.im]))
    (Real.log_le_log (by positivity) (by push_cast; linarith : ((1 : ℕ) : ℝ) * (|s.im| + 2) ≤ 5))]
theorem count_le (Z : Finset ℂ) (w : ℂ → ℝ) (F : ℝ → ℝ) (U h δ M : ℝ) (hh : 0 ≤ h) (hU : 0 ≤ U)
    (hM : 0 ≤ M) (hδ : 0 ≤ δ) (hZ : ∀ ρ ∈ Z, |ρ.im| + h ≤ U) (hF : IntervalIntegrable F volume (-U) U)
    (hF0 : ∀ τ, 0 ≤ F τ) (h1 : ∀ ρ ∈ Z, ∀ τ, |τ - ρ.im| ≤ h → δ ≤ F τ ∧
      ∑ z ∈ Z.filter (fun z => |τ - z.im| ≤ h), w z ≤ M) :
    δ * (2 * h) * ∑ ρ ∈ Z, w ρ ≤ M * ∫ τ in (-U)..U, F τ := by
  let g (ρ : ℂ) := (Set.Icc (ρ.im - h) (ρ.im + h)).indicator fun _ : ℝ => δ * w ρ
  have hgi (ρ) : IntegrableOn (g ρ) (Set.Icc (-U) U) := (integrableOn_const (by simp)).indicator measurableSet_Icc
  have hint (ρ) (hρ : ρ ∈ Z) : ∫ τ in Set.Icc (-U) U, g ρ τ = δ * (2 * h) * w ρ := by
    rw [setIntegral_indicator measurableSet_Icc, Set.inter_eq_self_of_subset_right (Set.Icc_subset_Icc
      (by linarith [hZ ρ hρ, neg_abs_le ρ.im]) (by linarith [hZ ρ hρ, le_abs_self ρ.im])),
      setIntegral_const, smul_eq_mul, Real.volume_real_Icc_of_le (by linarith)]; ring
  rw [Finset.mul_sum, ← Finset.sum_congr rfl hint, ← integral_finsetSum _ fun ρ _ => hgi ρ,
    ← intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  refine integral_mono (integrable_finsetSum _ fun ρ _ => hgi ρ)
    (((intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).1 hF).const_mul M) fun τ => ?_
  have hmem (z : ℂ) : τ ∈ Set.Icc (z.im - h) (z.im + h) ↔ |τ - z.im| ≤ h := by
    rw [Set.mem_Icc, abs_le]; exact ⟨fun ⟨a, b⟩ => ⟨by linarith, by linarith⟩, fun ⟨a, b⟩ => ⟨by linarith, by linarith⟩⟩
  simp only [g, Set.indicator, hmem, ← Finset.sum_filter, ← Finset.mul_sum]
  rcases (Z.filter fun z => |τ - z.im| ≤ h).eq_empty_or_nonempty with h0 | ⟨ρ, hρ⟩
  · simp [h0, mul_nonneg hM (hF0 τ)]
  · obtain ⟨c, d⟩ := h1 ρ (Finset.mem_filter.1 hρ).1 τ (Finset.mem_filter.1 hρ).2
    exact (mul_le_mul_of_nonneg_left d hδ).trans ((mul_le_mul_of_nonneg_right c hM).trans_eq (mul_comm _ _))
noncomputable def primeSum {q : ℕ} (χ : DirichletCharacter ℂ q) (N y τ : ℝ) : ℂ :=
  ∑ p ∈ primesIoc N y, ((Real.log p : ℂ) / p) * χ (p : ZMod q) * (p : ℂ) ^ (-(τ * I))
theorem norm_cpow_le (n : ℕ) (τ : ℝ) : ‖(n : ℂ) ^ (-(τ * I))‖ ≤ 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · by_cases h : (-(τ * I) : ℂ) = 0 <;> simp [h, Complex.zero_cpow]
  · simp [Complex.norm_natCast_cpow_of_pos hn]
theorem integrable_primeSum {q : ℕ} (χ : DirichletCharacter ℂ q) (N M T : ℝ) (hN : 1 ≤ N) :
    Integrable (Function.uncurry fun τ y : ℝ => ‖primeSum χ N y τ‖ ^ 2 / y)
      ((volume.restrict (Set.Ioc (-T) T)).prod (volume.restrict (Set.Ioc N M))) := by
  have hm1 : Measurable fun x : ℝ × ℕ => ∑ p ∈ (Finset.Ioc ⌊N⌋₊ x.2).filter Nat.Prime,
      ((Real.log p : ℂ) / p) * χ (p : ZMod q) * (p : ℂ) ^ (-(x.1 * I)) :=
    measurable_from_prod_countable_left fun n => (continuous_finsetSum _ fun p hp =>
      continuous_const.mul <| Continuous.const_cpow (by fun_prop) <| Or.inl <| by
        exact_mod_cast (Finset.mem_filter.1 hp).2.ne_zero :
      Continuous fun τ : ℝ => ∑ p ∈ (Finset.Ioc ⌊N⌋₊ n).filter Nat.Prime,
        ((Real.log p : ℂ) / p) * χ (p : ZMod q) * (p : ℂ) ^ (-(τ * I))).measurable
  refine Integrable.of_bound (((hm1.comp (measurable_fst.prodMk (Nat.measurable_floor.comp measurable_snd)) :
    Measurable fun x : ℝ × ℝ => primeSum χ N x.2 x.1).norm.pow_const 2).div measurable_snd).aestronglyMeasurable
    ((∑ p ∈ primesIoc N M, ‖(Real.log p : ℂ) / p‖) ^ 2) ?_
  rw [Measure.prod_restrict]; refine (ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)).mono
    fun ⟨τ, y⟩ ⟨_, hy1, hy2⟩ => ?_
  dsimp only [Function.uncurry] at hy1 hy2 ⊢; rw [Real.norm_of_nonneg (div_nonneg (by positivity) (by linarith))]
  refine (div_le_self (by positivity) (by linarith)).trans (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
  exact (norm_sum_le _ _).trans <| (Finset.sum_le_sum fun p _ => by
    rw [norm_mul, norm_mul, mul_assoc]
    exact mul_le_of_le_one_right (norm_nonneg _) ((mul_le_of_le_one_right (norm_nonneg _)
      (norm_cpow_le p τ)).trans (χ.norm_le_one _))).trans <| Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (Finset.Ioc_subset_Ioc_right (Nat.floor_mono hy2))) fun _ _ _ => norm_nonneg _
theorem sum_log_div_le : ∃ CM : ℝ, 0 ≤ CM ∧ ∀ N y : ℝ, 1 ≤ y →
    ∑ p ∈ primesIoc N y, (p : ℝ) * ‖(Real.log p : ℂ) / p‖ ^ 2 / Real.log p ≤ Real.log y + CM := by
  obtain ⟨CM, h0, H⟩ := GlobalTheory.mertens_first_vonMangoldt
  refine ⟨CM, h0, fun N y hy => ((Finset.sum_congr rfl fun p hp => ?_).trans_le
    (Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ => Λ n / (n : ℝ))
      (fun p hp => Finset.mem_Icc.2 ⟨(Finset.mem_filter.1 hp).2.pos, (Finset.mem_Ioc.1 (Finset.mem_filter.1 hp).1).2⟩)
      fun _ _ _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))).trans (by linarith [(abs_le.1 (H y hy)).2])⟩
  have hpp := (Finset.mem_filter.1 hp).2
  have hl := Real.log_pos (Nat.one_lt_cast.2 hpp.one_lt); have : (0 : ℝ) < p := Nat.cast_pos.2 hpp.pos
  rw [vonMangoldt_apply_prime hpp, norm_div, Complex.norm_real, Complex.norm_natCast, Real.norm_of_nonneg hl.le]; field_simp
theorem mean_le : ∃ C CM : ℝ, 0 < C ∧ 0 ≤ CM ∧ ∀ (q : ℕ) [NeZero q] (T N M : ℝ),
    1 ≤ T → 1 ≤ N → N ≤ M → (2 * q * T) ^ 2 ≤ N →
    ∑ χ : DirichletCharacter ℂ q, (∫ τ in (-T)..T, ∫ y in N..M, ‖primeSum χ N y τ‖ ^ 2 / y) ≤
      C * (Real.log M + CM) * Real.log M := by
  obtain ⟨C, hC, H⟩ := GlobalTheory.T.primeMeanValue_characters_twist_integral_le
  obtain ⟨CM, hCM, HM⟩ := sum_log_div_le
  refine ⟨C, CM, hC, hCM, fun q _ T N M hT hN hNM hq => ?_⟩
  have hT' : -T ≤ T := by linarith
  have hJ (χ : DirichletCharacter ℂ q) : Integrable (fun y : ℝ => ∫ τ in Set.Ioc (-T) T, ‖primeSum χ N y τ‖ ^ 2 / y)
      (volume.restrict (Set.Ioc N M)) := (integrable_primeSum χ N M T hN).integral_prod_right
  simp only [intervalIntegral.integral_of_le hT', intervalIntegral.integral_of_le hNM,
    fun χ : DirichletCharacter ℂ q => integral_integral_swap (integrable_primeSum χ N M T hN)]
  rw [← integral_finsetSum _ fun χ _ => hJ χ]
  have hc : IntegrableOn (fun y : ℝ => C * (Real.log M + CM) * y⁻¹) (Set.Ioc N M) :=
    (continuousOn_const.mul (continuousOn_id.inv₀ fun y hy => by
      dsimp; linarith [hy.1])).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  refine (setIntegral_mono_on (integrable_finsetSum _ fun χ _ => hJ χ) hc measurableSet_Ioc
    fun y ⟨hy1, hy2⟩ => ?_).trans ?_
  · have hy0 : 0 < y := by linarith
    simp only [integral_div]; rw [← Finset.sum_div, div_eq_mul_inv]
    have h1 := H q T N y (fun p => (Real.log p : ℂ) / p) hT hq
    simp only [intervalIntegral.integral_of_le hT'] at h1; gcongr
    exact h1.trans (by gcongr; exact (HM N y (by linarith)).trans (by gcongr))
  · rw [← intervalIntegral.integral_of_le hNM, intervalIntegral.integral_const_mul,
      integral_inv_of_pos (by linarith) (by linarith)]
    exact mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos (by linarith) (by linarith))
      (div_le_self (by linarith) hN)) (by have := Real.log_nonneg (by linarith : 1 ≤ M); positivity)
theorem derSeries_twist {q : ℕ} (χ : DirichletCharacter ℂ q) (k : ℕ) (x τ : ℝ) :
    derSeries (fun n : ℕ => χ (n : ZMod q)) k ((x : ℝ) + τ * I) =
      derSeries (fun n : ℕ => χ (n : ZMod q) * (n : ℂ) ^ (-(τ * I))) k (x : ℝ) := by
  refine tsum_congr fun n => ?_; rcases n.eq_zero_or_pos with rfl | hn; · simp
  rw [neg_add, Complex.cpow_add _ _ (by exact_mod_cast hn.ne')]; ring
theorem finite_zerosBox {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ} (T : ℝ) (hσ : 0 < σ) :
    (zerosBox χ σ T).Finite :=
  (GlobalTheory.Mem.An.ZeroWindow.finite_zeros χ 0 T).subset fun _ h =>
    ⟨hσ.trans_le h.1, h.2.1, by simpa using h.2.2.1, h.2.2.2⟩
theorem detect : ∃ a b C C' r₀ K₀ : ℝ, 0 < a ∧ a < b ∧ 0 < C ∧ 0 < C' ∧ 0 < r₀ ∧
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (τ r L : ℝ) (K : ℕ) (ρ : ℂ), (χ ≠ 1 ∨ 2 ≤ |τ|) →
      Real.log (q * (|τ| + 2)) ≤ L → 0 < r → 1 / L ≤ r → r ≤ r₀ → C' * r * L ≤ K → K₀ ≤ K →
      LFunction χ ρ = 0 → ‖ρ - (1 + τ * I)‖ ≤ r → Real.exp (-(C * K)) / r ^ 3 ≤
        ∫ y in (Real.exp (a * K / r))..(Real.exp (b * K / r)), ‖primeSum χ (Real.exp (a * K / r)) y τ‖ ^ 2 / y := by
  obtain ⟨A, C3, r3, hA, hC3, hr3, H3⟩ := GlobalTheory.T.exists_large_vonMangoldtLogPowerSeries_near_zero
  obtain ⟨a, b, C4, r4, K0, ha, hab, hC4, hr4, H4⟩ := GlobalTheory.T.integral_prime_sum_sq_ge_of_derSeries_large A hA
  refine ⟨a, b, C4, C3, min r3 r4, K0, ha, hab, hC4, hC3, lt_min hr3 hr4,
    fun q _ χ τ r L K ρ h1 h2 h3 h4 h5 h6 h7 h8 h9 => ?_⟩
  obtain ⟨k, k1, k2, k3⟩ := H3 q χ τ r L K ρ h1 h2 h4 (h5.trans (min_le_left _ _)) h6 h8 h9
  rw [derSeries_twist] at k3; refine (H4 _ r K k (fun n => by
    rw [norm_mul]; exact (mul_le_of_le_one_right (norm_nonneg _) (norm_cpow_le n τ)).trans (χ.norm_le_one _))
    h3 (h5.trans (min_le_right _ _)) h7 k1 k2 k3).trans_eq ?_
  congr 1; ext y; congr 3; exact Finset.sum_congr rfl fun _ _ => by ring
theorem near {ρ : ℂ} {σ r τ : ℝ} (h1 : σ ≤ ρ.re) (h2 : ρ.re < 1) (h3 : 2 * (1 - σ) ≤ r) (h4 : |τ - ρ.im| ≤ r / 2) :
    ‖ρ - (1 + τ * I)‖ ≤ r := by
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  rw [show (ρ - (1 + τ * I)).re = ρ.re - 1 by simp, show (ρ - (1 + τ * I)).im = ρ.im - τ by simp,
    abs_sub_comm ρ.im, abs_of_neg (by linarith)]; linarith
theorem count_param : ∃ a D C C' r₀ K₀ η : ℝ, 0 < a ∧ 0 < D ∧ 0 < C ∧ 0 < C' ∧ 0 < r₀ ∧ 0 < η ∧
    ∀ (q : ℕ) [NeZero q] (T σ r L : ℝ) (K : ℕ), 2 ≤ T → 1 - η ≤ σ → 2 * (1 - σ) ≤ r → 0 < r →
      r ≤ r₀ → 1 / L ≤ r → Real.log (q * (T + 3)) ≤ L → C' * r * L ≤ K → K₀ ≤ K → 1 ≤ K →
      (2 * q * (T + 1)) ^ 2 ≤ Real.exp (a * K / r) →
      ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ σ T, (ord χ ρ : ℝ)) ≤
        D * (1 + r * L) * Real.exp (C * K) * (K : ℝ) ^ 2 := by
  obtain ⟨η, hη, H1⟩ := principal_height; obtain ⟨C2, hC2, H2⟩ := GlobalTheory.T.dirichletL_few_zeros_small_disc
  obtain ⟨a, b, C4, C3, r0, K0, ha, hab, hC4, hC3, hr0, H3⟩ := detect; obtain ⟨C5, CM, hC5, hCM, H5⟩ := mean_le
  have hb : 0 < b := ha.trans hab
  refine ⟨a, C2 * C5 * (b + CM) * b, C4, C3, min (1 / 2) r0, K0, η, ha, by positivity, hC4, hC3,
    by positivity, hη, fun q _ T σ r L K hT hσ hσr hr hrr hL hqL hK3 hK0 hK1 hN => ?_⟩
  have hr2 : r ≤ 1 / 2 := hrr.trans (min_le_left _ _); have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.2 NeZero.one_le
  have hL0 : 0 ≤ L := (Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))).trans hqL
  set N := Real.exp (a * K / r); set M := Real.exp (b * K / r)
  have hN1 : 1 ≤ N := Real.one_le_exp (by positivity); have hNM : N ≤ M := Real.exp_le_exp.2 (by gcongr)
  have hmean := H5 q (T + 1) N M (by linarith) hN1 hNM hN; rw [Real.log_exp] at hmean
  have h6 : Real.exp (-(C4 * K)) / r ^ 3 * (2 * (r / 2)) *
      ∑ χ : DirichletCharacter ℂ q, ∑ᶠ ρ ∈ zerosBox χ σ T, (ord χ ρ : ℝ) ≤
      C2 * (1 + r * L) * (C5 * (b * K / r + CM) * (b * K / r)) := by
    rw [Finset.mul_sum]; refine (Finset.sum_le_sum fun χ _ => ?_).trans
      (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hmean (by positivity))
    have hfin := finite_zerosBox χ (σ := σ) T (by linarith)
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    refine count_le _ _ _ _ _ _ _ (by positivity) (by linarith) (by positivity) (by positivity)
      (fun ρ hρ => by linarith [(hfin.mem_toFinset.1 hρ).2.2.1]) ?_
      (fun _ => intervalIntegral.integral_nonneg hNM fun y hy => div_nonneg (by positivity) (by linarith [hy.1]))
      fun ρ hρ τ hτ => ?_
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]; simp only [intervalIntegral.integral_of_le hNM]
      exact (integrable_primeSum χ N M (T + 1) hN1).integral_prod_left
    · obtain ⟨z1, z2, z3, z4⟩ := hfin.mem_toFinset.1 hρ
      have hc : χ ≠ 1 ∨ 2 ≤ |τ| := (em (χ = 1)).symm.imp_right fun h => by
        subst h; linarith [H1 q ρ (hσ.trans z1) z2 z4, abs_sub_comm τ ρ.im ▸ abs_sub_abs_le_abs_sub ρ.im τ]
      have hlog : Real.log (q * (|τ| + 2)) ≤ L := (Real.log_le_log (by positivity)
        (by gcongr ?_ * ?_; linarith [abs_sub_abs_le_abs_sub τ ρ.im])).trans hqL
      obtain ⟨f1, f2⟩ := H2 q χ τ r hc hr hr2; rw [finsum_mem_eq_finite_toFinset_sum _ f1] at f2
      refine ⟨H3 q χ τ r L K ρ hc hlog hr hL (hrr.trans (min_le_right _ _)) hK3 hK0 z4 (near z1 z2 hσr hτ),
        (Finset.sum_le_sum_of_subset_of_nonneg (fun z hz => ?_) fun _ _ _ => Nat.cast_nonneg _).trans
          (f2.trans (by gcongr))⟩
      rcases Finset.mem_filter.1 hz with ⟨y0, y5⟩; rcases hfin.mem_toFinset.1 y0 with ⟨y1, y2, -, y4⟩
      exact f1.mem_toFinset.2 ⟨near y1 y2 hσr y5, Or.inr fun e => by simp [e] at y2, y4⟩
  generalize (∑ χ : DirichletCharacter ℂ q, ∑ᶠ ρ ∈ zerosBox χ σ T, (ord χ ρ : ℝ)) = S at h6 ⊢
  have he := Real.exp_pos (C4 * K)
  have h7 := mul_le_mul_of_nonneg_left h6 (show 0 ≤ Real.exp (C4 * K) * r ^ 2 by positivity)
  rw [Real.exp_neg] at h7
  calc S = Real.exp (C4 * K) * r ^ 2 * ((Real.exp (C4 * K))⁻¹ / r ^ 3 * (2 * (r / 2)) * S) := by field_simp
    _ ≤ C2 * C5 * (b * K + CM * r) * b * (1 + r * L) * Real.exp (C4 * K) * K := h7.trans_eq (by field_simp)
    _ ≤ C2 * C5 * (b * K + CM * K) * b * (1 + r * L) * Real.exp (C4 * K) * K := by
        gcongr; linarith [show (1 : ℝ) ≤ K by exact_mod_cast hK1]
    _ = _ := by ring
theorem zero_density : ∃ A C η : ℝ, 0 < A ∧ 0 < C ∧ 0 < η ∧ ∀ (q : ℕ) [NeZero q] (T σ : ℝ),
    2 ≤ T → 1 - η ≤ σ → σ ≤ 1 → ∑ χ : DirichletCharacter ℂ q, (∑ᶠ ρ ∈ zerosBox χ σ T, (ord χ ρ : ℝ)) ≤
      C * ((q : ℝ) * T) ^ (A * (1 - σ)) := by
  obtain ⟨a, D, C, C3, r0, K0, η, ha, hD, hC, hC3, hr0, hη, H⟩ := count_param
  set E : ℝ := C3 + |K0| + 4 / a; set B : ℝ := C * (E + 1) + 3
  have hE0 : 0 < E := by positivity
  refine ⟨6 * B, D * (E + 1) ^ 2 * Real.exp (2 * B), min η (r0 / 2), by positivity, by positivity,
    by positivity, fun q _ T σ hT hσ hσ1 => ?_⟩
  have hq : (1 : ℝ) ≤ q := Nat.one_le_cast.2 NeZero.one_le
  have hl0 : 0 ≤ Real.log (q * (T + 3)) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))
  set L : ℝ := Real.log (q * (T + 3)) + 1 / r0 with hL
  have hL0 : 0 < L := add_pos_of_nonneg_of_pos hl0 (by positivity)
  set r : ℝ := max (2 * (1 - σ)) (1 / L) with hrdef
  have r3 : 0 < r := lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have x1 : 1 ≤ r * L := (div_le_iff₀ hL0).1 (le_max_right _ _)
  have hlT : Real.log (q * (T + 3)) ≤ 3 * Real.log (q * T) := by
    have : 0 ≤ T ^ 3 - T - 6 := (mul_nonneg (show 0 ≤ T - 2 by linarith)
      (show 0 ≤ T ^ 2 + 2 * T + 3 by positivity)).trans_eq (by ring)
    exact (Real.log_le_log (by positivity) (show (q : ℝ) * (T + 3) ≤ (q * T) ^ 3 by
      rw [mul_pow]; gcongr; exacts [le_self_pow₀ hq (by decide), by linarith])).trans_eq (by rw [Real.log_pow]; norm_num)
  have x2 : r * L ≤ 2 + 6 * (1 - σ) * Real.log (q * T) := by
    have s0 : 0 ≤ 1 - σ := by linarith
    rcases max_choice (2 * (1 - σ)) (1 / L) with hr | hr
    · have : 2 * (1 - σ) / r0 ≤ 1 := (div_le_one hr0).2 (by linarith [min_le_right η (r0 / 2)])
      calc r * L = 2 * ((1 - σ) * Real.log (q * (T + 3))) + 2 * (1 - σ) / r0 := by rw [hrdef, hr, hL]; ring
        _ ≤ 2 * ((1 - σ) * (3 * Real.log (q * T))) + 1 := by gcongr
        _ ≤ _ := by linarith
    · rw [hrdef, hr, one_div_mul_cancel hL0.ne']
      have : 0 ≤ Real.log (q * T) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq (by linarith))
      linarith [show 0 ≤ 6 * (1 - σ) * Real.log (q * T) by positivity]
  set K : ℕ := ⌈E * (r * L)⌉₊; have k1 : E * (r * L) ≤ K := Nat.le_ceil _
  have k2 : (K : ℝ) ≤ (E + 1) * (r * L) := by linarith [Nat.ceil_lt_add_one (show 0 ≤ E * (r * L) by positivity)]
  have hN : (2 * q * (T + 1)) ^ 2 ≤ Real.exp (a * K / r) := by
    have : 0 ≤ (T + 3) ^ 2 - 2 * (T + 1) := (show 0 ≤ T ^ 2 + 4 * T + 7 by positivity).trans_eq (by ring)
    rw [← Real.exp_log (by positivity : 0 < (2 * (q : ℝ) * (T + 1)) ^ 2), Real.exp_le_exp]
    refine (Real.log_le_log (by positivity) (show (2 * (q : ℝ) * (T + 1)) ^ 2 ≤ ((q * (T + 3)) ^ 2) ^ 2 by
      gcongr; rw [mul_comm 2, mul_assoc, mul_pow]; gcongr
      exacts [le_self_pow₀ hq (by decide), by linarith])).trans ?_
    rw [← pow_mul, Real.log_pow]; norm_num
    exact (show 4 * Real.log (q * (T + 3)) ≤ 4 * L by linarith [show 0 < 1 / r0 by positivity]).trans <|
      (le_div_iff₀ r3).2 <| (by field_simp : 4 * L * r = a * (4 / a * (r * L))).trans_le <|
        mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right (by linarith [abs_nonneg K0])
          (by positivity)).trans k1) ha.le
  refine (H q T σ r L K hT (by linarith [min_le_left η (r0 / 2)]) (le_max_left _ _) r3
    (max_le (by linarith [min_le_right η (r0 / 2)]) ((div_le_comm₀ hL0 hr0).2 (by linarith)))
    (le_max_right _ _) (by linarith [show 0 < 1 / r0 by positivity])
    (by rw [mul_assoc]; exact (mul_le_mul_of_nonneg_right
      (by linarith [abs_nonneg K0, show 0 < 4 / a by positivity]) (by positivity)).trans k1)
    (by linarith [le_abs_self K0, show E * 1 ≤ E * (r * L) by gcongr, show 0 < 4 / a by positivity])
    (by exact_mod_cast lt_of_lt_of_le (by positivity : (0 : ℝ) < E * (r * L)) k1) hN).trans ?_
  generalize r * L = x at *
  have e1 : 1 + x ≤ Real.exp x := by linarith [Real.add_one_le_exp x]
  calc _ ≤ D * Real.exp x * Real.exp (C * ((E + 1) * x)) * ((E + 1) * Real.exp x) ^ 2 := by
        gcongr; exact k2.trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
    _ = D * (E + 1) ^ 2 * Real.exp (B * x) := by
        rw [show B * x = x + C * ((E + 1) * x) + x + x by dsimp [B]; ring]; simp only [Real.exp_add]; ring
    _ ≤ D * (E + 1) ^ 2 * Real.exp (B * (2 + 6 * (1 - σ) * Real.log (q * T))) := by gcongr
    _ = _ := by rw [Real.rpow_def_of_pos (by positivity), mul_assoc _ (Real.exp _), ← Real.exp_add]; congr 2; ring
end GlobalTheory.Lin.LogFree
