module

public import Formalism.LandauZeroFreeBounds.LogDerivRegionChiOf

@[expose] public section
open Complex Finset ArithmeticFunction
noncomputable section
namespace Formalism.ZeroFreeDirichlet

lemma log_analytic_conductor_pos (q : ℕ) [NeZero q] (t : ℝ) : 0 < Real.log ((q : ℝ) * (|t| + 2)) :=
  Real.log_pos (one_lt_mul_of_le_of_lt (Nat.one_le_cast.mpr (NeZero.pos q)) (by linarith [abs_nonneg t]))
lemma zero_free_region_mono {c c' : ℝ} (h : c ≤ c') {q : ℕ} [NeZero q] {s : ℂ}
    (hs : InRegion c q s) : InRegion c' q s := by
  unfold InRegion at hs ⊢; linarith [div_le_div_of_nonneg_right h (log_analytic_conductor_pos q s.im).le]

lemma half_le_of_real_in_region {c₁ : ℝ} (h : c₁ ≤ 1 / 20) {q : ℕ} [NeZero q] {β : ℝ}
    (hs : InRegion c₁ q (β : ℂ)) : 1 / 2 ≤ β := by
  unfold InRegion at hs; simp only [Complex.ofReal_re, Complex.ofReal_im, abs_zero, zero_add] at hs
  have hl2 : Real.log 2 ≤ Real.log ((q : ℝ) * 2) :=
    Real.log_le_log zero_lt_two (by linarith [(Nat.one_le_cast.mpr (NeZero.pos q) : (1 : ℝ) ≤ q)])
  have hL : 0 < Real.log ((q : ℝ) * 2) := (Real.log_pos one_lt_two).trans_le hl2
  linarith [(div_le_iff₀ hL).mpr (by linarith [Real.log_two_gt_d9] : c₁ ≤ 1 / 2 * Real.log (q * 2))]
lemma exists_exceptional_zero_set (cZ c₁ : ℝ) (hle : c₁ ≤ cZ)
    (hZ : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
      InRegion cZ q s → IsLZero χ s →
        χ ^ 2 = 1 ∧ χ ≠ 1 ∧ s.im = 0 ∧ deriv (DirichletCharacter.LFunction χ) s ≠ 0 ∧
        ∀ (χ' : DirichletCharacter ℂ q) (s' : ℂ), InRegion cZ q s' → IsLZero χ' s' → χ' = χ ∧ s' = s)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) : ∃ B : Finset ℝ, ExcZeros c₁ χ B := by
  by_cases h : ∃ s : ℂ, InRegion c₁ q s ∧ IsLZero χ s
  · obtain ⟨s, hs, hL⟩ := h
    obtain ⟨-, hχ1, him, hder, huniq⟩ := hZ q χ s (zero_free_region_mono hle hs) hL
    have hre : ((s.re : ℝ) : ℂ) = s := Complex.ext rfl him.symm
    refine ⟨{s.re}, by simp, fun β hβ => ?_, fun s' hs' hL' =>
      ⟨s.re, by simp, (huniq χ s' (zero_free_region_mono hle hs') hL').2.trans hre.symm⟩⟩
    rw [Finset.mem_singleton.mp hβ, hre]; exact ⟨hχ1, hs, hL.2, hder⟩
  · exact ⟨∅, by simp, by simp, fun s hs hL => (h ⟨s, hs, hL⟩).elim⟩

lemma chebyshev_character_trivial_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (x : ℝ)
    (hx : 1 ≤ x) : ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤ x * (Real.log x + 1) := by
  have hx0 : (0 : ℝ) ≤ x := zero_le_one.trans hx
  have h1 : ‖psiChi χ x‖ ≤ x * Real.log x := by
    refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (Real.log x) fun n hn => ?_).trans ?_)
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
      obtain ⟨hn1, hnx⟩ := Finset.mem_Icc.mp hn
      exact (mul_le_of_le_one_right vonMangoldt_nonneg (χ.norm_le_one _)).trans
        (vonMangoldt_le_log.trans (Real.log_le_log (Nat.cast_pos.mpr hn1)
          ((Nat.cast_le.mpr hnx).trans (Nat.floor_le hx0))))
    · rw [Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.floor_le hx0) (Real.log_nonneg hx)
  have h2 : ‖if χ = 1 then (x : ℂ) else 0‖ ≤ x := by split_ifs <;> simp [abs_of_nonneg hx0, hx0]
  linarith [norm_sub_le (psiChi χ x) (if χ = 1 then (x : ℂ) else 0)]
lemma exceptional_zero_term_bound (x A q cE β : ℝ) (hx : 2 ≤ x) (hA : 0 < A) (hq : 1 ≤ q)
    (hqL : q ≤ Real.log x ^ A) (hcE : 0 < cE) (hβ1 : 1 / 2 ≤ β)
    (hβ2 : β ≤ 1 - cE * q ^ (-(1 / (2 * A)))) :
    ‖(x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤ 2 * x * Real.exp (-cE * Real.sqrt (Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.ofReal_re, Complex.norm_real,
    Real.norm_of_nonneg (by linarith)]
  have h1 : q ^ (1 / (2 * A)) ≤ Real.sqrt (Real.log x) := by
    rw [Real.sqrt_eq_rpow, ← show A * (1 / (2 * A)) = 1 / 2 by field_simp, Real.rpow_mul hlog.le]
    exact Real.rpow_le_rpow (by linarith) hqL (by positivity)
  have h3 : cE / Real.sqrt (Real.log x) ≤ 1 - β :=
    (div_le_div_of_nonneg_left hcE.le (Real.rpow_pos_of_pos (by linarith) _) h1).trans
      (by rw [div_eq_mul_inv, ← Real.rpow_neg (by linarith)]; linarith)
  have h4a : cE * Real.sqrt (Real.log x) ≤ (1 - β) * Real.log x := by
    simpa [Real.mul_self_sqrt hlog.le, mul_assoc] using
      mul_le_mul_of_nonneg_right ((div_le_iff₀ (Real.sqrt_pos.mpr hlog)).mp h3)
        (Real.sqrt_nonneg (Real.log x))
  have hlin : Real.log x * β = Real.log x - (1 - β) * Real.log x := by ring
  have he : x * Real.exp (-cE * Real.sqrt (Real.log x)) =
      Real.exp (Real.log x + -cE * Real.sqrt (Real.log x)) := by rw [Real.exp_add, Real.exp_log hx0]
  have h5 : x ^ β ≤ x * Real.exp (-cE * Real.sqrt (Real.log x)) := by
    rw [he, Real.rpow_def_of_pos hx0]; exact Real.exp_le_exp.mpr (by linarith)
  exact ((div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le β) (by norm_num : (0 : ℝ) < 1 / 2)
    hβ1).trans_eq (by ring : x ^ β / (1 / 2) = 2 * x ^ β)).trans (by linarith)
lemma bounded_of_exp_sqrt_lt_pow (A c : ℝ) (_hA : 0 < A) (hc : 0 < c) :
    ∃ U : ℝ, 0 ≤ U ∧ ∀ L : ℝ, 0 < L → Real.exp (c * Real.sqrt L) < L ^ A → L ≤ U := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (((isLittleO_rpow_exp_pos_mul_atTop (2 * A) hc)
    |>.comp_tendsto Real.tendsto_sqrt_atTop).bound (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨max N 0, le_max_right _ _, fun L hL hlt => le_of_not_gt fun hcon => ?_⟩
  have h2 : ‖Real.sqrt L ^ (2 * A)‖ ≤ 1 / 2 * ‖Real.exp (c * Real.sqrt L)‖ :=
    hN L ((le_max_left _ _).trans hcon.le)
  have hs : Real.sqrt L ^ (2 * A) = L ^ A := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hL.le]; congr 1; ring
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg L) _),
    Real.norm_of_nonneg (Real.exp_pos _).le, hs] at h2
  linarith [Real.exp_pos (c * Real.sqrt L)]

theorem siegel_walfisz_character_of : SiegelWalfiszOf := by
  intro hP ⟨cZ, hcZ, hZ'⟩ hE A hA
  set c₁ : ℝ := min cZ (1 / 20)
  obtain ⟨c, C, hc, hPC⟩ := hP c₁ (lt_min hcZ (by norm_num)) (min_le_right _ _)
  obtain ⟨cE, hcE, hEB⟩ := hE (1 / (2 * A)) (by positivity)
  obtain ⟨U, hU0, hU⟩ := bounded_of_exp_sqrt_lt_pow A c hA hc
  set cf : ℝ := min c cE; have hcf0 : 0 < cf := lt_min hc hcE
  refine ⟨cf, (max C 0 + 2) + (U + 1) * Real.exp (cf * Real.sqrt U), hcf0, fun q _ χ x hx hqL => ?_⟩
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set E : ℝ := Real.exp (-cf * Real.sqrt (Real.log x)); rw [add_mul, add_mul]
  by_cases hsmall : Real.exp (c * Real.sqrt (Real.log x)) < Real.log x ^ A
  · refine le_add_of_nonneg_of_le (by positivity) ?_
    have hLU : Real.log x ≤ U := hU (Real.log x) (Real.log_pos (by linarith)) hsmall
    have he : 1 ≤ Real.exp (cf * Real.sqrt U) * E := by
      rw [← Real.exp_add, neg_mul, ← sub_eq_add_neg, ← mul_sub]
      exact Real.one_le_exp (mul_nonneg hcf0.le (sub_nonneg.mpr (Real.sqrt_le_sqrt hLU)))
    exact (chebyshev_character_trivial_bound χ x (by linarith)).trans
      ((mul_le_mul_of_nonneg_left (by linarith : Real.log x + 1 ≤ U + 1) hx0).trans
        ((le_mul_of_one_le_right (by positivity) he).trans_eq (by ring)))
  · refine le_add_of_le_of_nonneg ?_ (by positivity)
    obtain ⟨B, hB⟩ := exists_exceptional_zero_set cZ c₁ (min_le_left _ _) hZ' q χ
    have hmain := hPC q χ B x hB hx (hqL.trans (le_of_not_gt hsmall))
    have hsumB : ‖∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ)‖ ≤
        2 * x * Real.exp (-cE * Real.sqrt (Real.log x)) :=
      (norm_sum_le B _).trans ((Finset.sum_le_card_nsmul B _
        (2 * x * Real.exp (-cE * Real.sqrt (Real.log x))) fun β hβ => by
        obtain ⟨hχ1, hreg, hL0, -⟩ := hB.2.1 β hβ
        exact exceptional_zero_term_bound x A q cE β hx hA (Nat.one_le_cast.mpr (NeZero.pos q))
          hqL hcE (half_le_of_real_in_region (min_le_right _ _) hreg)
          (hEB q χ β (hZ' q χ (β : ℂ) (zero_free_region_mono (min_le_left _ _) hreg)
            ⟨Or.inl hχ1, hL0⟩).1 hχ1 hL0)).trans
        (by simpa using nsmul_le_nsmul_left (by positivity :
          0 ≤ 2 * x * Real.exp (-cE * Real.sqrt (Real.log x))) hB.1))
    have hexp {d : ℝ} (hd : cf ≤ d) : Real.exp (-d * Real.sqrt (Real.log x)) ≤ E :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hd) (Real.sqrt_nonneg _))
    have hC := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left C 0) hx0)
      (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_left (hexp (min_le_left _ _)) (by positivity))
    have hE2 := mul_le_mul_of_nonneg_left (hexp (min_le_right _ _)) (by positivity : 0 ≤ 2 * x)
    have htri := norm_sub_le
      (psiChi χ x - (if χ = 1 then (x : ℂ) else 0) + ∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ))
      (∑ β ∈ B, (x : ℂ) ^ (β : ℂ) / (β : ℂ))
    rw [add_sub_cancel_right] at htri
    have hsp : (max C 0 + 2) * x * E = max C 0 * x * E + 2 * x * E := by ring
    linarith

end Formalism.ZeroFreeDirichlet
