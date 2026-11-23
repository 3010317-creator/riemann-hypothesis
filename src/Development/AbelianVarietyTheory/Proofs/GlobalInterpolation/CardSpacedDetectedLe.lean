module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.NumberTheory.DirichletCharacter.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EnormSqLeLintegralDisc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HybridLargeSieve

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory.SpacedDetected

noncomputable def poly (Q : ℕ) (c : ℕ → ℂ) (x : Σ N : ℕ, DirichletCharacter ℂ (N + 1)) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6), c n * x.2 (n : ZMod (x.1 + 1)) * (n : ℂ) ^ (-s)

private theorem exists_card_divisors_le_mul_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, n ≠ 0 → (n.divisors.card : ℝ) ≤ K * (n : ℝ) ^ ε := by
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set M := 1 + 1 / (ε * Real.log 2)
  set B := ⌈Real.exp (1 / ε)⌉₊
  refine ⟨M ^ B, by positivity, fun n hn => ?_⟩
  rw [Nat.card_divisors hn]; push_cast
  rw [show (n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) by exact_mod_cast Nat.prod_primeFactors_pow_factorization hn,
    ← Real.finsetProd_rpow _ _ fun _ _ => by positivity]
  set f : ℕ → ℝ := fun p => if p < B then M else 1
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, (f p * ((p : ℝ) ^ n.factorization p) ^ ε) := by
        refine Finset.prod_le_prod₀ (fun _ _ => by positivity) fun p hp => ?_
        set a := n.factorization p
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        have hp0 : (0 : ℝ) < p := by linarith
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, Real.rpow_def_of_pos hp0]
        have hexp := Real.add_one_le_exp (Real.log p * (a * ε))
        simp only [f]; split_ifs with h
        · have hlog : Real.log 2 ≤ Real.log p := Real.log_le_log two_pos hp2
          have hMa : (a : ℝ) + 1 ≤ M * (Real.log p * (a * ε) + 1) := by
            calc (a : ℝ) + 1 = 1 / (ε * Real.log 2) * (Real.log 2 * (a * ε)) + 1 := by field_simp
              _ ≤ M * (Real.log p * (a * ε)) + M := by
                  gcongr; exact le_add_of_nonneg_left zero_le_one; exact le_add_of_nonneg_right (by positivity)
              _ = M * (Real.log p * (a * ε) + 1) := by ring
          exact hMa.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
        · rw [one_mul]
          have hBp : Real.exp (1 / ε) ≤ p := (Nat.le_ceil _).trans (by exact_mod_cast not_lt.mp h)
          have h1 : 1 ≤ Real.log p * ε := (div_le_iff₀ hε).1 ((Real.log_exp (1 / ε)).symm.trans_le (Real.log_le_log (Real.exp_pos _) hBp))
          linarith [le_mul_of_one_le_left (Nat.cast_nonneg a) h1, show Real.log (p : ℝ) * (a * ε) = Real.log p * ε * a by ring]
    _ = (∏ p ∈ n.primeFactors, f p) * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε := Finset.prod_mul_distrib
    _ ≤ M ^ B * ∏ p ∈ n.primeFactors, ((p : ℝ) ^ n.factorization p) ^ ε := by
        refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun _ _ => by positivity)
        rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const]
        exact pow_le_pow_right₀ (le_add_of_nonneg_right (by positivity))
          ((Finset.card_le_card fun p hp => Finset.mem_range.2 (Finset.mem_filter.1 hp).2).trans_eq (Finset.card_range B))

private theorem sum_weighted_coeff_sq_le {K : ℝ} (hK : 0 < K) {c : ℕ → ℂ}
    (hc : ∀ n ≠ 0, ‖c n‖ ≤ K * (n : ℝ) ^ ((1 : ℝ) / 400)) {Q : ℕ} (hQ : 2 ≤ Q) {σ : ℝ} (hσ : 1 - 3 / 800 ≤ σ) :
    ∑ n ∈ Finset.Icc 1 (Q ^ 6), ((Q : ℝ) ^ 2 * ((Q : ℝ) + 1) + n) *
      ‖if n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6) then c n * (n : ℂ) ^ (-(σ : ℂ)) else 0‖ ^ 2 ≤ 3 * K ^ 2 * 80 * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast (by omega : 1 ≤ Q)
  have hθ : ∑ n ∈ Finset.Icc 1 (Q ^ 6), (n : ℝ) ^ ((1 : ℝ) / 80 - 1) ≤ 80 * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, add_comm (1 : ℝ)]
    have htel : (∑ k ∈ Finset.range (Q ^ 6), ((k : ℝ) + 1) ^ ((1 : ℝ) / 80 - 1)) * (1 / 80) ≤ ((Q ^ 6 : ℕ) : ℝ) ^ ((1 : ℝ) / 80) := by
      rw [Finset.sum_mul]
      refine (Finset.sum_le_sum fun k _ => ?_).trans_eq (by rw [Finset.sum_range_sub (fun k : ℕ => (k : ℝ) ^ ((1 : ℝ) / 80)) (Q ^ 6)]; simp)
      set x : ℝ := (k : ℝ) + 1
      have hx : 1 ≤ x := by linarith [k.cast_nonneg (α := ℝ)]
      have hx0 : 0 < x := by linarith
      have hb := mul_le_mul_of_nonneg_left (rpow_one_add_le_one_add_mul_self (s := -(1 / x)) (by rw [neg_le_neg_iff, div_le_one hx0]; exact hx)
        (by norm_num : (0 : ℝ) ≤ 1 / 80) (by norm_num)) (by positivity : 0 ≤ x ^ ((1 : ℝ) / 80))
      have hsplit : (k : ℝ) ^ ((1 : ℝ) / 80) = x ^ ((1 : ℝ) / 80) * (1 + -(1 / x)) ^ ((1 : ℝ) / 80) := by
        rw [← Real.mul_rpow hx0.le (by rw [← sub_eq_add_neg, sub_nonneg, div_le_one hx0]; exact hx)]; congr 1; simp only [x]; field_simp; ring
      have hpow : x ^ ((1 : ℝ) / 80 - 1) * (1 / 80) = x ^ ((1 : ℝ) / 80) - x ^ ((1 : ℝ) / 80) * (1 + (1 / 80) * -(1 / x)) := by
        rw [Real.rpow_sub hx0, Real.rpow_one]; field_simp; ring
      show x ^ ((1 : ℝ) / 80 - 1) * (1 / 80) ≤ ((k + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 80) - (k : ℝ) ^ ((1 : ℝ) / 80); push_cast; linarith
    have hqpow : ((Q ^ 6 : ℕ) : ℝ) ^ ((1 : ℝ) / 80) ≤ (Q : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
    linarith
  refine (le_trans ?_ (mul_le_mul_of_nonneg_left hθ (by positivity : 0 ≤ 3 * K ^ 2))).trans_eq (by ring)
  rw [Finset.mul_sum]; refine Finset.sum_le_sum fun n hn => ?_
  split_ifs with hI
  · have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnQ : (Q : ℝ) ^ 3 < n := by exact_mod_cast (Finset.mem_Ioc.mp hI).1
    have hweight : (Q : ℝ) ^ 2 * ((Q : ℝ) + 1) + n ≤ 3 * n := by
      linarith [pow_le_pow_right₀ hQ1 (by omega : 2 ≤ 3), show (Q : ℝ) ^ 2 * ((Q : ℝ) + 1) = (Q : ℝ) ^ 3 + (Q : ℝ) ^ 2 by ring]
    have hcoef := hc n (by omega)
    rw [norm_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_neg, ← Complex.ofReal_cpow hn0.le, Complex.norm_real, Real.norm_of_nonneg (by positivity), mul_pow]
    calc _ ≤ (3 * (n : ℝ)) * ((K * (n : ℝ) ^ ((1 : ℝ) / 400)) ^ 2 * ((n : ℝ) ^ (-σ)) ^ 2) := by gcongr
      _ = 3 * K ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 200 + 1 - 2 * σ) := by
          rw [show (1 : ℝ) / 200 + 1 - 2 * σ = (1 / 400) * 2 + 1 + (-σ) * 2 by ring, Real.rpow_add hn0, Real.rpow_add hn0,
            Real.rpow_one, Real.rpow_mul hn0.le, Real.rpow_mul hn0.le, Real.rpow_two, Real.rpow_two]; ring
      _ ≤ 3 * K ^ 2 * (n : ℝ) ^ ((1 : ℝ) / 80 - 1) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) (by linarith)) (by positivity)
  · simp; positivity

theorem _root_.GlobalTheory.SpacedDetected.card_spaced_detected_le : ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 2 ≤ Q → ∀ T : Finset (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ), (∀ p ∈ T, p.1 + 1 ≤ Q ∧ p.2.1.IsPrimitive ∧ 1 - 1 / 400 ≤ p.2.2.re ∧ p.2.2.re ≤ 1 ∧ |p.2.2.im| ≤ Q ∧ (1 / 2 : ℝ) ≤ ‖∑ n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6), ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ) * p.2.1 (n : ZMod (p.1 + 1)) * (n : ℂ) ^ (-p.2.2)‖) → (∀ (N : ℕ) (χ : DirichletCharacter ℂ (N + 1)) (ρ ρ' : ℂ), (⟨N, χ, ρ⟩ : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ)) ∈ T → (⟨N, χ, ρ'⟩ : (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ)) ∈ T → ρ ≠ ρ' → 1 ≤ |ρ.im - ρ'.im|) → (T.card : ℝ) ≤ C * (Q : ℝ) ^ ((1 : ℝ) / 8) := by
  classical
  obtain ⟨C₁, hC₁, hmv⟩ := _root_.GlobalTheory.norm_sq_le_integral_square
  obtain ⟨C₂, hC₂, hls⟩ := _root_.GlobalTheory.HybridLargeSieve.hybrid_large_sieve
  obtain ⟨K, hK, hdiv⟩ := exists_card_divisors_le_mul_rpow (1 / 400) (by norm_num)
  refine ⟨4 * (C₁ / (1 / 800) ^ 2) * ((1 / 200) * (C₂ * (3 * K ^ 2 * 80))), by positivity, fun Q hQ T hT hsep => ?_⟩
  set r : ℝ := 1 / 800 with hr
  set c : ℕ → ℂ := fun n => ((∑ d ∈ n.divisors.filter (fun d => d ≤ Q ^ 3), (moebius d : ℤ) : ℤ) : ℂ)
  have hc : ∀ n ≠ 0, ‖c n‖ ≤ K * (n : ℝ) ^ ((1 : ℝ) / 400) := fun n hn => by
    refine le_trans ?_ (hdiv n hn); rw [Complex.norm_intCast, ← Int.cast_abs]
    exact_mod_cast (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_card_nsmul _ _ 1 fun _ _ => abs_moebius_le_one).trans
      (by simpa using Finset.card_filter_le n.divisors (fun d => d ≤ Q ^ 3)))
  set F : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → ℂ → ℂ := fun x s => poly Q c x s
  have hFdiff : ∀ x, Differentiable ℂ (F x) := fun x s => DifferentiableAt.fun_sum fun n hn =>
    (differentiableAt_id.neg.const_cpow (Or.inl (by exact_mod_cast (by have := (Finset.mem_Ioc.mp hn).1; omega : n ≠ 0)))).const_mul _
  set Tm : ℝ := Q + 1 with hTm
  have hTm1 : (1 : ℝ) ≤ Tm := by rw [hTm]; linarith [Q.cast_nonneg (α := ℝ)]
  set σ₀ : ℝ := 1 - 1 / 400 - r with hσ₀; set σ₁ : ℝ := 1 + r with hσ₁
  have hW : ∀ x (a b : ℝ), Continuous fun σ : ℝ => ∫ t in a..b, ‖F x (σ + t * I)‖ ^ 2 := fun x _ _ => by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'; have := (hFdiff x).continuous; fun_prop
  set G : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → ℝ → ℝ := fun x σ => ∫ t in (-Tm)..Tm, ‖F x (σ + t * I)‖ ^ 2 with hG
  have hle : σ₀ ≤ σ₁ := by rw [hσ₀, hσ₁, hr]; norm_num
  have hpt : ∀ p ∈ T, (1 / 4 : ℝ) ≤ C₁ / r ^ 2 * ∫ σ in σ₀..σ₁, ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2 := fun p hp => by
    obtain ⟨-, -, hre1, hre2, -, hbig⟩ := hT p hp
    change (1 / 2 : ℝ) ≤ ‖F ⟨p.1, p.2.1⟩ p.2.2‖ at hbig
    refine ((by norm_num : (1 / 4 : ℝ) = (1 / 2) ^ 2).trans_le (pow_le_pow_left₀ (by norm_num) hbig 2)).trans
      ((hmv _ p.2.2 r (hFdiff _) (by rw [hr]; norm_num)).trans (mul_le_mul_of_nonneg_left ?_ (by positivity)))
    exact intervalIntegral.integral_mono_interval (by rw [hσ₀]; linarith) (by rw [hr]; linarith) (by rw [hσ₁]; linarith)
      (Eventually.of_forall fun _ => intervalIntegral.integral_nonneg (by rw [hr]; linarith) fun _ _ => by positivity) ((hW _ _ _).intervalIntegrable _ _)
  set P := T.image fun p => (⟨p.1, p.2.1⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1))
  have hgroup : ∑ p ∈ T, ∫ σ in σ₀..σ₁, ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2 ≤ ∑ x ∈ P, ∫ σ in σ₀..σ₁, G x σ := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun p => (⟨p.1, p.2.1⟩ : Σ N : ℕ, DirichletCharacter ℂ (N + 1))) (fun p hp => Finset.mem_image_of_mem _ hp)]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [← intervalIntegral.integral_finsetSum fun p _ => (hW _ _ _).intervalIntegrable _ _]
    refine intervalIntegral.integral_mono_on hle ((continuous_finsetSum _ fun p _ => hW _ _ _).intervalIntegrable _ _)
      ((hW x _ _).intervalIntegrable _ _) fun σ _ => ?_
    have hcF : Continuous fun t : ℝ => ‖F x (σ + t * I)‖ ^ 2 := by have := (hFdiff x).continuous; fun_prop
    dsimp only [G]
    rw [intervalIntegral.integral_of_le (by linarith),
      Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2, intervalIntegral.integral_of_le (by rw [hr]; linarith)],
      ← MeasureTheory.integral_biUnion_finset _ (fun _ _ => measurableSet_Ioc)]
    · refine MeasureTheory.setIntegral_mono_set hcF.integrableOn_Ioc (Eventually.of_forall fun _ => by positivity) (Eventually.of_forall fun t ht => ?_)
      obtain ⟨p, hp, htp⟩ := Set.mem_iUnion₂.mp ht
      have hb := abs_le.mp (hT p (Finset.mem_filter.mp hp).1).2.2.2.2.1
      rw [Set.mem_Ioc, hTm]; rw [Set.mem_Ioc, hr] at htp; exact ⟨by linarith, by linarith⟩
    · rintro ⟨N, χ, ρ⟩ hp ⟨N', χ', ρ'⟩ hp' hne; rw [Function.onFun, Set.disjoint_left]; rintro t ⟨hta1, hta2⟩ ⟨htb1, htb2⟩
      obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hp').2.symm); cases h
      have hs := hsep N χ ρ ρ' (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp').1 fun e => hne (by rw [e])
      rw [hr] at hta1 hta2 htb1 htb2; rcases abs_cases (ρ.im - ρ'.im) with ⟨e, _⟩ | ⟨e, _⟩ <;> linarith
    · exact fun _ _ => hcF.integrableOn_Ioc
  have hsieve : ∀ σ ∈ Set.Icc σ₀ σ₁, ∑ x ∈ P, G x σ ≤ C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8) := fun σ hσ => by
    set a : ℕ → ℂ := fun n => if n ∈ Finset.Ioc (Q ^ 3) (Q ^ 6) then c n * (n : ℂ) ^ (-(σ : ℂ)) else 0
    have hsub : Finset.Ioc (Q ^ 3) (Q ^ 6) ⊆ Finset.Icc 1 (Q ^ 6) := fun n hn =>
      Finset.mem_Icc.2 ⟨by have := (Finset.mem_Ioc.mp hn).1; omega, (Finset.mem_Ioc.mp hn).2⟩
    have hrepr : ∀ x (t : ℝ), F x (σ + t * I) = ∑ n ∈ Finset.Icc 1 (Q ^ 6), a n * x.2 (n : ZMod (x.1 + 1)) * (n : ℂ) ^ (-(t * I)) := fun x t => by
      rw [← Finset.sum_subset hsub fun n _ hn => by simp only [a, hn, ↓reduceIte, zero_mul]]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by have := (Finset.mem_Ioc.mp hn).1; omega : n ≠ 0)
      simp only [a, hn, ↓reduceIte]; rw [neg_add, Complex.cpow_add _ _ hn0]; ring
    let H : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → ℝ := fun x =>
      ∫ t in (-Tm)..Tm, ‖∑ n ∈ Finset.Icc 1 (Q ^ 6), a n * x.2 (n : ZMod (x.1 + 1)) * (n : ℂ) ^ (-(t * I))‖ ^ 2
    have hPsub : P ⊆ (Finset.range Q).sigma fun q => Finset.univ.filter fun χ : DirichletCharacter ℂ (q + 1) => χ.IsPrimitive := fun x hx => by
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_sigma.2 ⟨Finset.mem_range.2 (by have := (hT p hp).1; dsimp only; omega), Finset.mem_filter.2 ⟨Finset.mem_univ _, (hT p hp).2.1⟩⟩
    calc ∑ x ∈ P, G x σ = ∑ x ∈ P, H x := by simp only [hG, H, hrepr]
      _ ≤ ∑ x ∈ (Finset.range Q).sigma (fun q => Finset.univ.filter fun χ : DirichletCharacter ℂ (q + 1) => χ.IsPrimitive), H x :=
          Finset.sum_le_sum_of_subset_of_nonneg hPsub fun _ _ _ => intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity
      _ = ∑ q ∈ Finset.range Q, ∑ᶠ (χ : DirichletCharacter ℂ (q + 1)) (_ : χ ∈ {χ | χ.IsPrimitive}),
            ∫ t in (-Tm)..Tm, ‖∑ n ∈ Finset.Icc 1 (Q ^ 6), a n * χ n * (n : ℂ) ^ (-(t * I))‖ ^ 2 := by
          rw [Finset.sum_sigma]; exact Finset.sum_congr rfl fun _ _ => by rw [finsum_mem_eq_toFinset_sum, Set.toFinset_ofPred]
      _ ≤ C₂ * ∑ n ∈ Finset.Icc 1 (Q ^ 6), ((Q : ℝ) ^ 2 * Tm + n) * ‖a n‖ ^ 2 := hls Q (Q ^ 6) a Tm (by omega) hTm1
      _ ≤ C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8) :=
          (mul_le_mul_of_nonneg_left (sum_weighted_coeff_sq_le hK hc hQ (by have := hσ.1; rw [hσ₀, hr] at this; linarith)) hC₂.le).trans_eq (by ring)
  have hint : ∑ x ∈ P, ∫ σ in σ₀..σ₁, G x σ ≤ (1 / 200) * (C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8)) := by
    rw [← intervalIntegral.integral_finsetSum fun x _ => (hW x _ _).intervalIntegrable _ _]
    refine (intervalIntegral.integral_mono_on hle ((continuous_finsetSum _ fun x _ => hW x _ _).intervalIntegrable _ _) intervalIntegrable_const hsieve).trans_eq ?_
    rw [intervalIntegral.integral_const, smul_eq_mul, hσ₀, hσ₁, hr]; norm_num
  calc (T.card : ℝ) = 4 * ∑ _ ∈ T, (1 / 4 : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ 4 * (C₁ / r ^ 2 * ∑ p ∈ T, ∫ σ in σ₀..σ₁, ∫ t in (p.2.2.im - r)..(p.2.2.im + r), ‖F ⟨p.1, p.2.1⟩ (σ + t * I)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (by rw [Finset.mul_sum]; exact Finset.sum_le_sum hpt) (by norm_num)
    _ ≤ 4 * (C₁ / r ^ 2 * ((1 / 200) * (C₂ * (3 * K ^ 2 * 80) * (Q : ℝ) ^ ((1 : ℝ) / 8)))) := by gcongr; exact hgroup.trans hint
    _ = _ := by rw [hr]; ring

end GlobalTheory.SpacedDetected
