module

public import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoBasic
public import GroundTheory.AutomorphicForms.PartialDifferential.AnalyticHypoCutoff
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section
namespace GroundTheory.Automorphic.Sobolev
open MeasureTheory SchwartzMap LineDeriv FourierTransform Real
open scoped ContDiff
noncomputable section
variable {n : ℕ}

theorem fourier_iteratedLineDerivOp_apply (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) {k : ℕ}
    (w : Fin k → EuclideanSpace ℝ (Fin n)) (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (∂^{w} f) ξ = (∏ l, (2 * π * Complex.I) * (inner ℝ ξ (w l) : ℂ)) * 𝓕 f ξ := by
  induction k generalizing f with
  | zero => simp
  | succ k ih =>
    have hg : (fun x : EuclideanSpace ℝ (Fin n) ↦ inner ℝ x (w 0)).HasTemperateGrowth :=
      ((innerSL ℝ).flip (w 0)).hasTemperateGrowth
    rw [iteratedLineDerivOp_succ_left, fourier_lineDerivOp_eq, smul_apply,
      smulLeftCLM_apply_apply hg, ih, Fin.prod_univ_succ]
    simp only [Fin.tail, Complex.real_smul, smul_eq_mul]; ring

section Plancherel
variable {v : EuclideanSpace ℝ (Fin n) → ℂ}
theorem pdT_eq_iteratedLineDerivOp (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) {k : ℕ}
    (J : Fin k → Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    pdT J v x = (∂^{fun l ↦ ev (J l)} (hvc.toSchwartzMap hv)) x := by
  rw [iteratedLineDerivOp_eq_iteratedFDeriv]; rfl
theorem integrable_norm_sq_schwartz (g : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) :
    Integrable (fun x ↦ ‖g x‖ ^ 2) := by
  simpa using (g.memLp 2).integrable_norm_pow (p := 2) two_ne_zero
theorem norm_sq_fourier_pdT (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) {k : ℕ} (J : Fin k → Fin n)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    ‖𝓕 (∂^{fun l ↦ ev (J l)} φ) ξ‖ ^ 2 = (∏ l, (2 * π) ^ 2 * ξ (J l) ^ 2) * ‖𝓕 φ ξ‖ ^ 2 := by
  rw [fourier_iteratedLineDerivOp_apply, norm_mul, norm_prod, mul_pow, ← Finset.prod_pow]; congr 1
  exact Finset.prod_congr rfl fun l _ ↦ by
    simp [ev, EuclideanSpace.inner_single_right, mul_pow, abs_of_pos Real.pi_pos, sq_abs]
private theorem sum_norm_sq_fourier_pdT (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v)
    (q : ℕ) (ξ : EuclideanSpace ℝ (Fin n)) :
    ∑ J : Fin q → Fin n,
      ‖(𝓕 (∂^{fun l ↦ ev (J l)} (hvc.toSchwartzMap hv)) : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ξ‖ ^ 2 =
      ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ q * ‖𝓕 v ξ‖ ^ 2 := by
  simp_rw [norm_sq_fourier_pdT, ← Finset.sum_mul, congrFun (fourier_coe _) ξ]; congr 1
  have h := Finset.prod_univ_sum (fun _ : Fin q ↦ (Finset.univ : Finset (Fin n)))
    fun _ i ↦ (2 * π) ^ 2 * ξ i ^ 2
  rw [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  rw [← h, ← Finset.mul_sum, EuclideanSpace.norm_eq,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)]; simp
theorem integral_hsD_sq (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (q : ℕ) :
    ∫ x, hsD q v x ^ 2 = ∫ ξ, ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ q * ‖𝓕 v ξ‖ ^ 2 := by
  simp_rw [hsD_sq, pdT_eq_iteratedLineDerivOp hv hvc]
  rw [integral_finsetSum _ fun _ _ ↦ integrable_norm_sq_schwartz _,
    Finset.sum_congr rfl fun _ _ ↦ (integral_norm_sq_fourier _).symm,
    ← integral_finsetSum _ fun _ _ ↦ integrable_norm_sq_schwartz _]
  exact integral_congr_ae (ae_of_all _ (sum_norm_sq_fourier_pdT hv hvc q))
end Plancherel

section Symbol
variable {m : ℕ} {A : Finset (Fin n → ℕ)} {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}
def frozenOp (A : Finset (Fin n → ℕ)) (a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ) (m : ℕ)
    (x₀ : EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n) → ℂ)
    (x : EuclideanSpace ℝ (Fin n)) : ℂ :=
  ∑ α ∈ A with mabs α = m, a α x₀ * pderiv α v x
theorem fourier_mdir_apply (φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (α : Fin n → ℕ)
    (ξ : EuclideanSpace ℝ (Fin n)) :
    𝓕 (∂^{mdir α} φ) ξ = (2 * π * Complex.I) ^ mabs α * (mpow α ξ : ℂ) * 𝓕 φ ξ := by
  rw [fourier_iteratedLineDerivOp_apply, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin, ← prod_inner_mdir α ξ]; push_cast; ring
theorem prinSymbol_smul (x₀ ξ : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    prinSymbol A a m x₀ (t • ξ) = (t : ℂ) ^ m * prinSymbol A a m x₀ ξ := by
  rw [prinSymbol, prinSymbol, Finset.mul_sum]; refine Finset.sum_congr rfl fun α hα ↦ ?_
  have h : mpow α (t • ξ) = t ^ m * mpow α ξ := by
    simp only [mpow, PiLp.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, show ∑ i, α i = m from (Finset.mem_filter.1 hα).2]
  rw [h]; push_cast; ring
theorem continuous_prinSymbol (x₀ : EuclideanSpace ℝ (Fin n)) :
    Continuous (prinSymbol A a m x₀) := by unfold prinSymbol mpow; fun_prop
theorem exists_prinSymbol_lower_bound (hnm : 0 < n ∨ 1 ≤ m) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hell : ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A a m x₀ ξ ≠ 0) :
    ∃ c > 0, ∀ ξ : EuclideanSpace ℝ (Fin n), c * ‖ξ‖ ^ m ≤ ‖prinSymbol A a m x₀ ξ‖ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_pos, fun ξ ↦ ?_⟩
    rw [Subsingleton.elim ξ 0, norm_zero, zero_pow (by omega), mul_zero]; exact norm_nonneg _
  obtain ⟨u₀, hu₀S, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ (Fin n)) 1).exists_isMinOn
    ⟨ev ⟨0, hn⟩, by simp [norm_ev]⟩ (continuous_prinSymbol x₀).norm.continuousOn
  refine ⟨‖prinSymbol A a m x₀ u₀‖, norm_pos_iff.2 (hell u₀ (by rintro rfl; simp at hu₀S)), fun ξ ↦ ?_⟩
  obtain ⟨u, huS, hξu⟩ : ∃ u ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1, ξ = ‖ξ‖ • u :=
    if hξ : ξ = 0 then ⟨u₀, hu₀S, by simp [hξ]⟩ else
      ⟨‖ξ‖⁻¹ • ξ, by simp [norm_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hξ)],
        by rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hξ), one_smul]⟩
  conv_rhs => rw [hξu]
  rw [prinSymbol_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), mul_comm]
  exact mul_le_mul_of_nonneg_left (hmin huS) (by positivity)
theorem exists_schwartz_frozenOp {v : EuclideanSpace ℝ (Fin n) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∃ ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), (∀ x, ψ x = frozenOp A a m x₀ v x) ∧
      ∀ ξ, ‖(𝓕 ψ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ξ‖ ^ 2 =
        (2 * π) ^ (2 * m) * ‖prinSymbol A a m x₀ ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2 := by
  set φ := hvc.toSchwartzMap hv
  refine ⟨∑ α ∈ A with mabs α = m, a α x₀ • ∂^{mdir α} φ, fun _ ↦ by
    simp only [frozenOp, sum_apply, smul_apply, smul_eq_mul, iteratedLineDerivOp_eq_iteratedFDeriv]
    rfl, fun ξ ↦ (congrArg (fun z : ℂ ↦ ‖z‖ ^ 2)
      (show _ = (2 * π * Complex.I) ^ m * prinSymbol A a m x₀ ξ * 𝓕 v ξ from ?_)).trans ?_⟩
  · simp only [FourierTransform.fourier_sum, FourierTransform.fourier_smul, sum_apply,
      smul_apply, smul_eq_mul, fourier_mdir_apply, prinSymbol, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun α hα ↦ by
      rw [(Finset.mem_filter.1 hα).2, show (𝓕 φ : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) ξ = 𝓕 v ξ from
        congrFun (fourier_coe φ) ξ]; ring
  · simp only [norm_mul, norm_pow, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]; ring
theorem integral_norm_sq_frozenOp {v : EuclideanSpace ℝ (Fin n) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∫ x, ‖frozenOp A a m x₀ v x‖ ^ 2 =
      ∫ ξ, (2 * π) ^ (2 * m) * ‖prinSymbol A a m x₀ ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2 := by
  obtain ⟨ψ, hψ, hFψ⟩ := exists_schwartz_frozenOp (A := A) (a := a) (m := m) hv hvc x₀
  rw [show (fun x ↦ ‖frozenOp A a m x₀ v x‖ ^ 2) = fun x ↦ ‖ψ x‖ ^ 2 from
    funext fun x ↦ by rw [hψ], ← integral_norm_sq_fourier]
  exact integral_congr_ae (ae_of_all _ hFψ)
theorem integrable_frozen_fourier {v : EuclideanSpace ℝ (Fin n) → ℂ} (hv : ContDiff ℝ ∞ v)
    (hvc : HasCompactSupport v) (x₀ : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun ξ ↦ (2 * π) ^ (2 * m) * ‖prinSymbol A a m x₀ ξ‖ ^ 2 * ‖𝓕 v ξ‖ ^ 2) := by
  obtain ⟨ψ, -, hFψ⟩ := exists_schwartz_frozenOp (A := A) (a := a) (m := m) hv hvc x₀
  simpa only [hFψ] using integrable_norm_sq_schwartz (𝓕 ψ)
end Symbol

section Helpers
variable {v : EuclideanSpace ℝ (Fin n) → ℂ}
private theorem iter_eq_zero' (k : ℕ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∉ tsupport v) :
    iteratedFDeriv ℝ k v x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hx (tsupport_iteratedFDeriv_subset k h)
private theorem memLp_hsD' (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (k : ℕ) :
    MemLp (hsD k v) 2 volume :=
  memLp_two_of_continuous_hasCompactSupport
    (Real.continuous_sqrt.comp <| continuous_finsetSum _ fun _ _ ↦ ((continuous_eval_const _).comp
      (hv.continuous_iteratedFDeriv (by exact_mod_cast le_top))).norm.pow 2)
    (hvc.mono' fun _ hx ↦ not_not.1 fun h ↦ hx (by simp [hsD, pdT_apply, iter_eq_zero' k h]))
theorem exists_mdir_eq_ev (α : Fin n → ℕ) : ∃ J : Fin (mabs α) → Fin n, ∀ l, mdir α l = ev (J l) := by
  have h (l) : ∃ i, mdir α l = ev i := by
    have hmem : mdir α l ∈ mdirList α := List.get_mem _ _
    simp only [mdirList, List.mem_flatMap, List.mem_replicate] at hmem
    obtain ⟨i, -, -, hi⟩ := hmem; exact ⟨i, hi⟩
  choose J hJ using h; exact ⟨J, hJ⟩
theorem norm_pdT_le_hsD {k : ℕ} (J : Fin k → Fin n) (x : EuclideanSpace ℝ (Fin n)) :
    ‖pdT J v x‖ ≤ hsD k v x :=
  Real.le_sqrt_of_sq_le <| Finset.single_le_sum (f := fun J ↦ ‖pdT J v x‖ ^ 2) (fun _ _ ↦ sq_nonneg _) (Finset.mem_univ J)
theorem norm_pderiv_le_hsD (α : Fin n → ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖pderiv α v x‖ ≤ hsD (mabs α) v x := by
  obtain ⟨J, hJ⟩ := exists_mdir_eq_ev α
  exact (by rw [pderiv_eq_dT, pdT, dT_apply, dT_apply, funext hJ] : pderiv α v x = pdT J v x) ▸ norm_pdT_le_hsD J x
private theorem memLp_norm_sum_pderiv {S : Finset (Fin n → ℕ)}
    {c : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ} (hc : ∀ α ∈ S, Continuous (c α))
    (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    MemLp (fun x ↦ ‖∑ α ∈ S, c α x * pderiv α v x‖) 2 volume :=
  memLp_two_of_continuous_hasCompactSupport
    (continuous_finsetSum _ fun α hα ↦ (hc α hα).mul
      ((continuous_eval_const _).comp (hv.continuous_iteratedFDeriv (by exact_mod_cast le_top)))).norm
    (hvc.mono' fun _ hx ↦ not_not.1 fun h ↦ hx (by simp [pderiv, iter_eq_zero' _ h]))
end Helpers

section Estimate
variable {m : ℕ} {A : Finset (Fin n → ℕ)} {a : (Fin n → ℕ) → EuclideanSpace ℝ (Fin n) → ℂ}
theorem l2Norm_derivative_le_frozen_operator {c : ℝ} (hc : 0 < c) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hσ : ∀ ξ : EuclideanSpace ℝ (Fin n), c * ‖ξ‖ ^ m ≤ ‖prinSymbol A a m x₀ ξ‖)
    {v : EuclideanSpace ℝ (Fin n) → ℂ} (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) :
    l2n (hsD m v) ≤ c⁻¹ * l2n (fun x ↦ ‖frozenOp A a m x₀ v x‖) := by
  have hP : MemLp (fun x ↦ ‖frozenOp A a m x₀ v x‖) 2 volume :=
    memLp_norm_sum_pderiv (fun _ _ ↦ continuous_const) hv hvc
  rw [l2Norm_eq_sqrt_integral_sq (memLp_hsD' hv hvc m), l2Norm_eq_sqrt_integral_sq hP,
    integral_hsD_sq hv hvc, integral_norm_sq_frozenOp hv hvc x₀,
    ← Real.sqrt_sq (inv_nonneg.2 hc.le), ← Real.sqrt_mul (sq_nonneg _), ← integral_const_mul]
  refine Real.sqrt_le_sqrt (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ by positivity)
    ((integrable_frozen_fourier hv hvc x₀).const_mul _) (ae_of_all _ fun ξ ↦ ?_))
  have h2 := pow_le_pow_left₀ (by positivity) ((le_inv_mul_iff₀ hc).2 (hσ ξ)) 2
  exact (by rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul]; ring :
      ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ m * ‖𝓕 v ξ‖ ^ 2 = (2 * π) ^ (2 * m) * (‖ξ‖ ^ m) ^ 2 * ‖𝓕 v ξ‖ ^ 2).trans_le
    ((by gcongr : _ ≤ (2 * π) ^ (2 * m) * (c⁻¹ * ‖prinSymbol A a m x₀ ξ‖) ^ 2 * ‖𝓕 v ξ‖ ^ 2).trans_eq (by ring))
theorem elliptic_estimate (hnm : 0 < n ∨ 1 ≤ m) (hA : ∀ α ∈ A, mabs α ≤ m)
    (ha : ∀ α ∈ A, Continuous (a α)) {x₀ : EuclideanSpace ℝ (Fin n)}
    (hell : ∀ ξ : EuclideanSpace ℝ (Fin n), ξ ≠ 0 → prinSymbol A a m x₀ ξ ≠ 0) :
    ∃ R₀ > 0, ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ v : EuclideanSpace ℝ (Fin n) → ℂ, ContDiff ℝ ∞ v →
      HasCompactSupport v → tsupport v ⊆ Metric.ball x₀ R₀ →
      l2n (hsD m v) ≤ C₀ * (l2n (fun x ↦ ‖diffOp A a v x‖) + ∑ j ∈ Finset.range m, l2n (hsD j v)) := by
  obtain ⟨c, hc, hσ⟩ := exists_prinSymbol_lower_bound hnm hell
  set N : ℝ := (A.card : ℝ); set ε := c / (2 * (N + 1)); have hε : 0 < ε := by positivity
  set M := ε + ∑ β ∈ A, ‖a β x₀‖; have hM0 : 0 ≤ M := by positivity
  obtain ⟨δ, hδ, hδε⟩ := Metric.eventually_nhds_iff.1 <| (Filter.eventually_all_finset A).2
    fun α hα ↦ by simpa only [dist_eq_norm] using Metric.tendsto_nhds.1 ((ha α hα).tendsto x₀) ε hε
  refine ⟨δ, hδ, 2 * c⁻¹ * max 1 (M * N), by positivity, fun v hv hvc hsupp ↦ ?_⟩
  have hpt (x) : ‖frozenOp A a m x₀ v x‖ ≤ ‖diffOp A a v x‖ + (ε * N) * hsD m v x +
      (M * N) * ∑ j ∈ Finset.range m, hsD j v x := by
    have hS0 : 0 ≤ ∑ j ∈ Finset.range m, hsD j v x := Finset.sum_nonneg fun _ _ ↦ hsD_nonneg _ _ _
    have hm0 := hsD_nonneg m v x
    by_cases hx : x ∈ tsupport v; swap
    · simp [frozenOp, pderiv, iter_eq_zero' _ hx]; positivity
    rw [show frozenOp A a m x₀ v x = diffOp A a v x +
        ∑ α ∈ A, (if mabs α = m then a α x₀ - a α x else -a α x) * pderiv α v x by
      rw [frozenOp, Finset.sum_filter, diffOp, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun _ _ ↦ by split_ifs <;> ring]
    refine (norm_add_le _ _).trans ((add_le_add le_rfl <| (norm_sum_le _ _).trans <|
      Finset.sum_le_card_nsmul A _ (ε * hsD m v x + M * ∑ j ∈ Finset.range m, hsD j v x)
        fun α hα ↦ ?_).trans_eq (by simp [nsmul_eq_mul, N]; ring))
    have hαε := (hδε (Metric.mem_ball.1 (hsupp hx)) α hα).le
    rw [norm_mul]; split_ifs with hm
    · rw [norm_sub_rev]
      exact (mul_le_mul hαε (hm ▸ norm_pderiv_le_hsD α x) (norm_nonneg _) hε.le).trans
        (le_add_of_nonneg_right (by positivity))
    · have hαM : ‖-a α x‖ ≤ M := by
        rw [norm_neg]; linarith [norm_sub_norm_le (a α x) (a α x₀),
          Finset.single_le_sum (f := fun β ↦ ‖a β x₀‖) (fun _ _ ↦ norm_nonneg _) hα]
      exact (mul_le_mul hαM ((norm_pderiv_le_hsD α x).trans (Finset.single_le_sum
        (f := fun j ↦ hsD j v x) (fun _ _ ↦ hsD_nonneg _ _ _)
        (Finset.mem_range.2 (lt_of_le_of_ne (hA α hα) hm)))) (norm_nonneg _) hM0).trans
        (le_add_of_nonneg_left (by positivity))
  have hDv : MemLp (fun x ↦ ‖diffOp A a v x‖) 2 volume := memLp_norm_sum_pderiv ha hv hvc
  have hR1 := (memLp_hsD' hv hvc m).const_mul (ε * N)
  have hR2 := (memLp_finsetSum (Finset.range m) fun j _ ↦ memLp_hsD' hv hvc j).const_mul (M * N)
  have hF : MemLp (fun x ↦ ‖frozenOp A a m x₀ v x‖) 2 volume :=
    memLp_norm_sum_pderiv (fun _ _ ↦ continuous_const) hv hvc
  have hfrozen : l2n (fun x ↦ ‖frozenOp A a m x₀ v x‖) ≤ l2n (fun x ↦ ‖diffOp A a v x‖) +
      (ε * N) * l2n (hsD m v) + (M * N) * ∑ j ∈ Finset.range m, l2n (hsD j v) := by
    refine (l2Norm_le_of_abs_le ((hDv.add hR1).add hR2) hF.aestronglyMeasurable
      fun x ↦ (abs_of_nonneg (norm_nonneg _)).trans_le (hpt x)).trans
      ((l2Norm_add_le_alt (hDv.add hR1) hR2).trans ((add_le_add (l2Norm_add_le_alt hDv hR1) le_rfl).trans ?_))
    rw [l2Norm_const_mul, l2Norm_const_mul, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    have hY := l2Norm_finset_sum_le (Finset.range m) _ fun j _ ↦ memLp_hsD' hv hvc j; gcongr
  have hεN : c⁻¹ * (ε * N) * l2n (hsD m v) ≤ 1 / 2 * l2n (hsD m v) := by
    refine mul_le_mul_of_nonneg_right ?_ (l2Norm_nonneg_alt _)
    rw [show c⁻¹ * (ε * N) = N / (2 * (N + 1)) by simp only [ε]; field_simp,
      div_le_div_iff₀ (by positivity) two_pos]; linarith
  have hZY : l2n (fun x ↦ ‖diffOp A a v x‖) + M * N * ∑ j ∈ Finset.range m, l2n (hsD j v) ≤
      max 1 (M * N) * (l2n (fun x ↦ ‖diffOp A a v x‖) + ∑ j ∈ Finset.range m, l2n (hsD j v)) := by
    linarith [le_mul_of_one_le_left (l2Norm_nonneg_alt (fun x ↦ ‖diffOp A a v x‖)) (le_max_left 1 (M * N)),
      mul_le_mul_of_nonneg_right (le_max_right 1 (M * N))
        (Finset.sum_nonneg fun j (_ : j ∈ Finset.range m) ↦ l2Norm_nonneg_alt (hsD j v))]
  linarith [(l2Norm_derivative_le_frozen_operator hc hσ hv hvc).trans
    (mul_le_mul_of_nonneg_left hfrozen (inv_nonneg.2 hc.le)),
    mul_le_mul_of_nonneg_left hZY (show 0 ≤ 2 * c⁻¹ by positivity)]
end Estimate

section Pointwise
variable {v : EuclideanSpace ℝ (Fin n) → ℂ}
theorem integrable_fourier_weight (hv : ContDiff ℝ ∞ v) (hvc : HasCompactSupport v) (q : ℕ) :
    Integrable (fun ξ ↦ ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ q * ‖𝓕 v ξ‖ ^ 2) :=
  (integrable_finsetSum _ fun _ _ ↦ integrable_norm_sq_schwartz _).congr
    (ae_of_all _ (sum_norm_sq_fourier_pdT hv hvc q))
theorem integrable_inv_one_add_weight {σ : ℕ} (hσ : n < 2 * σ) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin n) ↦ (1 + ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ)⁻¹) := by
  have hr : (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) : ℝ) < (2 * σ : ℕ) := by
    simpa [finrank_euclideanSpace_fin] using mod_cast hσ
  refine ((integrable_one_add_norm hr).const_mul ((2 : ℝ) ^ (2 * σ))).mono'
    (Continuous.inv₀ (by fun_prop) fun _ ↦ by positivity).aestronglyMeasurable (ae_of_all _ fun ξ ↦ ?_)
  have hW : ‖ξ‖ ^ (2 * σ) ≤ ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ := by
    rw [pow_mul, mul_pow]
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (one_le_pow₀ (by linarith [Real.pi_gt_three])))
  have h1 : (1 + ‖ξ‖) ^ (2 * σ) ≤ 2 ^ (2 * σ) * (1 + ‖ξ‖ ^ (2 * σ)) := by
    rcases le_total ‖ξ‖ 1 with h | h
    · exact (pow_le_pow_left₀ (by positivity) (by linarith) _).trans
        (le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (by positivity)))
    · exact (pow_le_pow_left₀ (by positivity) (by linarith) (2 * σ)).trans
        ((mul_pow 2 ‖ξ‖ _).trans_le (by gcongr; linarith))
  rw [Real.norm_of_nonneg (by positivity), Real.rpow_neg (by positivity), Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_le_iff₀ (by positivity)]
  exact (h1.trans (by gcongr)).trans_eq (mul_comm _ _)
theorem sobolev_pointwise : ∃ σ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ w : EuclideanSpace ℝ (Fin n) → ℂ,
    ContDiff ℝ ∞ w → HasCompactSupport w → ∀ x, ‖w x‖ ≤ C * (l2n (hsD 0 w) + l2n (hsD σ w)) := by
  set σ := n / 2 + 1
  set W : EuclideanSpace ℝ (Fin n) → ℝ := fun ξ ↦ 1 + ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ
  have hWpos (ξ) : 0 < W ξ := by positivity
  have hI₁int : Integrable (fun ξ ↦ (W ξ)⁻¹) := integrable_inv_one_add_weight (by omega)
  have hI₁ : 0 ≤ ∫ ξ, (W ξ)⁻¹ := integral_nonneg fun ξ ↦ (inv_pos.2 (hWpos ξ)).le
  refine ⟨σ, Real.sqrt (∫ ξ, (W ξ)⁻¹), Real.sqrt_nonneg _, fun w hw hwc x ↦ ?_⟩
  set φ := hwc.toSchwartzMap hw
  have hFint : Integrable (𝓕 w) := (𝓕 φ).integrable.congr (ae_of_all _ fun ξ ↦ congrFun (fourier_coe φ) ξ)
  have hx1 : ‖w x‖ ≤ ∫ ξ, ‖𝓕 w ξ‖ := by
    conv_lhs => rw [← hw.continuous.fourierInv_fourier_eq φ.integrable hFint, Real.fourierInv_eq]
    exact (norm_integral_le_integral_norm _).trans_eq
      (integral_congr_ae (ae_of_all _ fun _ ↦ by simp [Circle.norm_smul]))
  have hWint : Integrable (fun ξ ↦ W ξ * ‖𝓕 w ξ‖ ^ 2) :=
    ((integrable_fourier_weight hw hwc 0).add (integrable_fourier_weight hw hwc σ)).congr
      (ae_of_all _ fun _ ↦ by simp only [W, Pi.add_apply, pow_zero]; ring)
  set S := l2n (hsD 0 w) + l2n (hsD σ w)
  have hS0 : 0 ≤ S := add_nonneg (l2Norm_nonneg_alt _) (l2Norm_nonneg_alt _)
  have hWsq : ∫ ξ, W ξ * ‖𝓕 w ξ‖ ^ 2 ≤ S ^ 2 := by
    rw [← integral_congr_ae (ae_of_all _ fun ξ ↦ (by simp only [W, pow_zero]; ring :
      ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ 0 * ‖𝓕 w ξ‖ ^ 2 + ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ σ * ‖𝓕 w ξ‖ ^ 2 =
        W ξ * ‖𝓕 w ξ‖ ^ 2)), integral_add (integrable_fourier_weight hw hwc 0)
      (integrable_fourier_weight hw hwc σ), ← integral_hsD_sq hw hwc, ← integral_hsD_sq hw hwc,
      ← Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _), ← l2Norm_eq_sqrt_integral_sq (memLp_hsD' hw hwc 0),
      ← Real.sq_sqrt (integral_nonneg fun _ ↦ sq_nonneg _), ← l2Norm_eq_sqrt_integral_sq (memLp_hsD' hw hwc σ)]
    linarith [add_sq (l2n (hsD 0 w)) (l2n (hsD σ w)),
      mul_nonneg (l2Norm_nonneg_alt (hsD 0 w)) (l2Norm_nonneg_alt (hsD σ w))]
  have hd := discrim_le_zero (a := ∫ ξ, (W ξ)⁻¹) (b := -(2 * ∫ ξ, ‖𝓕 w ξ‖)) (c := S ^ 2) fun t ↦ by
    have hle := integral_mono (hFint.norm.const_mul (2 * t)) ((hI₁int.const_mul (t * t)).add hWint) fun ξ ↦ by
      have hW := hWpos ξ; have : 0 ≤ (t - W ξ * ‖𝓕 w ξ‖) ^ 2 / W ξ := by positivity
      have e : (t * t) * (W ξ)⁻¹ + W ξ * ‖𝓕 w ξ‖ ^ 2 - 2 * t * ‖𝓕 w ξ‖ =
          (t - W ξ * ‖𝓕 w ξ‖) ^ 2 / W ξ := by field_simp; ring
      show 2 * t * ‖𝓕 w ξ‖ ≤ _ + _; linarith
    have heq := integral_add (hI₁int.const_mul (t * t)) hWint
    simp only [Pi.add_apply] at hle heq; rw [integral_const_mul] at hle heq; linarith
  exact hx1.trans (abs_le_of_sq_le_sq'
    (by rw [discrim] at hd; rw [mul_pow, Real.sq_sqrt hI₁]; linarith) (by positivity)).2
end Pointwise
end
end GroundTheory.Automorphic.Sobolev
