module

public import Development.WeilBound.CoreStatements.OrbitDecayEstimates.CurveDerivativeDecay.HIntegrability

@[expose] public section

noncomputable section

open Matrix Finset MeasureTheory Formalism.REAL Formalism.MainNotions.S Filter Topology GlobalTheory.CompanionTheory.PairingAnalysis
open scoped InnerProductSpace ENNReal

namespace CompanionTheory.Lime.T3

open ReciprocityTheory.ChartRestriction.DS (smD smE actM isDerivedOn_smE isInfUnitary_of_isDerivedOn)

theorem volume_ratio_bound : VolR := fun _ ε μ _ hm _ _ hδ hδ2 hR => vol_ratio hm ε μ hδ hδ2 hR

theorem decay_estimate : Decay := by
  intro m N ε lam A _ _ _ π hm hmN hl hDS hg v hv hv1 g₀ Y hY g
  have hN : 1 ≤ 12 * N ^ 2 := by have : 1 ≤ N := hm.trans hmN; nlinarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := dec_conj hm hDS.2.2.1 (by positivity) (dec_low hm hmN hl hDS hg hv hv1 hN le_rfl) g₀ g
  have h2 := one_le_nG hm g
  have h3 : 0 ≤ hs (uMat g₀) := by rw [← nG_sq]; positivity
  have e1 : (Real.exp 1 * Real.sqrt m) ^ (12 * N ^ 2) =
      Real.exp (6 * (N : ℝ) ^ 2 * Real.log m + 12 * (N : ℝ) ^ 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hm0, ← Real.exp_add, ← Real.exp_nat_mul]
    congr 1; push_cast; ring
  have e2 : (nG g)⁻¹ ^ (12 * N ^ 2) = hs (um g) ^ (-(6 * (N : ℝ) ^ 2)) := by
    change _ = hs (uMat g) ^ _
    rw [← nG_sq, ← Real.rpow_natCast (nG g) 2, ← Real.rpow_mul (by linarith), inv_pow, ← Real.rpow_natCast,
      ← Real.rpow_neg (by linarith)]
    congr 1; push_cast; ring
  rw [e1, e2] at h1
  have h4 : 0 ≤ hs (um g) ^ (-(6 * (N : ℝ) ^ 2)) := by rw [← e2]; positivity
  exact h1.trans (by gcongr)

theorem integral_ratio_bound : IntR := by
  intro m ε μ hμ hm φ C a hφ ha hd
  have hC : 0 ≤ C := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans (hd 1))
    (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (one_le_hsG hm 1)) _)
  have hd' : ∀ g, ‖φ g‖ ≤ C * (nG g)⁻¹ ^ (2 * m ^ 2 + 1) := fun g =>
    (hd g).trans (mul_le_mul_of_nonneg_left (rpow_hs hm g _ (by push_cast; linarith)) hC)
  have hI := integrable_of_dec hm μ hφ hC le_rfl hd'
  refine ⟨hI, ?_⟩
  rw [integral_norm_eq_lintegral_eNorm hI.1]
  refine (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (nearSet_lt_top ε μ).ne)
    (lint_le hm μ hC one_pos le_rfl hd')).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), div_one]; rfl

/-- Gap-free Schur-orthogonality formal-degree neighborhood bound: for any unitary representation `π`
with formal degree `d`, any smooth unit vector `x` with 1st-order Lipschitz constant `C`, and any
radius `δ ∈ [0, 1/2]` satisfying `7 * δ * C ≤ 1/2`, we have `d * μ (nearSet ε δ) ≤ 4`. -/
theorem formalDeg_mul_nearSet_le {m : ℕ} {ε : Fin m → Bool}
    {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)} {μ : Measure (UJ ε)} {d : ℝ}
    (hπ : IsURepOn (UJset ε) π) (hd : IsFdeg μ π d)
    (x : smD ε π) (hx1 : ‖(x : A)‖ = 1) {C δ : ℝ}
    (hC : ∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ C)
    (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 2) (hδC : 7 * δ * C ≤ 1 / 2) :
    ENNReal.ofReal d * μ (nearSet ε δ) ≤ 4 := by
  have hnear : ∀ g ∈ nearSet ε δ, 1 / 4 ≤ ‖⟪(x : A), π (uMat g) x⟫_ℂ‖ ^ 2 := fun g hgn => by
    have h3 : ‖⟪(x : A), π (uMat g) x - x⟫_ℂ‖ ≤ 1 / 2 :=
      (norm_inner_le_norm _ _).trans <| by rw [hx1, one_mul]; exact (disp_le hπ x hC hδ0 hδ hgn).trans hδC
    rw [inner_sub_right, inner_self_eq_norm_sq_to_K, hx1] at h3
    have h4 := norm_sub_norm_le (1 : ℂ) (1 - ⟪(x : A), π (uMat g) x⟫_ℂ)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at h4
    have h5 : ‖⟪(x : A), π (uMat g) x⟫_ℂ - 1‖ ≤ 1 / 2 := by simpa using h3
    nlinarith [norm_nonneg ⟪(x : A), π (uMat g) x⟫_ℂ]
  obtain ⟨hI, hE⟩ := hd.2 x x x x
  have e1 : ∀ g : UJ ε, coefOn π x x g * star (coefOn π x x g) = ((‖⟪(x : A), π (uMat g) x⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := fun g => by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; rfl
  simp only [e1] at hI hE
  have hI' : Integrable (fun g : UJ ε => ‖⟪(x : A), π (uMat g) x⟫_ℂ‖ ^ 2) μ :=
    hI.re.congr (Filter.Eventually.of_forall fun _ => Complex.ofReal_re _)
  rw [integral_complex_ofReal, inner_self_eq_norm_sq_to_K, hx1] at hE
  have hE' : ∫ g : UJ ε, ‖⟪(x : A), π (uMat g) x⟫_ℂ‖ ^ 2 ∂μ = d⁻¹ := by
    exact_mod_cast (show ((∫ g : UJ ε, ‖⟪(x : A), π (uMat g) x⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) = ((d⁻¹ : ℝ) : ℂ) by rw [hE]; simp)
  have hmeas : MeasurableSet (nearSet ε δ) :=
    (isClosed_le (continuous_hs_real_place_taylor.comp ((continuous_coeMatrix ε).sub continuous_const)) continuous_const).measurableSet
  have h6 : ENNReal.ofReal (1 / 4) * μ (nearSet ε δ) ≤ ENNReal.ofReal d⁻¹ := by
    rw [← hE', ofReal_integral_eq_lintegral_ofReal hI' (Filter.Eventually.of_forall fun _ => by positivity),
      ← lintegral_indicator_const hmeas]
    refine lintegral_mono fun g => ?_
    by_cases hg' : g ∈ nearSet ε δ
    · rw [Set.indicator_of_mem hg']; exact ENNReal.ofReal_le_ofReal (hnear g hg')
    · rw [Set.indicator_of_notMem hg']; exact bot_le
  have hd0 := hd.1
  calc ENNReal.ofReal d * μ (nearSet ε δ)
      = ENNReal.ofReal (4 * d) * (ENNReal.ofReal (1 / 4) * μ (nearSet ε δ)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]; congr 2; ring
    _ ≤ ENNReal.ofReal (4 * d) * ENNReal.ofReal d⁻¹ := mul_le_mul_right h6 _
    _ = 4 := by rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, mul_inv_cancel₀ hd0.ne', mul_one]; simp

/-- Sharp linear-radius formal-degree neighborhood bound from the Cartan-splitting Casimir energy
estimate (`lowestKType_energy_le`), bypassing arbitrary-length Lie-word bounds. -/
theorem derivative_upper_bound_linear {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {B : ℝ}
    {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    {π : Matrix (Fin m) (Fin m) ℂ → (A →L[ℂ] A)} {μ : Measure (UJ ε)} {d : ℝ}
    (hm : 1 ≤ m) (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hDS : IsDS ε lam π)
    (hB : ∀ a, |lam a| ≤ B) (hB0 : 0 ≤ B)
    (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * (m : ℝ) ^ 3))
    (hd : IsFdeg μ π d) :
    ENNReal.ofReal d * μ (nearSet ε (20 * Real.sqrt m * (B + m))⁻¹) ≤ 4 := by
  have hπ : IsURepOn (UJset ε) π := hDS.2.2.1
  have hD := isDerivedOn_smE hπ
  obtain ⟨V, hVirr, _, hmapS, hcV⟩ := exists_lowestKType_data hm hl hDS hg
  obtain ⟨S, hS⟩ := hDS.2.2.2.2.2.1
  obtain ⟨v0, hv0, hne, -⟩ := hS.2.2.2.1
  have hvmem : v0 ∈ Submodule.map (smD ε π).subtype V :=
    hmapS.symm ▸ le_sSup (s := {S | IsKTypeOf ε π (Formalism.QuantumDeterminants.lowK ε lam) S}) hS hv0
  obtain ⟨x0, hx0V, hx0e⟩ := hvmem
  have hn0 : 0 < ‖(x0 : A)‖ := norm_pos_iff.2 fun h => hne (hx0e ▸ h)
  let x : smD ε π := ((‖(x0 : A)‖⁻¹ : ℝ) : ℂ) • x0
  have hxV : x ∈ V := Submodule.smul_mem V _ hx0V
  have hx1 : ‖(x : A)‖ = 1 := by
    change ‖((‖(x0 : A)‖⁻¹ : ℝ) : ℂ) • (x0 : A)‖ = 1
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hn0.ne']
  have hC : ∀ X, hs X ≤ 1 → ‖actM (smE ε π) X x‖ ≤ Real.sqrt 2 * Real.sqrt m * (B + m) := fun X hX => by
    have hE := lowestKType_energy_le hD.glRep (isInfUnitary_of_isDerivedOn hπ hD) hVirr hcV hB hB0 hxV
    refine norm_actM_le X hX x (by positivity) (hE.trans_eq ?_)
    have hxn : ‖x‖ = 1 := hx1
    rw [hxn, one_pow, mul_one, mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (Nat.cast_nonneg m)]
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hsm : 1 ≤ Real.sqrt m := Real.one_le_sqrt.2 hm1
  have hden : 0 < 20 * Real.sqrt m * (B + m) := by positivity
  have hδ : (20 * Real.sqrt m * (B + m))⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ hden (by norm_num)]; nlinarith
  have hsq2 : 7 * Real.sqrt 2 ≤ 10 := by
    have h1 : Real.sqrt 2 ≤ 10 / 7 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
    linarith
  have hδC : 7 * (20 * Real.sqrt m * (B + m))⁻¹ * (Real.sqrt 2 * Real.sqrt m * (B + m)) ≤ 1 / 2 := by
    have heq : 7 * (20 * Real.sqrt m * (B + m))⁻¹ * (Real.sqrt 2 * Real.sqrt m * (B + m)) = 7 * Real.sqrt 2 / 20 := by
      field_simp [hden.ne']
    rw [heq]; linarith
  exact formalDeg_mul_nearSet_le hπ hd x hx1 hC (by positivity) hδ hδC

theorem derivative_upper_bound : DUp := by
  intro m ε lam B A _ _ _ π μ d _ hm hl hDS hB hg hd
  have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hB0 : 0 ≤ B := by linarith [le_four_mul hm hl hB]
  have hsq : Real.sqrt m ≤ m := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hrad : ((100 * (m : ℝ) * (B + 1)) ^ 2)⁻¹ ≤ (20 * Real.sqrt m * (B + m))⁻¹ := by
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    have h1 : 20 * Real.sqrt m * (B + m) ≤ 20 * m * (B + m) := by gcongr
    have h2 : B + (m : ℝ) ≤ m * (B + 1) := by nlinarith
    have h3 : (m : ℝ) * (B + m) ≤ m ^ 2 * (B + 1) ^ 2 := by
      calc (m : ℝ) * (B + m) ≤ m * (m * (B + 1)) := by gcongr
        _ = m ^ 2 * (B + 1) := by ring
        _ ≤ m ^ 2 * (B + 1) ^ 2 := by gcongr; nlinarith
    nlinarith
  exact (mul_le_mul_right (measure_mono fun g hg => le_trans hg (pow_le_pow_left₀ (by positivity) hrad 2)) _).trans
    (derivative_upper_bound_linear (by omega) hl hDS hB hB0 hg hd)

end CompanionTheory.Lime.T3
