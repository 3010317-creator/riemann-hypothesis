module

public import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Statements

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBound

open Real

theorem CuspWeightBound.proof : CuspWeightBound.Statement := by
  intro f j' ρ rd lam NI covol h
  have hf : (1 : ℝ) ≤ f := by exact_mod_cast h.one_le_f
  have hj : (1 : ℝ) ≤ j' := by exact_mod_cast h.one_le_j'
  have hρ : (1 : ℝ) ≤ ρ := by exact_mod_cast h.one_le_ρ
  have hρj : (ρ : ℝ) ≤ j' := by exact_mod_cast h.ρ_le_j'
  have hrd := h.one_le_rd
  have hlam := h.lam_pos
  have hNI := h.NI_pos
  have h2fρ : (0 : ℝ) < 2 * f * ρ := by positivity
  have hsq := Real.sqrt_pos.mpr h2fρ

  have hmk : (lam / √(2 * f * ρ : ℝ)) ^ (2 * f * ρ) ≤ NI * rd ^ (f * ρ) :=
    h.covol_eq ▸ h.minkowski
  have hrdp : (0 : ℝ) < rd ^ (f * ρ) := by positivity
  have hlog := Real.log_le_log (by positivity) hmk
  rw [Real.log_pow, Real.log_mul hNI.ne' hrdp.ne', Real.log_pow,
    Real.log_div hlam.ne' hsq.ne', Real.log_sqrt h2fρ.le] at hlog
  push_cast at hlog

  have hρbound : -log NI ≤ f * ρ * (2 * log (1 / lam) + log (2 * f * ρ * rd)) := by
    have hrd0 : rd ≠ 0 := by positivity
    rw [one_div, Real.log_inv, Real.log_mul h2fρ.ne' hrd0]
    nlinarith

  have hB : 0 ≤ 2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd) := by
    have h2 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hf hj) hrd
    have := Real.log_nonneg (show (1 : ℝ) ≤ 2 * f * j' * rd by linarith)
    linarith [le_max_left 0 (log (1 / lam))]
  have hin : 2 * log (1 / lam) + log (2 * f * ρ * rd) ≤
      2 * max 0 (log (1 / lam)) + log (2 * f * j' * rd) := by
    linarith [le_max_right 0 (log (1 / lam)),
      Real.log_le_log (by positivity) (by gcongr : 2 * f * ρ * rd ≤ 2 * f * j' * rd)]
  refine hρbound.trans ((mul_le_mul_of_nonneg_left hin (by positivity)).trans ?_)
  gcongr

end GroundTheory.Heights₂.Heights.LowerBound
