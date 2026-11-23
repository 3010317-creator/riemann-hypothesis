module

public import Mathlib

@[expose] public section

namespace GlobalTheory

theorem _root_.GlobalTheory.bar_gap_param_ineq : ∀ (T D c0 h0 N f m k PP : ℝ), 4 * D + 4 ≤ T → 4 * T ^ 2 ≤ h0 → PP * T * N * f ^ 2 * m ^ 2 * k * D ≤ h0 →
    4 * (c0 + 2 * N + T + D + 1) ≤ h0 → 0 ≤ c0 → c0 ≤ 22 * f ^ 2 * N ^ 4 → D = f * (N * (N - 1) / 2) → 40 ≤ PP →
    N + 4 ≤ 2 * k → 2 ≤ m → 6 ≤ N → 8 ≤ f →
    (T + c0) * (T + D + 1) + c0 + 2 * N - 2 ≤ h0 ∧ 2 * N + D ≤ T := by
  intro T D c0 h0 N f m k PP hTD hT2 hP h4 hc0 hc0u hD hPP hk hm hN hf
  have hN0 : 0 ≤ N := by linarith only [hN]
  have hN1 : 0 ≤ N - 1 := by linarith only [hN]
  have hNN : 5 * N ≤ N * (N - 1) := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (show 5 ≤ N - 1 by linarith only [hN]) hN0
  have hD1 : 4 * (N * (N - 1)) ≤ D := by
    rw [hD]
    have hhalf : 0 ≤ N * (N - 1) / 2 := by positivity
    linarith only [mul_le_mul_of_nonneg_right hf hhalf]
  have hD0 : 0 ≤ D := by linarith only [hNN, hD1, hN0]
  have hgap : 2 * N + D ≤ T := by linarith only [hTD, hNN, hD1, hN0]
  refine ⟨?_, hgap⟩
  have hT0 : 0 ≤ T := by linarith only [hTD, hD0]
  have hm2 : 4 ≤ m ^ 2 := calc
    (4 : ℝ) = 2 ^ 2 := by norm_num
    _ ≤ m ^ 2 := pow_le_pow_left₀ (by norm_num) hm 2
  have hk0 : 0 ≤ k := by linarith only [hk, hN0]
  have hA : 160 ≤ PP * m ^ 2 := by
    calc
      (160 : ℝ) = 40 * 4 := by norm_num
      _ ≤ PP * m ^ 2 := mul_le_mul hPP hm2 (by norm_num) (by linarith only [hPP])
  have hB : 80 * N ≤ PP * m ^ 2 * k := by
    linarith only [hk, mul_le_mul_of_nonneg_right hA hk0]
  have hC : 320 * (N ^ 2 * (N - 1)) ≤ PP * m ^ 2 * k * D := by
    calc
      320 * (N ^ 2 * (N - 1)) = (80 * N) * (4 * (N * (N - 1))) := by ring
      _ ≤ PP * m ^ 2 * k * D :=
        mul_le_mul hB hD1 (by positivity) (by linarith only [hB, hN0])
  have hE : 264 * N ^ 3 ≤ PP * m ^ 2 * k * D := by
    have hfactor : 0 ≤ 56 * N - 320 := by linarith only [hN]
    linarith only [hC, mul_nonneg (sq_nonneg N) hfactor]
  have hX : 0 ≤ T * N * f ^ 2 := by positivity
  have hF : 264 * N ^ 3 * (T * N * f ^ 2) ≤ PP * T * N * f ^ 2 * m ^ 2 * k * D := by
    have := mul_le_mul_of_nonneg_right hE hX
    calc 264 * N ^ 3 * (T * N * f ^ 2) ≤ PP * m ^ 2 * k * D * (T * N * f ^ 2) := this
      _ = PP * T * N * f ^ 2 * m ^ 2 * k * D := by ring
  have hcT : 12 * (c0 * T) ≤ h0 := by
    have h1 : c0 * T ≤ 22 * f ^ 2 * N ^ 4 * T := mul_le_mul_of_nonneg_right hc0u hT0
    linarith only [h1, hF, hP]
  have hTD' : 4 * (D + 1) ≤ T := by linarith only [hTD]
  have hcD : c0 * (4 * (D + 1)) ≤ c0 * T := mul_le_mul_of_nonneg_left hTD' hc0
  have hTT : T * (4 * (D + 1)) ≤ T * T := mul_le_mul_of_nonneg_left hTD' hT0
  have hexp : (T + c0) * (T + D + 1) + c0 + 2 * N - 2
      = T ^ 2 + T * (D + 1) + c0 * T + c0 * (D + 1) + c0 + 2 * N - 2 := by ring
  rw [hexp]
  linarith only [hT2, h4, hcT, hcD, hTT, hT0, hD0, sq_nonneg T]

end GlobalTheory
