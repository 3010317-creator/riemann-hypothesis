module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsSmoothPts
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ArithmeticHilbertSamuelLowerBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace NormCountBounded

section Counts

variable {Ω : Type} [Field Ω]

theorem norm_count_bounded {h : ℕ → ℝ} {C : ℝ} (D : ℕ) (hC : ∀ τ, h τ ≤ C * ((τ : ℝ) + 1) ^ (D + 1)) :
    ∃ B, ∀ᶠ τ in atTop, h τ / ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤ B := by
  refine ⟨|C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ), eventually_atTop.2 ⟨1, fun τ hτ => ?_⟩⟩
  have hτ' : (1 : ℝ) ≤ τ := by exact_mod_cast hτ
  have hfac : (0 : ℝ) < (D + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hden : 0 < (τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
  rw [div_le_iff₀ hden]
  have h1 : ((τ : ℝ) + 1) ^ (D + 1) ≤ 2 ^ (D + 1) * (τ : ℝ) ^ (D + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc h τ ≤ C * ((τ : ℝ) + 1) ^ (D + 1) := hC τ
    _ ≤ |C| * ((τ : ℝ) + 1) ^ (D + 1) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 ^ (D + 1) * (τ : ℝ) ^ (D + 1)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = |C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) * ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
      field_simp

end Counts

end NormCountBounded


end

end GroundTheory.Heights₂.Heights.HilbertSamuel
