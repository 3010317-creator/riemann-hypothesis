module

public import Formalism.SharpRestriction.ElevenLe

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.MainNotions.S

variable {D : D7} (L : SizeData₂ D)

theorem sqrt_xd : Real.sqrt (L.sc.x * L.sc.delta1) = L.sc.x ^ ((1 - L.sc.eps / 8) / 2) := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have e : L.sc.x * L.sc.delta1 = L.sc.x ^ (1 - L.sc.eps / 8) := by
    unfold Scale.delta1
    rw [sub_eq_add_neg, Real.rpow_add hx, Real.rpow_one]
  rw [e, Real.sqrt_eq_rpow, ← Real.rpow_mul hx.le]
  congr 1; ring

end Formalism.MainNotions.S

namespace Formalism.BasicNotions

theorem m_pow_four_le_n {D : D7} (L : SizeData₂ D) (hN : SizeN L) (hM : SizeM L) : D.R.m ^ 4 ≤ D.R.n := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hm := hM.2
  rw [S.sqrt_xd L, ← Real.rpow_add hx] at hm
  have bound : (D.R.m : ℝ) ^ 4 ≤ (D.R.n : ℝ) := calc
    (D.R.m : ℝ) ^ 4 ≤ (L.sc.x ^ (szTh L + (1 - L.sc.eps / 8) / 2)) ^ 4 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hm 4
    _ = L.sc.x ^ ((szTh L + (1 - L.sc.eps / 8) / 2) * ((4 : ℕ) : ℝ)) := by
      rw [Real.rpow_mul hx.le, Real.rpow_natCast]
    _ ≤ L.sc.x ^ (2 + 8 * L.sc.eps - szTh L) := by
      apply Real.rpow_le_rpow_of_exponent_le L.sc.one_lt_alt.le
      unfold szTh
      have := L.sc.eps_pos
      push_cast
      linarith
    _ ≤ _ := hN.1
  exact_mod_cast bound

theorem m_pow_four_le_f {D : D7} (L : SizeData₂ D) (hN : SizeN L) (hM : SizeM L) : D.R.m ^ 4 ≤ D.R.f := by
  have := m_pow_four_le_n L hN hM
  show D.R.m ^ 4 ≤ 2 * D.R.n
  omega

end Formalism.BasicNotions
