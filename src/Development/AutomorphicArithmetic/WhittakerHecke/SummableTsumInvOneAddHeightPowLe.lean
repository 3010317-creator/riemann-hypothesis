module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Normed.Ring.InfiniteSum

@[expose] public section

theorem UpperTheory.summable_tsum_inv_one_add_height_pow_le :
    ∀ (n d : ℕ) (κ Bu : ℝ), 0 < d → 0 < κ → κ ≤ 1 → 1 ≤ Bu → ∃ B : ℝ, 0 ≤ B ∧
        ∀ (R : Set {r : Fin 2 → ℚ // r ≠ 0}) (β α T t : ℝ), 0 ≤ t → Bu⁻¹ ≤ α → α ≤ T → 1 ≤ T →
          (∀ ξ ∈ R, ∃ l : ℤ, (d : ℚ) * ξ.1 0 = l) →
          (∀ ξ ∈ R, ξ.1 0 = 0 → ∃ l : ℤ, (d : ℚ) * ξ.1 1 = l) →
          (∀ ξ ∈ R, ∀ ξ' ∈ R, ξ.1 0 = ξ'.1 0 → ∃ l : ℤ, (d : ℚ) * (ξ.1 1 - ξ'.1 1) = l) →
          Summable (R.indicator fun ξ : {r : Fin 2 → ℚ // r ≠ 0} =>
            ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹) ∧
          ∑' ξ : {r : Fin 2 → ℚ // r ≠ 0}, R.indicator (fun ξ : {r : Fin 2 → ℚ // r ≠ 0} =>
            ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹) ξ
            ≤ B * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2) := by
  intro n d κ Bu hd hκ hκ1 hBu; classical
  have h1m {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) : 1 ≤ x * y := by linarith [mul_le_mul hx hy zero_le_one (zero_le_one.trans hx)]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by positivity
  have hBu0 : 0 < Bu := by linarith
  have hw0 := (summable_nat_add_iff 1).mpr ((Real.summable_one_div_nat_pow (p := 2)).mpr one_lt_two)
  have hw1 : Summable (fun l : ℤ => ((1 + |(l : ℝ)|) ^ 2)⁻¹) :=
    .of_nat_of_neg (by simpa [add_comm] using hw0) (by simpa [add_comm] using hw0)
  let w : ℤ × ℤ → ℝ := fun p => ((1 + |(p.1 : ℝ)|) ^ 2)⁻¹ * ((1 + |(p.2 : ℝ)|) ^ 2)⁻¹
  have hw : Summable w := hw1.mul_of_nonneg hw1 (fun _ => by positivity) (fun _ => by positivity)
  let C : ℝ := 16 * ((d : ℝ) * Bu / κ) ^ n * (((d : ℝ) / κ) * (Bu * (d : ℝ) / κ)) ^ 2
  refine ⟨C * ∑' p, w p, mul_nonneg (by dsimp [C]; positivity) (tsum_nonneg fun _ => by dsimp [w]; positivity), ?_⟩
  intro R β α T t ht hα hαT hT h1 h2 h3
  have hT0 : 0 < T := by linarith
  have hα0 : 0 < α := (inv_pos.mpr hBu0).trans_le hα
  let τ : {r : Fin 2 → ℚ // r ≠ 0} → ℤ × ℤ := fun ξ => (round ((d : ℝ) * ξ.1 0), round ((d : ℝ) * (ξ.1 0 * β + ξ.1 1)))
  have hinj : Function.Injective (fun x : R => τ x.1) := by
    rintro ⟨ξ, hξ⟩ ⟨ξ', hξ'⟩ he; obtain ⟨l, hl⟩ := h1 ξ hξ; obtain ⟨l', hl'⟩ := h1 ξ' hξ'
    have he1 : l = l' := by
      simpa [τ, show (d : ℝ) * ξ.1 0 = l by exact_mod_cast hl,
        show (d : ℝ) * ξ'.1 0 = l' by exact_mod_cast hl'] using congrArg Prod.fst he
    have h0 : ξ.1 0 = ξ'.1 0 := mul_left_cancel₀ (Nat.cast_ne_zero.mpr hd.ne') (by rw [hl, hl', he1])
    obtain ⟨j, hj⟩ := h3 ξ hξ ξ' hξ' h0; have he2 := congrArg Prod.snd he
    have e : (d : ℝ) * (ξ.1 0 * β + ξ.1 1) = (d : ℝ) * (ξ'.1 0 * β + ξ'.1 1) + j := by
      rw [show (j : ℝ) = d * (ξ.1 1 - ξ'.1 1) by exact_mod_cast hj.symm, h0]; ring
    simp only [τ, e, round_add_intCast] at he2
    have h1' : ξ.1 1 = ξ'.1 1 :=
      sub_eq_zero.mp (mul_left_cancel₀ (Nat.cast_ne_zero.mpr hd.ne') (by simpa [show j = 0 by linarith] using hj))
    exact Subtype.ext (Subtype.ext (funext fun i => by fin_cases i <;> assumption))
  let K := C * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2)
  let f : {r : Fin 2 → ℚ // r ≠ 0} → ℝ := fun ξ =>
    ((1 + κ * Real.exp t * (|((ξ.1 0 : ℚ) : ℝ)| * α + |((ξ.1 0 : ℚ) : ℝ) * β + ((ξ.1 1 : ℚ) : ℝ)| / α)) ^ (n + 4))⁻¹
  have hb : ∀ x : R, f x.1 ≤ K * w (τ x.1) := by
    rintro ⟨ξ, hξ⟩; set y₀ : ℝ := (ξ.1 0 : ℝ); set y₁ : ℝ := (ξ.1 0 : ℝ) * β + (ξ.1 1 : ℝ)
    have h1d {q : ℚ} {l : ℤ} (hl : (d : ℚ) * q = l) (hq : q ≠ 0) : 1 ≤ (d : ℝ) * |(q : ℝ)| := by
      have hl0 : l ≠ 0 := by rintro rfl; exact mul_ne_zero (Nat.cast_ne_zero.mpr hd.ne') hq (by simpa using hl)
      simpa [show (l : ℝ) = d * q by exact_mod_cast hl.symm, abs_mul, abs_of_pos hd0] using
        (Int.cast_le (R := ℝ)).mpr (Int.one_le_abs hl0)
    have hab : 1 ≤ (d : ℝ) * |y₀| ∨ 1 ≤ (d : ℝ) * |y₁| := by
      by_cases hz : ξ.1 0 = 0
      · obtain ⟨l, hl⟩ := h2 ξ hξ hz
        exact Or.inr (by simpa [y₁, hz] using h1d hl fun h => ξ.2 (funext fun i => by fin_cases i <;> assumption))
      · obtain ⟨l, hl⟩ := h1 ξ hξ; exact Or.inl (h1d hl hz)
    set ν := |y₀| * α + |y₁| / α; set E := Real.exp t; set X := 1 + κ * E * ν
    have hBuα : 1 ≤ Bu * α := (mul_inv_cancel₀ hBu0.ne').symm.trans_le (by gcongr)
    have hν1 : 1 / (d * Bu * T) ≤ ν := by
      rw [div_le_iff₀ (by positivity), show ν * (d * Bu * T) =
        (d * |y₀|) * (Bu * α) * T + (d * |y₁|) * Bu * (T / α) by dsimp [ν]; field_simp]
      rcases hab with ha1 | hb1
      · linarith [h1m (h1m ha1 hBuα) hT, show 0 ≤ (d * |y₁|) * Bu * (T / α) by positivity]
      · linarith [h1m (h1m hb1 hBu) ((one_le_div hα0).mpr hαT), show 0 ≤ (d * |y₀|) * (Bu * α) * T by positivity]
    have hX1 : κ * E / (d * Bu * T) ≤ X := by linarith [show κ * E / (d * Bu * T) ≤ κ * E * ν by rw [div_eq_mul_one_div]; gcongr]
    have hX0 : 1 + κ * ν ≤ X := by dsimp [X]; rw [mul_assoc]; gcongr; exact le_mul_of_one_le_left (by dsimp [ν]; positivity) (Real.one_le_exp ht)
    have hbd {u : ℝ} (y : ℝ) (hu : 1 ≤ u) (hc : |y| / u ≤ ν) : κ / (2 * u * d) * (1 + |((round ((d : ℝ) * y) : ℤ) : ℝ)|) ≤ X := by
      have hu0 : 0 < u := by linarith
      have hZ : 1 + |((round ((d : ℝ) * y) : ℤ) : ℝ)| ≤ 2 * (1 + d * |y|) := by
        have := abs_sub_abs_le_abs_sub ((round ((d : ℝ) * y) : ℤ) : ℝ) ((d : ℝ) * y)
        rw [abs_sub_comm, abs_mul, abs_of_pos hd0] at this; linarith [abs_sub_round ((d : ℝ) * y), mul_nonneg hd0.le (abs_nonneg y)]
      have : κ / (u * d) ≤ 1 := div_le_one_of_le₀ (hκ1.trans (h1m hu hd1)) (by positivity)
      calc κ / (2 * u * d) * _ ≤ κ / (2 * u * d) * (2 * (1 + d * |y|)) := by gcongr
        _ = κ / (u * d) + κ * (|y| / u) := by field_simp
        _ ≤ 1 + κ * ν := by gcongr
        _ ≤ X := hX0
    have hXL := hbd y₀ hBu (le_add_of_le_of_nonneg (by rw [div_eq_mul_inv]; gcongr) (by positivity))
    have hXM := hbd y₁ hT (le_add_of_nonneg_of_le (by positivity) (by gcongr))
    have hmain : (κ * E / (d * Bu * T)) ^ n * (κ / (2 * Bu * d) * (1 + |((τ ξ).1 : ℝ)|)) ^ 2 *
        (κ / (2 * T * d) * (1 + |((τ ξ).2 : ℝ)|)) ^ 2 ≤ X ^ (n + 4) := by
      rw [show n + 4 = n + 2 + 2 by omega, pow_add, pow_add]; gcongr
    refine (inv_anti₀ (by positivity) hmain).trans (le_of_eq ?_)
    dsimp [K, C, w]; rw [Real.exp_neg, Real.exp_natCast_mul, pow_add T n 2]; simp only [E, div_pow, mul_pow]; field_simp; ring
  have hs := hw.comp_injective hinj
  have hs2 := Summable.of_nonneg_of_le (fun _ => by dsimp [f]; positivity) hb (hs.mul_left K)
  refine ⟨summable_subtype_iff_indicator.mp hs2, (tsum_subtype R f).symm.trans_le ?_⟩
  calc ∑' x : R, f x.1 ≤ ∑' x : R, K * w (τ x.1) := hs2.tsum_le_tsum hb (hs.mul_left K)
    _ = K * ∑' x : R, w (τ x.1) := tsum_mul_left
    _ ≤ K * ∑' p, w p := mul_le_mul_of_nonneg_left
        (hs.tsum_le_tsum_of_inj _ hinj (fun _ _ => by dsimp [w]; positivity) (fun _ => le_rfl) hw) (by dsimp [K, C]; positivity)
    _ = (C * ∑' p, w p) * Real.exp (-((n : ℝ) * t)) * T ^ (n + 2) := by dsimp [K]; ring
