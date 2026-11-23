module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ConstantLeRpowOfThreeLe
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DvdCoeffsOfMemSpanDistinguished
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.FormalSeriesValueAtTwoPointsGenericPoints
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open PowerSeries Formalism.MainNotions.N.FrobeniusPowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem den_bound {l : ℕ} [Fact l.Prime] (P : PhiData O l) (y B κ : ℕ) (hy : 1 ≤ y) (hB : 1 ≤ B)
    (x : O) (U₁ U₂ : O⟦X⟧)
    (h : P.p 1 ^ y * C x = C (l : O) ^ κ * 1 * U₁ - X ^ B * U₂) :
    (l : O) ^ (κ - ⌈max 0 ((y : ℝ) - B / l + 2 + Real.logb l y)⌉₊) ∣ x ∧
      (l * y < B → (l : O) ^ κ ∣ x) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨u, hu⟩ := l_eq_unit_mul_pow hϖ P.hl0
  set e := eO (O := O) l with he
  have hassoc : Associated (l : O) (ϖ ^ e) := by
    rw [hu]
    exact associated_unit_mul_left _ _ u.isUnit
  have hdiv : ∀ k : ℕ, ϖ ^ (e * k) ∣ x → (l : O) ^ k ∣ x := by
    intro k hk
    rw [pow_mul] at hk
    exact (hassoc.pow_pow (n := k)).dvd_iff_dvd_left.mpr hk
  set de := ⌈max 0 ((y : ℝ) - B / l + 2 + Real.logb l y)⌉₊ with hde
  by_cases hx0 : x = 0
  · subst hx0
    exact ⟨dvd_zero _, fun _ => dvd_zero _⟩
  obtain ⟨v, ε, hxe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hϖv : ϖ ^ v ∣ x := by
    rw [hxe]
    exact dvd_mul_left _ _
  by_cases hv : e * κ ≤ v
  · have h1 : (l : O) ^ κ ∣ x := hdiv κ ((pow_dvd_pow _ hv).trans hϖv)
    exact ⟨(pow_dvd_pow _ (Nat.sub_le _ _)).trans h1, fun _ => h1⟩
  have hvlt : v < e * κ := lt_of_not_ge hv
  set k := e * κ - v with hk
  have hdist := (ContPA.dist_X_pow (O := O) B).1

  have hmem : P.p 1 ^ y ∈ Ideal.span {C ϖ ^ k, (X : O⟦X⟧) ^ B} := by
    have hvk : v + k = e * κ := Nat.add_sub_cancel' hvlt.le
    have hlO : (l : O) ^ κ = ϖ ^ v * (ϖ ^ k * (↑u : O) ^ κ) := by
      rw [hu, mul_pow, ← pow_mul, ← hvk, pow_add, mul_comm ((u : O) ^ κ), mul_assoc]
    have hlk : (C (l : O) : O⟦X⟧) ^ κ = C ϖ ^ v * (C ϖ ^ k * C ((↑u : O) ^ κ)) := by
      rw [← map_pow, hlO, map_mul, map_mul, map_pow, map_pow]
    have hc : C ϖ ^ v * (P.p 1 ^ y * C (↑ε : O) - C ϖ ^ k * (C ((↑u : O) ^ κ) * U₁)) =
        (-U₂) * (X : O⟦X⟧) ^ B := by
      have hxC : (C x : O⟦X⟧) = C (↑ε : O) * C ϖ ^ v := by rw [hxe, map_mul, map_pow]
      rw [hxC, hlk] at h
      linear_combination h
    obtain ⟨z, hz⟩ := ContM_cancel_unif hϖ hdist v hc
    have hε : P.p 1 ^ y = C ϖ ^ k * (C ((↑u : O) ^ κ) * U₁ * C (↑(ε⁻¹) : O)) +
        (X : O⟦X⟧) ^ B * (z * C (↑(ε⁻¹) : O)) := by
      have hεε : (C (↑ε : O) : O⟦X⟧) * C (↑(ε⁻¹) : O) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      linear_combination (-(P.p 1 ^ y)) * hεε + C (↑(ε⁻¹) : O) * hz
    rw [hε]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  have hkc := (mem_iff_le_cont hϖ hdist _ k).1 hmem
  constructor
  · obtain ⟨hne, hle⟩ := P.constant_le_rpow_of_three_le hϖ B y hB hy
    have hkc' : k ≤ (cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y)).toNat := by
      rw [← ENat.coe_toNat hne] at hkc
      exact_mod_cast hkc
    have hr : max 0 ((y : ℝ) - B / l + 2 + Real.logb l y) ≤ (de : ℝ) := Nat.le_ceil _
    have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have hkr : (k : ℝ) ≤ (e : ℝ) * de := by
      have hk' : (k : ℝ) ≤ ((cont ϖ ((X : O⟦X⟧) ^ B) (P.p 1 ^ y)).toNat : ℝ) := by exact_mod_cast hkc'
      exact hk'.trans (hle.trans (mul_le_mul_of_nonneg_left hr he0))
    have hkn : k ≤ e * de := by exact_mod_cast hkr
    apply hdiv
    have hle2 : e * (κ - de) ≤ v := by rw [Nat.mul_sub]; omega
    exact (pow_dvd_pow _ hle2).trans hϖv
  · intro hlt
    have h0 := P.cont_X_pow_pow_eq_zero_of_gt hϖ B y hB hy hlt
    rw [h0] at hkc
    have : k = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp hkc
    omega

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
