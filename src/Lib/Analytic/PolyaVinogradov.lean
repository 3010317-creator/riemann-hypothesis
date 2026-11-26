import Lib.Analytic.ZeroSymmetry
import TauCeti.NumberTheory.DirichletCharacter.PolyaVinogradov

/-!
# Gauss sums of primitive characters and the Pólya–Vinogradov bound

The Gauss sum of a primitive Dirichlet character mod `q` has absolute value `√q`. For a
non-principal character mod `q`, every partial sum of its values is at most `2 √q (1 + log q)` in
absolute value.

* `New.norm_gaussSum_of_isPrimitive`: the modulus of the Gauss sum.
* `New.polya_vinogradov`: the Pólya–Vinogradov inequality.

## Relation to the literature

Known result: the Pólya–Vinogradov inequality for sums of a non-principal Dirichlet character. It is
proved here for initial intervals only, with the explicit bound `2 √q (1 + log q)`. The case of a
general character is reduced to the primitive character that induces it by Tau Ceti's
`DirichletCharacter.norm_sum_Icc_changeLevel_le`, with `2 ^ ω r ≤ 2 √r`. Source:
Pólya 1918, Vinogradov 1918; Davenport, Multiplicative Number Theory; Montgomery–Vaughan Thm 9.18.
-/

open Complex Finset DirichletCharacter Real ZMod ArithmeticFunction Moebius NeZero Nat

namespace New

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

/-- The Gauss sum of a primitive Dirichlet character mod `q`, taken with the standard additive
character `x ↦ exp (2 π i x / q)` of `ZMod q`, has absolute value `√q`. -/
lemma norm_gaussSum_of_isPrimitive (hχ : χ.IsPrimitive) : ‖gaussSum χ stdAddChar‖ = √q := by
  -- Fourier inversion at `-1`: the Gauss sum times its complex conjugate is `q`.
  have h_dft : dft (χ : ZMod q → ℂ) = fun k : ZMod q ↦ χ⁻¹ (-k) * gaussSum χ stdAddChar :=
    funext hχ.fourierTransform_eq_inv_mul_gaussSum
  have h_inversion : dft (dft (χ : ZMod q → ℂ)) (-1) = q := by simp [dft_dft]
  have h_conj : star (gaussSum χ stdAddChar) * gaussSum χ stdAddChar = q := by
    rw [← h_inversion, h_dft, dft_mul_const, dft_comp_neg, star_gaussSum_eq]
    simp [fourierTransform_eq_gaussSum_mulShift, ← AddChar.inv_mulShift]
  have h_sq : ‖gaussSum χ stdAddChar‖ * ‖gaussSum χ stdAddChar‖ = q := by
    simpa using congrArg norm h_conj
  rw [← h_sq, Real.sqrt_mul_self (norm_nonneg _)]

/-- A natural number `r` has at most `2 √r` divisors. -/
lemma card_divisors_le_two_mul_sqrt (r : ℕ) : (#r.divisors : ℝ) ≤ 2 * √r := by
  -- Of two complementary divisors one is at most `√r`.
  have h_sub : r.divisors ⊆ Ioc 0 r.sqrt ∪ (Ioc 0 r.sqrt).image fun d : ℕ ↦ r / d := by
    intro d hd
    obtain ⟨⟨e, rfl⟩, hr⟩ : d ∣ r ∧ r ≠ 0 := mem_divisors.mp hd
    obtain ⟨hd_pos, he_pos⟩ : 0 < d ∧ 0 < e := by simpa [Nat.pos_iff_ne_zero] using hr
    rcases le_sqrt_of_eq_mul (rfl : d * e = d * e) with hd_le | he_le
    · simp [hd_pos, hd_le]
    · exact mem_union_right _
        (mem_image.mpr ⟨e, mem_Ioc.mpr ⟨he_pos, he_le⟩, Nat.mul_div_cancel d he_pos⟩)
  grw [card_le_card h_sub, card_union_le, Finset.card_image_le, ← nat_sqrt_le_real_sqrt]
  simp [two_mul]

open scoped ArithmeticFunction.omega

/-- A positive natural number `r` has `2 ^ ω r ≤ 2 √r`: each prime factor at least doubles the
number of divisors. -/
lemma two_pow_cardDistinctFactors_le_two_mul_sqrt {r : ℕ} (hr : r ≠ 0) :
    (2 : ℝ) ^ ω r ≤ 2 * √r := by
  refine le_trans ?_ (card_divisors_le_two_mul_sqrt r)
  rw [Nat.card_divisors hr, cardDistinctFactors_eq_card_primeFactors]
  refine mod_cast Finset.pow_card_le_prod _ _ _ fun p hp ↦ ?_
  have : r.factorization p ≠ 0 := Finsupp.mem_support_iff.mp (by rwa [Nat.support_factorization])
  omega

/-- The **Pólya–Vinogradov inequality** for initial intervals: for a non-principal Dirichlet
character `χ` mod `q` one has `|∑_{1 ≤ v ≤ X} χ v| ≤ 2 √q (1 + log q)` for all `X`. -/
theorem polya_vinogradov (hχ : χ ≠ 1) (X : ℕ) :
    ‖∑ v ∈ Ioc 0 X, χ v‖ ≤ 2 * √q * (1 + Real.log q) := by
  -- `χ` is induced by its primitive character `ψ` mod the conductor `M`; write `q = M * r`.
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  obtain ⟨r, hr⟩ := χ.conductor_dvd_level
  have hψ : χ.primitiveCharacter ≠ 1 := fun h ↦
    hχ (by rw [← χ.changeLevel_primitiveCharacter, h, map_one])
  have hr0 : r ≠ 0 := right_ne_zero_of_mul (hr.symm.trans_ne (NeZero.ne q))
  have hM_pos : (0 : ℝ) < χ.conductor := Nat.cast_pos.mpr (NeZero.pos _)
  have hM_le : (χ.conductor : ℝ) ≤ q :=
    mod_cast Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level
  have h_log : 0 ≤ 1 + Real.log χ.conductor :=
    by linarith [Real.log_nonneg (one_le_cast.mpr (NeZero.one_le (n := χ.conductor)))]
  have h := χ.primitiveCharacter.norm_sum_Icc_changeLevel_le χ.primitiveCharacter_isPrimitive hψ
    χ.conductor_dvd_level X
  have h_div : q / χ.conductor = r :=
    Nat.div_eq_of_eq_mul_left (NeZero.pos _) (hr.trans (mul_comm _ _))
  have hq : (q : ℝ) = χ.conductor * r := mod_cast hr
  rw [χ.changeLevel_primitiveCharacter, h_div] at h
  rw [← Finset.Icc_add_one_left_eq_Ioc, zero_add]
  calc ‖∑ v ∈ Icc 1 X, χ v‖
      ≤ 2 ^ ω r * (√χ.conductor * (1 + Real.log χ.conductor)) := h
    _ ≤ 2 * √r * (√χ.conductor * (1 + Real.log q)) := by
        gcongr
        exact two_pow_cardDistinctFactors_le_two_mul_sqrt hr0
    _ = 2 * √q * (1 + Real.log q) := by
        rw [show √(q : ℝ) = √χ.conductor * √r by rw [hq, Real.sqrt_mul hM_pos.le]]
        ring

end New
