module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

theorem UpperTheory.V.HV.lossLe :
    ∀ l N n e : ℕ, l.Prime → l ≠ 2 → 2 ≤ N → n ≤ N → 1 ≤ e → lossAll l N n e ≤ (N * e) ^ 6 ∧ LDataCardLeFinrank.nuBound l N e ≤ 2 * N * e := by
  intro l N n e hl hl2 hN hn he
  have hfac (m : ℕ) : m.factorization l ≤ m := by
    cases m with
    | zero => simp
    | succ m => exact (Nat.factorization_lt l (Nat.succ_ne_zero m)).le
  set M := N * e
  have hNM : N ≤ M := Nat.le_mul_of_pos_right N he
  have hM2 : 2 ≤ M := hN.trans hNM
  have hnu : LDataCardLeFinrank.nuBound l N e ≤ 2 * M := by
    unfold LDataCardLeFinrank.nuBound
    simp only [ite_eq_right hl2]
    split_ifs
    · have hmax : max (N.factorization l) 1 ≤ N := max_le (hfac N) (by lia)
      have heM : e ≤ M := Nat.le_mul_of_pos_left e (by lia)
      lia [hfac e]
    · exact Nat.zero_le _
  have hk : N.primeFactors.card ≤ N := by
    calc N.primeFactors.card ≤ (Finset.Icc 1 N).card := Finset.card_le_card fun p hp =>
          Finset.mem_Icc.mpr ⟨(Nat.prime_of_mem_primeFactors hp).one_lt.le,
            Nat.le_of_dvd (by lia) (Nat.dvd_of_mem_primeFactors hp)⟩
      _ = N := by simp
  refine ⟨?_, by simpa [M, Nat.mul_assoc] using hnu⟩
  have hnM := hn.trans hNM
  have hkM := hk.trans hNM
  have hvM := (hfac n).trans hnM
  calc lossAll l N n e ≤ (M + M ^ 2) * (2 * M) + M * (M * M) + M * M := by
        unfold lossAll Chr.loss
        gcongr
    _ = 3 * M ^ 2 + 3 * M ^ 3 := by ring
    _ ≤ 6 * M ^ 3 := by
        have hpow : M ^ 2 ≤ M ^ 3 := Nat.pow_le_pow_right (by lia) (by decide)
        lia
    _ ≤ M ^ 3 * M ^ 3 := by
        apply Nat.mul_le_mul_right
        have := Nat.pow_le_pow_left hM2 3
        lia
    _ = _ := by ring
