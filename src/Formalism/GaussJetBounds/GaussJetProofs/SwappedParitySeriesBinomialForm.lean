module

public import Formalism.GaussJetBounds.GenLogInverse
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.Analysis.Normed.Group.Ultra

@[expose] public section

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open MvPowerSeries Formalism.IncomingBounds

theorem bnx_lin_pow {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] (x y : σ) (a b : K) (k : ℕ) (μ : σ →₀ ℕ) :
    coeff μ ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) =
      ∑ r ∈ Finset.range (k + 1), if Finsupp.single x r + Finsupp.single y (k - r) = μ then
        a ^ r * b ^ (k - r) * (k.choose r : K) else 0 := by
  rw [add_pow, map_sum]; refine Finset.sum_congr rfl fun r _ => ?_
  rw [show (C a * X x : MvPowerSeries σ K) ^ r * (C b * X y) ^ (k - r) * ((k.choose r : ℕ) : MvPowerSeries σ K) =
      C (a ^ r * b ^ (k - r) * (k.choose r : K)) * (X x ^ r * X y ^ (k - r)) by
    simp only [map_mul, map_pow, map_natCast]; ring,
    coeff_C_mul, X_pow_eq, X_pow_eq, monomial_mul_monomial, one_mul, coeff_monomial]
  by_cases h : Finsupp.single x r + Finsupp.single y (k - r) = μ
  · subst h; simp
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, mul_zero]

theorem bnx_single_add_single_eq {σ : Type*} {x y : σ} (hxy : x ≠ y) (r s i j : ℕ) :
    Finsupp.single x r + Finsupp.single y s = Finsupp.single x i + Finsupp.single y j ↔ r = i ∧ s = j :=
  ⟨fun h => ⟨by simpa [Finsupp.single_apply, hxy] using DFunLike.congr_fun h x,
    by simpa [Finsupp.single_apply, hxy.symm] using DFunLike.congr_fun h y⟩, by rintro ⟨rfl, rfl⟩; rfl⟩

theorem bnx_lin_pow_val {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] {x y : σ} (hxy : x ≠ y)
    (a b : K) (k i j : ℕ) :
    coeff (Finsupp.single x i + Finsupp.single y j) ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) =
      if i + j = k then a ^ i * b ^ j * (k.choose i : K) else 0 := by
  rw [bnx_lin_pow]; simp_rw [bnx_single_add_single_eq hxy]; split_ifs with hk
  · rw [Finset.sum_eq_single i]
    · simp [show k - i = j by omega]
    · intro _ _ hr; split_ifs with h <;> [exact absurd h.1 hr; rfl]
    · exact fun hi => absurd (Finset.mem_range.2 (by omega)) hi
  · refine Finset.sum_eq_zero fun r hr => ?_
    split_ifs with h <;> [exact absurd (by have := Finset.mem_range.1 hr; omega) hk; rfl]

theorem bnx_lin_pow_supp {K : Type u} [Field K] {σ : Type*} [DecidableEq σ] (x y : σ) (a b : K) (k : ℕ) (μ : σ →₀ ℕ)
    (h : coeff μ ((C a * X x + C b * X y : MvPowerSeries σ K) ^ k) ≠ 0) (z : σ) (hz : μ z ≠ 0) : z = x ∨ z = y := by
  rw [bnx_lin_pow] at h; obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  split_ifs at hr with hμ
  · subst hμ; by_contra hne; rw [not_or] at hne; exact hz (by simp [Ne.symm hne.1, Ne.symm hne.2])
  · exact absurd rfl hr

section Blocks
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]

def bnxA (a b : ZMod d → K) (s : ZMod d) : MvPowerSeries (V2 d) K :=
  C (a s) * X (false, s) + C (b s) * X (true, s)

def bnxRes (m : V2 d →₀ ℕ) (s : ZMod d) : V2 d →₀ ℕ :=
  Finsupp.single (false, s) (m (false, s)) + Finsupp.single (true, s) (m (true, s))

theorem bnxRes_apply (m : V2 d →₀ ℕ) (s : ZMod d) (z : V2 d) :
    bnxRes m s z = if z.2 = s then m z else 0 := by
  have _ := NeZero.ne d; obtain ⟨b, t⟩ := z
  by_cases h : t = s
  · subst h; cases b <;> simp [bnxRes]
  · cases b <;> simp [bnxRes, h]

theorem bnx_coeff_prod (a b : ZMod d → K) (k : ZMod d → ℕ) (m : V2 d →₀ ℕ) :
    coeff m (∏ s, bnxA a b s ^ k s) = ∏ s, coeff (bnxRes m s) (bnxA a b s ^ k s) := by
  suffices ∀ (S : Finset (ZMod d)) (m : V2 d →₀ ℕ), coeff m (∏ s ∈ S, bnxA a b s ^ k s) =
      if ∀ z : V2 d, z.2 ∉ S → m z = 0 then ∏ s ∈ S, coeff (bnxRes m s) (bnxA a b s ^ k s) else 0 by
    simpa using this Finset.univ m
  intro S m; induction S using Finset.induction_on generalizing m with
  | empty =>
    rw [Finset.prod_empty, Finset.prod_empty, coeff_one]; by_cases hm : m = 0
    · subst hm; simp
    · rw [ite_eq_right hm, ite_eq_right fun h => hm (Finsupp.ext fun z => h z (by simp))]
  | insert c S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, coeff_mul,
      Finset.sum_eq_single (bnxRes m c, m - bnxRes m c), ih]
    · have hcond : (∀ z : V2 d, z.2 ∉ S → (m - bnxRes m c) z = 0) ↔
          (∀ z : V2 d, z.2 ∉ insert c S → m z = 0) :=
        ⟨fun h z hz => by
          simpa [bnxRes_apply, show z.2 ≠ c from fun e => hz (e ▸ Finset.mem_insert_self c S)]
            using h z fun hS => hz (Finset.mem_insert_of_mem hS),
        fun h z hz => by
          simp only [Finsupp.tsub_apply, bnxRes_apply]
          split_ifs with hzc <;> [omega; simp [h z (by simp [hzc, hz])]]⟩
      by_cases hc : ∀ z : V2 d, z.2 ∉ insert c S → m z = 0
      · rw [ite_eq_left (hcond.2 hc), ite_eq_left hc]
        refine congrArg (_ * ·) (Finset.prod_congr rfl fun s hs => congrArg (coeff · _) ?_)
        ext z; simp only [bnxRes_apply, Finsupp.tsub_apply]
        by_cases hz : z.2 = s <;> [simp [hz, show s ≠ c from fun e => ha (e ▸ hs)]; simp [hz]]
      · rw [ite_eq_right (mt hcond.1 hc), ite_eq_right hc, mul_zero]
    · intro p hp hne; rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
      by_contra hnz; have h1 := left_ne_zero_of_mul hnz; have h2 := right_ne_zero_of_mul hnz; rw [ih] at h2
      have hP : ∀ z : V2 d, z.2 ∉ S → p.2 z = 0 := by split_ifs at h2 with hP <;> [exact hP; exact absurd rfl h2]
      have e1 : p.1 = bnxRes m c := by
        ext z; rw [bnxRes_apply]; split_ifs with hz
        · have h3 := DFunLike.congr_fun hp z; have h4 := hP z (hz ▸ ha); rw [Finsupp.add_apply] at h3; omega
        · by_contra hz0; rcases bnx_lin_pow_supp _ _ _ _ _ _ h1 z hz0 with rfl | rfl <;> exact hz rfl
      refine hne (Prod.ext e1 (Finsupp.ext fun z => ?_))
      have h3 := DFunLike.congr_fun hp z; rw [Finsupp.add_apply] at h3; rw [Finsupp.tsub_apply, ← e1]; omega
    · intro h; refine absurd (Finset.HasAntidiagonal.mem_antidiagonal.2 (Finsupp.ext fun z => ?_)) h
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, bnxRes_apply]; split_ifs <;> omega
end Blocks

section Subst
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]

def bnxN (m : V2 d →₀ ℕ) : ZMod d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun s => m (false, s) + m (true, s)

theorem bnxN_apply (m : V2 d →₀ ℕ) (s : ZMod d) : bnxN m s = m (false, s) + m (true, s) := rfl

theorem bnx_coeff_subst (a b : ZMod d → K) (f : MvPowerSeries (ZMod d) K) (m : V2 d →₀ ℕ) :
    coeff m (subst (bnxA a b) f) = coeff (bnxN m) f *
      ∏ s, (a s ^ m (false, s) * b s ^ m (true, s) * ((m (false, s) + m (true, s)).choose (m (false, s)) : K)) := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun s => by simp [bnxA])]
  have hterm : ∀ dd : ZMod d →₀ ℕ, coeff m (dd.prod fun s e => bnxA a b s ^ e) =
      ∏ s, (if m (false, s) + m (true, s) = dd s then
        a s ^ m (false, s) * b s ^ m (true, s) * ((dd s).choose (m (false, s)) : K) else 0) := fun dd => by
    rw [Finsupp.prod_fintype _ _ fun _ => pow_zero _, bnx_coeff_prod]
    exact Finset.prod_congr rfl fun s _ => bnx_lin_pow_val (x := (false, s)) (y := (true, s)) (by simp) (a s) (b s) (dd s) _ _
  rw [finsum_eq_single _ (bnxN m)]
  · simp only [hterm, smul_eq_mul, bnxN_apply, ↓reduceIte]
  · intro dd hdd
    obtain ⟨s, hs⟩ : ∃ s, dd s ≠ bnxN m s := by by_contra hc; push Not at hc; exact hdd (Finsupp.ext hc)
    rw [hterm, Finset.prod_eq_zero (Finset.mem_univ s), smul_zero]
    split_ifs with h <;> [exact absurd (h.symm.trans (bnxN_apply m s).symm) hs; rfl]

theorem evenIndicator_series_binomial_form : (s1 : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun _ => 1) (fun s => if s.val % 2 = 0 then 1 else 0) := by
  have _ := NeZero.ne d; funext s; simp only [s1, bnxA]; split_ifs <;> simp

theorem zero_series_binomial_form : (s0 : ZMod d → MvPowerSeries (V2 d) K) = bnxA (fun _ => 1) (fun _ => 0) := by
  have _ := NeZero.ne d; funext s; simp [s0, bnxA]

theorem swapped_parity_series_binomial_form : (s2 : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun s => if s.val % 2 = 0 then 0 else 1) (fun s => if s.val % 2 = 0 then 1 else 0) := by
  have _ := NeZero.ne d; funext s; simp only [s2, bnxA]; split_ifs <;> simp

theorem oddIndicator_series_binomial_form : (s1' : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun _ => 1) (fun s => if s.val % 2 = 0 then 0 else 1) := by
  have _ := NeZero.ne d; funext s; simp only [s1', bnxA]; split_ifs <;> simp

theorem parity_series_binomial_form : (s2' : ZMod d → MvPowerSeries (V2 d) K) =
    bnxA (fun s => if s.val % 2 = 0 then 1 else 0) (fun s => if s.val % 2 = 0 then 0 else 1) := by
  have _ := NeZero.ne d; funext s; simp only [s2', bnxA]; split_ifs <;> simp

def bnxM (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) : V2 d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun x => if x.1 then n x.2 - k x.2 else k x.2

theorem bnxM_false (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (s : ZMod d) : bnxM n k (false, s) = k s := rfl

theorem bnxM_true (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (s : ZMod d) : bnxM n k (true, s) = n s - k s := rfl

theorem bnxN_bnxM (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (hk : ∀ s, k s ≤ n s) : bnxN (bnxM n k) = n := by
  ext s; rw [bnxN_apply, bnxM_false, bnxM_true]; have := hk s; omega

theorem bnx_degree_bnxM (n : ZMod d →₀ ℕ) (k : ZMod d → ℕ) (hk : ∀ s, k s ≤ n s) : (bnxM n k).degree = n.degree := by
  rw [Finsupp.degree_eq_sum, Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, bnxM_true, bnxM_false, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by have := hk s; omega
end Subst

section De
variable {K : Type u} [Field K] {d : ℕ} [NeZero d]

theorem bnx_update_le (n : ZMod d →₀ ℕ) (s : ZMod d) (j : ℕ) (hj : j < n s) :
    ∀ t, Function.update (⇑n) s j t ≤ n t := fun t => by
  have _ := NeZero.ne d; rw [Function.update_apply]; split_ifs with h <;> [exact h ▸ hj.le; exact le_rfl]

theorem bnx_prod_choose (n : ZMod d →₀ ℕ) (s : ZMod d) (j : ℕ) (hj : j < n s) (e : ZMod d → K) (he : e s = 1) :
    ∏ t, ((1 : K) ^ Function.update (⇑n) s j t * e t ^ (n t - Function.update (⇑n) s j t) *
      ((Function.update (⇑n) s j t + (n t - Function.update (⇑n) s j t)).choose
        (Function.update (⇑n) s j t) : K)) = ((n s).choose j : K) := by
  rw [Finset.prod_eq_single s]
  · simp [he, Nat.add_sub_cancel' hj.le]
  · exact fun t _ hts => by simp [hts]
  · exact fun h => absurd (Finset.mem_univ s) h

private theorem deriv_binomial_coeff (P : ZMod d → Prop) [DecidablePred P]
    (be : MvPowerSeries (ZMod d) K) (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : P s)
    (j : ℕ) (hj : j < n s) (hpos : 0 < j ∨ ∃ t : ZMod d, P t ∧ t ≠ s ∧ n t ≠ 0) :
    coeff (bnxM n (Function.update (⇑n) s j))
      (subst (bnxA (fun _ => 1) (fun t => if P t then 1 else 0)) be - subst (bnxA (fun _ => 1) (fun _ => 0)) be -
        subst (bnxA (fun t => if P t then 0 else 1) (fun t => if P t then 1 else 0)) be) =
      coeff n be * ((n s).choose j : K) := by
  rw [map_sub, map_sub, bnx_coeff_subst, bnx_coeff_subst, bnx_coeff_subst, bnxN_bnxM n _ (bnx_update_le n s j hj)]
  simp only [bnxM_false, bnxM_true]
  rw [bnx_prod_choose n s j hj (fun t => if P t then (1 : K) else 0) (by simp [hs]),
    Finset.prod_eq_zero (Finset.mem_univ s) (by simp [zero_pow (by omega : n s - j ≠ 0)]), mul_zero, sub_zero]
  rcases hpos with hj0 | ⟨t, ht, hts, hnt⟩
  · rw [Finset.prod_eq_zero (Finset.mem_univ s) (by simp [hs, hj0.ne']), mul_zero, sub_zero]
  · rw [Finset.prod_eq_zero (Finset.mem_univ t) (by simp [hts, ht, hnt]), mul_zero, sub_zero]

theorem evenDerivative_binomial_coeff (be : MvPowerSeries (ZMod d) K) (n : ZMod d →₀ ℕ) (s : ZMod d)
    (hs : s.val % 2 = 0) (j : ℕ) (hj : j < n s) (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 = 0 ∧ t ≠ s ∧ n t ≠ 0) :
    coeff (bnxM n (Function.update (⇑n) s j)) (de1 be) = coeff n be * ((n s).choose j : K) := by
  rw [de1, evenIndicator_series_binomial_form, zero_series_binomial_form, swapped_parity_series_binomial_form]
  exact deriv_binomial_coeff (fun t => t.val % 2 = 0) be n s hs j hj hpos

theorem oddDerivative_binomial_coeff (be : MvPowerSeries (ZMod d) K) (n : ZMod d →₀ ℕ) (s : ZMod d)
    (hs : s.val % 2 ≠ 0) (j : ℕ) (hj : j < n s) (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 ≠ 0 ∧ t ≠ s ∧ n t ≠ 0) :
    coeff (bnxM n (Function.update (⇑n) s j)) (de2 be) = coeff n be * ((n s).choose j : K) := by
  rw [de2, oddIndicator_series_binomial_form, zero_series_binomial_form, parity_series_binomial_form]
  simpa only [ne_eq, ite_not] using deriv_binomial_coeff (fun t => t.val % 2 ≠ 0) be n s hs j hj hpos
end De

section NormNat
variable {K : Type u} [NormedField K] [IsUltrametricDist K]

theorem bnx_norm_one {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (B : ℕ) (hB : ¬ l ∣ B) : 1 ≤ ‖(B : K)‖ := by
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 (hl.coprime_iff_not_dvd.2 hB)
  have h1 : (u : K) * l + v * B = 1 := by simpa using congrArg (Int.cast : ℤ → K) huv
  have key : (1 : ℝ) ≤ max (‖(u : K)‖ * ‖(l : K)‖) (‖(v : K)‖ * ‖(B : K)‖) := by
    simpa [norm_mul, h1] using IsUltrametricDist.norm_add_le_max ((u : K) * l) ((v : K) * B)
  rcases le_max_iff.1 key with h | h
  · linarith [mul_le_of_le_one_left (norm_nonneg (l : K)) (IsUltrametricDist.norm_intCast_le_one K u)]
  · exact h.trans (mul_le_of_le_one_left (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one K v))

theorem bnx_norm_ge {l : ℕ} (hl : l.Prime) (hl1 : ‖(l : K)‖ < 1) (B : ℕ) (hB0 : B ≠ 0)
    (hB : ¬ l ^ 2 ∣ B) : ‖(l : K)‖ ≤ ‖(B : K)‖ := by
  let _ := hB0; by_cases hd : l ∣ B
  · obtain ⟨B', rfl⟩ := hd; rw [Nat.cast_mul, norm_mul]
    exact le_mul_of_one_le_right (norm_nonneg _) (bnx_norm_one hl hl1 B' fun h => hB (pow_two l ▸ mul_dvd_mul_left l h))
  · exact hl1.le.trans (bnx_norm_one hl hl1 B hd)
end NormNat

theorem bnx_choose_lucas {l : ℕ} (hl : l.Prime) (c : ℕ) : ∀ a : ℕ, (l ^ a * c).choose (l ^ a) ≡ c [MOD l] := by
  have := Fact.mk hl; intro a; induction a with
  | zero => simp [Nat.ModEq]
  | succ a ih =>
    have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := l * (l ^ a * c)) (k := l * l ^ a) (p := l)
    rw [Nat.mul_mod_right, Nat.mul_mod_right, Nat.mul_div_cancel_left _ hl.pos,
      Nat.mul_div_cancel_left _ hl.pos, Nat.choose_self, one_mul] at h
    rw [pow_succ', mul_assoc]; exact h.trans ih

theorem bnx_choose_nonpow {l : ℕ} (hl : l.Prime) (m : ℕ) (hm0 : m ≠ 0) (hm : ∀ e, m ≠ l ^ e) :
    ∃ j, 0 < j ∧ j < m ∧ ¬ l ∣ m.choose j := by
  obtain ⟨v, c, hc, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 l hl.ne_one
  have hc0 : c ≠ 0 := fun h => hm0 (by simp [h]); have hc1 : c ≠ 1 := fun h => hm v (by simp [h])
  refine ⟨l ^ v, pow_pos hl.pos v, lt_mul_of_one_lt_right (pow_pos hl.pos v) (by omega), fun hd => ?_⟩
  exact hc (Nat.modEq_zero_iff_dvd.1 ((bnx_choose_lucas hl c v).symm.trans (Nat.modEq_zero_iff_dvd.2 hd)))

theorem bnx_choose_pow {l : ℕ} (hl : l.Prime) (e : ℕ) (he : 1 ≤ e) :
    0 < l ^ (e - 1) ∧ l ^ (e - 1) < l ^ e ∧ (l ^ e).choose (l ^ (e - 1)) ≠ 0 ∧
      ¬ l ^ 2 ∣ (l ^ e).choose (l ^ (e - 1)) := by
  have hlp := hl.pos; have hk0 : 0 < l ^ (e - 1) := pow_pos hlp _
  have hN : l ^ e = l * l ^ (e - 1) := by rw [← pow_succ', Nat.sub_add_cancel he]
  have hlt : l ^ (e - 1) < l ^ e := hN ▸ lt_mul_of_one_lt_left hk0 hl.one_lt
  refine ⟨hk0, hlt, (Nat.choose_pos hlt.le).ne', fun hdiv => ?_⟩
  have hC : (l ^ e).choose (l ^ (e - 1)) = l * (l ^ e - 1).choose (l ^ (e - 1) - 1) := by
    apply Nat.eq_of_mul_eq_mul_right hk0
    have hid := Nat.add_one_mul_choose_eq (l ^ e - 1) (l ^ (e - 1) - 1)
    have e1 : l ^ e - 1 + 1 = l ^ e := by omega
    have e2 : l ^ (e - 1) - 1 + 1 = l ^ (e - 1) := by omega
    rw [e1, e2] at hid; rw [← hid, hN]; ring
  rw [hC, pow_two] at hdiv; have h7 := Nat.dvd_of_mul_dvd_mul_left hlp hdiv
  have hmod1 : ∀ b : ℕ, (l ^ (b + 1) - 1).choose (l ^ b - 1) ≡ 1 [MOD l] := by
    have := Fact.mk hl
    have hdm : ∀ a : ℕ, (l ^ (a + 1) - 1) % l = l - 1 ∧ (l ^ (a + 1) - 1) / l = l ^ a - 1 := fun a => by
      have hs : l ^ (a + 1) - 1 = (l - 1) + l * (l ^ a - 1) := by
        have : l ≤ l * l ^ a := Nat.le_mul_of_pos_right l (pow_pos hlp a); rw [pow_succ', Nat.mul_sub_one]; omega
      rw [hs, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hlp,
        Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega), zero_add]; exact ⟨rfl, rfl⟩
    intro b; induction b with
    | zero => simp [Nat.ModEq]
    | succ b ih =>
      have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := l ^ (b + 2) - 1) (k := l ^ (b + 1) - 1) (p := l)
      rw [(hdm (b + 1)).1, (hdm b).1, (hdm (b + 1)).2, (hdm b).2, Nat.choose_self, one_mul] at h
      exact h.trans ih
  have hm := hmod1 (e - 1); rw [Nat.sub_add_cancel he] at hm
  exact hl.not_dvd_one (Nat.modEq_zero_iff_dvd.1 (hm.symm.trans (Nat.modEq_zero_iff_dvd.2 h7)))

theorem bnx_pow_reduce (l d x : ℕ) (hl : 1 ≤ l) : l ^ x ≡ l ^ (x % d) [MOD l ^ d - 1] := by
  have h1 : l ^ d ≡ 1 [MOD l ^ d - 1] := ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hl)).2 dvd_rfl).symm
  calc l ^ x = (l ^ d) ^ (x / d) * l ^ (x % d) := by rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    _ ≡ 1 ^ (x / d) * l ^ (x % d) [MOD l ^ d - 1] := (h1.pow _).mul_right _
    _ = l ^ (x % d) := by rw [one_pow, one_mul]

theorem bnx_pow_mod (l d x y : ℕ) (hl : 3 ≤ l) (hd : 1 ≤ d) (h : l ^ x ≡ l ^ y [MOD l ^ d - 1]) : x % d = y % d := by
  have h' := (bnx_pow_reduce l d x (by omega)).symm.trans (h.trans (bnx_pow_reduce l d y (by omega)))
  have hlt : ∀ k < d, l ^ k < l ^ d - 1 := fun k hk => by
    have h1 : l ^ k ≤ l ^ (d - 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 3 * l ^ (d - 1) ≤ l ^ d := by
      rw [show l ^ d = l * l ^ (d - 1) by rw [← pow_succ', Nat.sub_add_cancel hd]]
      exact Nat.mul_le_mul_right _ hl
    have h3 : 1 ≤ l ^ (d - 1) := Nat.one_le_pow _ _ (by omega); omega
  unfold Nat.ModEq at h'
  rw [Nat.mod_eq_of_lt (hlt _ (Nat.mod_lt _ (by omega))), Nat.mod_eq_of_lt (hlt _ (Nat.mod_lt _ (by omega)))] at h'
  exact Nat.pow_right_injective (by omega) h'

theorem bnx_torus_cong {K : Type u} [Field K] (l d : ℕ) [NeZero d] (hl : l.Prime) (hl3 : 3 ≤ l)
    (hd2 : 2 ≤ d) (hde : Even d) (ζ : K) (hζ : IsPrimitiveRoot ζ (l ^ d - 1))
    (be : MvPowerSeries (ZMod d) K) (htor : subst (torus l ζ) be = be)
    (s s' : ZMod d) (hs : s.val % 2 = 0) (hs' : s'.val % 2 ≠ 0) (α β : ℕ)
    (hc : coeff (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β)) be ≠ 0) :
    s + (α : ZMod d) = s' + (β : ZMod d) := by
  let _ := PLift.up hl; let _ := PLift.up hde
  have htor_prod : ∀ dd : ZMod d →₀ ℕ, (dd.prod fun t e => (torus l ζ t : MvPowerSeries (ZMod d) K) ^ e) =
      C (∏ t, (ζ ^ lw l t) ^ dd t) * monomial dd 1 := fun dd => by
    rw [Finsupp.prod_fintype _ _ fun _ => pow_zero _]
    simp only [torus, mul_pow, ← map_pow, Finset.prod_mul_distrib, map_prod]
    suffices ∀ S : Finset (ZMod d), ∏ t ∈ S, (X t ^ dd t : MvPowerSeries (ZMod d) K) =
        monomial (∑ t ∈ S, Finsupp.single t (dd t)) 1 by
      rw [this, show ∑ t, Finsupp.single t (dd t) = dd by ext; simp]
    exact fun S => Finset.induction_on S (by simp [monomial_zero_eq_C_apply]) fun a S ha ih => by
      rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, X_pow_eq, monomial_mul_monomial, one_mul]
  have hk0 : 0 < l ^ d - 1 := by have := Nat.le_self_pow (by omega : d ≠ 0) l; omega
  have hss : s ≠ s' := fun e => hs' (e ▸ hs)
  have hcoef := congrArg (coeff (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))) htor
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun t => by simp [torus]),
    finsum_eq_single _ (Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β))] at hcoef
  swap
  · intro dd hdd; rw [htor_prod, coeff_C_mul, coeff_monomial]; simp [Ne.symm hdd]
  rw [htor_prod, coeff_C_mul, coeff_monomial] at hcoef; simp only [↓reduceIte, mul_one, smul_eq_mul] at hcoef
  have hprod := mul_left_cancel₀ hc (hcoef.trans (mul_one _).symm)
  rw [Finset.prod_eq_mul s s' hss (fun t _ ht => by simp [Ne.symm ht.1, Ne.symm ht.2])
    (fun h => absurd (Finset.mem_univ s) h) (fun h => absurd (Finset.mem_univ s') h)] at hprod
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hss,
    Finsupp.single_eq_of_ne (Ne.symm hss), add_zero, zero_add] at hprod
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add₀ (hζ.ne_zero hk0.ne'),
    hζ.zpow_eq_one_iff_dvd, show lw l s = (l : ℤ) ^ s.val by simp [lw, hs],
    show lw l s' = -(l : ℤ) ^ s'.val by simp [lw, hs']] at hprod
  have hmod : l ^ (s.val + α) ≡ l ^ (s'.val + β) [MOD l ^ d - 1] := by
    rw [Nat.modEq_iff_dvd]; convert dvd_neg.2 hprod using 1; push_cast; ring
  simpa [ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_zmod_val] using
    congrArg (Nat.cast : ℕ → ZMod d) (bnx_pow_mod l d _ _ hl3 (by omega) hmod)

theorem bnx_dot_const {ι : Type*} (n : ι →₀ ℕ) (c : ℝ) : dot n (fun _ => c) = (n.degree : ℝ) * c := by
  simp [dot, Finsupp.sum, ← Finset.sum_mul, Finsupp.degree_apply]

section Sides
variable {K : Type u} [NormedField K] {d : ℕ} [NeZero d]

theorem bnx_sideE (be : MvPowerSeries (ZMod d) K) (pi r w : ℝ) (h1 : WtGe pi (fun _ => r) w (de1 be))
    (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 = 0) (j : ℕ) (hj : j < n s)
    (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 = 0 ∧ t ≠ s ∧ n t ≠ 0) :
    ‖coeff n be‖ * ‖((n s).choose j : K)‖ ≤ pi ^ (w - dot n (fun _ => r)) := by
  simpa [MonoWtGe, evenDerivative_binomial_coeff be n s hs j hj hpos, norm_mul, bnx_dot_const,
    bnx_degree_bnxM n _ (bnx_update_le n s j hj)] using h1 (bnxM n (Function.update (⇑n) s j))

theorem bnx_sideO (be : MvPowerSeries (ZMod d) K) (pi r w : ℝ) (h2 : WtGe pi (fun _ => r) w (de2 be))
    (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 ≠ 0) (j : ℕ) (hj : j < n s)
    (hpos : 0 < j ∨ ∃ t : ZMod d, t.val % 2 ≠ 0 ∧ t ≠ s ∧ n t ≠ 0) :
    ‖coeff n be‖ * ‖((n s).choose j : K)‖ ≤ pi ^ (w - dot n (fun _ => r)) := by
  simpa [MonoWtGe, oddDerivative_binomial_coeff be n s hs j hj hpos, norm_mul, bnx_dot_const,
    bnx_degree_bnxM n _ (bnx_update_le n s j hj)] using h2 (bnxM n (Function.update (⇑n) s j))
end Sides

theorem bnx_div {pi a b X v : ℝ} (h0 : 0 < pi) (hb : pi ^ v ≤ b) (ha : 0 ≤ a) (h : a * b ≤ X) : a ≤ X / pi ^ v :=
  (le_div_iff₀ (Real.rpow_pos_of_pos h0 v)).2 ((mul_le_mul_of_nonneg_left hb ha).trans h)

theorem bnx_side_cases {d : ℕ} {l : ℕ} (hl : l.Prime) (P : ZMod d → Prop) (n : ZMod d →₀ ℕ) (h : ∃ s, P s ∧ n s ≠ 0) :
    (∃ s j, P s ∧ j < n s ∧ (0 < j ∨ ∃ t, P t ∧ t ≠ s ∧ n t ≠ 0) ∧ ¬ l ∣ (n s).choose j) ∨
    (∃ s e, P s ∧ (∀ t, P t → t ≠ s → n t = 0) ∧ n s = l ^ e) := by
  obtain ⟨s, hs, hns⟩ := h
  by_cases hex : ∃ t, P t ∧ t ≠ s ∧ n t ≠ 0
  · exact Or.inl ⟨s, 0, hs, Nat.pos_of_ne_zero hns, Or.inr hex, by simpa using hl.not_dvd_one⟩
  · push Not at hex; by_cases hpow : ∃ e, n s = l ^ e
    · obtain ⟨e, he⟩ := hpow; exact Or.inr ⟨s, e, hs, hex, he⟩
    · push Not at hpow; obtain ⟨j, hj0, hjn, hjd⟩ := bnx_choose_nonpow hl (n s) hns hpow
      exact Or.inl ⟨s, j, hs, hjn, Or.inl hj0, hjd⟩

theorem bnx_degE_eq {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 = 0)
    (hu : ∀ t : ZMod d, t.val % 2 = 0 → t ≠ s → n t = 0) : degE n = n s := by
  rw [degE, Finset.sum_eq_single s, ite_eq_left hs]
  · intro t _ hts; split_ifs with ht <;> [exact hu t ht hts; rfl]
  · exact fun h => absurd (Finset.mem_univ s) h

theorem bnx_degO_eq {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (s : ZMod d) (hs : s.val % 2 ≠ 0)
    (hu : ∀ t : ZMod d, t.val % 2 ≠ 0 → t ≠ s → n t = 0) : degO n = n s := by
  rw [degO, Finset.sum_eq_single s, ite_eq_right hs]
  · intro t _ hts; split_ifs with ht <;> [rfl; exact hu t ht hts]
  · exact fun h => absurd (Finset.mem_univ s) h

theorem bnx_exE {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (h : 0 < degE n) :
    ∃ s : ZMod d, s.val % 2 = 0 ∧ n s ≠ 0 := by
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  split_ifs at hs with he <;> [exact ⟨s, he, hs⟩; exact absurd rfl hs]

theorem bnx_exO {d : ℕ} [NeZero d] (n : ZMod d →₀ ℕ) (h : 0 < degO n) :
    ∃ s : ZMod d, s.val % 2 ≠ 0 ∧ n s ≠ 0 := by
  obtain ⟨s, _, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
  split_ifs at hs with he <;> [exact absurd rfl hs; exact ⟨s, he, hs⟩]

theorem binomial_coefficient_extraction : BinomExtract.{u} := by
  intro K _ _ _ l d _ hl ⟨m, hm⟩ hd2 hde hl1 ζ hζ be htor hlow h1 h2
  have hl3 : 3 ≤ l := by have := hl.two_le; omega
  have hpi0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (Nat.cast_ne_zero.2 hl.ne_zero)
  let r := rho l; let w : ℝ := 1 / ((l : ℝ) - 1)
  have key : ∀ n : ZMod d →₀ ℕ, coeff n be ≠ 0 →
      MonoWtGe ‖(l : K)‖ (fun _ => r) w n (coeff n be) ∨
        (IsBiPower l n ∧ MonoWtGe ‖(l : K)‖ (fun _ => r) (w - 1) n (coeff n be)) := fun n hn => by
    obtain ⟨hE, hO, hEO⟩ := hlow n hn; have hc0 := norm_nonneg (coeff n be); unfold MonoWtGe
    rcases bnx_side_cases hl (fun s : ZMod d => s.val % 2 = 0) n (bnx_exE n hE) with
      ⟨s, j, hs, hj, hpos, hnd⟩ | ⟨s, α, hs, hu, hα⟩
    · exact Or.inl ((le_mul_of_one_le_right hc0 (bnx_norm_one hl hl1 _ hnd)).trans
        (bnx_sideE be _ _ _ h1 n s hs j hj hpos))
    rcases bnx_side_cases hl (fun s : ZMod d => s.val % 2 ≠ 0) n (bnx_exO n hO) with
      ⟨s', j, hs', hj, hpos, hnd⟩ | ⟨s', β, hs', hu', hβ⟩
    · exact Or.inl ((le_mul_of_one_le_right hc0 (bnx_norm_one hl hl1 _ hnd)).trans
        (bnx_sideO be _ _ _ h2 n s' hs' j hj hpos))
    have hss : s ≠ s' := fun e => hs' (e ▸ hs)
    have hneq : n = Finsupp.single s (l ^ α) + Finsupp.single s' (l ^ β) := by
      ext t; rw [Finsupp.add_apply, Finsupp.single_apply, Finsupp.single_apply]
      by_cases ht : t.val % 2 = 0
      · by_cases hts : t = s
        · subst hts; simp [hss.symm, hα]
        · simp [Ne.symm hts, show s' ≠ t from fun e => hs' (e ▸ ht), hu t ht hts]
      · by_cases hts : t = s'
        · subst hts; simp [hss, hβ]
        · simp [Ne.symm hts, show s ≠ t from fun e => ht (e ▸ hs), hu' t ht hts]
    have hαβ : α ≠ 0 ∨ β ≠ 0 := by
      by_contra hc; rw [not_or, not_ne_iff, not_ne_iff] at hc
      exact hEO ⟨by simp [bnx_degE_eq n s hs hu, hα, hc.1], by simp [bnx_degO_eq n s' hs' hu', hβ, hc.2]⟩
    have hcong := bnx_torus_cong l d hl hl3 hd2 hde ζ hζ be htor s s' hs hs' α β (hneq ▸ hn)
    refine Or.inr ⟨⟨s, s', α, β, hs, Nat.mod_two_ne_zero.1 hs', hαβ, hcong, hneq⟩, ?_⟩
    have hpow_bd : ∀ {γ : ℕ}, γ ≠ 0 →
        (∀ j, j < l ^ γ → 0 < j → ‖coeff n be‖ * ‖((l ^ γ).choose j : K)‖ ≤ ‖(l : K)‖ ^ (w - dot n (fun _ => r))) →
        ‖coeff n be‖ ≤ ‖(l : K)‖ ^ (w - 1 - dot n (fun _ => r)) := fun hγ hside => by
      obtain ⟨hj0, hjlt, hCne, hC2⟩ := bnx_choose_pow hl _ (Nat.one_le_iff_ne_zero.2 hγ)
      have hb := (mul_le_mul_of_nonneg_left (bnx_norm_ge hl hl1 _ hCne hC2) hc0).trans (hside _ hjlt hj0)
      have h3 := bnx_div (v := 1) hpi0 (Real.rpow_one _).le hc0 hb
      rwa [← Real.rpow_sub hpi0, show w - dot n (fun _ => r) - 1 = w - 1 - dot n (fun _ => r) by ring] at h3
    rcases hαβ with hα0 | hβ0
    · exact hpow_bd hα0 fun j hj hj0 => hα ▸ bnx_sideE be _ _ _ h1 n s hs j (hα.symm ▸ hj) (Or.inl hj0)
    · exact hpow_bd hβ0 fun j hj hj0 => hβ ▸ bnx_sideO be _ _ _ h2 n s' hs' j (hβ.symm ▸ hj) (Or.inl hj0)
  refine ⟨fun n => (em (coeff n be = 0)).elim (fun hn => by simp [MonoWtGe, hn]; positivity) fun hn =>
    (key n hn).elim (fun h => h.trans (Real.rpow_le_rpow_of_exponent_ge hpi0 hl1.le (by linarith))) And.right,
    fun n hnb => (em (coeff n be = 0)).elim (fun hn => by simp [MonoWtGe, hn]; positivity) fun hn =>
      (key n hn).resolve_right fun hb => hnb hb.1⟩

end Formalism.DworkPowerSeriesWeights
