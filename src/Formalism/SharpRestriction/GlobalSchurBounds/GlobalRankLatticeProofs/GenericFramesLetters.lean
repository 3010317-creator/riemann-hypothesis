module

public import Formalism.SharpRestriction.GlobalSchurBounds.CMFieldLemmas
public import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.SecondPropositionEveryLocalisation

@[expose] public section
noncomputable section
namespace Formalism.MainNotions.UnusedSlot33

open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

namespace PrimeReciprocalSums
theorem sum_inv_sq_le (N : ℕ) : ∑ q ∈ Finset.Icc 1 N, (1 : ℝ) / (q : ℝ) ^ 2 ≤ 2 := by
  suffices h : ∑ q ∈ Finset.Icc 1 N, (1 : ℝ) / (q : ℝ) ^ 2 ≤ 2 - 2 / ((N : ℝ) + 1) by
    linarith [show (0 : ℝ) ≤ 2 / ((N : ℝ) + 1) by positivity]
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]; push_cast
    suffices 0 ≤ 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1) - 1 / ((n : ℝ) + 1) ^ 2 by linarith
    rw [show 2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 1 + 1) - 1 / ((n : ℝ) + 1) ^ 2 =
      (n : ℝ) / (((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) by field_simp; ring]; positivity

theorem log_step (x : ℝ) (hx : 1 ≤ x) :
    Real.log (x + 1) / (x + 1) ^ 2 ≤ (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have hl : 0 ≤ Real.log x - Real.log (x + 1) + 1 / x := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos hx1 hx0)
    rw [Real.log_div hx1.ne' hx0.ne', add_div, div_self hx0.ne'] at h1; linarith
  have hL := Real.log_nonneg (by linarith : 1 ≤ x + 1); have hx' : 0 ≤ x - 1 := by linarith
  rw [← sub_nonneg, show (Real.log x + 2) / x - (Real.log (x + 1) + 2) / (x + 1) -
    Real.log (x + 1) / (x + 1) ^ 2 = (Real.log x - Real.log (x + 1) + 1 / x) / x +
    Real.log (x + 1) / (x * (x + 1) ^ 2) + (x - 1) / (x ^ 2 * (x + 1)) by field_simp; ring]; positivity

theorem sum_log_sq_le (N : ℕ) : ∑ q ∈ Finset.Icc 1 N, Real.log q / (q : ℝ) ^ 2 ≤ 2 := by
  rcases N with _ | k
  · simp
  · suffices h : ∑ q ∈ Finset.Icc 1 (k + 1), Real.log q / (q : ℝ) ^ 2 ≤
        2 - (Real.log ((k : ℝ) + 1) + 2) / ((k : ℝ) + 1) by
      have hL := Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) k] : 1 ≤ (k : ℝ) + 1)
      linarith [show 0 ≤ (Real.log ((k : ℝ) + 1) + 2) / ((k : ℝ) + 1) by positivity]
    induction k with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hs := log_step ((n : ℝ) + 1) (by linarith [Nat.cast_nonneg (α := ℝ) n]); push_cast; linarith

theorem sum_inv_le (N : ℕ) (hN : 1 ≤ N) : ∑ q ∈ Finset.Icc 1 N, (1 : ℝ) / (q : ℝ) ≤ 1 + Real.log N := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩; clear hN
  suffices h : ∑ q ∈ Finset.Icc 1 (k + 1), (1 : ℝ) / (q : ℝ) ≤ 1 + Real.log ((k : ℝ) + 1) by
    exact_mod_cast h
  induction k with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]; have hy1 : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
    have h1 := Real.log_le_sub_one_of_pos (div_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1) hy1)
    rw [Real.log_div (by positivity) hy1.ne', show ((n : ℝ) + 1) / ((n : ℝ) + 1 + 1) =
      1 - 1 / ((n : ℝ) + 1 + 1) by rw [eq_sub_iff_add_eq, ← add_div, div_self hy1.ne']] at h1
    push_cast; linarith

private theorem sum_filter_le_Icc {m N : ℕ} (hm : 4 ≤ m) {T : Finset ℕ} {F G : ℕ → ℝ}
    (a : ℕ → ℕ) (hG0 : ∀ q, 0 ≤ G q) (hinj : Set.InjOn a T)
    (ha : ∀ l ∈ T, 1 ≤ a l ∧ a l ≤ N + 1 ∧ a l % m = 0 ∧
      (m * (a l / m) = a l → 1 ≤ a l / m → F l ≤ G (a l / m))) :
    ∑ l ∈ T, F l ≤ ∑ q ∈ Finset.Icc 1 N, G q := by
  classical
  have hq {l : ℕ} (hl : l ∈ T) :
      m * (a l / m) = a l ∧ F l ≤ G (a l / m) ∧ a l / m ∈ Finset.Icc 1 N := by
    obtain ⟨h1, hN, hmod, hF⟩ := ha l hl
    have hd := Nat.div_add_mod (a l) m; rw [hmod, add_zero] at hd
    have hq1 : 1 ≤ a l / m := Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at hd; omega
    have h4 := Nat.mul_le_mul_right (a l / m) hm
    exact ⟨hd, hF hd hq1, Finset.mem_Icc.mpr ⟨hq1, by omega⟩⟩
  exact (Finset.sum_le_sum fun l hl => (hq hl).2.1).trans <|
    (Finset.sum_image fun x hx y hy hxy => hinj hx hy <| by
      have e : a x / m = a y / m := hxy; rw [← (hq hx).1, ← (hq hy).1, e]).symm.trans_le <|
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.image_subset_iff.mpr fun _ hl => (hq hl).2.2) fun q _ _ => hG0 q

theorem sum_split (m : ℕ) (hm : 4 ≤ m) (S : Finset ℕ) (N : ℕ)
    (hS : ∀ l ∈ S, 2 ≤ l ∧ l ≤ N ∧ (l % m = 1 ∨ (l + 1) % m = 0))
    (F G : ℕ → ℝ) (hG0 : ∀ q, 0 ≤ G q)
    (hFG : ∀ l ∈ S, ∀ q : ℕ, 1 ≤ q → (l = m * q + 1 ∨ l + 1 = m * q) → F l ≤ G q) :
    ∑ l ∈ S, F l ≤ 2 * ∑ q ∈ Finset.Icc 1 N, G q := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not S (fun l => l % m = 1), two_mul]
  refine add_le_add (sum_filter_le_Icc hm (· - 1) hG0 ?_ ?_) (sum_filter_le_Icc hm (· + 1) hG0 ?_ ?_)
  · intro x hx y hy hxy; have := (hS x (Finset.mem_filter.mp hx).1).1
    have := (hS y (Finset.mem_filter.mp hy).1).1; dsimp at hxy; omega
  · intro l hl; obtain ⟨hlS, hl1⟩ := Finset.mem_filter.mp hl; obtain ⟨h2, hN, -⟩ := hS l hlS
    have hd := Nat.div_add_mod l m; rw [hl1] at hd
    exact ⟨by omega, by omega, by rw [show l - 1 = m * (l / m) by omega, Nat.mul_mod_right],
      fun hmq hq1 => hFG l hlS _ hq1 (Or.inl (by omega))⟩
  · intro x _ y _ hxy; dsimp at hxy; omega
  · intro l hl; obtain ⟨hlS, hn1⟩ := Finset.mem_filter.mp hl; obtain ⟨_, hN, hor⟩ := hS l hlS
    exact ⟨by omega, by omega, hor.resolve_left hn1, fun hmq hq1 => hFG l hlS _ hq1 (Or.inr hmq.symm)⟩

theorem size_of_form (m q l : ℕ) (hm : 4 ≤ m) (hq : 1 ≤ q) (h : l = m * q + 1 ∨ l + 1 = m * q) :
    (3 / 4 : ℝ) * ((m : ℝ) * q) ≤ l ∧ (l : ℝ) ≤ 2 * ((m : ℝ) * q) := by
  have hP : (4 : ℝ) ≤ (m : ℝ) * q := by exact_mod_cast Nat.mul_le_mul hm hq
  rcases h with rfl | h
  · push_cast; constructor <;> linarith
  · have hl : (l : ℝ) + 1 = (m : ℝ) * q := by exact_mod_cast h
    constructor <;> linarith

theorem sum_sq_bound (m : ℕ) (hm : 4 ≤ m) (S : Finset ℕ)
    (hS : ∀ l ∈ S, 2 ≤ l ∧ (l % m = 1 ∨ (l + 1) % m = 0)) :
    ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2 ≤
      2 * (16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) * 2 + 2)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hB := add_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (Real.log_natCast_nonneg m)
  have hFG (l : ℕ) (hl : l ∈ S) (q : ℕ) (hq : 1 ≤ q) (hlq : l = m * q + 1 ∨ l + 1 = m * q) :
      Real.log l / (l : ℝ) ^ 2 ≤ 16 / 9 / (m : ℝ) ^ 2 *
        ((Real.log 2 + Real.log m) / (q : ℝ) ^ 2 + Real.log q / (q : ℝ) ^ 2) := by
    have hsz := size_of_form m q l hm hq hlq; have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (hS l hl).1
    have hlog : Real.log l ≤ Real.log 2 + Real.log m + Real.log q := by
      rw [← Real.log_mul (by norm_num) hm0.ne', ← Real.log_mul (by positivity) hq0.ne']
      exact Real.log_le_log (by linarith) (by linarith [hsz.2])
    have hc : (0 : ℝ) < (3 / 4 : ℝ) * ((m : ℝ) * q) := by positivity
    exact ((div_le_div_of_nonneg_right hlog (sq_nonneg _)).trans
      (div_le_div_of_nonneg_left ((Real.log_nonneg (by linarith)).trans hlog)
        (sq_pos_of_pos hc) (pow_le_pow_left₀ hc.le hsz.1 2))).trans_eq (by field_simp; ring)
  calc ∑ l ∈ S, Real.log l / (l : ℝ) ^ 2
      ≤ 2 * ∑ q ∈ Finset.Icc 1 (S.sup id), 16 / 9 / (m : ℝ) ^ 2 *
          ((Real.log 2 + Real.log m) / (q : ℝ) ^ 2 + Real.log q / (q : ℝ) ^ 2) :=
        sum_split m hm S (S.sup id) (fun l hl => ⟨(hS l hl).1, Finset.le_sup (f := id) hl, (hS l hl).2⟩)
          _ _ (fun q => mul_nonneg (by positivity) (add_nonneg (div_nonneg hB (sq_nonneg _))
            (div_nonneg (Real.log_natCast_nonneg q) (sq_nonneg _)))) hFG
    _ = 2 * (16 / 9 / (m : ℝ) ^ 2 *
          ((Real.log 2 + Real.log m) * (∑ q ∈ Finset.Icc 1 (S.sup id), (1 : ℝ) / (q : ℝ) ^ 2) +
            ∑ q ∈ Finset.Icc 1 (S.sup id), Real.log q / (q : ℝ) ^ 2)) := by
        congr 1; simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ 2 * (16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) * 2 + 2)) := by
        have := sum_inv_sq_le (S.sup id); have := sum_log_sq_le (S.sup id); gcongr

theorem sum_lin_bound (m : ℕ) (hm : 4 ≤ m) (S : Finset ℕ) (N : ℕ) (Y : ℝ) (hN : 1 ≤ N)
    (hNY : (N : ℝ) ≤ Y) (hS : ∀ l ∈ S, 2 ≤ l ∧ l ≤ N ∧ (l % m = 1 ∨ (l + 1) % m = 0)) :
    ∑ l ∈ S, Real.log l / (l : ℝ) ≤ 2 * (4 / 3 * Real.log Y / (m : ℝ) * (1 + Real.log Y)) := by
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hN1 : (1 : ℝ) ≤ N := Nat.one_le_cast.2 hN; have hlY := Real.log_nonneg (by linarith : 1 ≤ Y)
  have hFG (l : ℕ) (hl : l ∈ S) (q : ℕ) (hq : 1 ≤ q) (hlq : l = m * q + 1 ∨ l + 1 = m * q) :
      Real.log l / (l : ℝ) ≤ 4 / 3 * Real.log Y / (m : ℝ) * (1 / (q : ℝ)) := by
    have hsz := size_of_form m q l hm hq hlq; have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
    have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast (hS l hl).1
    have hlN : (l : ℝ) ≤ N := by exact_mod_cast (hS l hl).2.1
    exact ((div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith))
      (by linarith)).trans (div_le_div_of_nonneg_left hlY (by positivity) hsz.1)).trans_eq (by field_simp)
  calc ∑ l ∈ S, Real.log l / (l : ℝ)
      ≤ 2 * ∑ q ∈ Finset.Icc 1 N, 4 / 3 * Real.log Y / (m : ℝ) * (1 / (q : ℝ)) :=
        sum_split m hm S N hS _ _ (fun _ => by positivity) hFG
    _ = 2 * (4 / 3 * Real.log Y / (m : ℝ) * ∑ q ∈ Finset.Icc 1 N, (1 : ℝ) / (q : ℝ)) := by
        congr 1; rw [← Finset.mul_sum]
    _ ≤ 2 * (4 / 3 * Real.log Y / (m : ℝ) * (1 + Real.log Y)) := by
        have := (sum_inv_le N hN).trans (add_le_add_right (Real.log_le_log (by positivity) hNY) 1); gcongr

theorem coprime_two {l : ℕ} (hl : l.Prime) (h2 : l ≠ 2) : Nat.Coprime l 2 :=
  (Nat.coprime_primes hl Nat.prime_two).mpr h2
theorem hOf_ord (e l : ℕ) (hl : Nat.Coprime l 2) :
    ordH (hOf e l) = orderOf (hcl e (ZMod.unitOfCoprime l (Nat.Coprime.pow_right (e + 2) hl))) := by
  simp only [hOf, dite_eq_left hl, ordH, ← orderOf_iotaH, iotaH_iotaHInv]

private theorem two_pow_dvd_sq_pm_one_iff_of_odd (x : ℤ) (hx : Odd x) (N : ℕ) :
    ((2 : ℤ) ^ N ∣ x ^ 2 - 1 ∨ (2 : ℤ) ^ N ∣ x ^ 2 + 1) ↔
      ((2 : ℤ) ^ (N - 1) ∣ x - 1 ∨ (2 : ℤ) ^ (N - 1) ∣ x + 1) := by
  obtain ⟨k, rfl⟩ := hx; rcases N with _ | _ | n
  · simp
  · exact iff_of_true (Or.inl ⟨2 * k ^ 2 + 2 * k, by ring⟩) (by simp)
  · rw [show n + 1 + 1 - 1 = n + 1 by omega]; constructor
    · rintro (⟨c, hc⟩ | ⟨c, hc⟩)
      · have hkk : k * (k + 1) = 2 ^ n * c :=
          mul_left_cancel₀ (by norm_num : (4 : ℤ) ≠ 0) (by linear_combination hc)
        rcases Int.even_or_odd k with ⟨r, hr⟩ | ⟨r, hr⟩
        · obtain ⟨d, hd⟩ := (show IsCoprime (2 : ℤ) (k + 1) from
            ⟨-r, 1, by rw [hr]; ring⟩).pow_left.dvd_of_dvd_mul_right ⟨c, hkk⟩
          exact Or.inl ⟨d, by linear_combination 2 * hd⟩
        · obtain ⟨d, hd⟩ := (show IsCoprime (2 : ℤ) k from
            ⟨-r, 1, by rw [hr]; ring⟩).pow_left.dvd_of_dvd_mul_left ⟨c, hkk⟩
          exact Or.inr ⟨d, by linear_combination 2 * hd⟩
      · exfalso
        have : (2 : ℤ) * (2 * (2 ^ n * c - k ^ 2 - k)) = 2 * 1 := by linear_combination -hc
        omega
    · rintro (⟨d, hd⟩ | ⟨d, hd⟩)
      · exact Or.inl ⟨d + 2 ^ n * d ^ 2, by linear_combination (2 * k + 2 ^ (n + 1) * d + 2) * hd⟩
      · exact Or.inl ⟨-d + 2 ^ n * d ^ 2, by linear_combination (2 * k + 2 ^ (n + 1) * d) * hd⟩
private theorem two_pow_dvd_pow_two_pow_pm_one_iff_of_odd (x : ℤ) (hx : Odd x) (j : ℕ) :
    ∀ N : ℕ, ((2 : ℤ) ^ N ∣ x ^ (2 ^ j) - 1 ∨ (2 : ℤ) ^ N ∣ x ^ (2 ^ j) + 1) ↔
      ((2 : ℤ) ^ (N - j) ∣ x - 1 ∨ (2 : ℤ) ^ (N - j) ∣ x + 1) := by
  induction j with
  | zero => intro N; simp
  | succ j ih =>
    intro N; rw [pow_succ, pow_mul, two_pow_dvd_sq_pm_one_iff_of_odd _ hx.pow N, ih (N - 1),
      show N - 1 - j = N - (j + 1) by omega]
private theorem intCast_eq_pm_one_zmod_two_pow_iff (M : ℕ) (a : ℤ) :
    ((a : ZMod (2 ^ M)) = 1 ∨ (a : ZMod (2 ^ M)) = -1) ↔
      ((2 : ℤ) ^ M ∣ a - 1 ∨ (2 : ℤ) ^ M ∣ a + 1) := by
  rw [← Int.cast_one, ← Int.cast_neg, ZMod.intCast_eq_intCast_iff_dvd_sub,
    ZMod.intCast_eq_intCast_iff_dvd_sub, show ((2 ^ M : ℕ) : ℤ) = (2 : ℤ) ^ M by norm_num,
    dvd_sub_comm, show (-1 : ℤ) - a = -(a + 1) by ring, dvd_neg]

theorem ord_pow (e : ℕ) (x : ZMod (2 ^ e)) : ∃ k ≤ e, ordH x = 2 ^ k :=
  (Nat.dvd_prime_pow Nat.prime_two).mp <|
    addOrderOf_dvd_of_nsmul_eq_zero (by rw [nsmul_eq_mul, ZMod.natCast_self (2 ^ e), zero_mul])
theorem ord_le_iff (e l j : ℕ) (hl : Nat.Coprime l 2) :
    ordH (hOf e l) ≤ 2 ^ j ↔
      ((l : ZMod (2 ^ (e + 2 - j))) = 1 ∨ (l : ZMod (2 ^ (e + 2 - j))) = -1) := by
  obtain ⟨k, -, hk⟩ := ord_pow e (hOf e l); have hord := hOf_ord e l hl; rw [hk] at hord ⊢
  rw [Nat.pow_le_pow_iff_right (by norm_num : 1 < 2),
    ← Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2), hord, orderOf_dvd_iff_pow_eq_one,
    hcl, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_zpowers_iff]
  have hmem : ∀ u : (ZMod (2 ^ (e + 2)))ˣ, (∃ m : ℤ, (-1) ^ m = u) ↔ u = 1 ∨ u = -1 := fun u =>
    ⟨fun ⟨m, hm⟩ => hm ▸ (Int.even_or_odd m).imp Even.neg_one_zpow Odd.neg_one_zpow,
      by rintro (rfl | rfl); exacts [⟨0, zpow_zero _⟩, ⟨1, zpow_one _⟩]⟩
  rw [hmem]; simp only [Units.ext_iff, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
    Units.val_one, Units.val_neg]
  have h1 := intCast_eq_pm_one_zmod_two_pow_iff (e + 2) ((l : ℤ) ^ (2 ^ j))
  have h2 := intCast_eq_pm_one_zmod_two_pow_iff (e + 2 - j) (l : ℤ)
  push_cast at h1 h2; rw [h1, h2]
  exact two_pow_dvd_pow_two_pow_pm_one_iff_of_odd (l : ℤ)
    ((Int.odd_natCast l).2 (Nat.coprime_two_right.1 hl)) j (e + 2)
theorem nsmul_iff (e l j : ℕ) (hl : Nat.Coprime l 2) :
    (2 ^ j : ℕ) • hOf e l = 0 ↔ ordH (hOf e l) ≤ 2 ^ j := by
  let _ := hl; obtain ⟨k, -, hk'⟩ := ord_pow e (hOf e l); unfold ordH at hk' ⊢
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hk', Nat.pow_dvd_pow_iff_le_right (by norm_num),
    Nat.pow_le_pow_iff_right (by norm_num)]

theorem mod_form (m l : ℕ) (hm : 4 ≤ m) (h : (l : ZMod m) = 1 ∨ (l : ZMod m) = -1) :
    l % m = 1 ∨ (l + 1) % m = 0 := by
  rcases h with h | h
  · have h' : ((l : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by rw [h, Nat.cast_one]
    rw [ZMod.natCast_eq_natCast_iff'] at h'; exact Or.inl (by rw [h', Nat.mod_eq_of_lt (by omega)])
  · have h' : ((l + 1 : ℕ) : ZMod m) = ((0 : ℕ) : ZMod m) := by push_cast; rw [h]; ring
    rw [ZMod.natCast_eq_natCast_iff'] at h'; exact Or.inr (by rw [h', Nat.zero_mod])
theorem le_of_form (m l : ℕ) (hl : 2 ≤ l) (h : l % m = 1 ∨ (l + 1) % m = 0) : m ≤ l + 1 := by
  rcases lt_or_ge (l + 1) m with hc | hc
  · rcases h with h | h <;> rw [Nat.mod_eq_of_lt (by omega)] at h <;> omega
  · exact hc

theorem modulus (e : ℕ) (J : ℝ) (hJ : 1 ≤ J) :
    ∃ m : ℕ, 4 ≤ m ∧ m ≤ 4 * 2 ^ e ∧ 4 * ((2 ^ e : ℕ) : ℝ) ≤ m * J ∧
      ∀ l : ℕ, l.Prime → l ≠ 2 → (ordH (hOf e l) : ℝ) ≤ J → (l % m = 1 ∨ (l + 1) % m = 0) := by
  classical
  set K := Nat.findGreatest (fun k => (2 : ℝ) ^ k ≤ J) e
  have hKe : K ≤ e := Nat.findGreatest_le e
  have hKJ : (2 : ℝ) ^ K ≤ J :=
    Nat.findGreatest_spec (P := fun k => (2 : ℝ) ^ k ≤ J) (Nat.zero_le e) (by simpa using hJ)
  have hm4 : 4 ≤ 2 ^ (e + 2 - K) :=
    (show 4 = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
  refine ⟨2 ^ (e + 2 - K), hm4,
    (Nat.pow_le_pow_right (by norm_num) (by omega : e + 2 - K ≤ e + 2)).trans_eq (by ring), ?_, ?_⟩
  · calc 4 * ((2 ^ e : ℕ) : ℝ) = ((2 ^ (e + 2 - K) : ℕ) : ℝ) * (2 : ℝ) ^ K := by
          push_cast; rw [← pow_add, show e + 2 - K + K = e + 2 by omega]; ring
      _ ≤ ((2 ^ (e + 2 - K) : ℕ) : ℝ) * J := by gcongr
  · intro l hl h2 hord; obtain ⟨k, hk, hk'⟩ := ord_pow e (hOf e l)
    have hkJ : (2 : ℝ) ^ k ≤ J := by rw [hk'] at hord; exact_mod_cast hord
    exact mod_form _ l hm4 <| (ord_le_iff e l K (coprime_two hl h2)).mp <| hk' ▸
      Nat.pow_le_pow_right (by norm_num) (Nat.le_findGreatest (P := fun k => (2 : ℝ) ^ k ≤ J) hk hkJ)

theorem log_n_ge (e : ℕ) (he : 2 ≤ e) : 2 * Real.log 2 ≤ Real.log ((2 ^ e : ℕ) : ℝ) := by
  rw [← show Real.log 4 = 2 * Real.log 2 by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num]
  exact Real.log_le_log (by norm_num)
    (by exact_mod_cast (show 4 = 2 ^ 2 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) he)

theorem square_term_le (e : ℕ) (he : 2 ≤ e) (m : ℕ) (hm4 : 4 ≤ m) (hmle : m ≤ 4 * 2 ^ e) (J : ℝ)
    (hJ : 1 ≤ J) (hmJ : 4 * ((2 ^ e : ℕ) : ℝ) ≤ m * J) :
    2 * (16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) * 2 + 2)) ≤
      100 * J ^ 2 * Real.log ((2 ^ e : ℕ) : ℝ) / (((2 ^ e : ℕ) : ℝ)) ^ 2 := by
  let _ := hJ; set n : ℝ := ((2 ^ e : ℕ) : ℝ) with hn
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 (by omega); have hn0 : (0 : ℝ) < n := by positivity
  have hLn := log_n_ge e he; have hl2 := Real.log_two_gt_d9
  have hlm : Real.log m ≤ 2 * Real.log 2 + Real.log n := by
    rw [← show Real.log (4 * n) = 2 * Real.log 2 + Real.log n by
      rw [Real.log_mul (by norm_num) hn0.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num]
    exact Real.log_le_log hm0 (by rw [hn]; exact_mod_cast hmle)
  have hK : (Real.log 2 + Real.log m) * 2 + 2 ≤ 7 * Real.log n := by linarith
  rw [show (2 : ℝ) * (16 / 9 / (m : ℝ) ^ 2 * ((Real.log 2 + Real.log m) * 2 + 2)) =
    (32 / 9 * ((Real.log 2 + Real.log m) * 2 + 2)) / (m : ℝ) ^ 2 by ring,
    le_div_iff₀ (sq_pos_of_pos hn0), div_mul_eq_mul_div, div_le_iff₀ (sq_pos_of_pos hm0)]
  calc 32 / 9 * ((Real.log 2 + Real.log m) * 2 + 2) * n ^ 2
      ≤ 32 / 9 * (7 * Real.log n) * n ^ 2 := by gcongr
    _ = 14 / 9 * Real.log n * (4 * n) ^ 2 := by ring
    _ ≤ 100 * Real.log n * ((m : ℝ) * J) ^ 2 :=
        mul_le_mul (by linarith) (pow_le_pow_left₀ (by positivity) hmJ 2) (sq_nonneg _) (by linarith)
    _ = 100 * J ^ 2 * Real.log n * (m : ℝ) ^ 2 := by ring

theorem linear_term_le (e : ℕ) (he : 2 ≤ e) (m : ℕ) (hm4 : 4 ≤ m) (J Y : ℝ)
    (hJ : 1 ≤ J) (hY : 3 ≤ Y) (hmJ : 4 * ((2 ^ e : ℕ) : ℝ) ≤ m * J) :
    2 * (4 / 3 * Real.log Y / (m : ℝ) * (1 + Real.log Y)) ≤
      100 * J * Real.log (((2 ^ e : ℕ) : ℝ) * Y) ^ 2 / ((2 ^ e : ℕ) : ℝ) := by
  let _ := hJ; set n : ℝ := ((2 ^ e : ℕ) : ℝ)
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.2 (by omega); have hn0 : (0 : ℝ) < n := by positivity
  have hLn := log_n_ge e he; have hl2 := Real.log_two_gt_d9
  have hy0 := Real.log_nonneg (by linarith : 1 ≤ Y)
  have hM : Real.log (n * Y) = Real.log n + Real.log Y := Real.log_mul hn0.ne' (by positivity)
  have hq : Real.log Y * (1 + Real.log Y) ≤ Real.log (n * Y) * (2 * Real.log (n * Y)) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  rw [show (2 : ℝ) * (4 / 3 * Real.log Y / (m : ℝ) * (1 + Real.log Y)) =
    (8 / 3 * (Real.log Y * (1 + Real.log Y))) / (m : ℝ) by ring,
    le_div_iff₀ hn0, div_mul_eq_mul_div, div_le_iff₀ hm0]
  calc 8 / 3 * (Real.log Y * (1 + Real.log Y)) * n
      ≤ 8 / 3 * (Real.log (n * Y) * (2 * Real.log (n * Y))) * n := by gcongr
    _ = 4 / 3 * Real.log (n * Y) ^ 2 * (4 * n) := by ring
    _ ≤ 100 * Real.log (n * Y) ^ 2 * ((m : ℝ) * J) :=
        mul_le_mul (by linarith [sq_nonneg (Real.log (n * Y))]) hmJ (by positivity) (by positivity)
    _ = 100 * J * Real.log (n * Y) ^ 2 * m := by ring
end PrimeReciprocalSums

open PrimeReciprocalSums

theorem generic_frames_letters (D : D7) : Conclusion4 D 100 := by
  set e := D.R.e; have he : 2 ≤ e := D.host.two_le_e
  refine ⟨fun l hl h2 j hj => ?_, fun J hJ l hl h2 hord => ?_, fun J hJ S hS => ?_, fun J hJ Y => ?_⟩
  · have hc := coprime_two hl h2
    rw [show 4 * 2 ^ e / 2 ^ j = 2 ^ (e + 2 - j) by
      rw [show 4 * 2 ^ e = 2 ^ (e + 2) by ring, Nat.pow_div (by omega) (by norm_num)],
      nsmul_iff e l j hc, ord_le_iff e l j hc]
  · obtain ⟨m, -, -, hmJ, hmod⟩ := modulus e J hJ
    have h1' : (m : ℝ) ≤ l + 1 := by exact_mod_cast le_of_form m l hl.two_le (hmod l hl h2 hord)
    have hJ0 : 0 < J := by linarith
    rw [sub_le_iff_le_add, div_le_iff₀ hJ0]; exact hmJ.trans (mul_le_mul_of_nonneg_right h1' hJ0.le)
  · obtain ⟨m, hm4, hmle, hmJ, hmod⟩ := modulus e J hJ
    exact (sum_sq_bound m hm4 S
      (fun l hl => ⟨(hS l hl).1.two_le, hmod l (hS l hl).1 (hS l hl).2.1 (hS l hl).2.2⟩)).trans
      (square_term_le e he m hm4 hmle J hJ hmJ)
  · obtain ⟨m, hm4, -, hmJ, hmod⟩ := modulus e J hJ
    rcases lt_or_ge Y 3 with hY | hY
    · rw [Finset.sum_eq_zero fun l hl => by
        rw [Finset.mem_filter, Finset.mem_range] at hl
        have := (Nat.floor_lt' (by norm_num)).2 (by exact_mod_cast hY : Y < (3 : ℕ))
        have := hl.2.1.two_le; exact absurd (by omega : l = 2) hl.2.2.1]
      exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (sq_nonneg _)) (by positivity)
    · exact (sum_lin_bound m hm4 _ ⌊Y⌋₊ Y ((Nat.one_le_floor_iff Y).2 (by linarith))
        (Nat.floor_le (by linarith)) fun l hl => by
          rw [Finset.mem_filter, Finset.mem_range] at hl
          exact ⟨hl.2.1.two_le, by omega, hmod l hl.2.1 hl.2.2.1 hl.2.2.2⟩).trans
        (linear_term_le e he m hm4 J Y hJ hY hmJ)
end Formalism.MainNotions.UnusedSlot33
end
