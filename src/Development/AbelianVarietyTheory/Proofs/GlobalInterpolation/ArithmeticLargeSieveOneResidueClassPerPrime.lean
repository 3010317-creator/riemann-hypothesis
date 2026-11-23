module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Totient
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultiplicativeLargeSieve
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Algebra.Order.Chebyshev

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

namespace GlobalTheory

private lemma totient_mul_sigma_pow_le_pow_succ (K n : ℕ) (hn : 0 < n) : n.totient * sigma 1 (n ^ K) ≤ n ^ (K + 1) := by
  induction n using Nat.recOnPosPrimePosCoprime with
  | prime_pow p a hp ha =>
    rw [← pow_mul, sigma_one_apply_prime_pow hp, Nat.totient_prime_pow hp ha, mul_assoc]
    have key : (p - 1) * ∑ i ∈ Finset.range (a * K + 1), p ^ i = p ^ (a * K + 1) - 1 := by
      zify [hp.one_le, Nat.one_le_pow _ _ hp.pos]; rw [mul_comm, geom_sum_mul]
    rw [key, ← pow_mul]; refine (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans_eq ?_
    rw [← pow_add]; congr 1; cases a with | zero => omega | succ a => simp; ring
  | zero => omega
  | one => simp
  | coprime a b ha hb hab iha ihb =>
    rw [mul_pow, Nat.totient_mul hab, isMultiplicative_sigma.map_mul_of_coprime (hab.pow K K), mul_pow]
    exact (by ring : _ = (a.totient * sigma 1 (a ^ K)) * (b.totient * sigma 1 (b ^ K))).trans_le (Nat.mul_le_mul (iha ha.pos) (ihb hb.pos))

private lemma sum_inv_le_mul_sum_squarefree_inv_totient (Q q : ℕ) (hq : 1 ≤ q) :
    ∑ n ∈ Finset.Icc 1 Q, (1 : ℝ) / n ≤ ((q : ℝ) / q.totient) *
      ∑ f ∈ (Finset.Icc 1 Q).filter (fun f => Squarefree f ∧ Nat.Coprime f q), (1 : ℝ) / f.totient := by
  set D := (Finset.Icc 1 Q).filter fun f => Squarefree f ∧ Nat.Coprime f q with hD
  set g : ℕ → ℕ := fun n => ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ q), p
  have hsq : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → Squarefree (∏ p ∈ s, p) := fun s hs => by
    rw [Nat.squarefree_iff_prime_squarefree]; intro x hx hxx
    have hmem : ∀ {t}, t ⊆ s → x ∣ ∏ p ∈ t, p → x ∈ t := fun ht hd => by
      obtain ⟨p, hp, hxp⟩ := (Prime.dvd_finsetProd_iff hx.prime _).1 hd; rwa [(Nat.prime_dvd_prime_iff_eq hx (hs p (ht hp))).1 hxp]
    rw [← Finset.mul_prod_erase s (fun p => p) (hmem subset_rfl ((dvd_mul_right x x).trans hxx))] at hxx
    have := hmem (Finset.erase_subset _ _) (Nat.dvd_of_mul_dvd_mul_left hx.pos hxx); simp at this
  have hgdvd : ∀ n, g n ∣ n := fun n => (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)).trans (Nat.prod_primeFactors_dvd n)
  have hgD : ∀ n ∈ Finset.Icc 1 Q, g n ∈ D := fun n hn => by
    rw [Finset.mem_Icc] at hn
    exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨Nat.pos_of_dvd_of_pos (hgdvd n) hn.1, (Nat.le_of_dvd hn.1 (hgdvd n)).trans hn.2⟩,
      hsq _ fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1,
      Nat.Coprime.prod_left fun p hp => (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1).coprime_iff_not_dvd.2 (Finset.mem_filter.1 hp).2⟩
  rw [← Finset.sum_fiberwise_of_maps_to hgD, Finset.mul_sum]; refine Finset.sum_le_sum fun f hf => ?_
  rw [hD, Finset.mem_filter, Finset.mem_Icc] at hf; set N := (f * q) ^ Q with hN
  have hfq0 : f * q ≠ 0 := (Nat.mul_pos hf.1.1 hq).ne'; have hN0 : N ≠ 0 := pow_ne_zero _ hfq0
  have hfib : ∀ n ∈ (Finset.Icc 1 Q).filter (fun n => g n = f), f ∣ n ∧ n ∣ N := fun n hn => by
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    refine ⟨hn.2 ▸ hgdvd n, ((Nat.factorization_le_iff_dvd (by omega) (pow_ne_zero n hfq0)).1 fun p => ?_).trans (pow_dvd_pow _ hn.1.2)⟩
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    by_cases hp : p.Prime ∧ p ∣ n
    · have hpdiv : p ∣ f * q := if hpq : p ∣ q then dvd_mul_of_dvd_right hpq _
        else dvd_mul_of_dvd_left (hn.2 ▸ Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hp.1.mem_primeFactors hp.2 (by omega), hpq⟩)) _
      exact (Nat.factorization_lt p (by omega : n ≠ 0)).le.trans (Nat.le_mul_of_pos_right _ ((hp.1.dvd_iff_one_le_factorization hfq0).1 hpdiv))
    · rw [if hp' : p.Prime then Nat.factorization_eq_zero_of_not_dvd fun hd => hp ⟨hp', hd⟩ else Nat.factorization_eq_zero_of_not_prime _ hp']; exact Nat.zero_le _
  calc ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => g n = f), (1 : ℝ) / n
      = ∑ m ∈ ((Finset.Icc 1 Q).filter (fun n => g n = f)).image (· / f), (1 : ℝ) / (f * m) := by
        rw [Finset.sum_image fun x hx y hy hxy => (Nat.div_left_inj (hfib x hx).1 (hfib y hy).1).1 hxy]
        exact Finset.sum_congr rfl fun n hn => by rw [← Nat.cast_mul, Nat.mul_div_cancel' (hfib n hn).1]
    _ ≤ ∑ m ∈ N.divisors, (1 : ℝ) / (f * m) := Finset.sum_le_sum_of_subset_of_nonneg
        (fun m hm => by obtain ⟨n, hn, rfl⟩ := Finset.mem_image.1 hm; exact Nat.mem_divisors.2 ⟨(Nat.div_dvd_of_dvd (hfib n hn).1).trans (hfib n hn).2, hN0⟩) fun _ _ _ => by positivity
    _ = (1 / f) * ((sigma 1 N : ℝ) / N) := by
        rw [sigma_one_apply, Nat.cast_sum, Finset.sum_div, ← Nat.sum_div_divisors, Finset.mul_sum]; refine Finset.sum_congr rfl fun d hd => ?_
        have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.pos_of_mem_divisors hd).ne'
        have hN0' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hN0
        rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0]; field_simp
    _ ≤ (q : ℝ) / q.totient * (1 / f.totient) := by
        have := hf.1.1; rw [hN, mul_pow, isMultiplicative_sigma.map_mul_of_coprime (hf.2.2.pow Q Q), one_div_mul_eq_div, div_div, mul_one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        exact_mod_cast (by ring : (sigma 1 (f ^ Q) * sigma 1 (q ^ Q)) * (q.totient * f.totient) = (f.totient * sigma 1 (f ^ Q)) * (q.totient * sigma 1 (q ^ Q))).trans_le
          ((Nat.mul_le_mul (totient_mul_sigma_pow_le_pow_succ Q f hf.1.1) (totient_mul_sigma_pow_le_pow_succ Q q hq)).trans_eq (by ring))

private lemma norm_sum_sq_le_pred_mul_of_avoids_class (p : ℕ) (hp : p.Prime) (c : ℕ) (S : Finset ℕ) (b : ℕ → ℂ) (hS : ∀ n ∈ S, ¬ n ≡ c [MOD p]) :
    ‖∑ n ∈ S, b n‖ ^ 2 ≤ (p - 1 : ℝ) * ∑ a ∈ (Finset.range p).erase 0, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / p)‖ ^ 2 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  set ψ : AddChar (ZMod p) ℂ := ZMod.stdAddChar
  set B : ZMod p → ℂ := fun r => ∑ n ∈ S.filter (fun n : ℕ => (n : ZMod p) = r), b n
  have hconj : ∀ u : ZMod p, starRingEnd ℂ (ψ u) = ψ (-u) := fun u => by
    dsimp only [ψ]; rw [← ZMod.natCast_zmod_val u, ← Int.cast_natCast, ZMod.stdAddChar_coe, ← Complex.exp_conj, ← Int.cast_neg, ZMod.stdAddChar_coe]
    congr 1; push_cast; simp only [map_mul, map_div₀, conj_ofReal, conj_I, map_natCast, map_ofNat]; ring
  have hgroup : ∀ a : ℕ, ∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / p) = ∑ r : ZMod p, B r * ψ (r * a) := fun a => by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun n : ℕ => (n : ZMod p)) (fun _ _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl fun r _ => ?_; dsimp only [B, ψ]; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun n hn => ?_
    have hcoe := ZMod.stdAddChar_coe (N := p) ((n * a : ℕ) : ℤ); push_cast at hcoe; rw [← (Finset.mem_filter.1 hn).2, hcoe]; congr 2; ring
  have hpar : ∑ a ∈ Finset.range p, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / p)‖ ^ 2 = p * ∑ r : ZMod p, ‖B r‖ ^ 2 := by
    simp_rw [hgroup]
    rw [show ∑ a ∈ Finset.range p, ‖∑ r : ZMod p, B r * ψ (r * a)‖ ^ 2 = ∑ a : ZMod p, ‖∑ r : ZMod p, B r * ψ (r * a)‖ ^ 2 from
      Finset.sum_nbij' (fun a => (a : ZMod p)) ZMod.val (fun _ _ => Finset.mem_univ _) (fun a _ => Finset.mem_range.2 (ZMod.val_lt a))
        (fun a ha => ZMod.val_cast_of_lt (Finset.mem_range.1 ha)) (fun _ _ => ZMod.natCast_zmod_val _) fun _ _ => rfl]
    apply Complex.ofReal_injective; push_cast; simp_rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, map_mul, hconj]
    rw [Finset.sum_comm, Finset.mul_sum]; refine Finset.sum_congr rfl fun r _ => ?_; rw [Finset.sum_comm]
    have horth : ∀ s : ZMod p, ∑ a : ZMod p, B r * ψ (r * a) * (starRingEnd ℂ (B s) * ψ (-(s * a))) =
        if r = s then p * (B r * starRingEnd ℂ (B s)) else 0 := fun s => by
      have hmul : ∀ a : ZMod p, B r * ψ (r * a) * (starRingEnd ℂ (B s) * ψ (-(s * a))) = B r * starRingEnd ℂ (B s) * ψ (a * (r - s)) := fun a => by
        calc B r * ψ (r * a) * (starRingEnd ℂ (B s) * ψ (-(s * a))) = B r * starRingEnd ℂ (B s) * (ψ (r * a) * ψ (-(s * a))) := by ring
          _ = B r * starRingEnd ℂ (B s) * ψ (a * (r - s)) := by rw [← AddChar.map_add_eq_mul]; congr 2; ring
      simp_rw [hmul, ← Finset.mul_sum]; rw [AddChar.sum_mulShift (r - s) (ZMod.isPrimitive_stdAddChar p), ZMod.card]
      by_cases hrs : r = s; · subst hrs; simp [mul_comm]
      · simp [sub_eq_zero, hrs]
    simp [horth, Complex.mul_conj']
  rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hp.pos)] at hpar
  simp only [Nat.cast_zero, mul_zero, zero_div, Complex.exp_zero, mul_one] at hpar
  have hc : B c = 0 := by dsimp only [B]; rw [Finset.filter_false_of_mem fun n hn h => hS n hn ((ZMod.natCast_eq_natCast_iff n c p).1 h)]; simp
  have hcs : ‖∑ n ∈ S, b n‖ ^ 2 ≤ (p - 1 : ℝ) * ∑ r : ZMod p, ‖B r‖ ^ 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := fun n : ℕ => (n : ZMod p)) (fun _ _ => Finset.mem_univ _) b, ← Finset.sum_erase _ hc]
    calc _ ≤ (∑ r ∈ Finset.univ.erase (c : ZMod p), ‖B r‖) ^ 2 := by gcongr; exact norm_sum_le _ _
      _ ≤ ((Finset.univ.erase (c : ZMod p)).card : ℝ) * ∑ r ∈ Finset.univ.erase (c : ZMod p), ‖B r‖ ^ 2 := sq_sum_le_card_mul_sum_sq
      _ ≤ (p - 1 : ℝ) * ∑ r : ZMod p, ‖B r‖ ^ 2 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card, Nat.cast_sub hp.one_le, Nat.cast_one]
          gcongr; exact sub_nonneg.2 (by exact_mod_cast hp.one_le); exact Finset.erase_subset _ _
  rw [← sub_nonneg]
  calc (0 : ℝ) ≤ p * ((p - 1) * ∑ r : ZMod p, ‖B r‖ ^ 2 - ‖∑ n ∈ S, b n‖ ^ 2) := mul_nonneg (Nat.cast_nonneg p) (sub_nonneg.2 hcs)
    _ = (p - 1) * (p * ∑ r : ZMod p, ‖B r‖ ^ 2) - p * ‖∑ n ∈ S, b n‖ ^ 2 := by ring
    _ = _ := by rw [← hpar]; ring

private lemma norm_sum_sq_le_totient_mul_of_avoids_classes (S : Finset ℕ) (d : ℕ) (hd : 0 < d)
    (hsq : Squarefree d) (hcl : ∀ p : ℕ, p.Prime → p ∣ d → ∃ c : ℕ, ∀ n ∈ S, ¬ n ≡ c [MOD p]) (b : ℕ → ℂ) :
    ‖∑ n ∈ S, b n‖ ^ 2 ≤ (d.totient : ℝ) * ∑ a ∈ (Finset.range d).filter d.Coprime, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / d)‖ ^ 2 := by
  induction d using Nat.strong_induction_on generalizing b with
  | _ d ih =>
  by_cases h1 : d = 1
  · subst h1; rw [show (Finset.range 1).filter (Nat.Coprime 1) = {0} by decide]; simp
  obtain ⟨p, hp, d₁, rfl⟩ := Nat.exists_prime_and_dvd h1; rw [mul_comm p d₁] at hsq hcl ⊢
  have hd₁ : 0 < d₁ := Nat.pos_of_ne_zero fun h => by subst h; simp at hd
  have hpd₁ : ¬ p ∣ d₁ := fun h => hp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p (Nat.mul_dvd_mul h dvd_rfl)))
  have hcop : Nat.Coprime d₁ p := (hp.coprime_iff_not_dvd.2 hpd₁).symm
  obtain ⟨c, hc⟩ := hcl p hp (dvd_mul_left _ _)
  have hd' : (d₁ : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hd₁.ne'; have hp' : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.pos.ne'
  have hmod : ∀ u v m, Nat.Coprime u (m % (u * v)) ↔ Nat.Coprime u m := fun u v m => by
    have hm : m % (u * v) + v * (m / (u * v)) * u = m := by
      have := Nat.mod_add_div m (u * v); linarith [mul_comm u v, mul_assoc u v (m / (u * v)), mul_comm (v * (m / (u * v))) u]
    conv_rhs => rw [← hm]
    exact (Nat.coprime_add_mul_right_right _ _ _).symm
  let R := ((Finset.range d₁).filter d₁.Coprime) ×ˢ ((Finset.range p).filter p.Coprime)
  have hmaps : ∀ x ∈ R, (x.1 * p + x.2 * d₁) % (d₁ * p) ∈ (Finset.range (d₁ * p)).filter (d₁ * p).Coprime := fun x hx => by
    simp only [R, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx ⊢
    refine ⟨Nat.mod_lt _ (Nat.mul_pos hd₁ hp.pos), Nat.Coprime.mul_left ?_ ?_⟩
    · rw [hmod, Nat.coprime_add_mul_right_right, Nat.coprime_mul_iff_right]; exact ⟨hx.1.2, hcop⟩
    · rw [mul_comm d₁ p, hmod, add_comm, Nat.coprime_add_mul_right_right, Nat.coprime_mul_iff_right]; exact ⟨hx.2.2, hcop.symm⟩
  have hinj : ∀ x ∈ R, ∀ y ∈ R, (x.1 * p + x.2 * d₁) % (d₁ * p) = (y.1 * p + y.2 * d₁) % (d₁ * p) → x = y := fun x hx y hy hxy => by
    simp only [R, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hx hy
    have hmod' : x.1 * p + x.2 * d₁ ≡ y.1 * p + y.2 * d₁ [MOD d₁ * p] := hxy
    have e1 := Nat.ModEq.cancel_right_of_coprime hcop (by simpa [Nat.ModEq, Nat.add_mul_mod_self_right] using hmod'.of_mul_right p)
    have e2 := Nat.ModEq.cancel_right_of_coprime hcop.symm (by simpa [Nat.ModEq, Nat.add_mul_mod_self_right] using hmod'.of_mul_left d₁)
    exact Prod.ext (by rw [Nat.ModEq, Nat.mod_eq_of_lt hx.1.1, Nat.mod_eq_of_lt hy.1.1] at e1; exact e1)
      (by rw [Nat.ModEq, Nat.mod_eq_of_lt hx.2.1, Nat.mod_eq_of_lt hy.2.1] at e2; exact e2)
  have hbij : ∑ a ∈ (Finset.range (d₁ * p)).filter (d₁ * p).Coprime, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a / ↑(d₁ * p))‖ ^ 2 =
      ∑ a₁ ∈ (Finset.range d₁).filter d₁.Coprime, ∑ a₂ ∈ (Finset.range p).filter p.Coprime,
        ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * ↑(a₁ * p + a₂ * d₁) / ↑(d₁ * p))‖ ^ 2 := by
    rw [← Finset.sum_product']; refine (Finset.sum_nbij _ hmaps hinj (fun z hz => ?_) fun x _ => ?_).symm
    · obtain ⟨x, hx, hxz⟩ := Finset.surj_on_of_inj_on_of_card_le _ hmaps (fun x y hx hy => hinj x hx y hy)
        (le_of_eq (by simp only [R]; rw [Finset.card_product, ← Nat.totient_eq_card_coprime, ← Nat.totient_eq_card_coprime, ← Nat.totient_eq_card_coprime, Nat.totient_mul hcop])) z hz
      exact ⟨x, hx, hxz.symm⟩
    · congr 2; refine Finset.sum_congr rfl fun n _ => ?_
      have hm : ((x.1 * p + x.2 * d₁ : ℕ) : ℂ) = (d₁ * p : ℕ) * ((x.1 * p + x.2 * d₁) / (d₁ * p) : ℕ) + ((x.1 * p + x.2 * d₁) % (d₁ * p) : ℕ) := by
        exact_mod_cast (Nat.div_add_mod (x.1 * p + x.2 * d₁) (d₁ * p)).symm
      generalize (x.1 * p + x.2 * d₁) / (d₁ * p) = k at hm; congr 1
      exact Complex.exp_eq_exp_iff_exists_int.2 ⟨(n * k : ℕ), by rw [hm]; push_cast; field_simp; ring⟩
  have hcrt : ∀ a₁ a₂ n : ℕ, cexp (2 * ↑Real.pi * I * n * ↑(a₁ * p + a₂ * d₁) / ↑(d₁ * p)) =
      cexp (2 * ↑Real.pi * I * n * a₁ / d₁) * cexp (2 * ↑Real.pi * I * n * a₂ / p) := fun _ _ _ => by rw [← Complex.exp_add]; congr 1; push_cast; field_simp
  have herase : (Finset.range p).filter p.Coprime = (Finset.range p).erase 0 := by
    ext a; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_erase, hp.coprime_iff_not_dvd]
    exact ⟨fun ⟨h1, h2⟩ => ⟨by rintro rfl; exact h2 (dvd_zero p), h1⟩, fun ⟨h0, h1⟩ => ⟨h1, fun hd => h0 (Nat.eq_zero_of_dvd_of_lt hd h1)⟩⟩
  rw [hbij]; simp_rw [hcrt, herase, Nat.totient_mul hcop, Nat.totient_prime hp]
  calc ‖∑ n ∈ S, b n‖ ^ 2 ≤ (d₁.totient : ℝ) * ∑ a₁ ∈ (Finset.range d₁).filter d₁.Coprime, ‖∑ n ∈ S, b n * cexp (2 * ↑Real.pi * I * n * a₁ / d₁)‖ ^ 2 :=
        ih d₁ (by rw [mul_comm]; exact lt_mul_of_one_lt_right hd₁ hp.one_lt) hd₁ (hsq.squarefree_of_dvd (dvd_mul_right _ _)) (fun q hq hqd => hcl q hq (dvd_mul_of_dvd_left hqd _)) b
    _ ≤ (d₁.totient : ℝ) * ∑ a₁ ∈ (Finset.range d₁).filter d₁.Coprime, (p - 1 : ℝ) * ∑ a₂ ∈ (Finset.range p).erase 0,
          ‖∑ n ∈ S, b n * (cexp (2 * ↑Real.pi * I * n * a₁ / d₁) * cexp (2 * ↑Real.pi * I * n * a₂ / p))‖ ^ 2 := by
        gcongr with a₁ _; simpa only [mul_assoc] using norm_sum_sq_le_pred_mul_of_avoids_class p hp c S (fun n => b n * cexp (2 * ↑Real.pi * I * n * a₁ / d₁)) hc
    _ = _ := by rw [← Finset.mul_sum]; push_cast [Nat.cast_sub hp.one_le]; ring

theorem _root_.GlobalTheory.arithmetic_large_sieve_one_class : ∀ (M N Q q : ℕ) (S : Finset ℕ), 1 ≤ Q → 1 ≤ q → S ⊆ Finset.Ioc M (M + N) →
    (∀ p : ℕ, p.Prime → p ≤ Q → ¬ p ∣ q → ∃ c : ℕ, ∀ n ∈ S, ¬ n ≡ c [MOD p]) →
    (S.card : ℝ) * ((q.totient : ℝ) / q * Real.log Q) ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N := by
  intro M N Q q S hQ hq hS hcl
  set D := (Finset.Icc 1 Q).filter fun f => Squarefree f ∧ Nat.Coprime f q with hD
  set Z : ℝ := (S.card : ℝ) with hZ
  have hZ0 : 0 ≤ Z := Nat.cast_nonneg _
  rcases hZ0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; positivity
  have hL : (q.totient : ℝ) / q * Real.log Q ≤ ∑ d ∈ D, (1 : ℝ) / d.totient := by
    have h1 := log_add_one_le_harmonic Q; rw [harmonic_eq_sum_Icc] at h1; push_cast at h1
    calc (q.totient : ℝ) / q * Real.log Q ≤ (q.totient : ℝ) / q * (((q : ℝ) / q.totient) * ∑ d ∈ D, (1 : ℝ) / d.totient) := by
          gcongr; exact ((Real.log_le_log (by exact_mod_cast hQ) (by linarith : (Q : ℝ) ≤ Q + 1)).trans (by simpa [one_div] using h1)).trans (sum_inv_le_mul_sum_squarefree_inv_totient Q q hq)
      _ = _ := by rw [← mul_assoc, show (q.totient : ℝ) / q * (q / q.totient) = 1 by field_simp, one_mul]
  set U : ℕ → ℝ := fun d => ∑ a ∈ (Finset.range d).filter d.Coprime, ‖∑ n ∈ S, (1 : ℂ) * cexp (2 * ↑Real.pi * I * n * a / d)‖ ^ 2
  have hmont : ∀ d ∈ D, Z ^ 2 * ((1 : ℝ) / d.totient) ≤ U d := fun d hd => by
    rw [hD, Finset.mem_filter, Finset.mem_Icc] at hd
    have h := norm_sum_sq_le_totient_mul_of_avoids_classes S d hd.1.1 hd.2.1
      (fun p hp hpd => hcl p hp ((Nat.le_of_dvd hd.1.1 hpd).trans hd.1.2) fun hpq => hp.coprime_iff_not_dvd.1 (hd.2.2.coprime_dvd_left hpd) hpq) (fun _ => 1)
    have hφd : (0 : ℝ) < d.totient := by exact_mod_cast Nat.totient_pos.2 hd.1.1
    rw [mul_one_div, div_le_iff₀ hφd, mul_comm]; simpa [hZ, U] using h
  have hls : ∑ d ∈ D, U d ≤ ((Q : ℝ) ^ 2 + 2 * Real.pi * N) * Z := by
    set P := D.sigma fun d => (Finset.range d).filter d.Coprime with hP
    set T : Finset ℝ := P.image fun x => (x.2 : ℝ) / x.1 with hT
    have hmemP : ∀ x ∈ P, 0 < x.1 ∧ x.1 ≤ Q ∧ x.2 < x.1 ∧ Nat.Coprime x.2 x.1 := fun x hx => by
      rw [hP, Finset.mem_sigma, hD, Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range] at hx; exact ⟨hx.1.1.1, hx.1.1.2, hx.2.1, hx.2.2.symm⟩
    have hinj : Set.InjOn (fun x : Σ _ : ℕ, ℕ => (x.2 : ℝ) / x.1) P := fun x hx y hy hxy => by
      obtain ⟨e1, e2⟩ := MultSieve.reduced_inj (hmemP x hx).1 (hmemP y hy).1 (hmemP x hx).2.2.2 (hmemP y hy).2.2.2 hxy; exact Sigma.ext e1 (heq_of_eq e2)
    calc ∑ d ∈ D, U d = ∑ x ∈ T, ‖∑ n ∈ Finset.Ioc M (M + N), (if n ∈ S then (1 : ℂ) else 0) * cexp (2 * ↑Real.pi * I * ↑n * ↑x)‖ ^ 2 := by
          rw [hT, Finset.sum_image hinj, hP, Finset.sum_sigma]; refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun a _ => ?_
          simp only [ite_mul, one_mul, zero_mul, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS]
          congr 2; exact Finset.sum_congr rfl fun n _ => by congr 1; push_cast; ring
      _ ≤ (1 / (1 / (Q : ℝ) ^ 2) + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖(if n ∈ S then (1 : ℂ) else 0)‖ ^ 2 :=
          additive_large_sieve M N _ T _ (by positivity) (by rw [div_le_one (by positivity)]; exact one_le_pow₀ (by exact_mod_cast hQ)) fun x hx y hy hxy k => by
            obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hx; obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hy
            exact MultSieve.farey_spaced Q u.1 v.1 u.2 v.2 (hmemP u hu).2.1 (hmemP v hv).2.1 (hmemP u hu).2.2.1 (hmemP v hv).2.2.1 hxy k
      _ = ((Q : ℝ) ^ 2 + 2 * Real.pi * N) * Z := by
          rw [one_div_one_div]; congr 1
          have hpt : ∀ n, ‖(if n ∈ S then (1 : ℂ) else 0)‖ ^ 2 = if n ∈ S then (1 : ℝ) else 0 := fun n => by split_ifs <;> simp
          simp_rw [hpt, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hS]; simp [hZ]
  have hbig : Z * (Z * ∑ d ∈ D, (1 : ℝ) / d.totient) ≤ Z * ((Q : ℝ) ^ 2 + 2 * Real.pi * N) := by
    calc _ = ∑ d ∈ D, Z ^ 2 * ((1 : ℝ) / d.totient) := by rw [← Finset.mul_sum]; ring
      _ ≤ _ := ((Finset.sum_le_sum hmont).trans hls).trans_eq (mul_comm _ _)
  exact (mul_le_mul_of_nonneg_left hL hZ0).trans (le_of_mul_le_mul_left hbig hpos)

end GlobalTheory
