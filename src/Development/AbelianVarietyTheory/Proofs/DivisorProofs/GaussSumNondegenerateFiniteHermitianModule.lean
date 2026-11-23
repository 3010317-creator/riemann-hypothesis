module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumEqZeroAddUnits

@[expose] public section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.HermitianGauss

section Fin

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]

noncomputable def pts (B : Submodule R M) : Finset M := Finset.univ.filter (· ∈ B)

@[simp] theorem mem_pts {B : Submodule R M} {x : M} : x ∈ pts B ↔ x ∈ B := by simp [pts]

theorem card_pts (B : Submodule R M) : (pts B).card = Nat.card B :=
  (Nat.card_eq_finsetCard _).symm.trans (Nat.card_congr (Equiv.subtypeEquivRight fun _ => mem_pts))

theorem card_pts_pos (B : Submodule R M) : 0 < (pts B).card :=
  Finset.card_pos.mpr ⟨0, mem_pts.mpr B.zero_mem⟩

theorem card_pts_dvd {A B : Submodule R M} (h : A ≤ B) : (pts A).card ∣ (pts B).card := by
  simpa [card_pts] using AddSubgroup.card_dvd_of_le (show A.toAddSubgroup ≤ B.toAddSubgroup from h)

theorem eq_of_card_pts {A B : Submodule R M} (h : A ≤ B) (hc : (pts B).card ≤ (pts A).card) :
    A = B := by
  have he := Finset.eq_of_subset_of_card_le (fun _ hy => mem_pts.mpr (h (mem_pts.mp hy))) hc
  exact le_antisymm h fun _ hy => mem_pts.mp (he ▸ mem_pts.mpr hy)

theorem sum_pts_add (B : Submodule R M) (f : M → ℂ) {z : M} (hz : z ∈ B) :
    ∑ y ∈ pts B, f (y + z) = ∑ y ∈ pts B, f y :=
  Finset.sum_nbij' (· + z) (· - z) (fun _ ha => mem_pts.mpr (B.add_mem (mem_pts.mp ha) hz))
    (fun _ ha => mem_pts.mpr (B.sub_mem (mem_pts.mp ha) hz)) (fun a _ => add_sub_cancel_right a z)
    (fun a _ => sub_add_cancel a z) fun _ _ => rfl

theorem sum_char (B : Submodule R M) (f : M → ℂ) (hf : ∀ a b, f (a + b) = f a * f b) :
    ∑ y ∈ pts B, f y = if ∀ y ∈ B, f y = 1 then ((pts B).card : ℂ) else 0 := by
  split_ifs with h
  · simp [Finset.sum_congr rfl fun y hy => h y (mem_pts.mp hy)]
  · push Not at h; obtain ⟨y0, hy0, hne⟩ := h
    have h1 := sum_pts_add B f hy0; simp_rw [hf, ← Finset.sum_mul] at h1
    exact (mul_eq_zero.mp (by rw [mul_sub, h1, mul_one, sub_self] :
      (∑ y ∈ pts B, f y) * (f y0 - 1) = 0)).resolve_right (sub_ne_zero.mpr hne)

private theorem mk_out {P : Ideal R} (a : R ⧸ P) : Ideal.Quotient.mk P (Quotient.out a) = a := Quotient.out_eq a

omit [Fintype M] in
private theorem mem_sup_span_singleton {D : Submodule R M} {x y : M}
    (hy : y ∈ D ⊔ Submodule.span R {x}) : ∃ d ∈ D, ∃ a : R, d + a • x = y := by
  obtain ⟨d, hd, _, hz, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨d, hd, a, rfl⟩

theorem finite_quot {D : Submodule R M} {x : M} {P : Ideal R} (hP : ∀ r, r • x ∈ D ↔ r ∈ P) :
    Finite (R ⧸ P) :=
  Finite.of_injective (fun a : R ⧸ P => (Quotient.out a : R) • x) fun a b (hab : _ • x = _) => by
    rw [← mk_out a, ← mk_out b, Ideal.Quotient.eq, ← hP, sub_smul, hab, sub_self]; exact D.zero_mem

theorem sum_sup {D : Submodule R M} {x : M} {P : Ideal R} [Fintype (R ⧸ P)]
    (hP : ∀ r, r • x ∈ D ↔ r ∈ P) {A : Type} [AddCommMonoid A] (f : M → A) :
    ∑ y ∈ pts (D ⊔ Submodule.span R {x}), f y =
      ∑ q : R ⧸ P, ∑ d ∈ pts D, f (d + (Quotient.out q : R) • x) := by
  rw [← Finset.sum_product']; symm
  refine Finset.sum_bij (fun p _ => p.2 + (Quotient.out p.1 : R) • x) ?_ ?_ ?_ fun _ _ => rfl
  · rintro ⟨q, d⟩ hp
    exact mem_pts.mpr (Submodule.add_mem_sup (mem_pts.mp (Finset.mem_product.mp hp).2)
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
  · rintro ⟨q1, d1⟩ h1 ⟨q2, d2⟩ h2 (heq : d1 + _ = d2 + _)
    have hq : q1 = q2 := by
      rw [← mk_out q1, ← mk_out q2, Ideal.Quotient.eq, ← hP,
        sub_smul, sub_eq_sub_iff_add_eq_add.mpr (add_comm d1 _ ▸ heq)]
      exact D.sub_mem (mem_pts.mp (Finset.mem_product.mp h2).2)
        (mem_pts.mp (Finset.mem_product.mp h1).2)
    subst hq; exact Prod.ext rfl (add_right_cancel heq)
  · intro y hy
    obtain ⟨d, hd, a, rfl⟩ := mem_sup_span_singleton (mem_pts.mp hy)
    set q := Ideal.Quotient.mk P a
    exact ⟨(q, d - (Quotient.out q - a) • x), Finset.mem_product.mpr ⟨Finset.mem_univ _,
      mem_pts.mpr (D.sub_mem hd ((hP _).mpr (Ideal.Quotient.eq.mp (mk_out q))))⟩,
      by dsimp only; rw [sub_smul]; abel⟩

theorem card_sup {D : Submodule R M} {x : M} {P : Ideal R} [Fintype (R ⧸ P)]
    (hP : ∀ r, r • x ∈ D ↔ r ∈ P) :
    (pts (D ⊔ Submodule.span R {x})).card = Fintype.card (R ⧸ P) * (pts D).card := by
  simpa [Finset.sum_const, Finset.card_univ] using sum_sup hP fun _ => (1 : ℕ)

variable {σ : R →+* R} {β : M → M → ℂ}

def perp (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y))
    (h0 : ∀ y, β 0 y = 1) (B N : Submodule R M) : Submodule R M where
  carrier := {x | x ∈ B ∧ ∀ y ∈ N, β x y = 1}
  add_mem' := fun {a b} ha hb => ⟨B.add_mem ha.1 hb.1, fun y hy => by rw [hadd, ha.2 y hy, hb.2 y hy, one_mul]⟩
  zero_mem' := ⟨B.zero_mem, fun y _ => h0 y⟩
  smul_mem' := fun r a ha => ⟨B.smul_mem r ha.1, fun y hy => by rw [hadj]; exact ha.2 _ (N.smul_mem _ hy)⟩

theorem card_perp (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    {B C N N' : Submodule R M} (hCN : C ≤ N) (hNB : N ≤ B) (hrad : ∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1)
    (hN' : ∀ x, x ∈ N' ↔ x ∈ B ∧ ∀ y ∈ N, β x y = 1) :
    (pts C).card * (pts B).card = (pts N').card * (pts N).card := by
  have hr (a b c) : β a (b + c) = β a b * β a c := by rw [hsym a, hadd, hsym b, hsym c]
  have h1 : ∑ y ∈ pts B, ∑ z ∈ pts N, β y z = ((pts N').card : ℂ) * (pts N).card := by
    rw [Finset.sum_congr rfl fun y _ => sum_char N (β y) (hr y), ← Finset.sum_filter,
      show (pts B).filter _ = pts N' by ext; simp [pts, hN'], Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ y ∈ pts B, ∑ z ∈ pts N, β y z = ((pts C).card : ℂ) * (pts B).card := by
    rw [Finset.sum_comm, Finset.sum_congr rfl fun z _ => sum_char B (β · z) (hadd · · z),
      ← Finset.sum_filter, show (pts N).filter _ = pts C from Finset.ext fun z => by
        simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun ⟨hz, h⟩ => (hrad z (hNB hz)).mpr fun y hy => hsym z y ▸ h y hy,
          fun hz => ⟨hCN hz, fun y hy => hsym y z ▸ (hrad z (hNB (hCN hz))).mp hz y hy⟩⟩,
      Finset.sum_const, nsmul_eq_mul]
  exact_mod_cast h2.symm.trans h1

set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
theorem quad_add {w : R} (hσ : ∀ r, σ (σ r) = r) (hw : w + σ w = 1)
    (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y)) (y z : M) :
    β (w • (y + z)) (y + z) = β (w • y) y * β (w • z) z * β z y := by
  have hr (a b c) : β a (b + c) = β a b * β a c := by rw [hsym a, hadd, hsym b, hsym c]
  have key : β (w • y) z * β (w • z) y = β z y := by
    rw [hadj w y z, hsym (w • z) y, ← hr, ← add_smul, add_comm (σ w), hw, one_smul, hsym]
  rw [smul_add, hadd, hr, hr, ← key]; ring

private theorem exists_mem_not_mem_annihilator_maximal_of_lt {C B : Submodule R M}
    (hCB : C ≤ B) (hne : C ≠ B) :
    ∃ x ∈ B, x ∉ C ∧ ∃ P : Ideal R, P.IsMaximal ∧ ∀ r : R, r • x ∈ C ↔ r ∈ P := by
  obtain ⟨x, hx, hmin⟩ := Finset.exists_min_image _ (fun x => (pts (C ⊔ Submodule.span R {x})).card)
    (Finset.sdiff_nonempty.mpr fun h =>
      hne (le_antisymm hCB fun _ hy => mem_pts.mp (h (mem_pts.mpr hy))))
  obtain ⟨hxB, hxC⟩ : x ∈ B ∧ x ∉ C := by simpa using hx
  let I : Ideal R := C.comap (LinearMap.toSpanSingleton R M x)
  refine ⟨x, hxB, hxC, I, Ideal.isMaximal_iff.mpr ⟨fun h1 => hxC (by simpa [I] using h1),
    fun J r hIJ hr hrJ => ?_⟩, fun r => by simp [I]⟩
  have hle : C ⊔ Submodule.span R {r • x} ≤ C ⊔ Submodule.span R {x} :=
    sup_le_sup_left (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
      (Submodule.smul_mem _ r (Submodule.mem_span_singleton_self x)))) C
  have heq := eq_of_card_pts hle (hmin _ (by simp [I, B.smul_mem r hxB] at hr ⊢; exact hr))
  obtain ⟨c, hc, s, hcz⟩ := mem_sup_span_singleton
    (heq.symm ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
  have h2 : 1 - s * r ∈ I := by simpa [I, sub_smul, mul_smul, sub_eq_iff_eq_add.mpr hcz.symm] using hc
  simpa using J.add_mem (hIJ h2) (J.mul_mem_left s hrJ)

theorem gauss_fin {w : R} (hσ : ∀ r, σ (σ r) = r) (hw : w + σ w = 1) {lam : ℕ →* ℂ} (hlam : GoodNorm σ lam)
    (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y)) (h0 : ∀ y, β 0 y = 1) (n : ℕ) :
    ∀ B C : Submodule R M, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → (pts B).card = n * (pts C).card →
      ∑ y ∈ pts B, β (w • y) y = (pts C).card * lam n ∧ lam n ^ 2 = n := by
  induction n using Nat.strong_induction_on with | _ n ih => ?_
  intro B C hCB hrad hcard
  have hr (a b c) : β a (b + c) = β a b * β a c := by rw [hsym a, hadd, hsym b, hsym c]
  have hC1 (c) (hc : c ∈ C) (y) (hy : y ∈ B) : β c y = 1 := (hrad c (hCB hc)).mp hc y hy
  have hQC (c) (hc : c ∈ C) : β (w • c) c = 1 := hsym _ _ ▸ hC1 c hc _ (B.smul_mem w (hCB hc))
  have hCpos := card_pts_pos C
  by_cases hBC : C = B
  · obtain rfl : n = 1 := Nat.eq_of_mul_eq_mul_right hCpos (by simpa [hBC] using hcard.symm)
    simp [← hBC, Finset.sum_congr rfl fun c hc => hQC c (mem_pts.mp hc)]
  obtain ⟨x, hxB, hxC, P, hPm, hP⟩ := exists_mem_not_mem_annihilator_maximal_of_lt hCB hBC
  have : Finite (R ⧸ P) := finite_quot hP; let _ : Fintype (R ⧸ P) := Fintype.ofFinite _
  set q := Fintype.card (R ⧸ P)
  have hq1 : 1 < q := have := hPm; Fintype.one_lt_card
  obtain ⟨hlq, hlqσ⟩ := hlam.2 P hPm ‹_›; rw [Nat.card_eq_fintype_card] at hlq hlqσ
  set N := C ⊔ Submodule.span R {x}
  have hNcard : (pts N).card = q * (pts C).card := card_sup hP
  have hxN : x ∈ N := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hNB : N ≤ B := sup_le hCB (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxB))
  set N' := perp hadd hadj h0 B N
  have hperp := card_perp hadd hsym le_sup_left hNB hrad (N' := N') fun _ => Iff.rfl
  have hBN' : (pts B).card = q * (pts N').card :=
    Nat.eq_of_mul_eq_mul_left hCpos (hperp.trans (by rw [hNcard]; ring))
  have hCN' : C ≤ N' := fun c hc => ⟨hCB hc, fun z hz => hC1 c hc z (hNB hz)⟩
  have hN'B : N' ≤ B := fun _ hy => hy.1
  have hlt {k m : ℕ} (hk : 1 < k) (h : n = k * m) : m < n := h ▸ lt_mul_of_one_lt_left
    (Nat.pos_of_ne_zero fun h0 => (card_pts_pos B).ne' (by simp [hcard, h, h0])) hk
  by_cases hiso : ∀ r : R, β x (r • x) = 1
  · have hxN' : x ∈ N' := ⟨hxB, fun z hz => by
      obtain ⟨c, hc, a, rfl⟩ := mem_sup_span_singleton hz
      rw [hr, hiso, mul_one, hsym]; exact hC1 c hc x hxB⟩
    have hNN' : N ≤ N' := sup_le hCN' (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxN'))
    have hQN (z) (hz : z ∈ N) : β (w • z) z = 1 := by
      obtain ⟨c, hc, a, rfl⟩ := mem_sup_span_singleton hz
      rw [quad_add hσ hw hadd hsym hadj, hQC c hc, one_mul, hsym (a • x) c,
        hC1 c hc _ (B.smul_mem a hxB), mul_one, smul_smul, hadj, smul_smul, hiso]
    obtain ⟨m, hm⟩ := card_pts_dvd hNN'
    have hn : n = q * q * m := Nat.eq_of_mul_eq_mul_right hCpos (by rw [← hcard, hBN', hm, hNcard]; ring)
    have hrad' (y) (hy : y ∈ N') : y ∈ N ↔ ∀ z ∈ N', β y z = 1 :=
      ⟨fun hyN z hz => hsym y z ▸ hz.2 y hyN, fun h => by
        have h2 := card_perp hadd hsym hCN' hN'B hrad (N' := perp hadd hadj h0 B N') fun _ => Iff.rfl
        have hc := Nat.eq_of_mul_eq_mul_right (card_pts_pos N')
          (h2.symm.trans (hperp.trans (mul_comm _ _)))
        exact eq_of_card_pts (B := perp hadd hadj h0 B N')
          (fun u hu => ⟨hNB hu, fun z hz => hsym u z ▸ hz.2 u hu⟩) hc.le ▸ ⟨hN'B hy, h⟩⟩
    obtain ⟨hs, hl⟩ := ih m (hlt (one_lt_mul'' hq1 hq1) hn) N' N hNN' hrad' (hm.trans (mul_comm _ _))
    refine ⟨mul_right_cancel₀ (Nat.cast_ne_zero.mpr (card_pts_pos N).ne') ?_,
      by rw [hn, map_mul, map_mul, mul_pow, mul_pow, hl, hlq]; push_cast; ring⟩
    have hf : (pts B).filter (fun y => ∀ z ∈ N, β y z = 1) = pts N' := by ext; simp [pts, N', perp]
    calc (∑ y ∈ pts B, β (w • y) y) * (pts N).card
        = ∑ y ∈ pts B, ∑ n ∈ pts N, β (w • (y + n)) (y + n) := by
          rw [← Finset.sum_comm, Finset.sum_congr rfl fun n hn =>
            sum_pts_add B (fun y => β (w • y) y) (hNB (mem_pts.mp hn)),
            Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = (∑ y ∈ pts N', β (w • y) y) * (pts N).card := by
          rw [Finset.sum_congr rfl fun y _ => by
            rw [Finset.sum_congr rfl fun n hn => by
              rw [quad_add hσ hw hadd hsym hadj, hQN n (mem_pts.mp hn), mul_one, hsym n y],
              ← Finset.mul_sum, sum_char N (β y) (hr y)]]
          simp_rw [mul_ite, mul_zero, ← Finset.sum_filter, hf, ← Finset.sum_mul]
      _ = (pts C).card * lam n * (pts N).card := by
          rw [hs, hNcard, hn, map_mul, map_mul, ← sq, hlq]; push_cast; ring
  · push Not at hiso; obtain ⟨r0, hr0⟩ := hiso
    let χ (t : R) : ℂ := β x (t • x)
    have hχadd (s t) : χ (s + t) = χ s * χ t := by simp only [χ, add_smul, hr]
    have hχ0 : χ 0 = 1 := by dsimp only [χ]; rw [zero_smul, hsym, h0]
    have hχP (t) (ht : t ∈ P) : χ t = 1 := by dsimp only [χ]; rw [hsym]; exact hC1 _ ((hP t).mpr ht) x hxB
    have hχσ (t) : χ (σ t) = χ t := by dsimp only [χ]; rw [← hadj, hsym]
    have hmemP {s : R} (hs : ∀ u, χ (s * u) = 1) : s ∈ P := by
      by_contra hsP
      obtain ⟨y, i, hi, hyi⟩ := hPm.exists_inv hsP
      have e1 : r0 = r0 * i + s * (y * r0) := (mul_one r0).symm.trans (by rw [← hyi]; ring)
      exact hr0 (show χ r0 = 1 by rw [e1, hχadd, hχP _ (P.mul_mem_left r0 hi), hs, mul_one])
    have hσP (p) (hp : p ∈ P) : σ p ∈ P := hmemP fun u => by
      rw [← hχσ, map_mul, hσ]; exact hχP _ (P.mul_mem_right _ hp)
    obtain ⟨hlqv, hex⟩ := hlqσ hσP
    have hG := NormFormGauss.gauss_quotient σ w hσ hw P hPm ‹_› hσP hex χ hχadd hχ0 hχP hχσ ⟨r0, hr0⟩
    rw [Nat.card_eq_fintype_card, finsum_eq_sum_of_fintype] at hG
    have hP' (r : R) : r • x ∈ N' ↔ r ∈ P :=
      ⟨fun h => hσ r ▸ hσP _ (hmemP fun u => by
        simpa [χ, mul_smul, ← hadj] using h.2 _ (N.smul_mem u hxN)),
       fun hrP => ⟨B.smul_mem r hxB, fun z hz => by
        obtain ⟨c, hc, a, rfl⟩ := mem_sup_span_singleton hz
        rw [hr, hC1 _ ((hP r).mpr hrP) c (hCB hc), one_mul, hadj, smul_smul]
        exact hχP _ (P.mul_mem_right a (hσP r hrP))⟩⟩
    have hsupB : N' ⊔ Submodule.span R {x} = B := eq_of_card_pts
      (sup_le hN'B (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxB)))
      (by rw [card_sup hP', hBN'])
    obtain ⟨m, hm⟩ := card_pts_dvd hCN'
    have hnqm : n = q * m := Nat.eq_of_mul_eq_mul_right hCpos (by rw [← hcard, hBN', hm]; ring)
    have hrad' (y) (hy : y ∈ N') : y ∈ C ↔ ∀ z ∈ N', β y z = 1 :=
      ⟨fun hyC z hz => hC1 y hyC z (hN'B hz), fun h => (hrad y (hN'B hy)).mpr fun b hb => by
        obtain ⟨d, hd, a, rfl⟩ := mem_sup_span_singleton (hsupB ▸ hb)
        rw [hr, h d hd, one_mul]; exact hy.2 _ (N.smul_mem a hxN)⟩
    obtain ⟨hs, hl⟩ := ih m (hlt hq1 hnqm) N' C hCN' hrad' (hm.trans (mul_comm _ _))
    refine ⟨?_, by rw [hnqm, map_mul, mul_pow, hl, hlq]; push_cast; ring⟩
    calc ∑ y ∈ pts B, β (w • y) y
        = (∑ d ∈ pts N', β (w • d) d) *
            ∑ q' : R ⧸ P, χ (w * (Quotient.out q' : R) * σ (Quotient.out q' : R)) := by
          rw [← hsupB, sum_sup hP', Finset.sum_comm, Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun q' _ => ?_
          rw [quad_add hσ hw hadd hsym hadj, hsym ((Quotient.out q' : R) • x) d,
            (mem_pts.mp hd).2 _ (N.smul_mem _ hxN), mul_one]
          congr 1; dsimp only [χ]; rw [hsym, hadj, smul_smul, smul_smul]; congr 2; ring
      _ = (pts C).card * lam n := by rw [hs, hG, hnqm, map_mul, ← hlqv]; ring

end Fin

theorem gauss_hermitian : ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ β : X → X → ℂ, (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y, β x y = β y x) → (∀ (r : R) x y, β (r • x) y = β x (σ r • y)) → ∀ B C : Submodule R X, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → ∀ (n : ℕ) (t : Fin n → X), (∀ k, t k ∈ B) → (∀ y ∈ B, ∃! k, y - t k ∈ C) → ∑ k, β (w • t k) (t k) = lam n ∧ lam n ^ 2 = n := by
  intro R X _ _ _ σ w hσ hw lam hlam β hadd hsym hadj B C hCB hrad n t htB huniq
  have hC1 (c) (hc : c ∈ C) (y) (hy : y ∈ B) : β c y = 1 := (hrad c (hCB hc)).mp hc y hy
  let C' : Submodule R B := C.comap B.subtype
  have hm := Submodule.Quotient.mk_surjective C'
  let e (k : Fin n) : B ⧸ C' := Submodule.Quotient.mk ⟨t k, htB k⟩
  have he : Function.Bijective e :=
    ⟨fun k l hkl => by
      obtain ⟨_, _, hk'⟩ := huniq (t k) (htB k)
      exact (hk' k (by simp)).trans (hk' l ((Submodule.Quotient.eq C').mp hkl)).symm,
     hm.forall.mpr fun y =>
      let ⟨k, hk, _⟩ := huniq y y.2
      ⟨k, (Submodule.Quotient.eq C').mpr (show t k - (y : X) ∈ C from
        neg_sub (y : X) (t k) ▸ C.neg_mem hk)⟩⟩
  have := Finite.of_surjective e he.2; let _ : Fintype (B ⧸ C') := Fintype.ofFinite _
  let β' (u v : B ⧸ C') : ℂ := β (Quotient.out u : B) (Quotient.out v : B)
  have hdesc {u v z : X} (huv : u - v ∈ C) (hz : z ∈ B) : β u z = β v z := by
    rw [← sub_add_cancel u v, hadd, hC1 _ huv z hz, one_mul]
  have hβ' (a b : B) : β' (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = β a b := by
    dsimp only [β']
    rw [hdesc ((Submodule.Quotient.eq C').mp (Quotient.out_eq _))
      (Quotient.out (Submodule.Quotient.mk b : B ⧸ C')).2, hsym,
      hdesc ((Submodule.Quotient.eq C').mp (Quotient.out_eq _)) a.2, hsym]
  have hadd' : ∀ u v z : B ⧸ C', β' (u + v) z = β' u z * β' v z := hm.forall₃.mpr fun a b c => by
    rw [← Submodule.Quotient.mk_add, hβ', hβ', hβ', Submodule.coe_add, hadd]
  have hsym' : ∀ u v : B ⧸ C', β' u v = β' v u := hm.forall₂.mpr fun a b => by rw [hβ', hβ', hsym]
  have hadj' (r : R) : ∀ u v : B ⧸ C', β' (r • u) v = β' u (σ r • v) := hm.forall₂.mpr fun a b => by
    simp only [← Submodule.Quotient.mk_smul, hβ', Submodule.coe_smul, hadj]
  have h0' : ∀ v : B ⧸ C', β' 0 v = 1 := hm.forall.mpr fun b => by
    rw [← Submodule.Quotient.mk_zero C', hβ']; exact hC1 0 C.zero_mem b b.2
  have hrad' : ∀ u ∈ (⊤ : Submodule R (B ⧸ C')), u ∈ (⊥ : Submodule R (B ⧸ C')) ↔
      ∀ v ∈ (⊤ : Submodule R (B ⧸ C')), β' u v = 1 := by
    simp only [Submodule.mem_top, forall_const, hm.forall, Submodule.mem_bot,
      Submodule.Quotient.mk_eq_zero, hβ']
    exact fun a => (hrad a a.2).trans ⟨fun h b => h b b.2, fun h y hy => h ⟨y, hy⟩⟩
  have hpt : pts (⊤ : Submodule R (B ⧸ C')) = Finset.univ := by ext; simp
  have hpb : pts (⊥ : Submodule R (B ⧸ C')) = {0} := by ext; simp
  obtain ⟨hs, hl⟩ := gauss_fin (w := w) hσ hw hlam hadd' hsym' hadj' h0' n ⊤ ⊥ bot_le hrad'
    (by simp [hpt, hpb, ← Fintype.card_of_bijective he])
  rw [hpt, hpb, Finset.card_singleton, Nat.cast_one, one_mul,
    ← he.sum_comp (fun u => β' (w • u) u)] at hs
  exact ⟨(Finset.sum_congr rfl fun k _ => by
    rw [← Submodule.Quotient.mk_smul, hβ']; rfl).trans hs, hl⟩

end GlobalTheory.HermitianGauss
