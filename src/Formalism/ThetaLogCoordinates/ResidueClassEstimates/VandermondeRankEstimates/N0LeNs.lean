module

public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementT

@[expose] public section

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

open Letters

lemma sum_filter_Icc_succ (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℕ) (a i : ℕ) (h : a ≤ i + 1) :
    ∑ l ∈ (Icc a (i + 1)).filter p, f l =
      (∑ l ∈ (Icc a i).filter p, f l) + if p (i + 1) then f (i + 1) else 0 := by
  rw [sum_filter, sum_filter, sum_Icc_succ_top h]

lemma card_filter_Icc_succ (p : ℕ → Prop) [DecidablePred p] (a i : ℕ) (h : a ≤ i + 1) :
    ((Icc a (i + 1)).filter p).card = ((Icc a i).filter p).card + if p (i + 1) then 1 else 0 := by
  rw [card_filter, card_filter, sum_Icc_succ_top h]

lemma Dom.anti {n : ℕ} {la : ℕ → ℤ} (h : Dom n la) : ∀ a b, a ≤ b → b < n → la b ≤ la a :=
  fun _ _ hab => Nat.le_induction (fun _ => le_rfl) (fun b _ ih hb => (h b hb).trans (ih (by omega))) _ hab

lemma HStrip.diff_le {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) (m : ℕ) (hm : m < n) :
    b m - a m ≤ wsize n b - wsize n a := by
  rw [wsize, wsize, ← sum_sub_distrib]
  exact single_le_sum (fun j hj => sub_nonneg.mpr (h.1 j (mem_range.mp hj))) (mem_range.mpr hm)

def revW (n : ℕ) (la : ℕ → ℤ) : ℕ → ℤ := fun m => -(la (n - 1 - m))
lemma tailNeg_eq (n : ℕ) (la : ℕ → ℤ) (u : ℕ) : tailNeg n la u = tailPos n (revW n la) u := rfl

lemma HStrip.rev {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) : HStrip n (revW n b) (revW n a) :=
  ⟨fun _ hm => neg_le_neg (h.1 _ (by omega)), fun m hm => by
    simp only [revW]; rw [show n - 1 - m = n - 1 - (m + 1) + 1 by omega]
    exact neg_le_neg (h.2 (n - 1 - (m + 1)) (by omega))⟩

lemma Interl.rev {n : ℕ} {a b : ℕ → ℤ} (h : Interl n a b) : Interl n (revW n a) (revW (n + 1) b) :=
  fun l hl => by
    obtain ⟨h1, h2⟩ := h (n - 1 - l) (by omega); simp only [revW]
    rw [show n + 1 - 1 - l = n - 1 - l + 1 by omega, show n + 1 - 1 - (l + 1) = n - 1 - l by omega]
    exact ⟨neg_le_neg h2, neg_le_neg h1⟩

lemma wsize_rev (n : ℕ) (la : ℕ → ℤ) : wsize n (revW n la) = - wsize n la := by
  simp [wsize, revW, sum_neg_distrib, sum_range_reflect]

lemma tailPos_succ (n : ℕ) (la : ℕ → ℤ) (u : ℕ) :
    tailPos (n + 1) la u = tailPos n la u + if u ≤ n then max (la n) 0 else 0 := by
  rw [tailPos, tailPos, sum_filter, sum_filter, sum_range_succ]

lemma tailPos_le_succ (n : ℕ) (la : ℕ → ℤ) (u : ℕ) : tailPos n la u ≤ tailPos (n + 1) la u := by
  rw [tailPos_succ]; split_ifs <;> linarith [le_max_right (la n) 0]

lemma tailPos_mono {n : ℕ} {a b : ℕ → ℤ} (h : ∀ m, m < n → a m ≤ b m) (u : ℕ) :
    tailPos n a u ≤ tailPos n b u :=
  sum_le_sum fun m hm => max_le_max (h m (mem_range.mp (mem_filter.mp hm).1)) le_rfl

lemma tail_pos_shift_le (a b : ℕ → ℤ) (u : ℕ) :
    ∀ n, (∀ m, m + 1 < n + 1 → b (m + 1) ≤ a m) → tailPos (n + 1) b (u + 1) ≤ tailPos n a u := by
  intro n; induction n with
  | zero => intro _; simp [tailPos, filter_singleton]
  | succ n ih =>
    intro h; rw [tailPos_succ (n + 1) b, tailPos_succ n a]
    simp only [show (u + 1 ≤ n + 1) ↔ u ≤ n by omega]
    have := ih fun m hm => h m (by omega)
    have := max_le_max (h n (by omega)) (le_rfl : (0 : ℤ) ≤ 0); split_ifs <;> linarith

lemma HStrip.tailPos_shift {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) (u : ℕ) :
    tailPos n b (u + 1) ≤ tailPos n a u := by
  rcases n with _ | k; · simp [tailPos]
  exact (tail_pos_shift_le a b u k h.2).trans (tailPos_le_succ k a u)

lemma HStrip.tailPos_le {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) (u : ℕ) : tailPos n a u ≤ tailPos n b u :=
  tailPos_mono h.1 u

lemma wsize_eq_tails (n : ℕ) (a : ℕ → ℤ) : wsize n a = tailPos n a 0 - tailPos n (revW n a) 0 := by
  simp only [wsize, tailPos, revW, sum_filter, Nat.zero_le, ↓reduceIte]
  rw [sum_range_reflect (fun m => max (-a m) 0) n, ← sum_sub_distrib]; refine sum_congr rfl fun m _ => ?_
  rcases le_total 0 (a m) with h | h <;>
    [rw [max_eq_left h, max_eq_right (by linarith)]; rw [max_eq_right h, max_eq_left (by linarith)]] <;> ring

lemma HStrip.tailPos_zero {n : ℕ} {a b : ℕ → ℤ} (h : HStrip n a b) :
    tailPos n b 0 - tailPos n a 0 ≤ wsize n b - wsize n a := by
  rw [wsize_eq_tails n b, wsize_eq_tails n a]; linarith [h.rev.tailPos_le 0]

lemma Interl.tailPos_le {n : ℕ} {a b : ℕ → ℤ} (h : Interl n a b) (u : ℕ) : tailPos n a u ≤ tailPos (n + 1) b u :=
  (tailPos_mono (fun m hm => (h m hm).1) u).trans (tailPos_le_succ n b u)

lemma Interl.size {n : ℕ} {a b : ℕ → ℤ} (h : Interl n a b) :
    b n ≤ wsize (n + 1) b - wsize n a ∧ wsize (n + 1) b - wsize n a ≤ b 0 :=
  ⟨by rw [wsize, wsize, sum_range_succ]; linarith [sum_le_sum fun m hm => (h m (mem_range.mp hm)).1],
    by rw [wsize, wsize, sum_range_succ']; linarith [sum_le_sum fun m hm => (h m (mem_range.mp hm)).2]⟩

lemma latest_succ (q : ℕ → Bool) (B : ℕ → ℕ) (i : ℕ) :
    (((List.range' 1 (i + 1)).filter q).reverse).map B =
      if q (i + 1) = true then B (i + 1) :: (((List.range' 1 i).filter q).reverse).map B
      else (((List.range' 1 i).filter q).reverse).map B := by
  cases hq : q (i + 1) <;> simp [List.range'_concat, List.filter_append, hq, add_comm]

lemma abs_bound (N : ℕ) (T : ℕ → ℕ → ℤ) (S : ℕ → ℕ → ℕ) (act : ℕ → Bool) (h0 : ∀ u, T 0 u ≤ S u 0)
    (hA : ∀ i u, i < N → act (i + 1) = true → T (i + 1) (u + 1) ≤ T i u ∧ S (u + 1) (i + 1) = S u i)
    (hA0 : ∀ i, i < N → act (i + 1) = true → T (i + 1) 0 - T i 0 ≤ (S 0 (i + 1) : ℤ) - S 0 i)
    (hI : ∀ i u, i < N → act (i + 1) = false → T (i + 1) u ≤ T i u ∧ S u (i + 1) = S u i) :
    ∀ i, i ≤ N → ∀ u, T i u ≤ S u i := by
  intro i; induction i with
  | zero => exact fun _ => h0
  | succ i ih =>
    intro hi u; specialize ih (by omega); cases ha : act (i + 1)
    · obtain ⟨h1, h2⟩ := hI i u (by omega) ha; exact h2 ▸ h1.trans (ih u)
    · rcases u with _ | u; · linarith [hA0 i (by omega) ha, ih 0]
      obtain ⟨h1, h2⟩ := hA i u (by omega) ha; exact h2 ▸ h1.trans (ih u)

lemma deficit_persists_of_active_inactive_recursion (N : ℕ) (T : ℕ → ℕ → ℤ) (S : ℕ → ℕ → ℕ) (act : ℕ → Bool)
    (hA : ∀ i u, i < N → act (i + 1) = true → T (i + 1) (u + 1) ≤ T i u ∧ S (u + 1) (i + 1) = S u i)
    (hI : ∀ i u, i < N → act (i + 1) = false → T (i + 1) u ≤ T i u ∧ S u (i + 1) = S u i)
    (i₀ u : ℕ) (X : ℝ) (h : ((T i₀ u : ℤ) : ℝ) ≤ (S u i₀ : ℝ) - X) : ∀ i, i₀ ≤ i → i ≤ N →
      ((T i (u + ((Icc (i₀ + 1) i).filter fun l => act l = true).card) : ℤ) : ℝ) ≤
        (S (u + ((Icc (i₀ + 1) i).filter fun l => act l = true).card) i : ℝ) - X := by
  intro i hi; induction i, hi using Nat.le_induction with
  | base => intro _; simpa using h
  | succ i hi ih =>
    intro hiN; specialize ih (by omega); rw [card_filter_Icc_succ _ (i₀ + 1) i (by omega)]
    generalize ((Icc (i₀ + 1) i).filter fun l => act l = true).card = c at ih ⊢
    cases ha : act (i + 1) <;> simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
    · obtain ⟨h1, h2⟩ := hI i (u + c) (by omega) ha; rw [h2]; linarith [Int.cast_le (R := ℝ).mpr h1]
    · obtain ⟨h1, h2⟩ := hA i (u + c) (by omega) ha; rw [← add_assoc, h2]; linarith [Int.cast_le (R := ℝ).mpr h1]

variable {D : Letters} {mu : D.Stages}

lemma n0_le_Ns (D : Letters) : D.n0 ≤ D.Ns := Nat.sub_le _ _
lemma Ns_eq (hW : D.Wf) : D.Ns = D.n0 + D.r := by have := hW.2.2.1; unfold Letters.n0; omega
lemma r_lt_k (hW : D.Wf) : D.r < D.k := by have := hW.2.1; unfold Letters.k; omega
lemma stage_le (i : ℕ) (h : i ≤ D.n0) : stage mu i = ent mu i :=
  funext fun _ => by simp [Letters.stage, Nat.sub_eq_zero_of_le h]
lemma stage_add (j l : ℕ) : stage mu (D.n0 + j) l = ent mu (D.n0 + j) (l + j) := by simp [Letters.stage]
lemma stLen_le (i : ℕ) (h : i ≤ D.n0) : D.stLen i = D.k := by rw [Letters.stLen, Nat.sub_eq_zero_of_le h, Nat.sub_zero]
lemma stLen_add (j : ℕ) : D.stLen (D.n0 + j) = D.k - j := by rw [Letters.stLen, Nat.add_sub_cancel_left]
lemma pre_of_path (h : D.IsPATH mu) : D.IsPre mu :=
  ⟨h.1, fun i hi => h.2.1 i (hi.trans (n0_le_Ns D)), fun i h1 h2 => h.2.2.1 i h1 (h2.trans (n0_le_Ns D)),
    fun i h1 h2 => h.2.2.2.1 i h1 (h2.trans (n0_le_Ns D)), h.2.2.2.2.1, h.2.2.2.2.2.1⟩
lemma be_eq (D : Letters) : D.be = D.bePos + D.beNeg := by
  rw [Letters.be, Letters.bePos, Letters.beNeg, ← sum_filter_add_sum_filter_not (Icc 1 D.n0) (D.vec · = true)]; congr 2

lemma pre_size (hk : 1 ≤ D.k) (hP : D.IsPre mu) : ∀ i, i ≤ D.n0 →
    -((∑ l ∈ (Icc 1 i).filter (fun l => D.vec l = false), D.B l : ℕ) : ℤ) ≤ ent mu i (D.k - 1) ∧
    ent mu i 0 ≤ ((∑ l ∈ (Icc 1 i).filter (fun l => D.vec l = true), D.B l : ℕ) : ℤ) := by
  intro i; induction i with
  | zero => intro _; simp [hP.1]
  | succ i ih =>
    intro hi; obtain ⟨ih1, ih2⟩ := ih (by omega)
    rw [sum_filter_Icc_succ _ _ _ _ (by omega), sum_filter_Icc_succ _ _ _ _ (by omega)]
    cases hv : D.vec (i + 1) <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
    · have hS := hP.2.2.2.1 (i + 1) (by omega) hi hv; have hW := hP.2.2.2.2.2 (i + 1) (by omega) hi hv
      simp only [Nat.add_sub_cancel] at hS hW; push_cast at ih1 ih2 ⊢
      exact ⟨by linarith [hS.diff_le (D.k - 1) (by omega)], by linarith [hS.1 0 (by omega)]⟩
    · have hS := hP.2.2.1 (i + 1) (by omega) hi hv; have hW := hP.2.2.2.2.1 (i + 1) (by omega) hi hv
      simp only [Nat.add_sub_cancel] at hS hW; push_cast at ih1 ih2 ⊢
      exact ⟨by linarith [hS.1 (D.k - 1) (by omega)], by linarith [hS.diff_le 0 (by omega)]⟩

lemma path_rows (hP : D.IsPATH mu) : ∀ i, i ≤ D.Ns →
    (∀ m, D.nVec i ≤ m → m < D.k → ent mu i m ≤ 0) ∧ ∀ m, m + D.nCov i < D.k → 0 ≤ ent mu i m := by
  intro i; induction i with
  | zero => intro _; exact ⟨fun _ _ _ => by simp [hP.1], fun _ _ => by simp [hP.1]⟩
  | succ i ih =>
    intro hi; obtain ⟨ih1, ih2⟩ := ih (by omega); simp only [Letters.nVec, Letters.nCov] at ih1 ih2 ⊢
    rw [card_filter_Icc_succ _ _ _ (by omega), card_filter_Icc_succ _ _ _ (by omega)]
    cases hv : D.vec (i + 1) <;> simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte]
    · have hS := hP.2.2.2.1 (i + 1) (by omega) hi hv; simp only [Nat.add_sub_cancel] at hS
      exact ⟨fun m hm hmk => (hS.1 m hmk).trans (ih1 m (by omega) hmk),
        fun m hm => (ih2 (m + 1) (by omega)).trans (hS.2 m (by omega))⟩
    · have hS := hP.2.2.1 (i + 1) (by omega) hi hv; simp only [Nat.add_sub_cancel] at hS
      refine ⟨fun m hm hmk => ?_, fun m hm => (ih2 m (by omega)).trans (hS.1 m (by omega))⟩
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      exact (hS.2 m' hmk).trans (ih1 m' (by omega) (by omega))

theorem pathEntryBounds : PathEntryBounds := fun D mu hW hP =>
  ⟨pre_size (by have := hW.1; unfold Letters.k; omega) (pre_of_path hP), path_rows hP⟩

lemma interl_of_path (hW : D.Wf) (hP : D.IsPATH mu) (j : ℕ) (hj : j < D.r) :
    Interl (D.k - (j + 1)) (stage mu (D.n0 + (j + 1))) (stage mu (D.n0 + j)) := fun l hl => by
  have hNs := Ns_eq hW
  have hS := hP.2.2.1 (D.n0 + (j + 1)) (by omega) (by omega) (hW.2.2.2.2 _ (by omega) (by omega))
  rw [show D.n0 + (j + 1) - 1 = D.n0 + j by omega] at hS; simp only [stage_add]
  exact ⟨by rw [show l + (j + 1) = l + j + 1 by omega]; exact hS.2 (l + j) (by omega),
    by rw [show l + 1 + j = l + (j + 1) by omega]; exact hS.1 (l + (j + 1)) (by omega)⟩

lemma tails_range (hD : Dom D.k (ent mu D.n0))
    (hI : ∀ j, j < D.r → Interl (D.k - (j + 1)) (stage mu (D.n0 + (j + 1))) (stage mu (D.n0 + j))) :
    ∀ j, j ≤ D.r → ∀ l, l < D.k - j →
      ent mu D.n0 (D.k - 1) ≤ stage mu (D.n0 + j) l ∧ stage mu (D.n0 + j) l ≤ ent mu D.n0 0 := by
  intro j; induction j with
  | zero => intro _ l hl; rw [stage_add]; exact ⟨hD.anti l (D.k - 1) (by omega) (by omega), hD.anti 0 l (by omega) (by omega)⟩
  | succ j ih =>
    intro hj l hl; obtain ⟨h1, h2⟩ := hI j (by omega) l (by omega)
    exact ⟨(ih (by omega) (l + 1) (by omega)).1.trans h2, h1.trans (ih (by omega) l (by omega)).2⟩

lemma path_of_interl (hW : D.Wf) (hPre : D.IsPre mu)
    (hH : ∀ i', 1 ≤ i' → i' ≤ D.r → ∀ m, m < i' → ent mu (D.n0 + i') m = D.be)
    (hI : ∀ j, j < D.r → Interl (D.k - (j + 1)) (stage mu (D.n0 + (j + 1))) (stage mu (D.n0 + j))) :
    D.IsPATH mu := by
  have hNs := Ns_eq hW; have hrk := r_lt_k hW; have hTR := tails_range (hPre.2.1 D.n0 le_rfl) hI
  have hn0be : ent mu D.n0 0 ≤ (D.be : ℤ) :=
    ((pre_size (by omega) hPre D.n0 le_rfl).2).trans (Nat.cast_le.mpr (by rw [be_eq]; exact Nat.le_add_right _ _))
  have hcur (j m : ℕ) (hm : j ≤ m) : ent mu (D.n0 + j) m = stage mu (D.n0 + j) (m - j) := by
    rw [stage_add, Nat.sub_add_cancel hm]
  have hVS : ∀ i, 1 ≤ i → i ≤ D.Ns → D.vec i = true → HStrip D.k (ent mu (i - 1)) (ent mu i) := by
    intro i h1 hi hv
    by_cases hin : i ≤ D.n0
    · exact hPre.2.2.1 i h1 hin hv
    obtain ⟨j', rfl⟩ : ∃ j', i = D.n0 + (j' + 1) := ⟨i - D.n0 - 1, by omega⟩
    have hjr : j' + 1 ≤ D.r := by omega
    have hIj := hI j' (by omega)
    rw [show D.n0 + (j' + 1) - 1 = D.n0 + j' by omega]; refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · rcases lt_trichotomy m j' with h | h | h
      · rw [hH j' (by omega) (by omega) m h, hH (j' + 1) (by omega) hjr m (by omega)]
      · rw [h, hH (j' + 1) (by omega) hjr j' (by omega), hcur j' j' le_rfl, Nat.sub_self]
        exact ((hTR j' (by omega) 0 (by omega)).2).trans hn0be
      · rw [hcur j' m (by omega), hcur (j' + 1) m (by omega), show m - j' = m - (j' + 1) + 1 by omega]
        exact (hIj (m - (j' + 1)) (by omega)).2
    · by_cases h : m < j'
      · rw [hH (j' + 1) (by omega) hjr (m + 1) (by omega), hH j' (by omega) (by omega) m h]
      · rw [hcur (j' + 1) (m + 1) (by omega), hcur j' m (by omega), show m + 1 - (j' + 1) = m - j' by omega]
        exact (hIj (m - j') (by omega)).1
  refine ⟨hPre.1, fun i hi => ?_, hVS, fun i h1 hi hv => ?_, hPre.2.2.2.2.1, hPre.2.2.2.2.2, hH⟩
  · exact if hin : i ≤ D.n0 then hPre.2.1 i hin else
      have hS := hVS i (by omega) hi (hW.2.2.2.2 i (by omega) hi)
      fun m hm => (hS.2 m hm).trans (hS.1 m (by omega))
  · exact if hin : i ≤ D.n0 then hPre.2.2.2.1 i h1 hin hv else absurd (hW.2.2.2.2 i (by omega) hi) (by simp [hv])

lemma wsize_head (j : ℕ) (hj : j ≤ D.k) (hH : ∀ m, m < j → ent mu (D.n0 + j) m = D.be) :
    wsize D.k (ent mu (D.n0 + j)) = (j : ℤ) * D.be + wsize (D.k - j) (stage mu (D.n0 + j)) := by
  unfold wsize; conv_lhs => rw [show D.k = j + (D.k - j) by omega]
  rw [sum_range_add, sum_congr rfl fun m hm => hH m (mem_range.1 hm), sum_const, card_range, nsmul_eq_mul]
  exact congrArg _ (sum_congr rfl fun m _ => by rw [stage_add, Nat.add_comm m j])

theorem pathInterlacingCriterion : PathInterlacingCriterion := by
  intro D mu hW; have hNs := Ns_eq hW; have hrk := r_lt_k hW; have hr1 := hW.1
  refine ⟨fun hPre hH => ⟨fun hP i' h1 h2 => ?_, fun h => path_of_interl hW hPre hH fun j hj => ?_⟩, fun hP => ?_⟩
  · simpa [show i' - 1 + 1 = i' by omega, show D.n0 + (i' - 1) = D.n0 + i' - 1 by omega] using
      interl_of_path hW hP (i' - 1) (by omega)
  · simpa [show D.n0 + (j + 1) - 1 = D.n0 + j by omega] using h (j + 1) (by omega) (by omega)
  · have hpre : -(D.beNeg : ℤ) ≤ ent mu D.n0 (D.k - 1) ∧ ent mu D.n0 0 ≤ (D.bePos : ℤ) :=
      pre_size (by omega) (pre_of_path hP) D.n0 le_rfl
    have hTR := tails_range (hP.2.1 D.n0 (n0_le_Ns D)) (interl_of_path hW hP)
    have hbe : (D.be : ℤ) = D.bePos + D.beNeg := by exact_mod_cast be_eq D
    refine ⟨hpre.1, hpre.2, hTR, fun i' h1 h2 => ?_⟩
    have e1 := wsize_head i' (by omega) (hP.2.2.2.2.2.2 i' h1 h2)
    have e2 := wsize_head (i' - 1) (by omega) fun m hm => hP.2.2.2.2.2.2 _ (by omega) (by omega) m hm
    have hsz := (interl_of_path hW hP (i' - 1) (by omega)).size
    rw [show i' - 1 + 1 = i' by omega, show D.k - i' + 1 = D.k - (i' - 1) by omega] at hsz
    rw [show D.n0 + i' - 1 = D.n0 + (i' - 1) by omega, e1, e2, show ((i' - 1 : ℕ) : ℤ) = (i' : ℤ) - 1 by omega]
    exact ⟨by ring, by linarith [(hTR (i' - 1) (by omega) 0 (by omega)).2],
      by linarith [(hTR (i' - 1) (by omega) (D.k - i') (by omega)).1]⟩

lemma latestV_succ (i : ℕ) (hi : i + 1 ≤ D.n0) :
    D.latestV (i + 1) = if D.vec (i + 1) = true then D.B (i + 1) :: D.latestV i else D.latestV i := by
  rw [Letters.latestV, Letters.latestV, min_eq_left hi, min_eq_left (by omega)]; exact latest_succ D.vec D.B i
lemma latestC_succ (i : ℕ) (hi : i + 1 ≤ D.n0) :
    D.latestC (i + 1) = if (!D.vec (i + 1)) = true then D.B (i + 1) :: D.latestC i else D.latestC i := by
  rw [Letters.latestC, Letters.latestC, min_eq_left hi, min_eq_left (by omega)]; exact latest_succ (!D.vec ·) D.B i
lemma latestV_frame (i j : ℕ) (hi : D.n0 ≤ i) (hj : D.n0 ≤ j) : D.latestV i = D.latestV j := by
  rw [Letters.latestV, Letters.latestV, min_eq_right hi, min_eq_right hj]
lemma latestC_frame (i j : ℕ) (hi : D.n0 ≤ i) (hj : D.n0 ≤ j) : D.latestC i = D.latestC j := by
  rw [Letters.latestC, Letters.latestC, min_eq_right hi, min_eq_right hj]
lemma tailPos_of_zero {n : ℕ} {a : ℕ → ℤ} (h : ∀ m, a m = 0) (u : ℕ) : tailPos n a u = 0 := by simp [tailPos, h]

def actV (D : Letters) (l : ℕ) : Bool := decide (l ≤ D.n0) && D.vec l
def actC (D : Letters) (l : ℕ) : Bool := decide (l ≤ D.n0) && !D.vec l
lemma actV_true {l : ℕ} : actV D l = true ↔ l ≤ D.n0 ∧ D.vec l = true := by simp [actV]
lemma actC_true {l : ℕ} : actC D l = true ↔ l ≤ D.n0 ∧ D.vec l = false := by simp [actC]

private lemma filter_Icc_le {a b c : ℕ} (hbc : b ≤ c) (p : ℕ → Prop) [DecidablePred p] :
    ((Icc a c).filter fun l => l ≤ b ∧ p l) = (Icc a b).filter p := by
  ext l; simp only [mem_filter, mem_Icc]
  exact ⟨fun ⟨⟨h1, _⟩, h3, h4⟩ => ⟨⟨h1, h3⟩, h4⟩, fun ⟨⟨h1, h2⟩, h4⟩ => ⟨⟨h1, h2.trans hbc⟩, h2, h4⟩⟩

lemma card_actV (i₀ : ℕ) : ((Icc (i₀ + 1) D.Ns).filter fun l => actV D l = true).card =
    ((Icc (i₀ + 1) D.n0).filter fun l => D.vec l = true).card := by simp_rw [actV_true, filter_Icc_le (n0_le_Ns D)]
lemma card_actC (i₀ : ℕ) : ((Icc (i₀ + 1) D.Ns).filter fun l => actC D l = true).card =
    ((Icc (i₀ + 1) D.n0).filter fun l => D.vec l = false).card := by simp_rw [actC_true, filter_Icc_le (n0_le_Ns D)]

lemma frame_step (hW : D.Wf) (hP : D.IsPATH mu) (i u : ℕ) (hi : i < D.Ns) (hn : D.n0 ≤ i) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailPos (D.stLen i) (stage mu i) u ∧
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailNeg (D.stLen i) (stage mu i) u := by
  obtain ⟨j, rfl⟩ : ∃ j, i = D.n0 + j := ⟨i - D.n0, by omega⟩
  have hI := interl_of_path hW hP j (by have := Ns_eq hW; omega)
  rw [show D.n0 + j + 1 = D.n0 + (j + 1) by omega, stLen_add, stLen_add,
    show D.k - j = D.k - (j + 1) + 1 by have := r_lt_k hW; have := Ns_eq hW; omega]
  exact ⟨hI.tailPos_le u, hI.rev.tailPos_le u⟩

private lemma stepV (hP : D.IsPATH mu) {i : ℕ} (hi : i + 1 ≤ D.n0) (hv : D.vec (i + 1) = true) :
    HStrip D.k (ent mu i) (ent mu (i + 1)) := by simpa using hP.2.2.1 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv
private lemma stepC (hP : D.IsPATH mu) {i : ℕ} (hi : i + 1 ≤ D.n0) (hv : D.vec (i + 1) = false) :
    HStrip D.k (ent mu (i + 1)) (ent mu i) := by simpa using hP.2.2.2.1 (i + 1) (by omega) (hi.trans (n0_le_Ns D)) hv

lemma pos_A (hP : D.IsPATH mu) (i u : ℕ) (ha : actV D (i + 1) = true) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) (u + 1) ≤ tailPos (D.stLen i) (stage mu i) u ∧
      D.SPos (u + 1) (i + 1) = D.SPos u i := by
  obtain ⟨hi, hv⟩ := actV_true.1 ha
  simpa [stLen_le _ hi, stLen_le _ (Nat.le_of_succ_le hi), stage_le _ hi, stage_le _ (Nat.le_of_succ_le hi),
    Letters.SPos, latestV_succ i hi, hv] using (stepV hP hi hv).tailPos_shift u

lemma pos_active_zero (hP : D.IsPATH mu) (i : ℕ) (ha : actV D (i + 1) = true) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) 0 - tailPos (D.stLen i) (stage mu i) 0 ≤
      (D.SPos 0 (i + 1) : ℤ) - D.SPos 0 i := by
  obtain ⟨hi, hv⟩ := actV_true.1 ha; have hW := hP.2.2.2.2.1 (i + 1) (by omega) hi hv
  simp only [Nat.add_sub_cancel] at hW
  rw [stLen_le _ hi, stLen_le _ (by omega), stage_le _ hi, stage_le _ (by omega)]
  simp only [Letters.SPos, latestV_succ i hi, hv, ↓reduceIte, List.drop_zero, List.sum_cons, Nat.cast_add]
  linarith [(stepV hP hi hv).tailPos_zero]

lemma pos_I (hW : D.Wf) (hP : D.IsPATH mu) (i u : ℕ) (hN : i < D.Ns) (ha : actV D (i + 1) = false) :
    tailPos (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailPos (D.stLen i) (stage mu i) u ∧
      D.SPos u (i + 1) = D.SPos u i := by
  by_cases hi : i + 1 ≤ D.n0
  · have hv : D.vec (i + 1) = false := by simp [actV, hi] at ha; exact ha
    simpa [stLen_le _ hi, stLen_le _ (Nat.le_of_succ_le hi), stage_le _ hi, stage_le _ (Nat.le_of_succ_le hi),
      Letters.SPos, latestV_succ i hi, hv] using (stepC hP hi hv).tailPos_le u
  · refine ⟨(frame_step hW hP i u hN (by omega)).1, ?_⟩
    rw [Letters.SPos, Letters.SPos, latestV_frame (i + 1) i (by omega) (by omega)]

lemma neg_A (hP : D.IsPATH mu) (i u : ℕ) (ha : actC D (i + 1) = true) :
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) (u + 1) ≤ tailNeg (D.stLen i) (stage mu i) u ∧
      D.SNeg (u + 1) (i + 1) = D.SNeg u i := by
  obtain ⟨hi, hv⟩ := actC_true.1 ha
  simpa [stLen_le _ hi, stLen_le _ (Nat.le_of_succ_le hi), stage_le _ hi, stage_le _ (Nat.le_of_succ_le hi),
    tailNeg_eq, Letters.SNeg, latestC_succ i hi, hv] using (stepC hP hi hv).rev.tailPos_shift u

lemma neg_active_zero (hP : D.IsPATH mu) (i : ℕ) (ha : actC D (i + 1) = true) :
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) 0 - tailNeg (D.stLen i) (stage mu i) 0 ≤
      (D.SNeg 0 (i + 1) : ℤ) - D.SNeg 0 i := by
  obtain ⟨hi, hv⟩ := actC_true.1 ha; have hW := hP.2.2.2.2.2.1 (i + 1) (by omega) hi hv
  simp only [Nat.add_sub_cancel] at hW
  rw [stLen_le _ hi, stLen_le _ (by omega), stage_le _ hi, stage_le _ (by omega), tailNeg_eq, tailNeg_eq]
  simp only [Letters.SNeg, latestC_succ i hi, hv, Bool.not_false, ↓reduceIte, List.drop_zero, List.sum_cons, Nat.cast_add]
  have h1 := (stepC hP hi hv).rev.tailPos_zero; rw [wsize_rev, wsize_rev] at h1; linarith

lemma neg_I (hW : D.Wf) (hP : D.IsPATH mu) (i u : ℕ) (hN : i < D.Ns) (ha : actC D (i + 1) = false) :
    tailNeg (D.stLen (i + 1)) (stage mu (i + 1)) u ≤ tailNeg (D.stLen i) (stage mu i) u ∧
      D.SNeg u (i + 1) = D.SNeg u i := by
  by_cases hi : i + 1 ≤ D.n0
  · have hv : D.vec (i + 1) = true := by simp [actC, hi] at ha; exact ha
    simpa [stLen_le _ hi, stLen_le _ (Nat.le_of_succ_le hi), stage_le _ hi, stage_le _ (Nat.le_of_succ_le hi),
      tailNeg_eq, Letters.SNeg, latestC_succ i hi, hv] using (stepV hP hi hv).rev.tailPos_le u
  · refine ⟨(frame_step hW hP i u hN (by omega)).2, ?_⟩
    rw [Letters.SNeg, Letters.SNeg, latestC_frame (i + 1) i (by omega) (by omega)]

theorem pathTailBounds : PathTailBounds := by
  intro D mu hW hP
  have h0 (u : ℕ) : tailPos (D.stLen 0) (stage mu 0) u = 0 :=
    tailPos_of_zero (fun m => by rw [stage_le 0 (Nat.zero_le _), hP.1]) u
  have h0' (u : ℕ) : tailNeg (D.stLen 0) (stage mu 0) u = 0 :=
    tailPos_of_zero (fun m => by simp [stage_le 0 (Nat.zero_le _), hP.1]) u
  have bP := abs_bound D.Ns (fun i u => tailPos (D.stLen i) (stage mu i) u) D.SPos (actV D)
    (fun u => by rw [h0]; exact Nat.cast_nonneg _) (fun i u _ => pos_A hP i u) (fun i _ => pos_active_zero hP i) (pos_I hW hP)
  have bN := abs_bound D.Ns (fun i u => tailNeg (D.stLen i) (stage mu i) u) D.SNeg (actC D)
    (fun u => by rw [h0']; exact Nat.cast_nonneg _) (fun i u _ => neg_A hP i u) (fun i _ => neg_active_zero hP i) (neg_I hW hP)
  refine ⟨fun i u hi => ⟨bP i hi u, bN i hi u⟩, fun i₀ u X hi₀ _ h => ?_, fun i₀ u X hi₀ _ h => ?_⟩
  · simpa [card_actV, Letters.SPos, latestV_frame D.Ns D.n0 (n0_le_Ns D) le_rfl] using
      deficit_persists_of_active_inactive_recursion D.Ns (fun i u => tailPos (D.stLen i) (stage mu i) u) D.SPos
        (actV D) (fun i u _ => pos_A hP i u) (pos_I hW hP) i₀ u X h D.Ns hi₀ le_rfl
  · simpa [card_actC, Letters.SNeg, latestC_frame D.Ns D.n0 (n0_le_Ns D) le_rfl] using
      deficit_persists_of_active_inactive_recursion D.Ns (fun i u => tailNeg (D.stLen i) (stage mu i) u) D.SNeg
        (actC D) (fun i u _ => neg_A hP i u) (neg_I hW hP) i₀ u X h D.Ns hi₀ le_rfl

end Formalism.InvariantFactorPaths.BranchingDimensions
