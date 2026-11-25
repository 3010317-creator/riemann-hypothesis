module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ColumnWordReductionOfFour
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Foundation
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ValuationLambdaFieldProperties
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Analysis.Complex.ExponentialBounds
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf
section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Per

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

theorem fr_period (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) (m : ℤ) :
    F.fr (j + m * F.J) i = F.fr j i + m * n' := by
  induction m using Int.induction_on with
  | zero => simp
  | succ k ih =>
    have := hV.2.1 (j + (k : ℤ) * F.J) i
    rw [show j + ((k : ℤ) + 1) * F.J = j + (k : ℤ) * F.J + F.J by ring, this, ih]; ring
  | pred k ih =>
    have := hV.2.1 (j + (-(k : ℤ) - 1) * F.J) i
    rw [show j + (-(k : ℤ) - 1) * F.J + F.J = j + -(k : ℤ) * F.J by ring, ih] at this
    linarith

theorem posOf_add_mul (x m : ℤ) : posOf n' (x + m * n') = posOf n' x := by
  simp [posOf, Int.add_mul_emod_self_right]

theorem late_reduce (hV : F.Valid L₁ N₁) (j x : ℤ) (hx : x ∈ F.letters j) (hW : ¬ F.IsW j x) :
    ∃ j' : ℕ, j' < F.J ∧ ∃ x' : ℤ, x' ∈ F.letters (j' : ℤ) ∧ ¬ F.IsW (j' : ℤ) x' ∧ posOf n' x' = posOf n' x ∧
      F.dist (j' : ℤ) x' = F.dist j x := by
  have hJ : (1 : ℤ) ≤ F.J := by exact_mod_cast hV.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = j % F.J :=
    ⟨_, Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))⟩
  have hkJ : (k : ℤ) < F.J := hk ▸ Int.emod_lt_of_pos _ (by omega)
  obtain ⟨m, hj⟩ : ∃ m : ℤ, j = (k : ℤ) + m * F.J := by
    refine ⟨j / F.J, ?_⟩
    have h := ((Int.ediv_emod_unique (a := j) (b := (F.J : ℤ)) (by omega)).1 ⟨rfl, rfl⟩).1
    rw [hk]
    linarith [mul_comm (F.J : ℤ) (j / F.J)]
  have e1 : F.fr j (r - 1) = F.fr (k : ℤ) (r - 1) + m * n' := by
    rw [hj]
    exact fr_period hV _ _ _
  have e2 : F.fr (j - 1) 0 = F.fr ((k : ℤ) - 1) 0 + m * n' := by
    rw [show j - 1 = ((k : ℤ) - 1) + m * F.J by rw [hj]; ring]
    exact fr_period hV _ _ _
  have e3 : F.fr (j - 1) (r - 1) = F.fr ((k : ℤ) - 1) (r - 1) + m * n' := by
    rw [show j - 1 = ((k : ℤ) - 1) + m * F.J by rw [hj]; ring]
    exact fr_period hV _ _ _
  have hpos : posOf n' (x - m * n') = posOf n' x := by
    have h := posOf_add_mul (n' := n') (x - m * n') m
    rw [sub_add_cancel] at h
    exact h.symm
  refine ⟨k, by exact_mod_cast hkJ, x - m * n', ?_, ?_, hpos, ?_⟩
  · simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
    rw [e1, e2] at hx
    rw [hpos]
    exact ⟨⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩, hx.2⟩
  · simp only [Frames.IsW] at hW ⊢
    rw [e3] at hW
    intro h
    exact hW (by linarith)
  · simp only [Frames.dist]
    rw [e1]
    congr 1
    ring

end Per

section Lab

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

open Classical in
def ellExp (l : Fin n' × Fin (r + K) →₀ ℕ) (j : ℤ) : ℤ × Fin (r + K) →₀ ℕ :=
  Finsupp.onFinset (X.toLate j ×ˢ (Finset.univ : Finset (Fin (r + K))))
    (fun v => if v.1 ∈ X.toLate j then l (posOf n' v.1, v.2) / p ^ X.F.dist j v.1 else 0)
    (fun v hv => by
      rw [Finset.mem_product]
      refine ⟨?_, Finset.mem_univ _⟩
      by_contra h
      exact hv (ite_eq_right h))

open Classical in
theorem ellExp_apply (l : Fin n' × Fin (r + K) →₀ ℕ) (j : ℤ) (v : ℤ × Fin (r + K)) :
    ellExp X p K l j v = if v.1 ∈ X.toLate j then l (posOf n' v.1, v.2) / p ^ X.F.dist j v.1 else 0 := rfl

open Classical in
theorem img_ellExp (l : Fin n' × Fin (r + K) →₀ ℕ) (j : ℤ) (t : Fin n') (c : Fin (r + K)) :
    imgMon (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2)) (fun v => p ^ X.F.dist j v.1) (ellExp X p K l j) (t, c) =
      ∑ x ∈ X.toLate j, if posOf n' x = t then p ^ X.F.dist j x * (l (t, c) / p ^ X.F.dist j x) else 0 := by
  unfold imgMon ellExp
  rw [Finsupp.sum_apply, Finsupp.onFinset_sum _ (fun v => by simp)]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Finset.sum_eq_single c]
  · by_cases h : posOf n' x = t
    · subst h
      simp [hx]
    · simp [hx, h, Prod.ext_iff]
  · intro b _ hb
    simp [Prod.ext_iff, hb]
  · simp

end Lab

private theorem phSeg_monomial_one {O : Type} [CommRing O] {n' r : ℕ} [NeZero n'] (K p : ℕ)
    (F : Frames n' r) (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) :
    phSeg O K p F j (monomial e 1) =
      monomial (imgMon (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2))
        (fun v => p ^ F.dist j v.1) e) (1 : O) := by
  rw [phSeg, aeval_monomial, map_one, one_mul, imgMon, Finsupp.sum, monomial_sum_one, Finsupp.prod]
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [← X_pow_eq_monomial, ← pow_mul]

private theorem eq_of_posOf_eq_of_dist_lt {n' : ℕ} [NeZero n'] {x y : ℤ} (hxy : posOf n' x = posOf n' y)
    (h1 : x - y < n') (h2 : y - x < n') : x = y := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have hm : x % (n' : ℤ) = y % (n' : ℤ) := by
    have h := congrArg Fin.val hxy
    simp only [posOf] at h
    have ha := Int.emod_nonneg x hn.ne'
    have hb := Int.emod_lt_of_pos x hn
    have hc := Int.emod_nonneg y hn.ne'
    have hd := Int.emod_lt_of_pos y hn
    generalize x % (n' : ℤ) = a at *
    generalize y % (n' : ℤ) = b at *
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
    omega
  exact (sub_eq_zero.1 (Int.eq_zero_of_abs_lt_dvd (show x ≡ y [ZMOD n'] from hm).dvd
    (abs_sub_lt_iff.2 ⟨h2, h1⟩))).symm

private theorem eq_of_posOf_eq_of_mem_letters_not_isW {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}
    (hV : F.Valid L₁ N₁) {j1 j2 : ℕ} (hj1 : j1 < F.J) (hj2 : j2 < F.J) {x1 x2 : ℤ}
    (h1 : x1 ∈ F.letters (j1 : ℤ)) (h1' : ¬ F.IsW (j1 : ℤ) x1)
    (h2 : x2 ∈ F.letters (j2 : ℤ)) (h2' : ¬ F.IsW (j2 : ℤ) x2)
    (hp : posOf n' x1 = posOf n' x2) : j1 = j2 ∧ x1 = x2 := by
  have hmono := eFr_strictMono hV
  have hper : F.fr ((F.J : ℤ) - 1) (r - 1) = F.fr (-1) (r - 1) + n' := by
    have h := fr_period hV (-1) (r - 1) 1
    rw [show (-1 : ℤ) + 1 * F.J = F.J - 1 by ring, one_mul] at h
    exact h
  have bnd : ∀ (j : ℕ), j < F.J → ∀ x, x ∈ F.letters (j : ℤ) → ¬ F.IsW (j : ℤ) x →
      F.fr ((j : ℤ) - 1) (r - 1) < x ∧ x ≤ F.fr (j : ℤ) (r - 1) ∧
        F.fr (-1) (r - 1) < x ∧ x ≤ F.fr (-1) (r - 1) + n' := by
    intro j hj x hx hW
    simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx
    simp only [Frames.IsW, not_le] at hW
    have a1 : F.fr (-1) (r - 1) ≤ F.fr ((j : ℤ) - 1) (r - 1) := hmono.monotone (by omega)
    have a2 : F.fr (j : ℤ) (r - 1) ≤ F.fr ((F.J : ℤ) - 1) (r - 1) := hmono.monotone (by omega)
    exact ⟨hW, hx.1.2, by linarith, by linarith⟩
  obtain ⟨b1, c1, d1, e1⟩ := bnd j1 hj1 x1 h1 h1'
  obtain ⟨b2, c2, d2, e2⟩ := bnd j2 hj2 x2 h2 h2'
  have hx : x1 = x2 := eq_of_posOf_eq_of_dist_lt hp (by linarith) (by linarith)
  subst hx
  refine ⟨?_, rfl⟩
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : F.fr (j1 : ℤ) (r - 1) ≤ F.fr ((j2 : ℤ) - 1) (r - 1) := hmono.monotone (by omega)
    linarith
  · have : F.fr (j2 : ℤ) (r - 1) ≤ F.fr ((j1 : ℤ) - 1) (r - 1) := hmono.monotone (by omega)
    linarith

theorem coarse_label_factorisation : CoarseLabelFactorisation := by
  intro p n' r K _ _ _ D O _ hH l hl
  have hV := hH.valid
  have hp : 0 < p := hH.prime.pos
  have hpp : ∀ k : ℕ, 0 < p ^ k := fun k => pow_pos hp k
  have hmem : ∀ (j x : ℤ), x ∈ D.toLate j ↔ x ∈ D.F.letters j ∧ ¬ D.F.IsW j x := fun j x => by
    simp [Dat.toLate, Finset.mem_filter]
  set S : Fin n' × Fin (r + K) →₀ ℕ := ∑ j ∈ Finset.range D.F.J,
    imgMon (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2))
      (fun v => p ^ D.F.dist (j : ℤ) v.1) (ellExp D p K l j) with hS
  have hSval : ∀ t c, S (t, c) = ∑ j ∈ Finset.range D.F.J, ∑ x ∈ D.toLate (j : ℤ),
      if posOf n' x = t then p ^ D.F.dist (j : ℤ) x * (l (t, c) / p ^ D.F.dist (j : ℤ) x) else 0 := by
    intro t c
    rw [hS, Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl (fun j _ => img_ellExp D p K l j t c)
  have hS1 : ∀ t c (j0 : ℕ) (x0 : ℤ), j0 < D.F.J → x0 ∈ D.toLate (j0 : ℤ) → posOf n' x0 = t →
      S (t, c) = p ^ D.F.dist (j0 : ℤ) x0 * (l (t, c) / p ^ D.F.dist (j0 : ℤ) x0) := by
    intro t c j0 x0 hj0 hx0 ht
    rw [hSval, Finset.sum_eq_single j0, Finset.sum_eq_single x0, ite_eq_left ht]
    · intro x hx hne
      rw [ite_eq_right]
      intro hxt
      rw [hmem] at hx hx0
      exact hne (eq_of_posOf_eq_of_mem_letters_not_isW hV hj0 hj0 hx.1 hx.2 hx0.1 hx0.2 (hxt.trans ht.symm)).2
    · intro h
      exact absurd hx0 h
    · intro b hb hne
      refine Finset.sum_eq_zero (fun x hx => ?_)
      rw [ite_eq_right]
      intro hxt
      rw [hmem] at hx hx0
      exact hne (eq_of_posOf_eq_of_mem_letters_not_isW hV (Finset.mem_range.1 hb) hj0 hx.1 hx.2 hx0.1 hx0.2
        (hxt.trans ht.symm)).1
    · intro h
      exact absurd (Finset.mem_range.2 hj0) h
  have hS0 : ∀ t c, (∀ (j : ℕ), j < D.F.J → ∀ x ∈ D.toLate (j : ℤ), posOf n' x ≠ t) →
      S (t, c) = 0 := by
    intro t c h
    rw [hSval]
    refine Finset.sum_eq_zero (fun j hj => Finset.sum_eq_zero (fun x hx => ?_))
    rw [ite_eq_right (h j (Finset.mem_range.1 hj) x hx)]
  have hle : ∀ t c, S (t, c) ≤ l (t, c) := by
    intro t c
    by_cases h : ∃ j0 : ℕ, j0 < D.F.J ∧ ∃ x0 ∈ D.toLate (j0 : ℤ), posOf n' x0 = t
    · obtain ⟨j0, hj0, x0, hx0, ht⟩ := h
      rw [hS1 t c j0 x0 hj0 hx0 ht]
      exact Nat.mul_div_le _ _
    · push Not at h
      rw [hS0 t c h]
      exact Nat.zero_le _
  have hsum : l - S + S = l := by
    ext ⟨t, c⟩
    rw [Finsupp.add_apply, Finsupp.tsub_apply]
    have := hle t c
    omega
  refine ⟨l - S, fun j => ellExp D p K l j, ?_, ?_, ?_⟩
  · intro j x hx hW c
    obtain ⟨j', hj', x', hx', hW', hpos, hdist⟩ := late_reduce hV j x hx hW
    rw [Finsupp.tsub_apply, ← hpos, hS1 _ c j' x' hj' ((hmem _ _).2 ⟨hx', hW'⟩) rfl, ← hdist]
    have h0 := Nat.mod_add_div (l (posOf n' x', c)) (p ^ D.F.dist (j' : ℤ) x')
    have hlt := Nat.mod_lt (l (posOf n' x', c)) (hpp (D.F.dist (j' : ℤ) x'))
    generalize l (posOf n' x', c) = a at *
    generalize p ^ D.F.dist (j' : ℤ) x' = b at *
    generalize b * (a / b) = w at *
    generalize a % b = m at *
    omega
  · intro j
    refine ⟨fun v hv => ?_, fun v => ?_⟩
    · simp only [ellExp_apply] at hv
      by_contra h
      exact hv (ite_eq_right h)
    · simp only [ellExp_apply]
      split_ifs with h
      · rw [hmem] at h
        have := hl j v.1 h.1 h.2 v.2
        rw [Nat.div_lt_iff_lt_mul (hpp _), ← pow_add, Nat.add_comm (D.Rj p K j)]
        exact this
      · exact hpp _
  · simp only [phSeg_monomial_one]
    rw [← monomial_sum_one, monomial_mul, one_mul]
    exact congrArg (fun m => monomial m (1 : O)) hsum.symm

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def LateIndexInjective : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j, ∀ x ∈ X.toLate j,
    Function.Injective (X.row j x) ∧ ∀ i, X.row j x i ∈ X.F.letters j ∧ Even (X.row j x i) ∧ X.row j x i < x

def EllDegreeLePowerBound : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j e, X.IsEll p K j e →
    X.dS K j e + X.dV K j e ≤ (r + K) * X.Ns * p ^ X.Rj p K j

def PowerExceedsMaxMultiplicity (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j, X.mStar < p ^ X.Rj p K j

def ThresholdPowerLowerBound (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j b, X.Step2 p K j b → ∀ x ∈ X.toLate j,
      X.th p j x ≤ ((p ^ X.Rj p K j : ℕ) : ℝ) * (X.thc p K j b x - (((r + K) * X.Ns : ℕ) : ℝ))

theorem mem_late {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ) :
    x ∈ X.toLate j ↔ x ∈ X.F.letters j ∧ ¬ X.F.IsW j x := by
  simp only [Dat.toLate, Finset.mem_filter]

section AG

variable (D : Formalism.BasicNotions.D7) (hV : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)
  [NeZero K] {R : Type} [Field R] (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) (S : Set ℤ)

include hV

theorem vg_ellP : ((-(X.dS K j e : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ S (X.ellP K R j e) := by
  have h := vg_prod D hV (R := R) S (X.toLate j)
    (fun x => ∏ c : Fin r, (MvPolynomial.X (x, c) : MvPolynomial (ℤ × Fin r) R) ^ e (x, Fin.castAdd K c))
    (fun x => ∑ c : Fin r, (e (x, Fin.castAdd K c) : ℤ) * (if Even x then 0 else -1))
    (fun x _ => vg_prod D hV S Finset.univ _ _ (fun c _ => vg_pow D hV S (vg_X (R := R) S (x, c)) _))
  have e1 : (∑ x ∈ X.toLate j, ∑ c : Fin r, (e (x, Fin.castAdd K c) : ℤ) * (if Even x then 0 else -1)) =
      -(X.dS K j e : ℤ) := by
    unfold Dat.dS
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [e1] at h
  exact h

theorem lg_ellN : lam1S LZ S (X.ellN K R j e) ≤ (((X.dV K j e : ℤ) : ℤ) : WithBot ℤ) := by
  have h := lg_prod D hV (R := R) S (X.toLate j)
    (fun x => ∏ c : Fin K, (MvPolynomial.X (x, c) : MvPolynomial (ℤ × Fin K) R) ^ e (x, Fin.natAdd r c))
    (fun x => ∑ c : Fin K, (e (x, Fin.natAdd r c) : ℤ) * (if Even x then 1 else 0))
    (fun x _ => lg_prod D hV S Finset.univ _ _ (fun c _ => lg_pow D hV S (lg_X (R := R) S (x, c)) _))
  have e1 : (∑ x ∈ X.toLate j, ∑ c : Fin K, (e (x, Fin.natAdd r c) : ℤ) * (if Even x then 1 else 0)) =
      (X.dV K j e : ℤ) := by
    unfold Dat.dV
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> simp
  rw [e1] at h
  exact h

theorem vg_DlSeg (hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i)) (x : ℤ) (hx : x ∈ X.toLate j)
    (hinj : Function.Injective (X.row j x)) (hS : ∀ i, X.row j x i ∈ S) :
    (((X.sg p K j x : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ S (X.DlSeg p K R j) := by
  classical
  have h := vg_prod D hV (R := R) S (X.toLate j) (fun x' => X.detPl R j x' ^ X.sg p K j x')
    (fun x' => if x' = x then (X.sg p K j x : ℤ) else 0) (fun x' hx' => by
      by_cases hxx : x' = x
      · subst hxx
        rw [ite_eq_left rfl]
        have h1 : ((1 : ℤ) : WithTop ℤ) ≤ valS LZ S (X.detPl R j x') := by
          unfold Dat.detPl valS
          rw [sDegs_det LZ S _ (X.row j x') hinj (fun i => ⟨hS i, by simp [LZ, hev x' hx' i]⟩)]
          simp
        have := vg_pow D hV S h1 (X.sg p K j x')
        simpa using this
      · rw [ite_eq_right hxx]
        have := vg_pow D hV S (vg_det D hV (R := R) S (X.row j x') (hev x' hx')) (X.sg p K j x')
        simpa [Dat.detPl] using this)
  rw [Finset.sum_ite_eq' (X.toLate j) x, ite_eq_left hx] at h
  exact h

theorem vg_Aw (hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i)) (x : ℤ) (hx : x ∈ X.toLate j)
    (hinj : Function.Injective (X.row j x)) (hS : ∀ i, X.row j x i ∈ S)
    (nu : Fin (segN X.F j + 1) → Fin r → ℤ) (I' : ℤ → Finset (Fin r)) (a : ℤ)
    (ha : (a : WithTop ℤ) ≤ valS LZ S (segRen X.F j R r (Psi R nu I'))) :
    ((((p ^ X.Rj p K j : ℕ) : ℤ) * a + -(X.dS K j e : ℤ) + (X.sg p K j x : ℤ) : ℤ) : WithTop ℤ) ≤
      valS LZ S (X.Aw p K R j e nu I') := by
  unfold Dat.Aw
  exact vg_mul D hV S (vg_mul D hV S (vg_pow D hV S ha _) (vg_ellP D hV X K j e S))
    (vg_DlSeg D hV X p K j S hev x hx hinj hS)

theorem lg_Gw (ka : Fin (segN X.F j + 1) → Fin K → ℤ) (I'' : ℤ → Finset (Fin K)) (a : ℤ)
    (ha : lam1S LZ S (segRen X.F j R K (Psi R ka I'')) ≤ (a : WithBot ℤ)) :
    lam1S LZ S (X.Gw p K R j e ka I'') ≤ ((((p ^ X.Rj p K j : ℕ) : ℤ) * a + (X.dV K j e : ℤ) : ℤ) : WithBot ℤ) := by
  unfold Dat.Gw
  exact lg_mul D hV S (lg_pow D hV S ha _) (lg_ellN D hV X K j e S)

end AG

theorem int_ineq (Q κ ν dS dV s mS kN : ℤ) (hQ : 0 ≤ Q) (h : κ + (kN + 1) ≤ ν) (hd : dS + dV ≤ kN * Q)
    (hm : mS < Q) : Q * κ + dV + (mS + s) ≤ Q * ν + -dS + s := by
  nlinarith [mul_le_mul_of_nonneg_left h hQ]

theorem geR_of_le {v : WithTop ℤ} {a : ℤ} {t : ℝ} (h : (a : WithTop ℤ) ≤ v) (ht : t ≤ (a : ℝ)) : geR v t := by
  unfold geR
  intro z hz
  rw [hz] at h
  have h' : a ≤ z := WithTop.coe_le_coe.mp h
  exact ht.trans (by exact_mod_cast h')

theorem column_conditions_of_numeric_bounds (D : Formalism.BasicNotions.D7) (hV : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (C₀ : ℝ)
    (hRow : LateIndexInjective) (hN0 : EllDegreeLePowerBound) (hN1 : PowerExceedsMaxMultiplicity C₀) (hN2 : ThresholdPowerLowerBound C₀) : ColumnConditionsWithMargin C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hc x hx hW
  have : Fact p.Prime := ⟨hc.hX.prime⟩
  obtain ⟨i, rfl⟩ := segE_surj X.F j hx
  obtain ⟨nu, ka⟩ := q
  obtain ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩, hcond⟩ := hc.hq
  have hI' := hc.hI'
  have hI'' := hc.hI''
  simp only at h1 h2 hcond hI' hI'' ⊢
  have hF3 : ∀ (N n : ℕ) [NeZero n] (LL : Letters (Fin N)) (B : Fin N → ℕ) (th M : Fin N → ℤ),
      Formalism.MainNotions.CovariantDegrees.A3at (FF O) N n LL B th M := fun N n _ LL B th M => (hA3 p O S N n LL B th M).2
  rw [← h1] at hI' hcond ⊢
  rw [← h2] at hI'' hcond ⊢
  have u1 := standard_polynomial_mem_bounds (segLL X.F j) b' (hF3 _ r _ b') P1 I' hI'
  have u2 := standard_polynomial_mem_bounds (segLL X.F j) b'' (hF3 _ K _ b'') P2 I'' hI''
  obtain ⟨sA1, sA2, -, -⟩ := seg_val X.F j (Psi (FF O) P1.mu I') i
  obtain ⟨-, -, sG3, sG4⟩ := seg_val X.F j (Psi (FF O) P2.mu I'') i
  obtain ⟨cE, cO, cR⟩ := (hcond i).2 hW
  have hxl : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hW⟩
  have hM : X.Mw p K j e P2.mu (segE X.F j i) = ((p ^ X.Rj p K j : ℕ) : ℤ) *
      (if Even (segE X.F j i) then P2.mu i.succ 0 else P2.mu i.castSucc 0) + (X.dV K j e : ℤ) :=
    (segE_strictMono X.F j).injective.extend_apply _ _ i
  have hrows := hRow p n' r K X hc.hX j
  have hev : ∀ x' ∈ X.toLate j, ∀ i, Even (X.row j x' i) := fun x' hx' i => ((hrows x' hx').2 i).2.1
  have hinj := (hrows _ hxl).1
  have hlt : ∀ a, X.row j (segE X.F j i) a < segE X.F j i := fun a => ((hrows _ hxl).2 a).2.2
  have n0 := hN0 p n' r K X hc.hX j e hc.he
  have n1 := hN1 p n' r K X hc.hX hc.hLa hc.hk j
  have n2 := hN2 p n' r K X hc.hX hc.hLa hc.hk j b hc.h2 _ hxl
  have n0' : (X.dS K j e : ℤ) + (X.dV K j e : ℤ) ≤ (((r + K) * X.Ns : ℕ) : ℤ) * ((p ^ X.Rj p K j : ℕ) : ℤ) := by
    exact_mod_cast n0
  have n1' : (X.mStar : ℤ) < ((p ^ X.Rj p K j : ℕ) : ℤ) := by exact_mod_cast n1
  have hm0 : (X.m0 K : ℤ) = (((r + K) * X.Ns : ℕ) : ℤ) + 1 := by unfold Dat.m0; push_cast; ring
  have vlt := vg_Aw D hV X p K (R := FF O) j e {y | y < segE X.F j i} hev _ hxl hinj hlt P1.mu I'
    (P1.mu i.castSucc (lastIdx r)) (by rw [sA2]; exact (u1.2 i.castSucc).1)
  have vle := vg_Aw D hV X p K (R := FF O) j e {y | y ≤ segE X.F j i} hev _ hxl hinj (fun a => (hlt a).le) P1.mu I'
    (P1.mu i.succ (lastIdx r)) (by rw [sA1]; exact (u1.2 i.succ).1)
  refine ⟨fun he => ⟨?_, ?_⟩, fun he => ⟨?_, ?_⟩, ?_⟩
  · rw [hM, ite_eq_left he]
    exact lg_Gw D hV X p K j e _ P2.mu I'' _ (by rw [sG3]; exact (u2.2 i.succ).2)
  · refine le_trans (WithTop.coe_le_coe.mpr ?_) vlt
    rw [hM, ite_eq_left he]
    unfold Dat.mg
    have hce := (cE he).1
    rw [hm0] at hce
    exact int_ineq _ _ _ _ _ _ _ _ (Int.natCast_nonneg _) hce n0' n1'
  · rw [hM, ite_eq_right he]
    exact lg_Gw D hV X p K j e _ P2.mu I'' _ (by rw [sG4]; exact (u2.2 i.castSucc).2)
  · refine le_trans (WithTop.coe_le_coe.mpr ?_) vle
    rw [hM, ite_eq_right he]
    unfold Dat.mg
    have hce := (cO he).1
    rw [hm0] at hce
    exact int_ineq _ _ _ _ _ _ _ _ (Int.natCast_nonneg _) hce n0' n1'
  · refine geR_of_le vlt ?_
    push_cast
    have hQ : (0 : ℝ) ≤ ((p : ℝ) ^ X.Rj p K j) := by positivity
    have n0r : (X.dS K j e : ℝ) + (X.dV K j e : ℝ) ≤ (((r : ℝ) + K) * X.Ns) * (p : ℝ) ^ X.Rj p K j := by
      exact_mod_cast n0
    push_cast at n2
    have := mul_le_mul_of_nonneg_left cR hQ
    nlinarith

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem expand_pow_zmod (p : ℕ) [Fact p.Prime] {σ : Type} (f : MvPolynomial σ (ZMod p)) (n : ℕ) :
    expand (p ^ n) f = f ^ (p ^ n) := by
  induction f using MvPolynomial.induction_on with
  | C a => rw [expand_C, ← map_pow, ZMod.pow_card_pow]
  | add u v hu hv => rw [map_add (f := _), hu, hv, add_pow_char_pow]
  | mul_X q v h => rw [map_mul, h, expand_X, mul_pow]

theorem charP_FF {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (S : UniformizedDVR p O) : CharP (FF O) p := by
  have h0 : ((p : ℕ) : FF O) = 0 := by
    have := (IsLocalRing.residue_eq_zero_iff (p : O)).mpr S.p_mem
    simpa using this
  exact (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr h0

theorem expand_pow_of_map (p : ℕ) [Fact p.Prime] {Fd : Type} [Field Fd] (φ : ZMod p →+* Fd) {σ : Type}
    (f : MvPolynomial σ (ZMod p)) (n : ℕ) :
    expand (p ^ n) (MvPolynomial.map φ f) = (MvPolynomial.map φ f) ^ (p ^ n) := by
  rw [← map_expand, expand_pow_zmod, map_pow]

theorem map_detPl {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ) :
    MvPolynomial.map f (X.detPl R j x) = X.detPl S j x := by
  unfold Dat.detPl
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp

theorem map_DlSeg {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n' r : ℕ} [NeZero n'] (X : Dat n' r)
    (p K : ℕ) (j : ℤ) : MvPolynomial.map f (X.DlSeg p K R j) = X.DlSeg p K S j := by
  unfold Dat.DlSeg
  rw [map_prod]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [map_pow, map_detPl]

theorem ell_split {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (R : Type) [CommRing R] (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (he : X.IsEll p K j e) :
    (monomial e 1 : SegRing R r K) = plEmb R r K (X.ellP K R j e) * nmEmb R r K (X.ellN K R j e) := by
  classical
  rw [monomial_eq, map_one, one_mul]
  have hsub : e.support ⊆ X.toLate j ×ˢ (Finset.univ : Finset (Fin (r + K))) := by
    intro v hv
    rw [Finset.mem_product]
    exact ⟨he.1 v (Finsupp.mem_support_iff.mp hv), Finset.mem_univ _⟩
  rw [Finsupp.prod_of_support_subset e hsub _ (fun _ _ => pow_zero _), Finset.prod_product]
  unfold Dat.ellP Dat.ellN plEmb nmEmb
  simp only [map_prod, map_pow, rename_X]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Fin.prod_univ_add]

theorem frobenius_reduction_product (C₀ : ℝ) : FrobeniusReductionProduct C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hc
  have : Fact p.Prime := ⟨hc.hX.prime⟩
  have : CharP (FF O) p := charP_FF S
  let φ : ZMod p →+* FF O := ZMod.castHom (dvd_refl p) (FF O)
  have hW : MvPolynomial.map (IsLocalRing.residue O) (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) =
      MvPolynomial.map φ (segRen X.F j (ZMod p) (r + K) (PsiPl (ZMod p) q.1 I' * PsiTan (ZMod p) q.2 I'')) := by
    simp only [segRen, map_rename, map_mul, PsiPl_map, PsiTan_map]
  have hW2 : MvPolynomial.map (IsLocalRing.residue O) (segRen X.F j O (r + K) (PsiPl O q.1 I' * PsiTan O q.2 I'')) =
      plEmb (FF O) r K (segRen X.F j (FF O) r (Psi (FF O) q.1 I')) *
        nmEmb (FF O) r K (segRen X.F j (FF O) K (Psi (FF O) q.2 I'')) := by
    rw [← segRen_mul]
    simp only [segRen, map_rename, map_mul, PsiPl_map, PsiTan_map]
    rfl
  unfold Dat.zSeg Dat.Aw Dat.Gw
  rw [map_mul, map_mul, map_expand, hW, expand_pow_of_map, ← hW, hW2, map_monomial, map_one,
    ell_split X p K (FF O) j e hc.he]
  have hD : MvPolynomial.map (IsLocalRing.residue O) (plEmb O r K (X.DlSeg p K O j)) =
      plEmb (FF O) r K (X.DlSeg p K (FF O) j) := by
    unfold plEmb
    rw [map_rename, map_DlSeg]
  rw [hD]
  simp only [map_mul, map_pow, mul_pow]
  ring

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem detPl_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ)
    (s : Set (ℤ × Fin r)) (h : ∀ a b, (X.row j x a, b) ∈ s) : X.detPl R j x ∈ supported R s := by
  unfold Dat.detPl
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem (prod_mem fun i _ => ?_) _
  rw [Matrix.of_apply]
  exact (MvPolynomial.X_mem_supported).2 (h _ _)

theorem DlSeg_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (j : ℤ)
    (s : Set (ℤ × Fin r)) (h : ∀ x ∈ X.toLate j, ∀ a b, (X.row j x a, b) ∈ s) : X.DlSeg p K R j ∈ supported R s := by
  unfold Dat.DlSeg
  exact prod_mem fun x hx => pow_mem (detPl_supported R X j x s (h x hx)) _

theorem ellP_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (s : Set (ℤ × Fin r)) (h : ∀ x ∈ X.toLate j, ∀ b, (x, b) ∈ s) :
    X.ellP K R j e ∈ supported R s := by
  unfold Dat.ellP
  exact prod_mem fun x hx => prod_mem fun c _ => pow_mem ((MvPolynomial.X_mem_supported).2 (h x hx c)) _

theorem ellN_supported (R : Type) [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (s : Set (ℤ × Fin K)) (h : ∀ x ∈ X.toLate j, ∀ b, (x, b) ∈ s) :
    X.ellN K R j e ∈ supported R s := by
  unfold Dat.ellN
  exact prod_mem fun x hx => prod_mem fun c _ => pow_mem ((MvPolynomial.X_mem_supported).2 (h x hx c)) _

theorem allowed_letters_of_late_rows (D : Formalism.BasicNotions.D7) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (C₀ : ℝ) (hRow : LateIndexInjective) : ProductAllowedLetters C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hW
  classical
  have hX := hW.hX
  haveI : Fact p.Prime := ⟨hX.prime⟩
  have hlet : ∀ i : Fin (segN X.F j), segE X.F j i ∈ X.F.letters j := fun i =>
    ((X.F.letters j).orderIsoOfFin rfl i).2
  have hren : ∀ {k : ℕ} (P : MvPolynomial (Fin (segN X.F j) × Fin k) (FF O)) (s : Set (ℤ × Fin k)),
      (∀ v ∈ P.vars, (segE X.F j v.1, v.2) ∈ s) → segRen X.F j (FF O) k P ∈ supported (FF O) s := by
    intro k P s hs
    rw [MvPolynomial.mem_supported]
    intro v hv
    unfold segRen at hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ P hv)
    exact hs w hw
  obtain ⟨b', b'', ⟨P1, hP1⟩, ⟨P2, hP2⟩, hcond⟩ := hW.hq
  refine ⟨?_, ?_⟩
  · unfold Dat.Aw
    refine mul_mem (mul_mem (pow_mem (hren _ _ fun v _ => hlet v.1) _) ?_) ?_
    · exact ellP_supported (FF O) X K j e _ fun x hx c => (Finset.mem_filter.1 hx).1
    · exact DlSeg_supported (FF O) X p K j _ fun x hx a c => ((hRow p n' r K X hX j x hx).2 a).1
  · unfold Dat.Gw
    have hA := (hA3 p O S (segN X.F j) K (segLL X.F j) b'' (fun i => q.2 i.succ (lastIdx K))
      (fun i => q.2 i.succ 0)).2
    have hPol : Psi (FF O) q.2 I'' ∈ Pol (FF O) K b'' :=
      ((Set.ext_iff.1 hA _).2 (Submodule.subset_span ⟨P2, I'', by rw [hP2]; exact hW.hI'',
        fun i => by rw [hP2]; exact ⟨le_rfl, le_rfl⟩, by rw [hP2]⟩)).1
    have hseg : segRen X.F j (FF O) K (Psi (FF O) q.2 I'') ∈
        supported (FF O) {v : ℤ × Fin K | v.1 ∈ X.F.letters j ∧ ¬ X.F.IsW j v.1} := by
      refine hren _ _ fun v hv => ⟨hlet v.1, fun hWv => ?_⟩
      obtain ⟨m, hm, hvm⟩ := (MvPolynomial.mem_vars_iff_mem_support _).1 hv
      have hb0 : b'' v.1 = 0 := (hcond v.1).1 hWv
      have hsum : multideg m v.1 = b'' v.1 := ((MvPolynomial.mem_restrictSupport_iff _).1 hPol) hm v.1
      rw [hb0] at hsum
      have h0 : m (v.1, v.2) = 0 := Finset.sum_eq_zero_iff.1 hsum v.2 (Finset.mem_univ _)
      exact (Finsupp.mem_support_iff.1 hvm) h0
    refine mul_mem (pow_mem hseg _) ?_
    exact ellN_supported (FF O) X K j e _ fun x hx c =>
      ⟨(Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2⟩

def DegAt {R : Type} [CommRing R] {ι : Type} {n : ℕ} (x : ι) (d : ℕ) (P : MvPolynomial (ι × Fin n) R) : Prop :=
  ∀ m ∈ P.support, multideg m x = d

section DegAt

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ} {x : ι}

theorem degAt_mul {d d' : ℕ} {P Q : MvPolynomial (ι × Fin n) R} (hP : DegAt x d P) (hQ : DegAt x d' Q) :
    DegAt x (d + d') (P * Q) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul P Q hm)
  simp only [multideg, Finsupp.add_apply, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) (hP a ha) (hQ b hb)

theorem degAt_one : DegAt x 0 (1 : MvPolynomial (ι × Fin n) R) := by
  classical
  intro m hm
  have h0 : m = 0 := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_one, ite_eq_right (Ne.symm hne)])
  subst h0
  simp [multideg]

theorem degAt_pow {d : ℕ} {P : MvPolynomial (ι × Fin n) R} (hP : DegAt x d P) (k : ℕ) : DegAt x (k * d) (P ^ k) := by
  induction k with
  | zero => rw [pow_zero, zero_mul]; exact degAt_one
  | succ k ih => rw [pow_succ, add_mul, one_mul]; exact degAt_mul ih hP

theorem degAt_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ι × Fin n) R) (d : κ → ℕ)
    (h : ∀ i ∈ s, DegAt x (d i) (f i)) : DegAt x (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact degAt_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact degAt_mul (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem degAt_X [DecidableEq ι] (v : ι × Fin n) : DegAt x (if v.1 = x then 1 else 0) (X v : MvPolynomial (ι × Fin n) R) := by
  classical
  intro m hm
  have h0 : Finsupp.single v 1 = m := by
    by_contra hne
    exact (MvPolynomial.mem_support_iff.1 hm) (by rw [MvPolynomial.coeff_X', ite_eq_right hne])
  subst h0
  obtain ⟨a, c0⟩ := v
  by_cases ha : a = x
  · subst ha
    simp [multideg, Finsupp.single_apply, Prod.ext_iff]
  · simp [multideg, Prod.ext_iff, ha]

theorem degAt_of_supported {P : MvPolynomial (ι × Fin n) R} (s : Set (ι × Fin n)) (hP : P ∈ supported R s)
    (hs : ∀ v ∈ s, v.1 ≠ x) : DegAt x 0 P := by
  intro m hm
  rw [MvPolynomial.mem_supported] at hP
  show ∑ c, m (x, c) = 0
  refine Finset.sum_eq_zero fun c _ => ?_
  by_contra hne
  have hv : (x, c) ∈ P.vars := (MvPolynomial.mem_vars_iff_mem_support _).2 ⟨m, hm, Finsupp.mem_support_iff.2 hne⟩
  exact hs _ (hP hv) rfl

end DegAt

theorem degAt_segRen {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (F : Frames n' r) (j : ℤ) {n : ℕ}
    {b : Fin (segN F j) → ℕ} {A : MvPolynomial (Fin (segN F j) × Fin n) R} (hA : A ∈ Pol R n b) (i : Fin (segN F j)) :
    DegAt (segE F j i) (b i) (segRen F j R n A) := by
  classical
  have hinj : Function.Injective (fun v : Fin (segN F j) × Fin n => (segE F j v.1, v.2)) := by
    rintro ⟨a, c⟩ ⟨a', c'⟩ h
    simp only [Prod.mk.injEq] at h
    have ha : a = a' := ((F.letters j).orderIsoOfFin rfl).injective (Subtype.ext (by exact h.1))
    rw [ha, h.2]
  intro m hm
  unfold segRen at hm
  rw [MvPolynomial.support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  have h0 := ((MvPolynomial.mem_restrictSupport_iff _).1 hA) hm0
  show ∑ c, (Finsupp.mapDomain _ m0) (segE F j i, c) = b i
  rw [← h0 i]
  exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply_of_injective hinj m0 (i, c)

theorem ordDeg_prod {R : Type} [CommRing R] {r K : ℕ} {x : ℤ} {dA dG : ℕ} {A : MvPolynomial (ℤ × Fin r) R}
    {G : MvPolynomial (ℤ × Fin K) R} (hA : ¬ Even x → DegAt x dA A) (hG : Even x → DegAt x dG G) :
    ∀ mm ∈ (plEmb R r K A * nmEmb R r K G).support, ordDeg mm x = if Even x then dG else dA := by
  classical
  intro mm hmm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul _ _ hmm)
  have hi1 : Function.Injective (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) := by
    rintro ⟨u1, u2⟩ ⟨w1, w2⟩ h
    simp only [Prod.mk.injEq, Fin.castAdd_inj] at h
    rw [h.1, h.2]
  have hi2 : Function.Injective (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) := by
    rintro ⟨u1, u2⟩ ⟨w1, w2⟩ h
    simp only [Prod.mk.injEq, Fin.natAdd_inj] at h
    rw [h.1, h.2]
  unfold plEmb at ha
  unfold nmEmb at hb
  rw [MvPolynomial.support_rename_of_injective hi1, Finset.mem_image] at ha
  rw [MvPolynomial.support_rename_of_injective hi2, Finset.mem_image] at hb
  obtain ⟨a0, ha0, rfl⟩ := ha
  obtain ⟨b0, hb0, rfl⟩ := hb
  unfold ordDeg
  split_ifs with hx
  · have h1 : ∀ c : Fin K, (Finsupp.mapDomain (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) a0)
        (x, Fin.natAdd r c) = 0 := fun c => by
      refine Finsupp.mapDomain_notin_range _ _ ?_
      rintro ⟨⟨y, d⟩, h⟩
      simp only [Prod.mk.injEq] at h
      have := congrArg Fin.val h.2
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
      omega
    simp only [Finsupp.add_apply, h1, zero_add]
    rw [← hG hx b0 hb0]
    exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply_of_injective hi2 b0 (x, c)
  · have h1 : ∀ c : Fin r, (Finsupp.mapDomain (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) b0)
        (x, Fin.castAdd K c) = 0 := fun c => by
      refine Finsupp.mapDomain_notin_range _ _ ?_
      rintro ⟨⟨y, d⟩, h⟩
      simp only [Prod.mk.injEq] at h
      have := congrArg Fin.val h.2
      simp only [Fin.coe_castAdd, Fin.coe_natAdd] at this
      omega
    simp only [Finsupp.add_apply, h1, add_zero]
    rw [← hA hx a0 ha0]
    exact Finset.sum_congr rfl fun c _ => Finsupp.mapDomain_apply_of_injective hi1 a0 (x, c)

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def OldestLetterInSegment : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j, ∀ x ∈ X.toLate j,
    X.F.oldest j x ∈ X.F.letters j ∧ (¬ X.F.IsW j (X.F.oldest j x) → X.F.oldest j x ∈ X.F.LLset j)

def OrderNumericBound (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j, ∀ x ∈ X.toLate j,
      ((p ^ X.Rj p K j : ℕ) : ℝ) * X.oc p K j x + Dat.k (r := r) K * ((p ^ X.Rj p K j : ℕ) : ℝ) ≤ X.o p K j x

section Num

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem frame_zero_le {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) : ∀ i, i < r → F.fr j 0 ≤ F.fr j i := by
  intro i
  induction i with
  | zero => intro _; exact le_rfl
  | succ i ih => intro h; exact (ih (by omega)).trans (hV.2.2.1 j i h).le

theorem reflection_mem_Glev_castSucc {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) : F.fr (j - 1) 0 ∈ F.letters j := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := frame_zero_le hV (j - 1) (r - 1) (by omega)
  have h2 := hV.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h2
  have h3 := frame_zero_le hV j (r - 1) (by omega)
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨le_rfl, by omega⟩, (hV.2.2.2.2.1 (j - 1) 0 hr).1⟩

theorem mem_letters_bounds {F : Frames n' r} {j x : ℤ} (hx : x ∈ F.letters j) :
    F.fr (j - 1) 0 ≤ x ∧ x ≤ F.fr j (r - 1) ∧ posOf n' x ∈ F.TT := by
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx
  exact ⟨hx.1.1, hx.1.2, hx.2⟩

structure Basics (X : Dat n' r) (p K : ℕ) : Prop where
  p1 : (1 : ℝ) < p
  Ns1 : (1 : ℝ) ≤ X.Ns
  k5 : (5 : ℝ) ≤ Dat.k (r := r) K
  rk : (r : ℝ) ≤ Dat.k (r := r) K
  Q1 : (1 : ℝ) ≤ X.Q
  Y1 : (1 : ℝ) ≤ X.Y

theorem basics (hX : X.Hyp p K) : Basics X p K := by
  have hV := hX.valid
  have hw := reflection_mem_Glev_castSucc hV 0
  have hp : (13 : ℝ) ≤ p := by exact_mod_cast hX.p13
  have hc : 1 ≤ (X.F.letters 0).card := Finset.card_pos.mpr ⟨_, hw⟩
  have hNs : 1 ≤ X.Ns := hc.trans (hX.card 0)
  have hK := hX.NsK
  have hr := hX.r2
  have hQ := hX.twist 0 _ hw
  refine ⟨by linarith, by exact_mod_cast hNs, ?_, ?_, ?_, hX.Y1⟩
  · unfold Dat.k
    exact_mod_cast (by omega : 5 ≤ r + K)
  · unfold Dat.k
    exact_mod_cast (by omega : r ≤ r + K)
  · exact le_trans (one_le_pow₀ (by linarith : (1 : ℝ) ≤ p)) hQ

def Tj (X : Dat n' r) (p K : ℕ) (j : ℤ) : ℝ :=
  X.a / (8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0))

theorem den_pos (hX : X.Hyp p K) (j : ℤ) :
    0 < 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := by
  have B := basics hX
  have h1 : (0 : ℝ) < p := by linarith [B.p1]
  have h2 : (0 : ℝ) < X.Y := by linarith [B.Y1]
  have h3 : (0 : ℝ) < Dat.k (r := r) K := by linarith [B.k5]
  have h4 : (0 : ℝ) < X.Ns := by linarith [B.Ns1]
  positivity

theorem Tj_ge (hX : X.Hyp p K) (j : ℤ) : 4 * (p : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) ≤ Tj X p K j := by
  have b := basics hX
  have hd := den_pos hX j
  have hw := reflection_mem_Glev_castSucc hX.valid j
  have hQ := hX.twist j _ hw
  have P3 := hX.P3
  have hY : 0 ≤ X.Y := by linarith [b.Y1]
  have hp0 : (0 : ℝ) ≤ p := by linarith [b.p1]
  have hdQ : (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) ≤ X.Q ^ 2 := hQ.trans (by nlinarith [b.Q1])
  have hk : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  have hc : 0 ≤ (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hp0 hY) (sq_nonneg _)) (Nat.cast_nonneg _))
      (by positivity)
  have hm := mul_le_mul_of_nonneg_left hdQ hc
  unfold Tj
  rw [le_div_iff₀ hd, hk]
  calc 4 * (p : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) * (8 * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0))
        = 32 * ((p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0)) := by ring
    _ ≤ 32 * ((p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) * X.Q ^ 2) := by linarith
    _ = 32 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) := by ring
    _ ≤ X.a := P3

theorem pow_Rj_le (hX : X.Hyp p K) (j : ℤ) : ((p : ℝ) ^ X.Rj p K j) ≤ Tj X p K j := by
  have B := basics hX
  have hT := Tj_ge hX j
  have hT1 : (1 : ℝ) ≤ Tj X p K j := by
    have h0 : (0 : ℝ) ≤ (X.E₀ : ℝ) + X.mStar := by positivity
    nlinarith [B.p1]
  have hfl : ⌊Tj X p K j⌋₊ ≠ 0 := by
    have : 1 ≤ ⌊Tj X p K j⌋₊ := Nat.le_floor (by simpa using hT1)
    omega
  have h1 : p ^ X.Rj p K j ≤ ⌊Tj X p K j⌋₊ := Nat.pow_log_le_self p hfl
  have h2 : ((⌊Tj X p K j⌋₊ : ℕ) : ℝ) ≤ Tj X p K j := Nat.floor_le (by linarith)
  have h3 : ((p ^ X.Rj p K j : ℕ) : ℝ) ≤ ((⌊Tj X p K j⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith

theorem lt_pow_Rj (hX : X.Hyp p K) (j : ℤ) : Tj X p K j < (p : ℝ) ^ (X.Rj p K j + 1) := by
  have h1 : ⌊Tj X p K j⌋₊ < p ^ (X.Rj p K j + 1) := Nat.lt_pow_succ_log_self hX.prime.one_lt _
  have h2 : Tj X p K j < (⌊Tj X p K j⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have h3 : ((⌊Tj X p K j⌋₊ : ℕ) : ℝ) + 1 ≤ ((p ^ (X.Rj p K j + 1) : ℕ) : ℝ) := by exact_mod_cast h1
  push_cast at h3
  linarith

theorem power_exceeds_max_multiplicity (C₀ : ℝ) : PowerExceedsMaxMultiplicity C₀ := by
  intro p n' r K _ _ _ X hX _ _ j
  have B := basics hX
  have h1 := Tj_ge hX j
  have h2 := lt_pow_Rj hX j
  rw [pow_succ] at h2
  have hp : (0 : ℝ) < p := by linarith [B.p1]
  have hE : (0 : ℝ) ≤ X.E₀ := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ X.mStar := Nat.cast_nonneg _
  have h3 : 4 * ((X.E₀ : ℝ) + X.mStar + 1) < (p : ℝ) ^ X.Rj p K j := by
    by_contra! hcon
    have := mul_le_mul_of_nonneg_right hcon hp.le
    nlinarith
  have h4 : (X.mStar : ℝ) < ((p ^ X.Rj p K j : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast h4

theorem l42b (hX : X.Hyp p K) (j y : ℤ) (hy : y ∈ X.F.letters j) :
    8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j) ≤ X.a := by
  have b := basics hX
  have hd := den_pos hX j
  have hy' := mem_letters_bounds hy
  have hdist : X.F.dist j y ≤ X.F.dist j (X.F.fr (j - 1) 0) := by
    unfold Frames.dist
    exact Int.toNat_le_toNat (by linarith [hy'.1])
  have hp1 : (1 : ℝ) ≤ p := b.p1.le
  have hpow : (p : ℝ) ^ X.F.dist j y ≤ (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := pow_le_pow_right₀ hp1 hdist
  have hR := pow_Rj_le hX j
  have hY : 0 ≤ X.Y := by linarith [b.Y1]
  have hTa : 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * Tj X p K j = X.a := by
    unfold Tj
    exact mul_div_cancel₀ _ hd.ne'
  have hc0 : 0 ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hY) (sq_nonneg _)) (Nat.cast_nonneg _)
  have hm := mul_le_mul_of_nonneg_left (mul_le_mul hpow hR (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _)) hc0
  rw [pow_add]
  calc 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ X.F.dist j y * (p : ℝ) ^ X.Rj p K j)
      ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * Tj X p K j) := hm
    _ = X.a := by rw [← hTa]; ring

end Num

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def LateVectorsDistinctLeadingTerms : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ j, ∀ x ∈ X.toLate j,
    Function.Injective fun a : Fin r => posOf n' (X.row j x a)

open Classical in
theorem ph_detPl_ne_zero {R : Type} [CommRing R] [Nontrivial R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)
    (hp : 0 < p) (j x : ℤ) (hinj : Function.Injective fun a : Fin r => posOf n' (X.row j x a)) :
    phSeg R K p X.F j (plEmb R r K (X.detPl R j x)) ≠ 0 := by
  intro h
  let v : Fin n' × Fin (r + K) → R := fun tc =>
    if ∃ a : Fin r, posOf n' (X.row j x a) = tc.1 ∧ tc.2 = Fin.castAdd K a then 1 else 0
  let f : MvPolynomial (ℤ × Fin r) R →+* R :=
    (MvPolynomial.eval v).comp ((phSeg R K p X.F j).toRingHom.comp (plEmb R r K).toRingHom)
  have h1 : f (X.detPl R j x) = 0 := by
    show MvPolynomial.eval v (phSeg R K p X.F j (plEmb R r K (X.detPl R j x))) = 0
    rw [h, map_zero]
  have hm : f.mapMatrix (Matrix.of fun a b : Fin r => MvPolynomial.X (X.row j x a, b)) = 1 := by
    ext a b
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    show MvPolynomial.eval v (phSeg R K p X.F j (plEmb R r K (MvPolynomial.X (X.row j x a, b)))) = (1 : Matrix (Fin r) (Fin r) R) a b
    simp only [plEmb, rename_X, phSeg, aeval_X, map_pow, eval_X]
    by_cases hab : a = b
    · subst hab
      have hv : v (posOf n' (X.row j x a), Fin.castAdd K a) = 1 := ite_eq_left ⟨a, rfl, rfl⟩
      rw [hv, one_pow, Matrix.one_apply_eq]
    · have hv : v (posOf n' (X.row j x a), Fin.castAdd K b) = 0 := by
        apply ite_eq_right
        rintro ⟨a', ha, hb⟩
        have e1 : a' = a := hinj ha
        have e2 : b = a' := Fin.castAdd_injective _ _ hb
        exact hab (e2.trans e1).symm
      rw [hv, zero_pow (pow_ne_zero _ hp.ne'), Matrix.one_apply_ne hab]
  have h2 : f (X.detPl R j x) = 1 := by
    unfold Dat.detPl
    rw [RingHom.map_det, hm, Matrix.det_one]
  rw [h1] at h2
  exact zero_ne_one h2

theorem discriminant_nonzero_of_injective_tops (hInj : LateVectorsDistinctLeadingTerms) : DiscriminantNonzeroModUniformiser := by
  intro p n' r K _ _ _ X O _ _ _ hX
  have hp : 0 < p := hX.prime.pos
  have hpl : ∀ P : MvPolynomial (ℤ × Fin r) O,
      map (IsLocalRing.residue O) (plEmb O r K P) = plEmb _ r K (map (IsLocalRing.residue O) P) := by
    intro P
    simp [plEmb, MvPolynomial.map_rename]
  simp only [Dat.Dl, Dat.DlSeg, map_prod, map_pow, map_phSeg, hpl, map_detPl]
  rw [Finset.prod_ne_zero_iff]
  intro j _
  rw [Finset.prod_ne_zero_iff]
  intro x hx
  exact pow_ne_zero _ (ph_detPl_ne_zero X p K hp _ _ (hInj p n' r K X hX _ x hx))

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Rows

variable {n' r : ℕ} [NeZero n'] [NeZero r]

open Classical in
def evL (F : Frames n' r) (j x : ℤ) : List ℤ := ((F.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·)

theorem row_eq (X : Dat n' r) (j x : ℤ) (i : Fin r) :
    X.row j x i = (evL X.F j x).getD ((evL X.F j x).length - r + i.val) 0 := rfl

theorem oldest_eq (F : Frames n' r) (j x : ℤ) : F.oldest j x = (evL F j x).getD ((evL F j x).length - r) 0 := rfl

theorem mem_evL (F : Frames n' r) (j x z : ℤ) : z ∈ evL F j x ↔ z ∈ F.letters j ∧ Even z ∧ z < x := by
  classical
  unfold evL
  rw [Finset.mem_sort, Finset.mem_filter]

theorem bk_fr_lt {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) :
    ∀ i', i < i' → i' < r → F.fr j i < F.fr j i' :=
  TE.fr_lt hV j i

theorem bk_fr_le {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) (i i' : ℕ) (h : i ≤ i') (h' : i' < r) :
    F.fr j i ≤ F.fr j i' :=
  TE.fr_le hV j i i' h h'

theorem r_le_length {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j x : ℤ)
    (hW : ¬ F.IsW j x) : r ≤ (evL F j x).length := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hW' : F.fr (j - 1) (r - 1) < x := lt_of_not_ge hW
  have h4 : F.fr (j - 1) (r - 1) < F.fr j 0 := by
    have := hV.2.2.2.1 (j - 1)
    rwa [sub_add_cancel] at this
  have hj0 : F.fr j 0 ≤ F.fr j (r - 1) := bk_fr_le hV j 0 (r - 1) (Nat.zero_le _) (by omega)
  have hsub : (Finset.range r).image (fun i => F.fr (j - 1) i) ⊆
      (F.letters j).filter (fun z => Even z ∧ z < x) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Finset.mem_range] at hi
    have hle : F.fr (j - 1) i ≤ F.fr (j - 1) (r - 1) := bk_fr_le hV (j - 1) i (r - 1) (by omega) (by omega)
    have hge : F.fr (j - 1) 0 ≤ F.fr (j - 1) i := bk_fr_le hV (j - 1) 0 i (Nat.zero_le _) hi
    have h5 := hV.2.2.2.2.1 (j - 1) i hi
    rw [Finset.mem_filter]
    refine ⟨?_, h5.2, lt_of_le_of_lt hle hW'⟩
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨hge, by linarith⟩, h5.1⟩
  have hinj : Set.InjOn (fun i => F.fr (j - 1) i) (Finset.range r : Set ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1
    · exact absurd hab (ne_of_lt (bk_fr_lt hV (j - 1) a b h1 hb))
    · exact absurd hab (ne_of_gt (bk_fr_lt hV (j - 1) b a h1 ha))
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hc
  unfold evL
  rw [Finset.length_sort]
  exact hc

theorem evL_nodup (F : Frames n' r) (j x : ℤ) : (evL F j x).Nodup := by
  classical
  unfold evL
  exact Finset.sort_nodup _ _

theorem evL_mono (F : Frames n' r) (j x : ℤ) {a b : ℕ} (hab : a ≤ b) (hb : b < (evL F j x).length) :
    (evL F j x)[a]'(lt_of_le_of_lt hab hb) ≤ (evL F j x)[b]'hb := by
  have hp : (evL F j x).Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  rcases Nat.lt_or_eq_of_le hab with h1 | h1
  · exact List.pairwise_iff_getElem.mp hp a b _ hb h1
  · subst h1
    exact le_refl _

end Rows

theorem late_row_injective : LateIndexInjective := by
  intro p n' r K _ _ _ X hX j x hx
  unfold Dat.toLate at hx
  simp only [Finset.mem_filter] at hx
  have hlen := r_le_length hX.valid j x hx.2
  have hidx : ∀ i : Fin r, (evL X.F j x).length - r + i.val < (evL X.F j x).length := by
    intro i
    have := i.isLt
    omega
  have hrow : ∀ i : Fin r, X.row j x i = (evL X.F j x)[(evL X.F j x).length - r + i.val]'(hidx i) := by
    intro i
    rw [row_eq, List.getD_eq_getElem]
  refine ⟨?_, ?_⟩
  · intro a b h
    rw [hrow, hrow] at h
    have := (evL_nodup X.F j x).getElem_inj_iff.mp h
    exact Fin.ext (by omega)
  · intro i
    rw [hrow]
    exact (mem_evL X.F j x _).mp (List.getElem_mem _)

theorem oldest_letter_in_segment : OldestLetterInSegment := by
  intro p n' r K _ _ _ X hX j x hx
  unfold Dat.toLate at hx
  simp only [Finset.mem_filter] at hx
  have hV := hX.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hlen := r_le_length hV j x hx.2
  have hk : (evL X.F j x).length - r < (evL X.F j x).length := by omega
  have hold : X.F.oldest j x = (evL X.F j x)[(evL X.F j x).length - r]'hk := by
    rw [oldest_eq, List.getD_eq_getElem]
  have hmem := (mem_evL X.F j x _).mp (List.getElem_mem hk)
  rw [hold]
  refine ⟨hmem.1, ?_⟩
  intro hnW
  have hlet := hmem.1
  unfold Frames.letters at hlet
  rw [Finset.mem_filter, Finset.mem_Icc] at hlet
  unfold Frames.LLset
  rw [Finset.mem_filter, Finset.mem_Ioo]
  refine ⟨⟨lt_of_not_ge hnW, ?_⟩, hlet.2⟩
  by_contra! hge
  have frame : ∀ y ∈ X.F.letters j, X.F.fr j 0 ≤ y → ∃ i < r, X.F.fr j i = y := by
    intro y hy hy0
    unfold Frames.letters at hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hy
    by_contra! hne
    have hall : ∀ i, i < r → X.F.fr j i < y := by
      intro i
      induction i with
      | zero => intro h0; exact lt_of_le_of_ne hy0 (hne 0 h0)
      | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        by_contra! h2
        rcases lt_or_eq_of_le h2 with h3 | h3
        · exact hV.2.2.2.2.2.1 j m y hm h1 h3 hy.2
        · exact hne (m + 1) hm h3.symm
    have := hall (r - 1) (by omega)
    linarith [hy.1.2]
  set l := evL X.F j x with hl
  set k := l.length - r with hkdef
  have hdl : (l.drop k).length = r := by
    rw [List.length_drop]
    omega
  have hnd : (l.drop k).Nodup := (evL_nodup X.F j x).sublist (List.drop_sublist _ _)
  have hxn : x ∉ (l.drop k).toFinset := by
    intro h
    rw [List.mem_toFinset] at h
    have := ((mem_evL X.F j x x).mp (List.mem_of_mem_drop h)).2.2
    exact lt_irrefl _ this
  have hsub : insert x (l.drop k).toFinset ⊆ (Finset.range r).image (fun i => X.F.fr j i) := by
    intro y hy
    rw [Finset.mem_image]
    rw [Finset.mem_insert, List.mem_toFinset] at hy
    rcases hy with rfl | hy
    · obtain ⟨i, hi, he⟩ := frame y hx.1 (le_trans hge (le_of_lt hmem.2.2))
      exact ⟨i, Finset.mem_range.mpr hi, he⟩
    · have hyl := (mem_evL X.F j x y).mp (List.mem_of_mem_drop hy)
      obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hy
      have hm' : k + m < l.length := by
        rw [hdl] at hm
        omega
      have hge2 : l[k]'hk ≤ (l.drop k)[m] := by
        rw [List.getElem_drop]
        exact evL_mono X.F j x (Nat.le_add_right k m) hm'
      obtain ⟨i, hi, he⟩ := frame _ hyl.1 (le_trans hge hge2)
      exact ⟨i, Finset.mem_range.mpr hi, he⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hxn, List.toFinset_card_of_nodup hnd, hdl] at hc
  have hc2 := Finset.card_image_le (s := Finset.range r) (f := fun i => X.F.fr j i)
  rw [Finset.card_range] at hc2
  omega

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Img

variable {ι ι' : Type} {n : ℕ}

theorem multideg_imgMon [DecidableEq ι'] (ga : ι → ι') (ep : ι → ℕ) (m : ι × Fin n →₀ ℕ) (t : ι') :
    multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m) t =
      m.sum fun v k => (if ga v.1 = t then ep v.1 else 0) * k := by
  classical
  unfold multideg imgMon
  simp only [Finsupp.sum_apply]
  unfold Finsupp.sum
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [Finsupp.single_apply, Prod.mk.injEq]
  by_cases h : ga v.1 = t
  · simp [h]
  · simp [h]

theorem sum_eq_multideg (h : ι → ℕ) (m : ι × Fin n →₀ ℕ) (T : Finset ι) (hT : ∀ v ∈ m.support, v.1 ∈ T) :
    (m.sum fun v k => h v.1 * k) = ∑ x ∈ T, h x * multideg m x := by
  classical
  have hsub : m.support ⊆ T ×ˢ (Finset.univ : Finset (Fin n)) := by
    intro v hv
    rw [Finset.mem_product]
    exact ⟨hT v hv, Finset.mem_univ _⟩
  rw [Finsupp.sum_of_support_subset m hsub _ (fun _ _ => mul_zero _), Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold multideg
  rw [Finset.mul_sum]

theorem multideg_imgMon_congr (ga : ι → ι') (ep : ι → ℕ) (m m' : ι × Fin n →₀ ℕ)
    (h : ∀ x, multideg m x = multideg m' x) (t : ι') :
    multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m) t =
      multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m') t := by
  classical
  rw [multideg_imgMon, multideg_imgMon]
  let T : Finset ι := m.support.image Prod.fst ∪ m'.support.image Prod.fst
  rw [sum_eq_multideg (fun x => if ga x = t then ep x else 0) m T
      (fun v hv => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hv)),
    sum_eq_multideg (fun x => if ga x = t then ep x else 0) m' T
      (fun v hv => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hv))]
  exact Finset.sum_congr rfl fun x _ => by rw [h x]

theorem degAt_aeval {R : Type} [CommRing R] (ga : ι → ι') (ep : ι → ℕ) {β : ι → ℕ}
    {P Q : MvPolynomial (ι × Fin n) R} (hP : P ∈ Pol R n β) (hQ : Q ∈ Pol R n β) (hQ0 : Q ≠ 0) :
    ∃ δ : ι' → ℕ, (∀ t, DegAt t (δ t)
        (aeval (fun v : ι × Fin n => (X (ga v.1, v.2) : MvPolynomial (ι' × Fin n) R) ^ ep v.1) P)) ∧
      ∀ t, DegAt t (δ t)
        (aeval (fun v : ι × Fin n => (X (ga v.1, v.2) : MvPolynomial (ι' × Fin n) R) ^ ep v.1) Q) := by
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hQ0
  have hm0' : m0 ∈ Q.support := MvPolynomial.mem_support_iff.mpr hm0
  refine ⟨fun t => multideg (imgMon (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) m0) t,
    fun t m' hm' => ?_, fun t m' hm' => ?_⟩
  · obtain ⟨m, hm, rfl⟩ := supp_aeval_pow (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) P hm'
    exact multideg_imgMon_congr ga ep m m0
      (fun x => (mem_Pol_iff.mp hP m hm x).trans (mem_Pol_iff.mp hQ m0 hm0' x).symm) t
  · obtain ⟨m, hm, rfl⟩ := supp_aeval_pow (fun v : ι × Fin n => (ga v.1, v.2)) (fun v => ep v.1) Q hm'
    exact multideg_imgMon_congr ga ep m m0
      (fun x => (mem_Pol_iff.mp hQ m hm x).trans (mem_Pol_iff.mp hQ m0 hm0' x).symm) t

end Img

theorem degAt_monomial {R : Type} [CommRing R] {ι : Type} {n : ℕ} (l : ι × Fin n →₀ ℕ) (c : R) (t : ι) :
    DegAt t (multideg l t) (monomial l c : MvPolynomial (ι × Fin n) R) := by
  classical
  intro m hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  rw [this]

theorem mem_Pol_of_degAt {R : Type} [CommRing R] {ι : Type} {n : ℕ} {d : ι → ℕ} {P : MvPolynomial (ι × Fin n) R}
    (h : ∀ t, DegAt t (d t) P) : P ∈ Pol R n d := mem_Pol_iff.mpr fun m hm t => h t m hm

theorem segment_product_degree_determined : SegmentProductDegreeDetermined := by
  intro p n' r K _ F O _ x z β l0 d hx hz hdeg hne
  classical
  have hz0 : ∀ j ∈ Finset.range F.J, z (j : ℤ) ≠ 0 := by
    intro j hj h0
    apply hne
    rw [Finset.prod_eq_zero hj (by rw [h0, map_zero]), zero_mul]
  have key : ∀ j : ℕ, ∃ δ : Fin n' → ℕ, j ∈ Finset.range F.J →
      (∀ t, DegAt t (δ t) (phSeg O K p F (j : ℤ) (x j))) ∧ ∀ t, DegAt t (δ t) (phSeg O K p F (j : ℤ) (z j)) := by
    intro j
    by_cases hj : j ∈ Finset.range F.J
    · obtain ⟨δ, h1, h2⟩ := degAt_aeval (R := O) (n := r + K) (fun y : ℤ => posOf n' y)
        (fun y : ℤ => p ^ F.dist (j : ℤ) y) (hx j) (hz j) (hz0 j hj)
      exact ⟨δ, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose δ hδ using key
  have hX : ∀ t, DegAt t (∑ j ∈ Finset.range F.J, δ j t + multideg l0 t)
      ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (x j)) * monomial l0 1) := fun t =>
    degAt_mul (degAt_prod _ _ _ fun j hj => (hδ j hj).1 t) (degAt_monomial l0 1 t)
  have hZ : ∀ t, DegAt t (∑ j ∈ Finset.range F.J, δ j t + multideg l0 t)
      ((∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (z j)) * monomial l0 1) := fun t =>
    degAt_mul (degAt_prod _ _ _ fun j hj => (hδ j hj).2 t) (degAt_monomial l0 1 t)
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hm0' := MvPolynomial.mem_support_iff.mpr hm0
  rw [RRdeg_eq_Pol] at hdeg ⊢
  refine mem_Pol_of_degAt fun t => ?_
  have e : d t = ∑ j ∈ Finset.range F.J, δ j t + multideg l0 t :=
    (mem_Pol_iff.mp hdeg m0 hm0' t).symm.trans (hZ t m0 hm0')
  rw [e]
  exact hX t

theorem degAt_sum {R : Type} [CommRing R] {ι : Type} {n : ℕ} {x : ι} {d : ℕ} {κ : Type} (s : Finset κ)
    (f : κ → MvPolynomial (ι × Fin n) R) (h : ∀ i ∈ s, DegAt x d (f i)) : DegAt x d (∑ i ∈ s, f i) := by
  classical
  intro m hm
  obtain ⟨i, hi, hmi⟩ := Finset.mem_biUnion.mp (support_sum hm)
  exact h i hi m hmi

theorem degAt_C_mul {R : Type} [CommRing R] {ι : Type} {n : ℕ} {x : ι} {d : ℕ} (c : R)
    {P : MvPolynomial (ι × Fin n) R} (h : DegAt x d P) : DegAt x d (C c * P) := by
  intro m hm
  refine h m ?_
  rw [mem_support_iff] at hm ⊢
  intro h0
  exact hm (by rw [coeff_C_mul, h0, mul_zero])

theorem degAt_detPl {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x t : ℤ) :
    DegAt t (∑ a : Fin r, if X.row j x a = t then 1 else 0) (X.detPl R j x) := by
  classical
  unfold Dat.detPl
  rw [Matrix.det_apply]
  refine degAt_sum _ _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  have h1 : (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (ℤ × Fin r) R) = C (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : R) := by
    simp
  rw [h1]
  refine degAt_C_mul _ ?_
  have h2 := degAt_prod (R := R) (x := t) Finset.univ
    (fun i : Fin r => (Matrix.of fun a b : Fin r => (MvPolynomial.X (X.row j x a, b) : MvPolynomial (ℤ × Fin r) R)) (σ i) i)
    (fun i => if X.row j x (σ i) = t then 1 else 0) (fun i _ => degAt_X (x := t) (X.row j x (σ i), i))
  rw [Equiv.sum_comp σ (fun a => if X.row j x a = t then 1 else 0)] at h2
  exact h2

theorem segment_image_multihomogeneous : SegmentImageMultihomogeneous := by
  intro p n' r K _ _ _ X O _ j b y e hy
  classical
  by_cases hy0 : y = 0
  · exact ⟨0, by rw [hy0]; simp [Dat.zSeg]⟩
  have hexp : ∀ P : SegRing O r K, expand (p ^ X.Rj p K j) P =
      aeval (fun v : ℤ × Fin (r + K) => (MvPolynomial.X ((fun z : ℤ => z) v.1, v.2) : SegRing O r K) ^
        (fun _ : ℤ => p ^ X.Rj p K j) v.1) P := by
    intro P
    have : expand (p ^ X.Rj p K j) = aeval (fun v : ℤ × Fin (r + K) =>
        (MvPolynomial.X ((fun z : ℤ => z) v.1, v.2) : SegRing O r K) ^ (fun _ : ℤ => p ^ X.Rj p K j) v.1) := by
      apply MvPolynomial.algHom_ext
      intro v
      simp
    rw [this]
  obtain ⟨δ, h1, -⟩ := degAt_aeval (R := O) (n := r + K) (fun z : ℤ => z) (fun _ : ℤ => p ^ X.Rj p K j) hy hy hy0
  have hD : X.DlSeg p K O j ∈ Pol O r (fun t => ∑ x ∈ X.toLate j, X.sg p K j x *
      ∑ a : Fin r, if X.row j x a = t then 1 else 0) := by
    refine mem_Pol_of_degAt fun t => ?_
    unfold Dat.DlSeg
    exact degAt_prod _ _ _ fun x _ => degAt_pow (degAt_detPl X j x t) _
  have h := hom_Pol_mul O (hom_Pol_mul O (plEmb_Pol r K hD) (mem_Pol_of_degAt h1))
    (mem_Pol_of_degAt fun t => degAt_monomial e (1 : O) t)
  unfold Dat.zSeg
  rw [hexp]
  exact ⟨_, h⟩

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem threshold_arith_letter_case (k Ns c q bo : ℝ) (hk5 : 5 ≤ k) (hN : 1 ≤ Ns) (hc : 40 * (k * Ns) ≤ c) (hq : 9 / 10 * c ≤ q)
    (hb : q - k < bo) : c / 2 ≤ 2 / 3 * bo - k * Ns := by
  have hkN : k ≤ k * Ns := by nlinarith
  linarith

theorem threshold_arith_w_case (k Ns c q fl r : ℝ) (hk5 : 5 ≤ k) (hN : 1 ≤ Ns) (hr : r ≤ k) (hc : 40 * (k * Ns) ≤ c)
    (hq : 9 / 10 * c ≤ q) (hfl : q - 1 < fl) :
    c / 2 ≤ 2 / 3 * (fl - (k + r + 1) - (k * Ns + 1)) - k * Ns := by
  have hkN : k ≤ k * Ns := by nlinarith
  linarith

theorem natDiv_gt (n m : ℕ) (hm : 0 < m) : (n : ℝ) / (m : ℝ) - 1 < ((n / m : ℕ) : ℝ) := by
  have h := Nat.div_add_mod n m
  have hr := Nat.mod_lt n hm
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have e1 : (n : ℝ) = (m : ℝ) * ((n / m : ℕ) : ℝ) + ((n % m : ℕ) : ℝ) := by exact_mod_cast h.symm
  have e2 : ((n % m : ℕ) : ℝ) < m := by exact_mod_cast hr
  rw [div_sub_one hm'.ne', div_lt_iff₀ hm']
  linarith

theorem threshold_power_bound_of_counts (C₀ : ℝ) (h41 : TopCountLowerBounds C₀) (hOld : OldestLetterInSegment) : ThresholdPowerLowerBound C₀ := by
  unfold ThresholdPowerLowerBound
  intro p n' r K _ _ _ X hX hC1 hC2 j bb hS x hx
  have b0 := basics hX
  have hO := hOld p n' r K X hX j x hx
  have hob := mem_letters_bounds hO.1
  have h41' := (h41 p n' r K X hX hC1 hC2).1 _ hob.2.2
  have hdeg := (hX.degs _ hob.2.2).1
  have hk : Dat.k (r := r) K = ((r : ℝ) + (K : ℝ)) := by unfold Dat.k; push_cast; rfl
  have hk5 : (5 : ℝ) ≤ ((r : ℝ) + (K : ℝ)) := hk ▸ b0.k5
  have hN := b0.Ns1
  have hY := b0.Y1
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := b0.p1.le
  have hRT := pow_Rj_le hX j
  have hRp : (0 : ℝ) ≤ (p : ℝ) ^ (X.Rj p K j) := by positivity
  have hTp : (0 : ℝ) ≤ Tj X p K j := hRp.trans hRT
  have hden := den_pos hX j
  have hTa : 8 * X.Y * ((r : ℝ) + (K : ℝ)) ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j = X.a := by
    rw [← hk]
    unfold Tj
    exact mul_div_cancel₀ _ hden.ne'
  have hEW : (X.F.dist j (X.F.oldest j x)) ≤ (X.F.dist j (X.F.fr (j - 1) 0)) := by
    unfold Frames.dist
    omega
  have hPe : (p : ℝ) ^ (X.F.dist j (X.F.oldest j x)) ≤ (p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) := pow_le_pow_right₀ hP1 hEW
  have hDpos : 0 < ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) := by positivity
  have hc : 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) ≤ (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) := by
    rw [le_div_iff₀ hDpos, pow_add]
    have hkN : 0 ≤ ((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ) := by positivity
    have h40 : (40 : ℝ) ≤ 8 * X.Y * ((r : ℝ) + (K : ℝ)) := by nlinarith
    have h1 : 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) ≤ 8 * X.Y * ((r : ℝ) + (K : ℝ)) ^ 2 * (X.Ns : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_right h40 hkN]
    have hq0 : 0 ≤ (p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j := by positivity
    calc 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) * ((p : ℝ) ^ (X.F.dist j (X.F.oldest j x)) * (p : ℝ) ^ (X.Rj p K j))
        ≤ 40 * (((r : ℝ) + (K : ℝ)) * (X.Ns : ℝ)) * ((p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hPe hRT hRp (by positivity)) (by positivity)
      _ ≤ 8 * X.Y * ((r : ℝ) + (K : ℝ)) ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ (X.F.dist j (X.F.fr (j - 1) 0)) * Tj X p K j) := mul_le_mul_of_nonneg_right h1 hq0
      _ = X.a := by rw [← hTa]; ring
      _ ≤ ((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) := hdeg
  have hq : 9 / 10 * (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) ≤ (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) := by
    calc 9 / 10 * (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) = (9 / 10 * ((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ)) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) := by ring
      _ ≤ (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) := by gcongr
  have hsplit : ((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / (p : ℝ) ^ (X.F.dist j (X.F.oldest j x)) / 2 = (p : ℝ) ^ (X.Rj p K j) * ((((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) / 2) := by
    rw [pow_add]
    field_simp
  unfold Dat.th Dat.Bo Dat.thc
  rw [hsplit]
  push_cast
  refine mul_le_mul_of_nonneg_left ?_ hRp
  split_ifs with hW
  · have hfl := natDiv_gt (X.a' p K (posOf n' (X.F.oldest j x))) (p ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) (pow_pos (by have := hX.p13; omega) _)
    push_cast at hfl
    have := threshold_arith_w_case ((r : ℝ) + (K : ℝ)) (X.Ns : ℝ) (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) _ (r : ℝ) hk5 hN (by linarith) hc hq hfl
    unfold Dat.Bw Dat.m0
    push_cast
    have hcast : ((((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℤ) / ((p : ℤ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j))) : ℤ) : ℝ) = (((X.a' p K (posOf n' (X.F.oldest j x))) / p ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)) : ℕ) : ℝ) := by
      rw [← Nat.cast_pow, ← Int.natCast_div, Int.cast_natCast]
    rw [hcast]
    linarith
  · have hb := hS _ (hO.2 hW)
    rw [hk] at hb
    have := threshold_arith_letter_case ((r : ℝ) + (K : ℝ)) (X.Ns : ℝ) (((X.deg (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) (((X.a' p K (posOf n' (X.F.oldest j x)) : ℕ) : ℝ) / ((p : ℝ) ^ ((X.F.dist j (X.F.oldest j x)) + (X.Rj p K j)))) _ hk5 hN hc hq hb
    linarith

theorem order_numeric_bound_of_oldest (C₀ : ℝ) (hOld : OldestLetterInSegment) : OrderNumericBound C₀ := by
  unfold OrderNumericBound
  intro p n' r K _ _ _ X hX _ _ j x hx
  have b := basics hX
  have hO := hOld p n' r K X hX j x hx
  simp only [Dat.toLate, Finset.mem_filter] at hx
  have hxb := mem_letters_bounds hx.1
  have hob := mem_letters_bounds hO.1
  have hL : (X.L₁ : ℤ) < x - X.F.oldest j x := hX.valid.2.2.2.2.2.2.2.2 j x hx.1 hx.2
  have hde : X.F.dist j x + X.L₁ + 1 ≤ X.F.dist j (X.F.oldest j x) := by
    unfold Frames.dist
    omega
  have hew : X.F.dist j (X.F.oldest j x) ≤ X.F.dist j (X.F.fr (j - 1) 0) := by
    unfold Frames.dist
    omega
  have hP : (13 : ℝ) ≤ p := by exact_mod_cast hX.p13
  have hP1 : (1 : ℝ) ≤ p := by linarith
  have hk : (5 : ℝ) ≤ Dat.k (r := r) K := b.k5
  have hY := b.Y1
  have hNs := b.Ns1
  have hden := den_pos hX j
  have hTa : 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * Tj X p K j = X.a := by
    unfold Tj
    exact mul_div_cancel₀ _ hden.ne'
  have hRT := pow_Rj_le hX j
  have hRp : (0 : ℝ) ≤ (p : ℝ) ^ X.Rj p K j := by positivity
  have hTp : (0 : ℝ) ≤ Tj X p K j := hRp.trans hRT
  have ha : 0 ≤ X.a := hTa ▸ mul_nonneg hden.le hTp
  have hLd : (p : ℝ) ^ (X.L₁ + X.F.dist j x) ≤ (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) :=
    pow_le_pow_right₀ hP1 (by omega)
  have hLe : (p : ℝ) * (p : ℝ) ^ (X.L₁ + X.F.dist j x) ≤ (p : ℝ) ^ X.F.dist j (X.F.oldest j x) := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ hP1 (by omega)
  have hLpos : (0 : ℝ) < (p : ℝ) ^ (X.L₁ + X.F.dist j x) := by positivity
  have hEpos : (0 : ℝ) < (p : ℝ) ^ X.F.dist j (X.F.oldest j x) := by positivity
  have hA : Dat.k (r := r) K * (p : ℝ) ^ X.Rj p K j ≤ X.a / (p : ℝ) ^ (X.L₁ + X.F.dist j x) := by
    rw [le_div_iff₀ hLpos]
    have h8 : 1 ≤ 8 * X.Y * Dat.k (r := r) K * (X.Ns : ℝ) := by
      have : (1 : ℝ) ≤ X.Y * Dat.k (r := r) K := by nlinarith
      have : (1 : ℝ) ≤ X.Y * Dat.k (r := r) K * (X.Ns : ℝ) := by nlinarith
      linarith
    have hq : 0 ≤ Dat.k (r := r) K * Tj X p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := by positivity
    calc Dat.k (r := r) K * (p : ℝ) ^ X.Rj p K j * (p : ℝ) ^ (X.L₁ + X.F.dist j x)
        ≤ Dat.k (r := r) K * Tj X p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hRT (by linarith)) hLd hLpos.le (by positivity)
      _ ≤ (8 * X.Y * Dat.k (r := r) K * (X.Ns : ℝ)) * (Dat.k (r := r) K * Tj X p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0)) := le_mul_of_one_le_left hq h8
      _ = X.a := by rw [← hTa]; ring
  have hB : (p : ℝ) ^ X.Rj p K j * (4 * X.a * ((p : ℝ) ^ (X.F.dist j (X.F.oldest j x) + X.Rj p K j))⁻¹) ≤ X.a / (p : ℝ) ^ (X.L₁ + X.F.dist j x) := by
    rw [pow_add, mul_inv, le_div_iff₀ hLpos]
    have e : (p : ℝ) ^ X.Rj p K j * (4 * X.a * (((p : ℝ) ^ X.F.dist j (X.F.oldest j x))⁻¹ * ((p : ℝ) ^ X.Rj p K j)⁻¹)) = 4 * X.a / (p : ℝ) ^ X.F.dist j (X.F.oldest j x) := by
      field_simp
    rw [e, div_mul_eq_mul_div, div_le_iff₀ hEpos]
    nlinarith [mul_le_mul_of_nonneg_left hLe ha, mul_nonneg (mul_nonneg ha hLpos.le) (by linarith : (0 : ℝ) ≤ p - 4)]
  have z1 : (p : ℝ) ^ (-((X.F.dist j (X.F.oldest j x) : ℤ) + (X.Rj p K j : ℤ))) = ((p : ℝ) ^ (X.F.dist j (X.F.oldest j x) + X.Rj p K j))⁻¹ := by
    rw [← Nat.cast_add, zpow_neg, zpow_natCast]
  have z2 : (p : ℝ) ^ (-((X.L₁ : ℤ) + (X.F.dist j x : ℤ))) = ((p : ℝ) ^ (X.L₁ + X.F.dist j x))⁻¹ := by
    rw [← Nat.cast_add, zpow_neg, zpow_natCast]
  have hkne : Dat.k (r := r) K ≠ 0 := by linarith
  have hT1 : (p : ℝ) ^ X.Rj p K j * (X.La * X.a / ((p : ℝ) * Dat.k (r := r) K * (p : ℝ) ^ (X.F.dist j x + X.Rj p K j))) = X.La * X.a / ((p : ℝ) * Dat.k (r := r) K * (p : ℝ) ^ X.F.dist j x) := by
    rw [pow_add]
    field_simp
  rw [div_eq_mul_inv] at hA hB
  have hI : 0 ≤ X.a * ((p : ℝ) ^ (X.L₁ + X.F.dist j x))⁻¹ := mul_nonneg ha (inv_nonneg.mpr hLpos.le)
  unfold Dat.oc Dat.o
  push_cast
  rw [z1, z2, mul_add, hT1]
  split_ifs <;> linarith

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

open Classical in
def LeadingLetterInAtMostTwoSegments : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → ∀ t : Fin n',
    ∑ j ∈ Finset.range X.F.J, ((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card ≤ 2

section locP_coef_Lsh

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem oldest_le_row (hX : X.Hyp p K) (j x : ℤ) (hx : x ∈ X.toLate j) (i : Fin r) :
    X.F.oldest j x ≤ X.row j x i := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hmem := (mem_late X j x).1 hx
  have hlen := r_le_length hX.valid j x hmem.2
  have hi := i.isLt
  rw [oldest_eq, row_eq]
  have h1 : (evL X.F j x).length - r < (evL X.F j x).length := by omega
  have h2 : (evL X.F j x).length - r + (i : ℕ) < (evL X.F j x).length := by omega
  rw [List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2]
  exact evL_mono X.F j x (by omega) h2

theorem sg_mul_le (hX : X.Hyp p K) (j x : ℤ) (hx : x ∈ X.toLate j) (i : Fin r) :
    (X.sg p K j x : ℝ) * (p : ℝ) ^ X.F.dist j (X.row j x i) ≤ 2 * X.a / (Dat.k (r := r) K ^ 2 * X.Y) := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hmem := (mem_late X j x).1 hx
  have hlen := r_le_length hX.valid j x hmem.2
  have hold : X.F.oldest j x ∈ X.F.letters j := by
    rw [oldest_eq]
    have h1 : (evL X.F j x).length - r < (evL X.F j x).length := by omega
    rw [List.getD_eq_getElem _ _ h1]
    exact ((mem_evL X.F j x _).1 (List.getElem_mem h1)).1
  have hle := oldest_le_row hX j x hx i
  have hdist : X.F.dist j (X.row j x i) ≤ X.F.dist j (X.F.oldest j x) := by
    unfold Frames.dist
    omega
  obtain ⟨-, -, hpos⟩ := mem_letters_bounds hold
  have hdeg := (hX.degs _ hpos).2
  have hp1 : 1 ≤ p := le_trans (by norm_num) hX.p13
  have hp : (1:ℝ) ≤ p := by exact_mod_cast hp1
  have hp0 : (0:ℝ) < p := by linarith
  have hK0 : 0 < K := Nat.pos_of_ne_zero (NeZero.ne K)
  have hkpos : (0:ℝ) < Dat.k (r := r) K := by
    unfold Dat.k
    exact_mod_cast (by omega : 0 < r + K)
  have hY := hX.Y1
  have hk : 0 < Dat.k (r := r) K ^ 2 * X.Y := by positivity
  have hpd : (0:ℝ) < (p:ℝ) ^ X.F.dist j (X.F.oldest j x) := pow_pos hp0 _
  have hBo : 0 ≤ X.Bo p j x := by
    unfold Dat.Bo
    exact div_nonneg (Nat.cast_nonneg _) hpd.le
  have hsg : (X.sg p K j x : ℝ) ≤ X.Bo p j x / (Dat.k (r := r) K ^ 2 * X.Y) := by
    unfold Dat.sg
    exact Nat.floor_le (div_nonneg hBo hk.le)
  have hpow : (p:ℝ) ^ X.F.dist j (X.row j x i) ≤ (p:ℝ) ^ X.F.dist j (X.F.oldest j x) :=
    pow_le_pow_right₀ hp hdist
  calc (X.sg p K j x : ℝ) * (p:ℝ) ^ X.F.dist j (X.row j x i)
      ≤ X.Bo p j x / (Dat.k (r := r) K ^ 2 * X.Y) * (p:ℝ) ^ X.F.dist j (X.F.oldest j x) :=
        mul_le_mul hsg hpow (by positivity) (div_nonneg hBo hk.le)
    _ = (X.deg (posOf n' (X.F.oldest j x)) : ℝ) / (Dat.k (r := r) K ^ 2 * X.Y) := by
        unfold Dat.Bo
        field_simp
    _ ≤ 2 * X.a / (Dat.k (r := r) K ^ 2 * X.Y) := by
        gcongr

private theorem late_index_map_mem_letters (hX : X.Hyp p K) (j x : ℤ) (hx : x ∈ X.toLate j) (i : Fin r) :
    X.row j x i ∈ X.F.letters j := by
  have hmem := (mem_late X j x).1 hx
  have hlen := r_le_length hX.valid j x hmem.2
  have hi := i.isLt
  rw [row_eq]
  have h2 : (evL X.F j x).length - r + (i : ℕ) < (evL X.F j x).length := by omega
  rw [List.getD_eq_getElem _ _ h2]
  exact ((mem_evL X.F j x _).1 (List.getElem_mem h2)).1

private theorem late_index_map_injective (hX : X.Hyp p K) (j x : ℤ) (hx : x ∈ X.toLate j) :
    Function.Injective (X.row j x) := by
  have hmem := (mem_late X j x).1 hx
  have hlen := r_le_length hX.valid j x hmem.2
  intro i i' h
  have hi := i.isLt
  have hi' := i'.isLt
  rw [row_eq, row_eq] at h
  have h2 : (evL X.F j x).length - r + (i : ℕ) < (evL X.F j x).length := by omega
  have h2' : (evL X.F j x).length - r + (i' : ℕ) < (evL X.F j x).length := by omega
  rw [List.getD_eq_getElem _ _ h2, List.getD_eq_getElem _ _ h2'] at h
  have h3 := (evL_nodup X.F j x).getElem_inj_iff.1 h
  ext
  omega

open Classical in
theorem Et_le (hOcc : LeadingLetterInAtMostTwoSegments) (hX : X.Hyp p K) (t : Fin n') :
    (X.Et p K t : ℝ) ≤ 4 * (X.Ns : ℝ) * X.a / (Dat.k (r := r) K ^ 2 * X.Y) := by
  have B := basics hX
  have hY0 : 0 ≤ X.Y := by linarith [B.Y1]
  have hlhs : 0 ≤ (32:ℝ) * p * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (Nat.cast_nonneg _)) hY0) (sq_nonneg _)) (Nat.cast_nonneg _)) (sq_nonneg _)) (by positivity)
  have ha0 : 0 ≤ X.a := le_trans hlhs hX.P3
  have hk5 := B.k5
  have hden : 0 < Dat.k (r := r) K ^ 2 * X.Y := by
    have : (0:ℝ) < Dat.k (r := r) K := by linarith
    have : (0:ℝ) < X.Y := by linarith [B.Y1]
    positivity
  set c : ℝ := 2 * X.a / (Dat.k (r := r) K ^ 2 * X.Y) with hc
  have hcnt : ∀ j : ℤ, ∀ x ∈ X.toLate j,
      (Finset.univ.filter fun i : Fin r => posOf n' (X.row j x i) = t).card ≤
        ((X.F.letters j).filter fun y => posOf n' y = t).card := by
    intro j x hx
    apply Finset.card_le_card_of_injOn (fun i => X.row j x i)
    · intro i hi
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hi ⊢
      exact ⟨late_index_map_mem_letters hX j x hx i, hi⟩
    · intro i _ i' _ h
      exact late_index_map_injective hX j x hx h
  have hterm : ∀ j : ℤ, ∀ x ∈ X.toLate j,
      (((X.sg p K j x * ∑ i : Fin r, if posOf n' (X.row j x i) = t then p ^ X.F.dist j (X.row j x i) else 0 : ℕ)) : ℝ)
        ≤ c * (((X.F.letters j).filter fun y => posOf n' y = t).card : ℝ) := by
    intro j x hx
    push_cast
    rw [Finset.mul_sum]
    calc ∑ i : Fin r, (X.sg p K j x : ℝ) *
          (if posOf n' (X.row j x i) = t then (p : ℝ) ^ X.F.dist j (X.row j x i) else 0)
        ≤ ∑ i : Fin r, (if posOf n' (X.row j x i) = t then c else 0) := by
          apply Finset.sum_le_sum
          intro i _
          split_ifs
          · exact sg_mul_le hX j x hx i
          · simp
      _ = c * ((Finset.univ.filter fun i : Fin r => posOf n' (X.row j x i) = t).card : ℝ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ _ := by
          gcongr
          exact_mod_cast hcnt j x hx
  have hOcc' := hOcc p n' r K X hX t
  have hOccR : (∑ j ∈ Finset.range X.F.J,
      (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ)) ≤ 2 := by
    exact_mod_cast hOcc'
  unfold Dat.Et
  rw [Nat.cast_sum]
  calc _ ≤ ∑ j ∈ Finset.range X.F.J,
        (X.Ns : ℝ) * (c * (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ)) := by
        apply Finset.sum_le_sum
        intro j _
        rw [Nat.cast_sum]
        calc _ ≤ ∑ x ∈ X.toLate (j : ℤ),
              c * (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ) :=
              Finset.sum_le_sum fun x hx => hterm _ x hx
          _ = ((X.toLate (j : ℤ)).card : ℝ) *
              (c * (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ _ := by
              have hl : (X.toLate (j : ℤ)).card ≤ X.Ns := (Finset.card_filter_le _ _).trans (hX.card _)
              gcongr
    _ = (X.Ns : ℝ) * (c * ∑ j ∈ Finset.range X.F.J,
          (((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card : ℝ)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ (X.Ns : ℝ) * (c * 2) := by gcongr
    _ = 4 * (X.Ns : ℝ) * X.a / (Dat.k (r := r) K ^ 2 * X.Y) := by
        rw [hc]
        ring

theorem a_ge (hX : X.Hyp p K) : 32 * ((X.E₀ : ℝ) + X.mStar + 1) ≤ X.a := by
  have B := basics hX
  have hE : (0:ℝ) ≤ (X.E₀ : ℝ) + X.mStar + 1 := by positivity
  have hrK : (1:ℝ) ≤ ((r + K : ℕ) : ℝ) := by
    have h := B.k5
    unfold Dat.k at h
    linarith
  have hsq : (1:ℝ) ≤ ((r + K : ℕ) : ℝ) ^ 2 := one_le_pow₀ hrK
  have hq : (1:ℝ) ≤ X.Q ^ 2 := one_le_pow₀ B.Q1
  have hp : (1:ℝ) ≤ p := by linarith [B.p1]
  have hY := B.Y1
  have hNs := B.Ns1
  have h1 : (1:ℝ) ≤ (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * X.Q ^ 2 := by
    have e1 : (1:ℝ) ≤ (p : ℝ) * X.Y := one_le_mul_of_one_le_of_one_le hp hY
    have e2 := one_le_mul_of_one_le_of_one_le e1 hsq
    have e3 := one_le_mul_of_one_le_of_one_le e2 hNs
    exact one_le_mul_of_one_le_of_one_le e3 hq
  have h2 := mul_le_mul_of_nonneg_right h1 hE
  have h3 := hX.P3
  nlinarith

theorem k_sq_mul_Y_ge_Ns (hX : X.Hyp p K) (hC : 32 ≤ X.Ck) : 160 * (X.Ns : ℝ) ≤ Dat.k (r := r) K ^ 2 * X.Y := by
  have B := basics hX
  have ha := a_ge hX
  have hlog : 1 ≤ Real.log X.a := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hNs := B.Ns1
  have hNs2 : (X.Ns : ℝ) ≤ (X.Ns : ℝ) ^ 2 * Real.log X.a := by
    have e1 : (X.Ns : ℝ) ≤ (X.Ns : ℝ) ^ 2 := by nlinarith
    have e2 : (X.Ns : ℝ) ^ 2 ≤ (X.Ns : ℝ) ^ 2 * Real.log X.a :=
      le_mul_of_one_le_right (sq_nonneg _) hlog
    linarith
  have hCk : 32 * ((X.Ns : ℝ) ^ 2 * Real.log X.a) ≤ X.Ck * (X.Ns : ℝ) ^ 2 * Real.log X.a := by
    rw [mul_assoc X.Ck]
    exact mul_le_mul_of_nonneg_right hC (mul_nonneg (sq_nonneg _) (by linarith))
  have hP1 := hX.P1
  have hkdef : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  have hY := hX.Y1
  rw [hkdef]
  have e1 : 0 ≤ ((r + K : ℕ) : ℝ) ^ 2 * (X.Y - 1) := mul_nonneg (sq_nonneg _) (by linarith)
  have e2 : 0 ≤ ((r + K : ℕ) : ℝ) * (((r + K : ℕ) : ℝ) - 5) := mul_nonneg (by linarith) (by linarith)
  nlinarith

end locP_coef_Lsh

theorem top_count_lower_bounds_of_occurrence (C₀ : ℝ) (hC : 32 ≤ C₀) (hOcc : LeadingLetterInAtMostTwoSegments) : TopCountLowerBounds C₀ := by
  intro p n' r K _ _ _ X hX _ hCk
  have hCk' : 32 ≤ X.Ck := le_trans hC hCk
  have hk := k_sq_mul_Y_ge_Ns hX hCk'
  have ha := a_ge hX
  have B := basics hX
  have hNs : (1:ℝ) ≤ X.Ns := B.Ns1
  have ha0 : 0 ≤ X.a := by linarith
  have hEt40 : ∀ t, (X.Et p K t : ℝ) ≤ X.a / 40 := by
    intro t
    refine (Et_le hOcc hX t).trans ?_
    have hpos : 0 < Dat.k (r := r) K ^ 2 * X.Y := by linarith
    rw [div_le_div_iff₀ hpos (by norm_num)]
    have := mul_le_mul_of_nonneg_left hk ha0
    nlinarith
  have hd : ∀ t ∈ X.F.TT, (X.d t : ℝ) = X.deg t - X.E' t := by
    intro t ht
    have hdeg := (hX.degs t ht).1
    have hE' : (X.E' t : ℝ) ≤ X.E₀ := by exact_mod_cast hX.E'le t ht
    have hle : X.E' t ≤ X.deg t := by
      have : (X.E' t : ℝ) ≤ X.deg t := by linarith
      exact_mod_cast this
    unfold Dat.d
    rw [ite_eq_left ht, Nat.cast_sub hle]
  have hEtd : ∀ t ∈ X.F.TT, X.Et p K t ≤ X.d t := by
    intro t ht
    have hdeg := (hX.degs t ht).1
    have hE' : (X.E' t : ℝ) ≤ X.E₀ := by exact_mod_cast hX.E'le t ht
    have h : (X.Et p K t : ℝ) ≤ X.d t := by
      rw [hd t ht]
      linarith [hEt40 t]
    exact_mod_cast h
  constructor
  · intro t ht
    have hdeg := (hX.degs t ht).1
    have hE' : (X.E' t : ℝ) ≤ X.E₀ := by exact_mod_cast hX.E'le t ht
    unfold Dat.a'
    rw [Nat.cast_sub (hEtd t ht), hd t ht]
    linarith [hEt40 t]
  · intro t
    by_cases ht : t ∈ X.F.TT
    · exact hEtd t ht
    · have h0 : X.Et p K t = 0 := by
        unfold Dat.Et
        apply Finset.sum_eq_zero
        intro j _
        apply Finset.sum_eq_zero
        intro x hx
        apply mul_eq_zero_of_right
        apply Finset.sum_eq_zero
        intro i _
        rw [ite_eq_right]
        intro hpos
        apply ht
        rw [← hpos]
        exact (mem_letters_bounds (late_index_map_mem_letters hX _ x hx i)).2.2
      rw [h0]
      exact Nat.zero_le _

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem idx_unique {e : ℤ → ℤ} (hm : StrictMono e) {a b x : ℤ} (h1 : e (a - 1) < x) (h2 : x ≤ e a)
    (h3 : e (b - 1) < x) (h4 : x ≤ e b) : a = b := by
  rcases lt_trichotomy a b with h | h | h
  · exfalso
    have := hm.monotone (show a ≤ b - 1 by omega)
    linarith
  · exact h
  · exfalso
    have := hm.monotone (show b ≤ a - 1 by omega)
    linarith

section U

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

theorem LL_unique (hV : F.Valid L₁ N₁) (j0 : ℕ) (hj0 : j0 < F.J) (z : ℤ) (hz : z ∈ F.LLset (j0 : ℤ))
    (j : ℕ) (hj : j < F.J) (x : ℤ) (hx : x ∈ F.letters (j : ℤ)) (hxz : posOf n' x = posOf n' z) :
    j = j0 ∧ x = z := by
  obtain ⟨hJ, hper, hinc, hgap, -, -, -, -, -⟩ := hV

  have hperT : ∀ t : ℤ, ∀ (j' : ℤ) i, F.fr (j' + t * F.J) i = F.fr j' i + t * n' := by
    intro t
    induction t using Int.induction_on with
    | zero => intro j' i; simp
    | succ t ih =>
      intro j' i
      have e : j' + (t + 1) * F.J = (j' + t * F.J) + F.J := by ring
      rw [e, hper, ih]
      ring
    | pred t ih =>
      intro j' i
      have e1 := hper (j' + (-(t : ℤ) - 1) * F.J) i
      have e : j' + (-(t : ℤ) - 1) * F.J + F.J = j' + -(t : ℤ) * F.J := by ring
      rw [e, ih] at e1
      linarith

  have hin : ∀ (j' : ℤ) (i : ℕ), i ≤ r - 1 → F.fr j' 0 ≤ F.fr j' i := by
    intro j' i
    induction i with
    | zero => intro _; exact le_rfl
    | succ i ih =>
      intro hi
      have := hinc j' i (by omega)
      linarith [ih (by omega)]
  have hr0 : ∀ j' : ℤ, F.fr j' 0 ≤ F.fr j' (r - 1) := fun j' => hin j' (r - 1) le_rfl
  have mono0 : StrictMono (fun j' : ℤ => F.fr j' 0) :=
    strictMono_int_of_lt_succ (fun j' => by have := hgap j'; have := hr0 j'; linarith)
  have monoL : StrictMono (fun j' : ℤ => F.fr j' (r - 1)) :=
    strictMono_int_of_lt_succ (fun j' => by have := hgap j'; have := hr0 (j' + 1); linarith)

  have key : ∀ (g j' : ℤ) (y : ℤ), F.fr (g - 1) (r - 1) < y → y < F.fr g 0 →
      F.fr (j' - 1) 0 ≤ y → y ≤ F.fr j' (r - 1) → j' = g := by
    intro g j' y h1 h2 h3 h4
    rcases lt_trichotomy j' g with h | h | h
    · exfalso
      have := monoL.monotone (show j' ≤ g - 1 by omega)
      linarith
    · exact h
    · exfalso
      have := mono0.monotone (show g ≤ j' - 1 by omega)
      linarith

  simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hz
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx
  obtain ⟨⟨hz1, hz2⟩, -⟩ := hz
  obtain ⟨⟨hx1, hx2⟩, -⟩ := hx
  have hmod : x % (n' : ℤ) = z % (n' : ℤ) := by
    rw [← posOf_val, ← posOf_val, hxz]
  obtain ⟨t, ht⟩ := Int.ModEq.dvd hmod

  have hxt : x = z + (-t) * n' := by linarith
  have g1 := hperT (-t) ((j0 : ℤ) - 1) (r - 1)
  have g2 := hperT (-t) (j0 : ℤ) 0
  have e1 : (j0 : ℤ) - 1 + -t * F.J = ((j0 : ℤ) + -t * F.J) - 1 := by ring
  rw [e1] at g1
  have hjj := key ((j0 : ℤ) + -t * F.J) (j : ℤ) x (by rw [g1, hxt]; linarith) (by rw [g2, hxt]; linarith) hx1 hx2
  have hJ1 : (1 : ℤ) ≤ F.J := by exact_mod_cast hJ
  have ht0 : t = 0 := by
    have hj' : (j : ℤ) < F.J := by exact_mod_cast hj
    have hj0' : (j0 : ℤ) < F.J := by exact_mod_cast hj0
    rcases lt_trichotomy t 0 with h | h | h
    · exfalso
      have : (1 : ℤ) ≤ -t := by omega
      nlinarith
    · exact h
    · exfalso
      have : (1 : ℤ) ≤ t := by omega
      nlinarith
  subst ht0
  constructor
  · simp at hjj
    exact_mod_cast hjj
  · simpa using hxt

end U

theorem top_degree_comparison : TopDegreeComparison := by
  intro p n' r K _ _ _ X O _ _ hX b y l hy hl hdeg hne j0 hj0 z hz
  classical
  have hV := hX.valid
  have hj0' : j0 < X.F.J := Finset.mem_range.mp hj0
  have hzz := hz
  unfold Frames.LLset at hzz
  rw [Finset.mem_filter, Finset.mem_Ioo] at hzz
  obtain ⟨⟨hz1, hz2⟩, hzT⟩ := hzz
  have hzW : ¬ X.F.IsW (j0 : ℤ) z := not_le.mpr hz1
  have hzl : z ∈ X.F.letters (j0 : ℤ) := by
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨(fr_zero_le_eFr hV _).trans hz1.le, hz2.le.trans (fr_zero_le_eFr hV _)⟩, hzT⟩
  set t := posOf n' z with ht
  set P : ℕ := p ^ (X.F.dist (j0 : ℤ) z + X.Rj p K (j0 : ℤ)) with hP
  have hδ : ∀ j ∈ Finset.range X.F.J, DegAt t (if j = j0 then P * b j0 z else 0) (X.phc p K O (j : ℤ) (y j)) := by
    intro j hj m' hm'
    have hj' : j < X.F.J := Finset.mem_range.mp hj
    obtain ⟨m, hm, rfl⟩ := supp_aeval_pow (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2))
      (fun v => p ^ (X.F.dist (j : ℤ) v.1 + X.Rj p K (j : ℤ))) (y j) hm'
    have hsup := XX'_supported O X.F (j : ℤ) _ _ _ (hy j).1.1
    have hT : ∀ v ∈ m.support, v.1 ∈ X.F.letters (j : ℤ) := by
      intro v hv
      have hvv : v ∈ (y j).vars := (mem_vars_iff_mem_support v).mpr ⟨m, hm, hv⟩
      exact ((mem_supported.mp hsup) (Finset.mem_coe.mpr hvv)).1
    have hPol : y j ∈ Pol O (r + K) (b j) := by rw [← segDeg_eq_Pol]; exact (hy j).1.2
    rw [multideg_imgMon (fun x : ℤ => posOf n' x) (fun x : ℤ => p ^ (X.F.dist (j : ℤ) x + X.Rj p K (j : ℤ))) m t,
      sum_eq_multideg (fun x => if posOf n' x = t then p ^ (X.F.dist (j : ℤ) x + X.Rj p K (j : ℤ)) else 0) m
        (X.F.letters (j : ℤ)) hT]
    by_cases hjj : j = j0
    · subst hjj
      rw [ite_eq_left rfl, Finset.sum_eq_single z]
      · rw [ite_eq_left rfl, mem_Pol_iff.mp hPol m hm z]
      · intro x hx hxz
        rw [ite_eq_right, zero_mul]
        intro h
        exact hxz (LL_unique hV j hj0' z hz j hj' x hx h).2
      · intro h; exact absurd hzl h
    · rw [ite_eq_right hjj]
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [ite_eq_right, zero_mul]
      intro h
      exact hjj (LL_unique hV j0 hj0' z hz j hj' x hx h).1
  have hU := degAt_mul (degAt_prod _ _ _ hδ) (degAt_monomial l (1 : O) t)
  rw [Finset.sum_ite_eq' (Finset.range X.F.J) j0, ite_eq_left hj0] at hU
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hm0' := MvPolynomial.mem_support_iff.mpr hm0
  rw [RRdeg_eq_Pol] at hdeg
  have ha' : X.a' p K t = P * b j0 z + multideg l t := (mem_Pol_iff.mp hdeg m0 hm0' t).symm.trans (hU m0 hm0')
  have hP0 : 0 < P := Nat.pow_pos hX.prime.pos
  have hl' : multideg l t ≤ (r + K) * (P - 1) := by
    unfold multideg
    have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin (r + K) => l (t, c)) (P - 1)
      (fun c _ => Nat.le_sub_one_of_lt (hl (j0 : ℤ) z hzl hzW c))
    simpa using this
  have hrK : 0 < r + K := Nat.add_pos_left (NeZero.pos r) K
  have hlt : X.a' p K t < (b j0 z + (r + K)) * P := by
    rw [ha']
    have : (r + K) * (P - 1) < (r + K) * P := Nat.mul_lt_mul_of_pos_left (by omega) hrK
    nlinarith
  have hltR : (X.a' p K t : ℝ) < ((b j0 z : ℝ) + Dat.k (r := r) K) * (P : ℝ) := by
    unfold Dat.k
    exact_mod_cast hlt
  have hPR : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP0
  have hPe : ((p : ℝ) ^ (X.F.dist (j0 : ℤ) z + X.Rj p K (j0 : ℤ))) = (P : ℝ) := by rw [hP]; push_cast; rfl
  rw [hPe, sub_lt_iff_lt_add, div_lt_iff₀ hPR]
  exact hltR

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Occ

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

open Classical in
theorem occ_Ioc (hV : F.Valid L₁ N₁) (c : ℤ) (t : Fin n') :
    ∑ j ∈ Finset.range F.J, ((Finset.Ioc (eFr F ((j : ℤ) + c)) (eFr F (((j + 1 : ℕ) : ℤ) + c))).filter
      fun y => posOf n' y = t).card ≤ 1 := by
  have hm := eFr_strictMono hV
  have h3 := sum_card_Ioc (fun i : ℕ => eFr F ((i : ℤ) + c)) (fun a b hab => hm.monotone (by omega))
    (fun y => posOf n' y = t) F.J
  rw [h3]
  have h2 : eFr F ((F.J : ℤ) + c) = eFr F (((0 : ℕ) : ℤ) + c) + n' := by
    have := hV.2.1 c (r - 1)
    simp only [eFr]
    rw [show (F.J : ℤ) + c = c + F.J by ring, show ((0 : ℕ) : ℤ) + c = c by simp, this]
  simp only [h2]
  rw [Finset.card_le_one]
  intro a ha b hb
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  exact posOf_injOn _ (Finset.mem_Ioc.mp ha'.1) (Finset.mem_Ioc.mp hb'.1) (ha'.2.trans hb'.2.symm)

end Occ

theorem top_occurs_in_at_most_two_segments : LeadingLetterInAtMostTwoSegments := by
  intro p n' r K _ _ _ X hX t
  classical
  have hV := hX.valid
  have h1 := occ_Ioc hV (-2) t
  have h2 := occ_Ioc hV (-1) t
  have key : ∀ j ∈ Finset.range X.F.J, ((X.F.letters (j : ℤ)).filter fun y => posOf n' y = t).card ≤
      ((Finset.Ioc (eFr X.F ((j : ℤ) + -2)) (eFr X.F (((j + 1 : ℕ) : ℤ) + -2))).filter fun y => posOf n' y = t).card +
      ((Finset.Ioc (eFr X.F ((j : ℤ) + -1)) (eFr X.F (((j + 1 : ℕ) : ℤ) + -1))).filter fun y => posOf n' y = t).card := by
    intro j _
    refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
    intro y hy
    obtain ⟨hyl, hyt⟩ := Finset.mem_filter.mp hy
    have hb := mem_letters_bounds hyl
    have e1 : ((j + 1 : ℕ) : ℤ) + -2 = (j : ℤ) - 1 := by push_cast; ring
    have e2 : ((j + 1 : ℕ) : ℤ) + -1 = (j : ℤ) := by push_cast; ring
    have e3 : (j : ℤ) + -1 = (j : ℤ) - 1 := by ring
    have h4 := hV.2.2.2.1 ((j : ℤ) + -2)
    have e4 : (j : ℤ) + -2 + 1 = (j : ℤ) - 1 := by ring
    rw [e4] at h4
    rw [e1, e2, e3, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ioc]
    simp only [eFr]
    by_cases hc : y ≤ X.F.fr ((j : ℤ) - 1) (r - 1)
    · exact Or.inl ⟨⟨lt_of_lt_of_le h4 hb.1, hc⟩, hyt⟩
    · exact Or.inr ⟨⟨not_le.mp hc, hb.2.1⟩, hyt⟩
  refine le_trans (Finset.sum_le_sum key) ?_
  rw [Finset.sum_add_distrib]
  omega

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem degAt_ph_detPl {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (j x : ℤ) (t : Fin n') :
    DegAt t (∑ a : Fin r, if posOf n' (X.row j x a) = t then p ^ X.F.dist j (X.row j x a) else 0)
      (phSeg R K p X.F j (plEmb R r K (X.detPl R j x))) := by
  have key : ∀ σ : Equiv.Perm (Fin r), DegAt t
      (∑ a : Fin r, if posOf n' (X.row j x a) = t then p ^ X.F.dist j (X.row j x a) else 0)
      (∏ i : Fin r, phSeg R K p X.F j (plEmb R r K (MvPolynomial.X (X.row j x (σ i), i)))) := by
    intro σ
    rw [← Equiv.sum_comp σ (fun a => if posOf n' (X.row j x a) = t then p ^ X.F.dist j (X.row j x a) else 0)]
    apply degAt_prod
    intro i _
    simp only [plEmb, phSeg, rename_X, aeval_X]
    have h := degAt_pow (R := R) (degAt_X (x := t) (posOf n' (X.row j x (σ i)), Fin.castAdd K i))
      (p ^ X.F.dist j (X.row j x (σ i)))
    convert h using 2
    split_ifs <;> simp
  unfold Dat.detPl
  rw [Matrix.det_apply']

  simp only [map_sum, map_mul, map_prod, Matrix.of_apply, map_intCast]
  apply degAt_sum
  intro σ _
  have e : ((Equiv.Perm.sign σ : ℤ) : RRing R n' (r + K)) = C ((Equiv.Perm.sign σ : ℤ) : R) := by simp
  rw [e]
  exact degAt_C_mul _ (key σ)

theorem discriminant_multihomogeneous : DiscriminantMultihomogeneous := by
  intro p n' r K _ _ _ X O _
  rw [RRdeg, mem_restrictSupport_iff]
  intro m hm t
  have hdeg : DegAt t (X.Et p K t) (X.Dl p K O) := by
    unfold Dat.Dl Dat.DlSeg Dat.Et
    simp only [map_prod, map_pow]
    apply degAt_prod
    intro j _
    apply degAt_prod
    intro x _
    exact degAt_pow (degAt_ph_detPl X p K j x t) _
  exact hdeg m hm

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem late_vectors_distinct_tops : LateVectorsDistinctLeadingTerms := by
  intro p n' r K _ _ _ X hX j x hx
  obtain ⟨-, -, -, hnext, hTT, -⟩ := hX.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hn : (0 : ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have hstep : ∀ t : ℤ, ∀ i < r, ∀ i' < r, X.F.fr t i < X.F.fr (t + 1) i' := by
    intro t i hi i' hi'
    calc X.F.fr t i ≤ X.F.fr t (r - 1) := bk_fr_le hX.valid t i (r - 1) (by omega) (by omega)
      _ < X.F.fr (t + 1) 0 := hnext t
      _ ≤ X.F.fr (t + 1) i' := fr_zero_le hX.valid (t + 1) i' hi'
  have hlt' : ∀ t : ℤ, ∀ k : ℕ, ∀ i < r, ∀ i' < r, X.F.fr t i < X.F.fr (t + 1 + k) i' := by
    intro t k
    induction k with
    | zero =>
      intro i hi i' hi'
      simpa using hstep t i hi i' hi'
    | succ k ih =>
      intro i hi i' hi'
      rw [show t + 1 + ((k + 1 : ℕ) : ℤ) = t + 1 + k + 1 by push_cast; ring]
      exact (ih i hi 0 hr).trans (hstep _ 0 hr i' hi')
  have hlt : ∀ t t' : ℤ, t < t' → ∀ i < r, ∀ i' < r, X.F.fr t i < X.F.fr t' i' := by
    intro t t' htt i hi i' hi'
    obtain ⟨k, hk⟩ : ∃ k : ℕ, t' = t + 1 + k := ⟨(t' - t - 1).toNat, by omega⟩
    rw [hk]
    exact hlt' t k i hi i' hi'
  have hinjfr : ∀ t t' : ℤ, ∀ i < r, ∀ i' < r, X.F.fr t i = X.F.fr t' i' → t = t' ∧ i = i' := by
    intro t t' i hi i' hi' h
    rcases lt_trichotomy t t' with h1 | rfl | h1
    · exact absurd h (hlt t t' h1 i hi i' hi').ne
    · refine ⟨rfl, ?_⟩
      rcases lt_trichotomy i i' with h2 | h2 | h2
      · exact absurd h (bk_fr_lt hX.valid t i i' h2 hi').ne
      · exact h2
      · exact absurd h.symm (bk_fr_lt hX.valid t i' i h2 hi).ne
    · exact absurd h.symm (hlt t' t h1 i' hi' i hi).ne
  rw [mem_late] at hx
  obtain ⟨-, hxW⟩ := hx
  simp only [Frames.IsW, not_le] at hxW
  obtain ⟨S, hS⟩ : ∃ S : Finset ℤ, S = {z ∈ X.F.letters j | Even z ∧ z < x} := ⟨_, rfl⟩
  have hmem : ∀ z, z ∈ evL X.F j x ↔ z ∈ S := fun z => by
    rw [hS]
    exact Finset.mem_sort _
  have hsort : (evL X.F j x).Pairwise (· < ·) := by
    rw [evL, ← hS]
    exact ((Finset.pairwise_sort S _).and (Finset.sort_nodup S _)).imp (fun h => lt_of_le_of_ne h.1 h.2)
  have hlen : (evL X.F j x).length = S.card := by
    rw [evL, ← hS]
    exact Finset.length_sort _
  have hfrS : ∀ t : ℤ, ∀ i < r, X.F.fr (j - 1) 0 ≤ X.F.fr t i → X.F.fr t i ≤ X.F.fr j (r - 1) →
      X.F.fr t i < x → X.F.fr t i ∈ S := by
    intro t i hi h1 h2 h3
    rw [hS]
    simp only [Finset.mem_filter, Frames.letters, Finset.mem_Icc]
    exact ⟨⟨⟨h1, h2⟩, (hTT t i hi).1⟩, (hTT t i hi).2, h3⟩
  have hSlo : ∀ z ∈ S, X.F.fr (j - 1) 0 ≤ z ∧ z ≤ X.F.fr j (r - 1) ∧ z < x := by
    intro z hz
    rw [hS, Finset.mem_filter] at hz
    have hb := mem_letters_bounds hz.1
    exact ⟨hb.1, hb.2.1, hz.2.2⟩
  have hlenr : r ≤ S.card := by
    have hsub : (Finset.range r).image (fun i => X.F.fr (j - 1) i) ⊆ S := by
      intro z hz
      simp only [Finset.mem_image, Finset.mem_range] at hz
      obtain ⟨i, hi, rfl⟩ := hz
      have hA : X.F.fr (j - 1) i ≤ X.F.fr (j - 1) (r - 1) :=
        bk_fr_le hX.valid _ i (r - 1) (by omega) (by omega)
      have hB : X.F.fr (j - 1) i < X.F.fr j (r - 1) := hlt (j - 1) j (by omega) i hi (r - 1) (by omega)
      exact hfrS _ i hi (fr_zero_le hX.valid _ i hi) hB.le (lt_of_le_of_lt hA hxW)
    have hinj' : Set.InjOn (fun i => X.F.fr (j - 1) i) ↑(Finset.range r) := by
      intro a ha b hb h
      simp only [Finset.coe_range, Set.mem_Iio] at ha hb
      exact (hinjfr _ _ a ha b hb h).2
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injOn hinj', Finset.card_range] at hc
    exact hc
  simp only [row_eq]
  generalize evL X.F j x = l at hmem hsort hlen ⊢
  have hget : ∀ k (hk : k < l.length), l.getD k 0 = l[k] := fun k hk => List.getD_eq_getElem _ _ hk
  have hpw := List.pairwise_iff_getElem.mp hsort
  have hm : l.length - r < l.length := by omega
  have hinS : ∀ k, k < l.length → l.getD k 0 ∈ S := by
    intro k hk
    rw [hget k hk]
    exact (hmem _).1 (List.getElem_mem _)
  have hbound : ∀ k, l.length - r ≤ k → k < l.length →
      l.getD (l.length - r) 0 ≤ l.getD k 0 ∧ l.getD k 0 < l.getD (l.length - r) 0 + n' := by
    intro k hk1 hk2
    refine ⟨?_, ?_⟩
    · rcases eq_or_lt_of_le hk1 with h | h
      · rw [h]
      · rw [hget _ hm, hget _ hk2]
        exact (hpw _ _ hm hk2 h).le
    · by_contra! hz
      have hy1S := hinS _ hm
      have hzS := hinS _ hk2
      obtain ⟨hy1lo, -, -⟩ := hSlo _ hy1S
      obtain ⟨-, hzhi, hzx⟩ := hSlo _ hzS
      obtain ⟨y1, hy1⟩ : ∃ y1, y1 = l.getD (l.length - r) 0 := ⟨_, rfl⟩
      obtain ⟨z, hzdef⟩ : ∃ z, z = l.getD k 0 := ⟨_, rfl⟩
      rw [← hy1, ← hzdef] at hz
      rw [← hy1] at hy1lo hy1S
      rw [← hzdef] at hzhi hzx hzS
      let w : ℕ → ℤ := fun i => X.F.fr (0 + (-((X.F.fr 0 i - y1) / n')) * X.F.J) i
      have hwr : ∀ i < r, y1 ≤ w i ∧ w i < y1 + n' := by
        intro i hi
        have hw : w i = X.F.fr 0 i + (-((X.F.fr 0 i - y1) / n')) * n' :=
          fr_period hX.valid 0 i (-((X.F.fr 0 i - y1) / n'))
        have e1 := Int.mul_ediv_add_emod (X.F.fr 0 i - y1) (n' : ℤ)
        have e2 := Int.emod_nonneg (X.F.fr 0 i - y1) (ne_of_gt hn)
        have e3 := Int.emod_lt_of_pos (X.F.fr 0 i - y1) hn
        constructor <;> linarith
      obtain ⟨T, hT⟩ : ∃ T : Finset ℤ, T = S.filter (fun s => y1 ≤ s) := ⟨_, rfl⟩
      have hTcard : T.card ≤ r := by
        have hsub : T ⊆ (Finset.Ico (l.length - r) l.length).image (fun k => l.getD k 0) := by
          intro s hs
          rw [hT, Finset.mem_filter] at hs
          obtain ⟨k', hk', rfl⟩ := List.getElem_of_mem ((hmem _).2 hs.1)
          refine Finset.mem_image.2 ⟨k', Finset.mem_Ico.2 ⟨?_, hk'⟩, hget k' hk'⟩
          by_contra! hlt2
          have h3 := hpw k' _ hk' hm hlt2
          have h2 := hs.2
          rw [hy1, hget _ hm] at h2
          exact absurd h2 (not_le.2 h3)
        have := (Finset.card_le_card hsub).trans Finset.card_image_le
        rw [Nat.card_Ico] at this
        omega
      have hwinj : Set.InjOn w ↑(Finset.range r) := by
        intro a ha b hb h
        simp only [Finset.coe_range, Set.mem_Iio] at ha hb
        exact (hinjfr _ _ a ha b hb h).2
      have hznot : z ∉ (Finset.range r).image w := by
        intro hzin
        simp only [Finset.mem_image, Finset.mem_range] at hzin
        obtain ⟨i, hi, hwi⟩ := hzin
        have := (hwr i hi).2
        linarith
      have hUsub : insert z ((Finset.range r).image w) ⊆ T := by
        intro s hs
        rw [Finset.mem_insert] at hs
        rw [hT, Finset.mem_filter]
        rcases hs with rfl | hs
        · exact ⟨hzS, by linarith⟩
        · simp only [Finset.mem_image, Finset.mem_range] at hs
          obtain ⟨i, hi, rfl⟩ := hs
          obtain ⟨hw1, hw2⟩ := hwr i hi
          exact ⟨hfrS _ i hi (by linarith) (by linarith) (by linarith), hw1⟩
      have hc := Finset.card_le_card hUsub
      rw [Finset.card_insert_of_notMem hznot, Finset.card_image_of_injOn hwinj, Finset.card_range] at hc
      omega
  intro a b hab
  simp only at hab
  have ha := hbound (l.length - r + a) (by omega) (by omega)
  have hb := hbound (l.length - r + b) (by omega) (by omega)
  have he := posOf_injOn (l.getD (l.length - r) 0 - 1)
    (show l.getD (l.length - r + a) 0 ∈ Set.Ioc _ _ from ⟨by linarith [ha.1], by linarith [ha.2]⟩)
    (show l.getD (l.length - r + b) 0 ∈ Set.Ioc _ _ from ⟨by linarith [hb.1], by linarith [hb.2]⟩) hab
  have hia : l.length - r + (a : ℕ) < l.length := by omega
  have hib : l.length - r + (b : ℕ) < l.length := by omega
  rw [hget _ hia, hget _ hib] at he
  apply Fin.ext
  rcases lt_trichotomy (l.length - r + (a : ℕ)) (l.length - r + (b : ℕ)) with h | h | h
  · exact absurd he (hpw _ _ hia hib h).ne
  · omega
  · exact absurd he.symm (hpw _ _ hib hia h).ne

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem ell_degree_le_power_bound : EllDegreeLePowerBound := by
  intro p n' r K _ _ _ X hX j e he
  classical
  unfold Dat.dS Dat.dV
  rw [← Finset.sum_add_distrib]
  have h1 : ∀ x ∈ X.toLate j, ((if Even x then 0 else ∑ c : Fin r, e (x, Fin.castAdd K c)) +
      (if Even x then ∑ c : Fin K, e (x, Fin.natAdd r c) else 0)) ≤ (r + K) * p ^ X.Rj p K j := by
    intro x _
    have a1 : ∑ c : Fin r, e (x, Fin.castAdd K c) ≤ r * p ^ X.Rj p K j := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin r => e (x, Fin.castAdd K c)) (p ^ X.Rj p K j)
        (fun c _ => (he.2 _).le)
      simpa using this
    have a2 : ∑ c : Fin K, e (x, Fin.natAdd r c) ≤ K * p ^ X.Rj p K j := by
      have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin K => e (x, Fin.natAdd r c)) (p ^ X.Rj p K j)
        (fun c _ => (he.2 _).le)
      simpa using this
    rw [add_mul]
    split_ifs <;> omega
  have h2 := Finset.sum_le_card_nsmul (X.toLate j) _ _ h1
  have h3 : (X.toLate j).card ≤ X.Ns := le_trans (by unfold Dat.toLate; exact Finset.card_filter_le _ _) (hX.card j)
  calc _ ≤ (X.toLate j).card • ((r + K) * p ^ X.Rj p K j) := h2
    _ = (X.toLate j).card * ((r + K) * p ^ X.Rj p K j) := smul_eq_mul _ _
    _ ≤ X.Ns * ((r + K) * p ^ X.Rj p K j) := Nat.mul_le_mul_right _ h3
    _ = (r + K) * X.Ns * p ^ X.Rj p K j := by ring

theorem degAt_ellP {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (x : ℤ) (hx : x ∈ X.toLate j) :
    DegAt x (∑ c : Fin r, e (x, Fin.castAdd K c)) (X.ellP K R j e) := by
  classical
  have h := degAt_prod (R := R) (x := x) (X.toLate j)
    (fun x' => ∏ c : Fin r, (MvPolynomial.X (x', c) : MvPolynomial (ℤ × Fin r) R) ^ e (x', Fin.castAdd K c))
    (fun x' => ∑ c : Fin r, e (x', Fin.castAdd K c) * (if x' = x then 1 else 0))
    (fun x' _ => degAt_prod Finset.univ _ _ (fun c _ => degAt_pow (degAt_X (x := x) (x', c)) _))
  have hD : (∑ x' ∈ X.toLate j, ∑ c : Fin r, e (x', Fin.castAdd K c) * (if x' = x then 1 else 0)) =
      ∑ c : Fin r, e (x, Fin.castAdd K c) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · intro h; exact absurd hx h
  rw [hD] at h
  exact h

theorem degAt_ellN {R : Type} [CommRing R] {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ) (j : ℤ)
    (e : ℤ × Fin (r + K) →₀ ℕ) (x : ℤ) (hx : x ∈ X.toLate j) :
    DegAt x (∑ c : Fin K, e (x, Fin.natAdd r c)) (X.ellN K R j e) := by
  classical
  have h := degAt_prod (R := R) (x := x) (X.toLate j)
    (fun x' => ∏ c : Fin K, (MvPolynomial.X (x', c) : MvPolynomial (ℤ × Fin K) R) ^ e (x', Fin.natAdd r c))
    (fun x' => ∑ c : Fin K, e (x', Fin.natAdd r c) * (if x' = x then 1 else 0))
    (fun x' _ => degAt_prod Finset.univ _ _ (fun c _ => degAt_pow (degAt_X (x := x) (x', c)) _))
  have hD : (∑ x' ∈ X.toLate j, ∑ c : Fin K, e (x', Fin.natAdd r c) * (if x' = x then 1 else 0)) =
      ∑ c : Fin K, e (x, Fin.natAdd r c) := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy; simp [hy]
    · intro h; exact absurd hx h
  rw [hD] at h
  exact h

theorem word_order_bound_of_numeric_bound (D : Formalism.BasicNotions.D7) (hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D) (C₀ : ℝ) (hRow : LateIndexInjective) (hN3 : OrderNumericBound C₀) :
    ProductOrdersBounded C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S j b e q I' I'' hc mm hmm x hx hW
  have : Fact p.Prime := ⟨hc.hX.prime⟩
  obtain ⟨i, rfl⟩ := segE_surj X.F j hx
  obtain ⟨nu, ka⟩ := q
  obtain ⟨b', b'', ⟨P1, h1⟩, ⟨P2, h2⟩, hcond⟩ := hc.hq
  have hI' := hc.hI'
  have hI'' := hc.hI''
  simp only at h1 h2 hcond hI' hI'' hmm
  rw [← h1] at hI' hcond hmm
  rw [← h2] at hI'' hcond hmm
  have u1 := standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).2) P1 I' hI'
  have u2 := standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).2) P2 I'' hI''
  obtain ⟨cE, cO, -⟩ := (hcond i).2 hW
  have hxl : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hW⟩
  have hrows := hRow p n' r K X hc.hX j
  have n3 := hN3 p n' r K X hc.hX hc.hLa hc.hk j _ hxl
  have hQ0 : (0 : ℝ) ≤ ((p ^ X.Rj p K j : ℕ) : ℝ) := Nat.cast_nonneg _
  have dG : DegAt (segE X.F j i) (p ^ X.Rj p K j * b'' i + ∑ c : Fin K, e (segE X.F j i, Fin.natAdd r c))
      (X.Gw p K (FF O) j e P2.mu I'') := by
    unfold Dat.Gw
    exact degAt_mul (degAt_pow (degAt_segRen X.F j u2.1 i) _) (degAt_ellN X K j e _ hxl)
  have dA : ¬ Even (segE X.F j i) →
      DegAt (segE X.F j i) (p ^ X.Rj p K j * b' i + ∑ c : Fin r, e (segE X.F j i, Fin.castAdd K c) + 0)
      (X.Aw p K (FF O) j e P1.mu I') := by
    intro he
    unfold Dat.Aw
    refine degAt_mul (degAt_mul (degAt_pow (degAt_segRen X.F j u1.1 i) _) (degAt_ellP X K j e _ hxl)) ?_
    refine degAt_of_supported {v : ℤ × Fin r | Even v.1} (DlSeg_supported _ X p K j _
      fun x' hx' a _ => ((hrows x' hx').2 a).2.1) ?_
    intro v hv hvx
    exact he (hvx ▸ hv)
  have a1 : ∑ c : Fin r, e (segE X.F j i, Fin.castAdd K c) ≤ r * p ^ X.Rj p K j := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin r => e (segE X.F j i, Fin.castAdd K c))
      (p ^ X.Rj p K j) (fun c _ => (hc.he.2 _).le)
    simpa using this
  have a2 : ∑ c : Fin K, e (segE X.F j i, Fin.natAdd r c) ≤ K * p ^ X.Rj p K j := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun c : Fin K => e (segE X.F j i, Fin.natAdd r c))
      (p ^ X.Rj p K j) (fun c _ => (hc.he.2 _).le)
    simpa using this
  have a1r : ((∑ c : Fin r, e (segE X.F j i, Fin.castAdd K c) : ℕ) : ℝ) ≤ (r : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by
    exact_mod_cast a1
  have a2r : ((∑ c : Fin K, e (segE X.F j i, Fin.natAdd r c) : ℕ) : ℝ) ≤ (K : ℝ) * ((p ^ X.Rj p K j : ℕ) : ℝ) := by
    exact_mod_cast a2
  have hkd : Dat.k (r := r) K = (r : ℝ) + K := by unfold Dat.k; push_cast; ring
  rw [hkd] at n3
  rw [ordDeg_prod dA (fun _ => dG) mm hmm]
  refine le_trans ?_ n3
  split_ifs with he
  · have hb := mul_le_mul_of_nonneg_left (cE he).2 hQ0
    rw [Nat.cast_add, Nat.cast_mul]
    linarith
  · have hb := mul_le_mul_of_nonneg_left (cO he).2 hQ0
    rw [add_zero, Nat.cast_add, Nat.cast_mul]
    linarith

end

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem discriminant_nonzero_mod_uniformiser : DiscriminantNonzeroModUniformiser := discriminant_nonzero_of_injective_tops late_vectors_distinct_tops

theorem generator_modulo_uniformiser_of_adm (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) (hC : 32 ≤ C₀) : GeneratorModuloUniformiser C₀ := by
  have hV1 : Formalism.MainNotions.CovariantDegrees.ValuationsAdditive D := hAdm.2.2.2.2.2.2.2.1.1
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  have hB12 : NestedTypeBound D := hAdm.2.2.2.2.2.2.2.2.2.2.2.1
  have h41b : TopCountLowerBounds C₀ := top_count_lower_bounds_of_occurrence C₀ hC top_occurs_in_at_most_two_segments
  have hW3 := column_conditions_of_numeric_bounds D hV1 hA3 C₀ late_row_injective ell_degree_le_power_bound (power_exceeds_max_multiplicity C₀) (threshold_power_bound_of_counts C₀ h41b oldest_letter_in_segment)
  have hW4 := word_order_bound_of_numeric_bound D hA3 C₀ late_row_injective (order_numeric_bound_of_oldest C₀ oldest_letter_in_segment)
  have hW2 := allowed_letters_of_late_rows D hA3 C₀ late_row_injective
  have hWord := column_word_reduction_of_four D hB12 C₀ (frobenius_reduction_product C₀) hW2 hW3 hW4
  exact generator_of_segment_reductions C₀ coarse_label_factorisation top_degree_comparison discriminant_multihomogeneous (discriminant_ne_zero_of_residue_ne_zero discriminant_nonzero_mod_uniformiser) h41b (segment_reduction_of_column_words D hB12 C₀ hWord)
    segment_image_multihomogeneous segment_product_degree_determined

theorem top_count_lower_bounds (C₀ : ℝ) (hC : 32 ≤ C₀) : TopCountLowerBounds C₀ := top_count_lower_bounds_of_occurrence C₀ hC top_occurs_in_at_most_two_segments

end Formalism.MainNotions.SelectionLemmas.Pf
