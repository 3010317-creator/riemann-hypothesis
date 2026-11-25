module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Discriminant
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Foundation
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LeIffLtColH
public import Formalism.SharpRestriction.GrowthBounds.ObjPol
public import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
public import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeRename
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.StatementT
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Basic.Real.Basic
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Fintype.Pi
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Nat.ModEq
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {n N : ℕ} {LL : Letters (Fin N)} {dd : Fin N → ℕ}

theorem step_vec (P : PPath n N LL dd) (i : Fin N) (h : LL.vec i = true) :
    HStrip (P.mu i.castSucc) (P.mu i.succ) (dd i) := by
  simpa [h] using P.step i

theorem step_cov (P : PPath n N LL dd) (i : Fin N) (h : LL.vec i = false) :
    HStrip (P.mu i.succ) (P.mu i.castSucc) (dd i) := by
  simpa [h] using P.step i

theorem mu_nonneg (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), m.val + s < n → 0 ≤ P.mu ⟨s, hs⟩ m := by
  intro s
  induction s with
  | zero =>
    intro hs m _
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m hm
    have hsN : s < N := by omega
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have hm1 : m.val + 1 < n := by omega
      calc (0 : ℤ) ≤ P.mu ⟨s, by omega⟩ ⟨m.val + 1, hm1⟩ :=
            ih (by omega) ⟨m.val + 1, hm1⟩ (show m.val + 1 + s < n by omega)
        _ ≤ P.mu ⟨s + 1, hs⟩ m := hstr.2.1 m hm1
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      calc (0 : ℤ) ≤ P.mu ⟨s, by omega⟩ m := ih (by omega) m (by omega)
        _ ≤ P.mu ⟨s + 1, hs⟩ m := hstr.1 m

theorem mu_nonpos (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), s ≤ m.val → P.mu ⟨s, hs⟩ m ≤ 0 := by
  intro s
  induction s with
  | zero =>
    intro hs m _
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m hm
    have hsN : s < N := by omega
    obtain ⟨mv, hmv⟩ := m
    have hm' : s + 1 ≤ mv := hm
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      calc P.mu ⟨s + 1, hs⟩ ⟨mv, hmv⟩ ≤ P.mu ⟨s, by omega⟩ ⟨mv, hmv⟩ := hstr.1 _
        _ ≤ 0 := ih (by omega) ⟨mv, hmv⟩ (show s ≤ mv by omega)
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      obtain _ | mv := mv
      · omega
      · calc P.mu ⟨s + 1, hs⟩ ⟨mv + 1, hmv⟩ ≤ P.mu ⟨s, by omega⟩ ⟨mv, by omega⟩ := hstr.2.1 ⟨mv, by omega⟩ hmv
          _ ≤ 0 := ih (by omega) ⟨mv, by omega⟩ (show s ≤ mv by omega)

def dplus (LL : Letters (Fin N)) (dd : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∑ l : Fin N, if l.val < s ∧ LL.vec l = true then dd l else 0

def dminus (LL : Letters (Fin N)) (dd : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∑ l : Fin N, if l.val < s ∧ LL.vec l = false then dd l else 0

theorem dsum_succ (f : Fin N → Prop) [DecidablePred f] (dd : Fin N → ℕ) (s : ℕ) (hs : s < N) :
    (∑ l : Fin N, if l.val < s + 1 ∧ f l then dd l else 0) =
      (∑ l : Fin N, if l.val < s ∧ f l then dd l else 0) + if f ⟨s, hs⟩ then dd ⟨s, hs⟩ else 0 := by
  have key : ∀ l : Fin N, (if l.val < s + 1 ∧ f l then dd l else 0) =
      (if l.val < s ∧ f l then dd l else 0) + (if l = ⟨s, hs⟩ then (if f ⟨s, hs⟩ then dd ⟨s, hs⟩ else 0) else 0) := by
    intro l
    by_cases h1 : l = ⟨s, hs⟩
    · subst h1
      simp
    · have hne : l.val ≠ s := fun h => h1 (Fin.ext h)
      have hiff : (l.val < s + 1 ∧ f l) ↔ (l.val < s ∧ f l) :=
        ⟨fun ⟨a, b⟩ => ⟨by omega, b⟩, fun ⟨a, b⟩ => ⟨by omega, b⟩⟩
      simp only [hiff, h1, ite_false, add_zero]
  rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_add_distrib]
  simp

theorem strip_le_add {nu mu : Fin n → ℤ} {b : ℕ} (h : HStrip nu mu b) (m : Fin n) : mu m ≤ nu m + b := by
  have h1 : mu m - nu m ≤ ∑ a, (mu a - nu a) :=
    Finset.single_le_sum (f := fun a => mu a - nu a) (fun a _ => sub_nonneg.mpr (h.1 a)) (Finset.mem_univ m)
  rw [h.2.2] at h1
  linarith

theorem mu_le_dplus (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), P.mu ⟨s, hs⟩ m ≤ (dplus LL dd s : ℤ) := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m
    have hsN : s < N := by omega
    have hd : (∑ l : Fin N, if l.val < s + 1 ∧ LL.vec l = true then dd l else 0) =
        (∑ l : Fin N, if l.val < s ∧ LL.vec l = true then dd l else 0) +
          if LL.vec ⟨s, hsN⟩ = true then dd ⟨s, hsN⟩ else 0 :=
      dsum_succ (fun l : Fin N => LL.vec l = true) dd s hsN
    have h1 := ih (by omega) m
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have h2 : dplus LL dd (s + 1) = dplus LL dd s := by
        unfold dplus
        rw [hd, hv]
        simp
      rw [h2]
      exact (hstr.1 m).trans h1
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have h2 : dplus LL dd (s + 1) = dplus LL dd s + dd ⟨s, hsN⟩ := by
        unfold dplus
        rw [hd, hv]
        simp
      have h3 := strip_le_add hstr m
      rw [h2]
      push_cast
      linarith

theorem neg_dminus_le_mu (P : PPath n N LL dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin n), -(dminus LL dd s : ℤ) ≤ P.mu ⟨s, hs⟩ m := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := Fin.ext (by simp)
    rw [h0, P.zero]
    simp
  | succ s ih =>
    intro hs m
    have hsN : s < N := by omega
    have hd : (∑ l : Fin N, if l.val < s + 1 ∧ LL.vec l = false then dd l else 0) =
        (∑ l : Fin N, if l.val < s ∧ LL.vec l = false then dd l else 0) +
          if LL.vec ⟨s, hsN⟩ = false then dd ⟨s, hsN⟩ else 0 :=
      dsum_succ (fun l : Fin N => LL.vec l = false) dd s hsN
    have h1 := ih (by omega) m
    cases hv : LL.vec ⟨s, hsN⟩
    · have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      have h2 : dminus LL dd (s + 1) = dminus LL dd s + dd ⟨s, hsN⟩ := by
        unfold dminus
        rw [hd, hv]
        simp
      have h3 := strip_le_add hstr m
      rw [h2]
      push_cast
      linarith
    · have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have h2 : dminus LL dd (s + 1) = dminus LL dd s := by
        unfold dminus
        rw [hd, hv]
        simp
      rw [h2]
      exact h1.trans (hstr.1 m)

def vcount (LL : Letters (Fin N)) (t s : ℕ) : ℕ :=
  (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s ∧ LL.vec l = true).card

theorem vcount_self (LL : Letters (Fin N)) (t : ℕ) : vcount LL t t = 0 := by
  unfold vcount
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro l _ h
  obtain ⟨h1, h2, -⟩ := h
  omega

theorem vcount_succ (LL : Letters (Fin N)) (t s : ℕ) (hts : t ≤ s) (hs : s < N) :
    vcount LL t (s + 1) = vcount LL t s + if LL.vec ⟨s, hs⟩ = true then 1 else 0 := by
  unfold vcount
  by_cases hv : LL.vec ⟨s, hs⟩ = true
  · rw [ite_eq_left hv]
    have hset : (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s + 1 ∧ LL.vec l = true) =
        insert ⟨s, hs⟩ (Finset.univ.filter fun l : Fin N => t ≤ l.val ∧ l.val < s ∧ LL.vec l = true) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2, h3⟩
        by_cases hl : l.val = s
        · left
          exact Fin.ext hl
        · right
          exact ⟨h1, by omega, h3⟩
      · rintro (rfl | ⟨h1, h2, h3⟩)
        · exact ⟨hts, Nat.lt_succ_self s, hv⟩
        · exact ⟨h1, by omega, h3⟩
    rw [hset, Finset.card_insert_of_notMem]
    simp
  · rw [ite_eq_right hv, add_zero]
    congr 1
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨h1, ?_, h3⟩
      by_contra hc
      have hl : l = ⟨s, hs⟩ := Fin.ext (show l.val = s by omega)
      subst hl
      exact hv h3
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by omega, h3⟩

theorem row_back (P : PPath n N LL dd) (t : ℕ) :
    ∀ (s : ℕ) (_hts : t ≤ s) (hs : s < N + 1) (m m' : Fin n), m'.val = m.val + vcount LL t s →
      P.mu ⟨s, hs⟩ m' ≤ P.mu ⟨t, by omega⟩ m := by
  intro s hts
  induction s, hts using Nat.le_induction with
  | base =>
    intro hs m m' hm
    rw [vcount_self, add_zero] at hm
    have he : m' = m := Fin.ext hm
    subst he
    exact le_refl _
  | succ s hts ih =>
    intro hs m m' hm
    have hsN : s < N := by omega
    rw [vcount_succ LL t s hts hsN] at hm
    cases hv : LL.vec ⟨s, hsN⟩
    · rw [hv] at hm
      simp only [Bool.false_eq_true, ite_false, add_zero] at hm
      have hstr : HStrip (P.mu ⟨s + 1, hs⟩) (P.mu ⟨s, by omega⟩) (dd ⟨s, hsN⟩) := step_cov P ⟨s, hsN⟩ hv
      exact (hstr.1 m').trans (ih (by omega) m m' hm)
    · rw [hv] at hm
      simp only [ite_true] at hm
      have hstr : HStrip (P.mu ⟨s, by omega⟩) (P.mu ⟨s + 1, hs⟩) (dd ⟨s, hsN⟩) := step_vec P ⟨s, hsN⟩ hv
      have hlt := m'.isLt
      have ha : m.val + vcount LL t s < n := by omega
      have he : m' = ⟨m.val + vcount LL t s + 1, by omega⟩ := Fin.ext hm
      rw [he]
      exact (hstr.2.1 ⟨m.val + vcount LL t s, ha⟩ (by simp only; omega)).trans
        (ih (by omega) m ⟨m.val + vcount LL t s, ha⟩ rfl)

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def beA (n0 : ℕ) (B : Fin N → ℕ) : ℕ := ∑ i : Fin N, if i.val < n0 then B i else 0

structure IsPATHa (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ)
    (dd : Fin N → ℕ) : Prop where
  path : ∃ P : PPath (r + K) N LL dd, P.mu = μ
  degs : ∀ i : Fin N, i.val < n0 → dd i = B i
  head : ∀ (i : Fin N) (m : Fin (r + K)), n0 ≤ i.val → m.val ≤ i.val - n0 → μ i.succ m = (beA n0 B : ℤ)

def posS {n : ℕ} (la : Fin n → ℤ) : ℤ := ∑ m, max (la m) 0

def negS {n : ℕ} (la : Fin n → ℤ) : ℤ := ∑ m, max (-la m) 0

def Xi (r K : ℕ) (bb : Fin N → ℝ) (La : ℝ) (p : ℕ) (i : Fin N) : ℝ := La * bb i / ((p : ℝ) * ((r + K : ℕ) : ℝ))

def Typ [NeZero r] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ) (La : ℝ) (p : ℕ)
    (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Prop :=
  ∀ i : Fin N,
    (LL.vec i = false → ((posS (μ i.castSucc) - posS (μ i.succ) : ℤ) : ℝ) ≤ Xi r K bb La p i) ∧
    (LL.vec i = true → r ≤ i.val → ((negS (μ i.castSucc) - negS (μ i.succ) : ℤ) : ℝ) ≤ Xi r K bb La p i) ∧
    (r ≤ i.val → (2 / 3 : ℝ) * (B (od i) : ℝ) ≤ ((plPart μ i.castSucc (lastIdx r) : ℤ) : ℝ))

def GoodA [NeZero r] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ) (La : ℝ) (p : ℕ)
    (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Prop :=
  ∀ i : Fin N, r ≤ i.val →
    (2 / 3 : ℝ) * (B (od i) : ℝ) ≤ ((plPart μ i.castSucc (lastIdx r) : ℤ) : ℝ) ∧
    (LL.vec i = true → ((∑ c, (tanPart μ i.succ c - tanPart μ i.castSucc c) : ℤ) : ℝ) ≤
      Xi r K bb La p i + 2 * (B (od i) : ℝ)) ∧
    (LL.vec i = false → ((∑ c, (plPart μ i.castSucc c - plPart μ i.succ c) : ℤ) : ℝ) ≤ Xi r K bb La p i)

def rkA (r K n0 : ℕ) (B : Fin N → ℕ) : ℕ :=
  ∏ i : Fin N, if i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1

structure HypT (N n0 r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ) : Prop where
  hN : N = n0 + r
  r1 : 1 ≤ r
  a3 : 3 ≤ a
  p13 : 13 ≤ p
  H1 : ∀ i : Fin N, i.val < n0 → ((r + K : ℕ) : ℝ) ≤ (B i : ℝ) ∧ (B i : ℝ) ≤ 2 * a
  H2 : ∀ i i' : Fin N, i < i' → i'.val < n0 → LL.vec i = LL.vec i' → (p : ℝ) ^ 2 / 5 * (B i : ℝ) ≤ (B i' : ℝ)
  vec_true_of_early : ∀ i : Fin N, i.val < r → LL.vec i = true
  vec_true_of_late : ∀ i : Fin N, n0 ≤ i.val + r → LL.vec i = true
  two_r_le_n0 : 2 * r ≤ n0
  N_add_r_le_K : N + r ≤ K
  H4 : ((r + K : ℕ) : ℝ) / 2 ≤ (K : ℝ) - 2 * (N : ℝ)
  N_le_a : (N : ℝ) ≤ a
  od_lt : ∀ i : Fin N, r ≤ i.val → od i < i
  od_vec : ∀ i : Fin N, r ≤ i.val → LL.vec (od i) = true
  od_card : ∀ i : Fin N, r ≤ i.val →
    (Finset.univ.filter fun l : Fin N => od i ≤ l ∧ l < i ∧ LL.vec l = true).card = r
  bb_pos : ∀ i : Fin N, r ≤ i.val → 0 < bb i
  bb_le : ∀ i l : Fin N, r ≤ i.val → l < i → l.val < n0 → (B l : ℝ) ≤ 4 * bb i / (p : ℝ)
  La_pos : 0 < La

def ell0 (N : ℕ) (a : ℝ) : ℝ := Real.log (1 + 2 * a * (N : ℝ))

abbrev QT (N r K : ℕ) := (Fin (N + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K))

def SP (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) : Set (Fin (N + 1) → Fin (r + K) → ℤ) :=
  {μ | ∃ dd, IsPATHa LL n0 B μ dd}

def SAll (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) : Set (QT N r K) :=
  {q | q.1 ∈ SP LL n0 B ∧ IsSt (tanPart q.1) q.2}

def SGood [NeZero r] (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ) (La : ℝ)
    (p : ℕ) : Set (QT N r K) :=
  {q | q.1 ∈ SP LL n0 B ∧ GoodA LL B od bb La p q.1 ∧ IsSt (tanPart q.1) q.2}

def PathWeightEqRank : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    (SAll (r := r) (K := K) LL n0 B).Finite ∧ (SAll (r := r) (K := K) LL n0 B).ncard = rkA r K n0 B

def PathCountFinite : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    (SP (r := r) (K := K) LL n0 B).Finite ∧
      ((SP (r := r) (K := K) LL n0 B).ncard : ℝ) ≤ Real.exp (2 * (N : ℝ) ^ 2 * ell0 N a)

def AtypicalPathSmallWeight : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    ∀ μ ∈ SP (r := r) (K := K) LL n0 B, ¬ Typ LL B od bb La p μ →
      (({I | IsSt (tanPart μ) I} : Set (ℤ → Finset (Fin K))).ncard : ℝ) ≤
        Real.exp (9 * (N : ℝ) ^ 2 * ell0 N a -
          min (La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ))) (((K : ℝ) - 2 * N) / 12)) * (rkA r K n0 B : ℝ)

def TypicalPathOrdersSmall : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    ∀ μ ∈ SP (r := r) (K := K) LL n0 B, Typ LL B od bb La p μ → GoodA LL B od bb La p μ

def LemT : Prop :=
  ∀ (N n0 r K : ℕ) [NeZero r] [NeZero K] (LL : Letters (Fin N)) (B : Fin N → ℕ) (od : Fin N → Fin N) (bb : Fin N → ℝ)
    (a La : ℝ) (p : ℕ), HypT N n0 r K LL B od bb a La p →
    (SGood (r := r) (K := K) LL n0 B od bb La p).Finite ∧
      (1 - Real.exp (11 * (N : ℝ) ^ 2 * ell0 N a - min La ((r + K : ℕ) : ℝ) / 32)) * (rkA r K n0 B : ℝ) ≤
        ((SGood (r := r) (K := K) LL n0 B od bb La p).ncard : ℝ)

theorem lemT_of (ha : PathWeightEqRank) (hb : PathCountFinite) (hc : AtypicalPathSmallWeight) (hd : TypicalPathOrdersSmall) : LemT := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  obtain ⟨hfin, hcard⟩ := ha N n0 r K LL B od bb a La p H
  obtain ⟨hPfin, hPcard⟩ := hb N n0 r K LL B od bb a La p H
  have hc' := hc N n0 r K LL B od bb a La p H
  have hd' := hd N n0 r K LL B od bb a La p H
  set SA := SAll (r := r) (K := K) LL n0 B with hSA
  set SG := SGood (r := r) (K := K) LL n0 B od bb La p with hSG
  have hGA : SG ⊆ SA := fun q hq => ⟨hq.1, hq.2.2⟩
  have hGfin : SG.Finite := hfin.subset hGA
  refine ⟨hGfin, ?_⟩
  let SB : Set (QT N r K) := {q | q ∈ SA ∧ ¬ Typ LL B od bb La p q.1}
  have hBfin : SB.Finite := hfin.subset fun q hq => hq.1
  have hcov : SA ⊆ SG ∪ SB := by
    intro q hq
    by_cases ht : Typ LL B od bb La p q.1
    · exact Or.inl ⟨hq.1, hd' q.1 hq.1 ht, hq.2⟩
    · exact Or.inr ⟨hq, ht⟩
  have h1 : SA.ncard ≤ SG.ncard + SB.ncard :=
    le_trans (Set.ncard_le_ncard hcov (hGfin.union hBfin)) (Set.ncard_union_le _ _)
  set cR : ℝ := Real.exp (9 * (N : ℝ) ^ 2 * ell0 N a -
          min (La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ))) (((K : ℝ) - 2 * N) / 12)) * (rkA r K n0 B : ℝ) with hcR
  have hcR0 : 0 ≤ cR := by positivity

  have h2 : (SB.ncard : ℝ) ≤ ((SP (r := r) (K := K) LL n0 B).ncard : ℝ) * cR := by
    rw [Set.ncard_eq_toFinset_card _ hBfin, Set.ncard_eq_toFinset_card _ hPfin]
    have hmaps : ∀ q ∈ hBfin.toFinset, q.1 ∈ hPfin.toFinset := by
      intro q hq
      rw [Set.Finite.mem_toFinset] at hq ⊢
      exact hq.1.1
    have hfib : ∀ μ ∈ hPfin.toFinset, ((hBfin.toFinset.filter fun q => q.1 = μ).card : ℝ) ≤ cR := by
      intro μ hμ
      rw [Set.Finite.mem_toFinset] at hμ
      by_cases ht : Typ LL B od bb La p μ
      · have : hBfin.toFinset.filter (fun q => q.1 = μ) = ∅ := by
          rw [Finset.filter_eq_empty_iff]
          intro q hq hqμ
          rw [Set.Finite.mem_toFinset] at hq
          exact hq.2 (hqμ ▸ ht)
        rw [this]; simpa using hcR0
      · refine le_trans ?_ (hc' μ hμ ht)
        have hIfin : ({I | IsSt (tanPart μ) I} : Set (ℤ → Finset (Fin K))).Finite := by
          refine (hfin.image Prod.snd).subset ?_
          intro I hI
          exact ⟨(μ, I), ⟨hμ, hI⟩, rfl⟩
        rw [Set.ncard_eq_toFinset_card _ hIfin]
        have : (hBfin.toFinset.filter fun q => q.1 = μ).card ≤ hIfin.toFinset.card := by
          refine Finset.card_le_card_of_injOn Prod.snd ?_ ?_
          · intro q hq
            simp only [Finset.coe_filter, Set.mem_setOf_eq, Set.Finite.mem_toFinset] at hq
            simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
            have := hq.1.1.2
            rwa [hq.2] at this
          · intro q hq q' hq' hqq
            simp only [Finset.coe_filter, Set.mem_setOf_eq] at hq hq'
            exact Prod.ext (hq.2.trans hq'.2.symm) hqq
        exact_mod_cast this
    have hsum : (hBfin.toFinset.card : ℝ) =
        ∑ μ ∈ hPfin.toFinset, ((hBfin.toFinset.filter fun q => q.1 = μ).card : ℝ) := by
      have := Finset.card_eq_sum_card_fiberwise (f := Prod.fst) (s := hBfin.toFinset) (t := hPfin.toFinset)
        (fun q hq => hmaps q hq)
      rw [this]; push_cast; rfl
    rw [hsum]
    calc ∑ μ ∈ hPfin.toFinset, ((hBfin.toFinset.filter fun q => q.1 = μ).card : ℝ)
        ≤ ∑ _μ ∈ hPfin.toFinset, cR := Finset.sum_le_sum hfib
      _ = (hPfin.toFinset.card : ℝ) * cR := by rw [Finset.sum_const, nsmul_eq_mul]

  have hk0 : (0 : ℝ) < ((r + K : ℕ) : ℝ) := by
    have : 0 < r + K := by have := H.r1; omega
    exact_mod_cast this
  have hmin : min La ((r + K : ℕ) : ℝ) / 32 ≤
      min (La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ))) (((K : ℝ) - 2 * N) / 12) := by
    have hH4 := H.H4
    refine le_min ?_ ?_
    · have h3 : La / 32 ≤ La * ((K : ℝ) - 2 * N) / (16 * ((r + K : ℕ) : ℝ)) := by
        rw [div_le_div_iff₀ (by norm_num) (by positivity)]
        have := mul_le_mul_of_nonneg_left hH4 H.La_pos.le
        nlinarith
      exact le_trans (div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)) h3
    · have h3 : ((r + K : ℕ) : ℝ) / 32 ≤ ((K : ℝ) - 2 * N) / 12 := by linarith
      exact le_trans (div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)) h3
  have hrk0 : (0 : ℝ) ≤ (rkA r K n0 B : ℝ) := Nat.cast_nonneg _
  have h3 : (SB.ncard : ℝ) ≤
      Real.exp (11 * (N : ℝ) ^ 2 * ell0 N a - min La ((r + K : ℕ) : ℝ) / 32) * (rkA r K n0 B : ℝ) := by
    refine le_trans h2 (le_trans (mul_le_mul_of_nonneg_right hPcard hcR0) ?_)
    rw [hcR, ← mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) hrk0
    linarith
  have h1' : (rkA r K n0 B : ℝ) ≤ (SG.ncard : ℝ) + (SB.ncard : ℝ) := by
    rw [← hcard]; exact_mod_cast h1
  linarith

end

section
open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas
open Formalism.InvariantFactorPaths

theorem filter_ge_get_eq_take : ∀ (L : List ℕ), L.Pairwise (· > ·) → ∀ (e : ℕ) (he : e < L.length),
    L.filter (fun y => decide (L[e] ≤ y)) = L.take (e + 1) := by
  intro L
  induction L with
  | nil => intro _ e he; simp at he
  | cons x xs ih =>
    intro hp e he
    rw [List.pairwise_cons] at hp
    cases e with
    | zero =>
      simp only [List.getElem_cons_zero, List.take_succ_cons, List.take_zero]
      rw [List.filter_cons_of_pos (by simp)]
      congr 1
      rw [List.filter_eq_nil_iff]
      intro y hy
      have h1 := hp.1 y hy
      simp only [decide_eq_true_eq, not_le]
      omega
    | succ e =>
      simp only [List.getElem_cons_succ, List.take_succ_cons]
      have hlt : xs[e]'(by simp at he; omega) < x := hp.1 _ (List.getElem_mem _)
      rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; omega),
        ih hp.2 e (by simp at he; omega)]

def latestList (P : ℕ → Bool) (M : ℕ) : List ℕ := ((List.range' 1 M).filter P).reverse

theorem mem_latest_list (P : ℕ → Bool) (M y : ℕ) : y ∈ latestList P M ↔ (1 ≤ y ∧ y ≤ M) ∧ P y = true := by
  simp only [latestList, List.mem_reverse, List.mem_filter, List.mem_range'_1]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.1, by omega⟩, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1.1, by omega⟩, h2⟩

theorem latest_list_pairwise_gt (P : ℕ → Bool) (M : ℕ) : (latestList P M).Pairwise (· > ·) := by
  rw [latestList, List.pairwise_reverse]
  exact (List.pairwise_lt_range' (s := 1) (n := M)).filter _

theorem latest_list_nodup (P : ℕ → Bool) (M : ℕ) : (latestList P M).Nodup :=
  (latest_list_pairwise_gt P M).imp ne_of_gt

def countFrom (P : ℕ → Bool) (M x : ℕ) : ℕ := ((Finset.Icc 1 M).filter fun y => P y = true ∧ x ≤ y).card

theorem count_from_eq_filter_length (P : ℕ → Bool) (M x : ℕ) :
    countFrom P M x = ((latestList P M).filter fun y => decide (x ≤ y)).length := by
  unfold countFrom
  have hnd : ((latestList P M).filter fun y => decide (x ≤ y)).Nodup := (latest_list_nodup P M).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext y
  simp only [Finset.mem_filter, Finset.mem_Icc, List.mem_toFinset, List.mem_filter, mem_latest_list,
    decide_eq_true_eq]
  tauto

theorem latest_list_get_spec (P : ℕ → Bool) (M e : ℕ) (he : e < (latestList P M).length) :
    ((1 ≤ (latestList P M)[e] ∧ (latestList P M)[e] ≤ M) ∧ P (latestList P M)[e] = true) ∧
      countFrom P M (latestList P M)[e] = e + 1 := by
  refine ⟨(mem_latest_list P M _).1 (List.getElem_mem _), ?_⟩
  rw [count_from_eq_filter_length, filter_ge_get_eq_take _ (latest_list_pairwise_gt P M) e he, List.length_take]
  omega

theorem latest_list_get_of_count (P : ℕ → Bool) (M e x : ℕ) (hx : (1 ≤ x ∧ x ≤ M) ∧ P x = true) (hc : countFrom P M x = e + 1) :
    ∃ he : e < (latestList P M).length, (latestList P M)[e] = x := by
  obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.1 ((mem_latest_list P M x).2 hx)
  have h1 := (latest_list_get_spec P M i hi).2
  rw [hix, hc] at h1
  have hie : i = e := by omega
  subst hie
  exact ⟨hi, hix⟩

theorem latest_list_succ_lt (P : ℕ → Bool) (M e : ℕ) (he : e + 1 < (latestList P M).length) :
    (latestList P M)[e + 1] < (latestList P M)[e]'(by omega) := by
  exact List.pairwise_iff_getElem.1 (latest_list_pairwise_gt P M) e (e + 1) (by omega) he (by omega)

variable {N r K : ℕ}

def toL (r K : ℕ) (LL : Letters (Fin N)) (B : Fin N → ℕ) : BranchingDimensions.Letters where
  r := r
  K := K
  Ns := N
  vec := fun i => if h : 1 ≤ i ∧ i ≤ N then LL.vec ⟨i - 1, by omega⟩ else true
  B := fun i => if h : 1 ≤ i ∧ i ≤ N then B ⟨i - 1, by omega⟩ else 0

theorem toL_vec (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : ℕ) (h : 1 ≤ i ∧ i ≤ N) :
    (toL r K LL B).vec i = LL.vec ⟨i - 1, by omega⟩ := by
  simp only [toL]
  rw [dite_eq_left h]

theorem toL_B (LL : Letters (Fin N)) (B : Fin N → ℕ) (i : ℕ) (h : 1 ≤ i ∧ i ≤ N) :
    (toL r K LL B).B i = B ⟨i - 1, by omega⟩ := by
  simp only [toL]
  rw [dite_eq_left h]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem letters_n0_eq (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).n0 = n0 := by
  show N - r = n0
  have := H.hN
  omega

theorem toL_Wf [NeZero K] (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).Wf := by
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have hN := H.hN
  have h3 := H.two_r_le_n0
  refine ⟨H.r1, Nat.one_le_iff_ne_zero.2 (NeZero.ne K), ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_⟩
  · show 3 * r ≤ N
    omega
  · simp only [toL] at h2
    rw [toL_vec LL B i ⟨h1, by omega⟩]
    exact H.vec_true_of_early _ (by simp only; omega)
  · rw [hn0] at h1
    simp only [toL] at h2
    rw [toL_vec LL B i ⟨by omega, h2⟩]
    exact H.vec_true_of_late _ (by simp only; omega)

theorem latest_thresholds_decay (H : HypT N n0 r K LL B od bb a La p) (P : ℕ → Bool) (v : Bool)
    (hP : ∀ i (h : 1 ≤ i ∧ i ≤ N), P i = true → LL.vec ⟨i - 1, by omega⟩ = v) (l : ℕ)
    (hl : l + 1 < ((latestList P n0).map (toL r K LL B).B).length) :
    13 ^ 2 * ((latestList P n0).map (toL r K LL B).B).getD (l + 1) 0 ≤
      5 * ((latestList P n0).map (toL r K LL B).B).getD l 0 := by
  have hlen : l + 1 < (latestList P n0).length := by simpa using hl
  have e1 : ((latestList P n0).map (toL r K LL B).B).getD (l + 1) 0 =
      (toL r K LL B).B ((latestList P n0)[l + 1]) := by
    simp [List.getD_eq_getElem?_getD, hlen]
  have e2 : ((latestList P n0).map (toL r K LL B).B).getD l 0 =
      (toL r K LL B).B ((latestList P n0)[l]'(by omega)) := by
    simp [List.getD_eq_getElem?_getD, show l < (latestList P n0).length by omega]
  rw [e1, e2]
  have hxy := latest_list_succ_lt P n0 l hlen
  have hxs := (latest_list_get_spec P n0 (l + 1) hlen).1
  have hys := (latest_list_get_spec P n0 l (by omega)).1
  generalize (latestList P n0)[l + 1] = x at hxy hxs ⊢
  generalize (latestList P n0)[l]'(by omega) = y at hxy hys ⊢
  have hN := H.hN
  rw [toL_B LL B x ⟨hxs.1.1, by omega⟩, toL_B LL B y ⟨hys.1.1, by omega⟩]
  have hv : LL.vec ⟨x - 1, by omega⟩ = LL.vec ⟨y - 1, by omega⟩ := by
    rw [hP x ⟨hxs.1.1, by omega⟩ hxs.2, hP y ⟨hys.1.1, by omega⟩ hys.2]
  have h2 := H.H2 ⟨x - 1, by omega⟩ ⟨y - 1, by omega⟩
    (by rw [Fin.lt_iff_val_lt_val]; simp only; omega) (by simp only; omega) hv
  have hp13 : (13 : ℝ) ≤ p := by exact_mod_cast H.p13
  have hB0 : (0 : ℝ) ≤ (B ⟨x - 1, by omega⟩ : ℝ) := Nat.cast_nonneg _
  have h3 : ((13 ^ 2 * B ⟨x - 1, by omega⟩ : ℕ) : ℝ) ≤ ((5 * B ⟨y - 1, by omega⟩ : ℕ) : ℝ) := by
    push_cast
    have hp2 : (169 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have h8 := mul_le_mul_of_nonneg_right hp2 hB0
    linarith
  exact_mod_cast h3

theorem toL_Hyp [NeZero K] (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).Hyp a 13 := by
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have hN := H.hN
  have h3n := H.two_r_le_n0
  have h3K := H.N_add_r_le_K
  have h4 := H.H4
  have h4a := H.N_le_a
  have eV : (toL r K LL B).latestV (toL r K LL B).n0 =
      (latestList (fun l => (toL r K LL B).vec l) n0).map (toL r K LL B).B := by
    simp only [BranchingDimensions.Letters.latestV, latestList, hn0, min_self]
  have eC : (toL r K LL B).latestC (toL r K LL B).n0 =
      (latestList (fun l => !(toL r K LL B).vec l) n0).map (toL r K LL B).B := by
    simp only [BranchingDimensions.Letters.latestC, latestList, hn0, min_self]
  refine ⟨H.a3, by norm_num, le_rfl, fun i h1 h2 => ?_, fun l hl => ?_, fun l hl => ?_,
    fun i h1 h2 => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hn0] at h2
    rw [toL_B LL B i ⟨h1, by omega⟩]
    have h5 := H.H1 ⟨i - 1, by omega⟩ (by simp only; omega)
    refine ⟨?_, h5.2⟩
    show r + K ≤ B ⟨i - 1, by omega⟩
    exact_mod_cast h5.1
  · rw [eV] at hl ⊢
    exact latest_thresholds_decay H _ true (fun i hi hPi => by rw [← toL_vec LL B i hi]; exact hPi) l hl
  · rw [eC] at hl ⊢
    exact latest_thresholds_decay H _ false (fun i hi hPi => by
      rw [← toL_vec LL B i hi]
      simpa using hPi) l hl
  · rw [hn0] at h1 h2
    simp only [toL] at h1
    rw [toL_vec LL B i ⟨by omega, by omega⟩]
    exact H.vec_true_of_late _ (by simp only; omega)
  · show N + r ≤ K
    omega
  · show 2 * r ≤ N
    omega
  · show r + K ≤ 2 * (K - 2 * N)
    have hK : 2 * N ≤ K := by
      have h6 : (2 * N : ℝ) ≤ K := by
        have : (0 : ℝ) ≤ ((r + K : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
      exact_mod_cast h6
    have h7 : ((r + K : ℕ) : ℝ) ≤ ((2 * (K - 2 * N) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub hK]
      push_cast at h4 ⊢
      linarith
    exact_mod_cast h7
  · show (N : ℝ) ≤ a
    exact h4a

def toB (bb : Fin N → ℝ) (p : ℕ) : ℕ → ℝ := fun i =>
  if h : 1 ≤ i ∧ i ≤ N then 13 * bb ⟨i - 1, by omega⟩ / (p : ℝ) else 1

theorem toL_TData (H : HypT N n0 r K LL B od bb a La p) : (toL r K LL B).TData 13 La (toB bb p) := by
  have hN := H.hN
  have hp : (0 : ℝ) < p := by
    have := H.p13
    exact_mod_cast (by omega : 0 < p)
  refine ⟨H.La_pos, fun i h1 h2 => ?_⟩
  simp only [toL] at h1 h2
  have hi : 1 ≤ i ∧ i ≤ N := ⟨by omega, h2⟩
  have hb : toB bb p i = 13 * bb ⟨i - 1, by omega⟩ / (p : ℝ) := by
    simp only [toB]
    rw [dite_eq_left hi]
  refine ⟨?_, fun l hl1 hl2 hl3 => ?_⟩
  · rw [hb]
    have := H.bb_pos ⟨i - 1, by omega⟩ (by simp only; omega)
    positivity
  · rw [letters_n0_eq H] at hl3
    rw [toL_B LL B l ⟨hl1, by omega⟩, hb]
    have h5 := H.bb_le ⟨i - 1, by omega⟩ ⟨l - 1, by omega⟩ (by simp only; omega)
      (by rw [Fin.lt_iff_val_lt_val]; simp only; omega) (by simp only; omega)
    refine le_trans h5 (le_of_eq ?_)
    push_cast
    ring

end
end

section
open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem sum_shift_le : ∀ (K : ℕ) [NeZero K] (f g : Fin K → ℤ), (∀ c, 0 ≤ g c) →
    (∀ (c : Fin K) (h : c.val + 1 < K), f ⟨c.val + 1, h⟩ ≤ g c) → ∑ c, f c ≤ f 0 + ∑ c, g c := by
  intro K
  cases K with
  | zero => intro h; exact absurd rfl (NeZero.ne (0 : ℕ))
  | succ K =>
    intro _ f g hg hfg
    rw [Fin.sum_univ_succ f, Fin.sum_univ_castSucc g]
    have h1 : ∑ c : Fin K, f c.succ ≤ ∑ c : Fin K, g c.castSucc :=
      Finset.sum_le_sum fun c _ => hfg c.castSucc (by simp)
    have h2 := hg (Fin.last K)
    linarith

theorem int_pos_neg (x : ℤ) : x = max x 0 - max (-x) 0 := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

variable {N r K : ℕ}

theorem posS_split (la : Fin (r + K) → ℤ) :
    posS la = ∑ c : Fin r, max (la (Fin.castAdd K c)) 0 + ∑ c : Fin K, max (la (Fin.natAdd r c)) 0 := by
  unfold posS; rw [Fin.sum_univ_add]

theorem negS_split (la : Fin (r + K) → ℤ) :
    negS la = ∑ c : Fin r, max (-la (Fin.castAdd K c)) 0 + ∑ c : Fin K, max (-la (Fin.natAdd r c)) 0 := by
  unfold negS; rw [Fin.sum_univ_add]

theorem dplus_le_geom {LL : Letters (Fin N)} {B : Fin N → ℕ} {n0 p : ℕ} (hp : 13 ≤ p)
    (H2 : ∀ i i' : Fin N, i < i' → i'.val < n0 → LL.vec i = LL.vec i' → (p : ℝ) ^ 2 / 5 * (B i : ℝ) ≤ (B i' : ℝ)) :
    ∀ (m : ℕ) (l : Fin N), LL.vec l = true → m ≤ l.val → l.val < n0 →
      (dplus LL B m : ℝ) ≤ 10 / (p : ℝ) ^ 2 * (B l : ℝ) := by
  have hp' : (13 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp2 : (169 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  intro m
  induction m with
  | zero =>
    intro l _ _ _
    have : dplus LL B 0 = 0 := by unfold dplus; simp
    rw [this]; push_cast; positivity
  | succ m ih =>
    intro l hl hml hln
    have hmN : m < N := by have := l.2; omega
    have hd : dplus LL B (m + 1) = dplus LL B m + if LL.vec ⟨m, hmN⟩ = true then B ⟨m, hmN⟩ else 0 :=
      dsum_succ (fun l => LL.vec l = true) B m hmN
    rw [hd]
    by_cases hv : LL.vec ⟨m, hmN⟩ = true
    · rw [ite_eq_left hv]
      have h1 := ih ⟨m, hmN⟩ hv le_rfl (by simp only; omega)
      have h2 := H2 ⟨m, hmN⟩ l (by rw [Fin.lt_def]; simp only; omega) hln (by rw [hv, hl])
      push_cast
      have hB : (0 : ℝ) ≤ (B ⟨m, hmN⟩ : ℝ) := Nat.cast_nonneg _
      have h3 : (B ⟨m, hmN⟩ : ℝ) ≤ 5 / (p : ℝ) ^ 2 * (B l : ℝ) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have : (p : ℝ) ^ 2 / 5 * (B ⟨m, hmN⟩ : ℝ) = (B ⟨m, hmN⟩ : ℝ) * (p : ℝ) ^ 2 / 5 := by ring
        rw [this, div_le_iff₀ (by norm_num)] at h2
        linarith
      have h4 : 10 / (p : ℝ) ^ 2 ≤ 10 / 169 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp2
      have h5 : 10 / (p : ℝ) ^ 2 * (B ⟨m, hmN⟩ : ℝ) ≤ 10 / 169 * (B ⟨m, hmN⟩ : ℝ) :=
        mul_le_mul_of_nonneg_right h4 hB
      have h6 : 10 / (p : ℝ) ^ 2 * (B l : ℝ) = 2 * (5 / (p : ℝ) ^ 2 * (B l : ℝ)) := by ring
      rw [h6]
      linarith
    · rw [ite_eq_right hv]
      simpa using ih l hl (by omega) hln

theorem oldest_lt_n0 {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}
    (H : HypT N n0 r K LL B od bb a La p) (i : Fin N) (hi : r ≤ i.val) : (od i).val < n0 := by
  by_contra hcon
  have h1 := H.od_card i hi
  have h2 : (Finset.univ.filter fun l : Fin N => od i ≤ l ∧ l < i ∧ LL.vec l = true).card ≤
      (Finset.Ico (od i) i).card := by
    refine Finset.card_le_card ?_
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    exact Finset.mem_Ico.mpr ⟨hl.1, hl.2.1⟩
  rw [Fin.card_Ico] at h2
  have := i.2
  have := H.hN
  omega

theorem vcount_od {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}
    (H : HypT N n0 r K LL B od bb a La p) (i : Fin N) (hi : r ≤ i.val) :
    vcount LL ((od i).val + 1) i.val + 1 = r := by
  classical
  have h1 := H.od_card i hi
  have h2 : (Finset.univ.filter fun l : Fin N => od i ≤ l ∧ l < i ∧ LL.vec l = true) =
      insert (od i) (Finset.univ.filter fun l : Fin N => (od i).val + 1 ≤ l.val ∧ l.val < i.val ∧ LL.vec l = true) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2, h3⟩
      by_cases hl : l = od i
      · exact Or.inl hl
      · refine Or.inr ⟨?_, h2, h3⟩
        have : (od i).val ≠ l.val := fun h => hl (Fin.ext h.symm)
        omega
    · rintro (rfl | ⟨h1, h2, h3⟩)
      · exact ⟨le_rfl, H.od_lt i hi, H.od_vec i hi⟩
      · exact ⟨by rw [Fin.le_def]; omega, h2, h3⟩
  rw [h2, Finset.card_insert_of_notMem (by simp)] at h1
  exact h1

theorem nu_last_le [NeZero r] {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ}
    {a La : ℝ} {p : ℕ} (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hdd : ∀ i : Fin N, i.val < n0 → dd i = B i) (i : Fin N) (hi : r ≤ i.val) :
    ((plPart P.mu i.castSucc (lastIdx r) : ℤ) : ℝ) ≤ 2 * (B (od i) : ℝ) := by
  have hr := H.r1
  have hod := oldest_lt_n0 H i hi
  have hvc := vcount_od H i hi
  have hlt : (od i).val < i.val := H.od_lt i hi
  have h1 := row_back P ((od i).val + 1) i.val (by omega) (by have := i.2; omega) ⟨0, by omega⟩
    (Fin.castAdd K (lastIdx r)) (by simp [lastIdx]; omega)
  have h2 := mu_le_dplus P ((od i).val + 1) (by have := i.2; omega) ⟨0, by omega⟩
  have h3 : dplus LL dd ((od i).val + 1) = dplus LL B ((od i).val + 1) := by
    unfold dplus
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hl : l.val < (od i).val + 1 ∧ LL.vec l = true
    · rw [ite_eq_left hl, ite_eq_left hl, hdd l (by omega)]
    · rw [ite_eq_right hl, ite_eq_right hl]
  have h4 : dplus LL B ((od i).val + 1) = dplus LL B (od i).val + B (od i) := by
    have := dsum_succ (fun l => LL.vec l = true) B (od i).val (od i).2
    rw [ite_eq_left (H.od_vec i hi)] at this
    exact this
  have h5 := dplus_le_geom H.p13 H.H2 (od i).val (od i) (H.od_vec i hi) le_rfl hod
  have hp' : (13 : ℝ) ≤ (p : ℝ) := by exact_mod_cast H.p13
  have hp2 : (169 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
  have h6 : 10 / (p : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hB : (0 : ℝ) ≤ (B (od i) : ℝ) := Nat.cast_nonneg _
  have h7 : (plPart P.mu i.castSucc (lastIdx r) : ℤ) ≤ (dplus LL dd ((od i).val + 1) : ℤ) := le_trans h1 h2
  have h8 : ((plPart P.mu i.castSucc (lastIdx r) : ℤ) : ℝ) ≤ ((dplus LL dd ((od i).val + 1) : ℕ) : ℝ) := by
    exact_mod_cast h7
  rw [h3, h4] at h8
  push_cast at h8
  have h9 : 10 / (p : ℝ) ^ 2 * (B (od i) : ℝ) ≤ 1 * (B (od i) : ℝ) := mul_le_mul_of_nonneg_right h6 hB
  linarith

theorem typical_path_orders_small : TypicalPathOrdersSmall := by
  intro N n0 r K _ _ LL B od bb a La p H μ hμ hTyp i hi
  obtain ⟨dd, hP⟩ := hμ
  obtain ⟨P, rfl⟩ := hP.path
  have hr := H.r1
  have hK := H.N_add_r_le_K
  have F1 : ∀ (s : Fin (N + 1)) (m : Fin (r + K)), m.val ≤ r → 0 ≤ P.mu s m := by
    intro s m hm
    exact mu_nonneg P s.val s.2 m (by have := s.2; omega)
  obtain ⟨hT1, hT2, hT3⟩ := hTyp i
  refine ⟨hT3 hi, ?_, ?_⟩
  · intro hv
    have hstep := step_vec P i hv
    have hX := hT2 hv hi

    have hneg : ∀ s : Fin (N + 1), negS (P.mu s) = ∑ c : Fin K, max (-tanPart P.mu s c) 0 := by
      intro s
      rw [negS_split]
      have : ∑ c : Fin r, max (-P.mu s (Fin.castAdd K c)) 0 = 0 := by
        refine Finset.sum_eq_zero fun c _ => ?_
        have := F1 s (Fin.castAdd K c) (by simp)
        exact max_eq_right (by linarith)
      rw [this, zero_add]; rfl
    have hshift : ∑ c : Fin K, max (tanPart P.mu i.succ c) 0 ≤
        max (tanPart P.mu i.succ 0) 0 + ∑ c : Fin K, max (tanPart P.mu i.castSucc c) 0 := by
      refine sum_shift_le K (fun c => max (tanPart P.mu i.succ c) 0) (fun c => max (tanPart P.mu i.castSucc c) 0)
        (fun c => le_max_right _ _) ?_
      intro c h
      refine max_le_max ?_ le_rfl
      have := hstep.2.1 (Fin.natAdd r c) (by simp; omega)
      exact this
    have hfirst : tanPart P.mu i.succ 0 ≤ plPart P.mu i.castSucc (lastIdx r) := by
      have := hstep.2.1 (Fin.castAdd K (lastIdx r)) (by simp [lastIdx]; omega)
      have he : (⟨(Fin.castAdd K (lastIdx r)).val + 1, by simp [lastIdx]; omega⟩ : Fin (r + K)) =
          Fin.natAdd r (0 : Fin K) := by
        apply Fin.ext; simp [lastIdx]; omega
      rw [he] at this
      exact this
    have hnn : 0 ≤ plPart P.mu i.castSucc (lastIdx r) := F1 _ _ (by simp [lastIdx])
    have hsum : ∑ c, (tanPart P.mu i.succ c - tanPart P.mu i.castSucc c) =
        (∑ c : Fin K, max (tanPart P.mu i.succ c) 0 - ∑ c : Fin K, max (tanPart P.mu i.castSucc c) 0) +
        (negS (P.mu i.castSucc) - negS (P.mu i.succ)) := by
      rw [hneg, hneg, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h1 := int_pos_neg (tanPart P.mu i.succ c)
      have h2 := int_pos_neg (tanPart P.mu i.castSucc c)
      linarith
    have hle : ∑ c, (tanPart P.mu i.succ c - tanPart P.mu i.castSucc c) ≤
        plPart P.mu i.castSucc (lastIdx r) + (negS (P.mu i.castSucc) - negS (P.mu i.succ)) := by
      rw [hsum]
      have : max (tanPart P.mu i.succ 0) 0 ≤ plPart P.mu i.castSucc (lastIdx r) := max_le hfirst hnn
      linarith
    have hle' : ((∑ c, (tanPart P.mu i.succ c - tanPart P.mu i.castSucc c) : ℤ) : ℝ) ≤
        ((plPart P.mu i.castSucc (lastIdx r) : ℤ) : ℝ) + ((negS (P.mu i.castSucc) - negS (P.mu i.succ) : ℤ) : ℝ) := by
      exact_mod_cast hle
    have hnu := nu_last_le H P hP.degs i hi
    linarith
  · intro hv
    have hstep := step_cov P i hv
    have hX := hT1 hv
    have hpos : ∀ s : Fin (N + 1), posS (P.mu s) = ∑ c : Fin r, plPart P.mu s c +
        ∑ c : Fin K, max (tanPart P.mu s c) 0 := by
      intro s
      rw [posS_split]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      exact max_eq_left (F1 s (Fin.castAdd K c) (by simp))
    have hmono : ∑ c : Fin K, max (tanPart P.mu i.succ c) 0 ≤ ∑ c : Fin K, max (tanPart P.mu i.castSucc c) 0 :=
      Finset.sum_le_sum fun c _ => max_le_max (hstep.1 (Fin.natAdd r c)) le_rfl
    have hle : ∑ c, (plPart P.mu i.castSucc c - plPart P.mu i.succ c) ≤
        posS (P.mu i.castSucc) - posS (P.mu i.succ) := by
      rw [hpos, hpos, Finset.sum_sub_distrib]
      linarith
    have hle' : ((∑ c, (plPart P.mu i.castSucc c - plPart P.mu i.succ c) : ℤ) : ℝ) ≤
        ((posS (P.mu i.castSucc) - posS (P.mu i.succ) : ℤ) : ℝ) := by exact_mod_cast hle
    linarith
end

section
open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem two_N_lt_K (H : HypT N n0 r K LL B od bb a La p) : 2 * N < K := by
  have h := H.H4
  have hr := H.r1
  have hk : (0 : ℝ) < ((r + K : ℕ) : ℝ) := by
    have : 0 < r + K := by omega
    exact_mod_cast this
  have : (2 * N : ℝ) < (K : ℝ) := by linarith
  exact_mod_cast this

theorem dplus_le_beA (_H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ}
    (hdd : ∀ i : Fin N, i.val < n0 → dd i = B i) (s : ℕ) (hs : s ≤ n0) : dplus LL dd s ≤ beA n0 B := by
  unfold dplus beA
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : l.val < s ∧ LL.vec l = true
  · rw [ite_eq_left hl, ite_eq_left (by omega), hdd l (by omega)]
  · rw [ite_eq_right hl]; exact Nat.zero_le _

theorem dminus_le_beA (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ}
    (hdd : ∀ i : Fin N, i.val < n0 → dd i = B i) (s : ℕ) : dminus LL dd s ≤ beA n0 B := by
  unfold dminus beA
  refine Finset.sum_le_sum fun l _ => ?_
  by_cases hl : l.val < s ∧ LL.vec l = false
  · have hln : l.val < n0 := by
      by_contra hcon
      have := H.vec_true_of_late l (by omega)
      rw [hl.2] at this
      exact absurd this (by simp)
    rw [ite_eq_left hl, ite_eq_left hln, hdd l hln]
  · rw [ite_eq_right hl]; exact Nat.zero_le _

theorem path_le_beA (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hP : IsPATHa LL n0 B P.mu dd) :
    ∀ (s : ℕ) (hs : s < N + 1) (m : Fin (r + K)), P.mu ⟨s, hs⟩ m ≤ (beA n0 B : ℤ) := by
  intro s
  induction s with
  | zero =>
    intro hs m
    have h0 : (⟨0, hs⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, P.zero]; simp
  | succ s ih =>
    intro hs m
    by_cases hsn : s + 1 ≤ n0
    · refine le_trans (mu_le_dplus P (s + 1) hs m) ?_
      exact_mod_cast dplus_le_beA H hP.degs (s + 1) hsn
    · have hsN : s < N := by omega
      have hv : LL.vec ⟨s, hsN⟩ = true := H.vec_true_of_late ⟨s, hsN⟩ (by simp only; omega)
      by_cases hm : m.val = 0
      · have := hP.head ⟨s, hsN⟩ m (by simp only; omega) (by omega)
        exact le_of_eq this
      · have h := step_vec P ⟨s, hsN⟩ hv
        have hm1 : (m.val - 1) + 1 < r + K := by have := m.2; omega
        have h2 := h.2.1 ⟨m.val - 1, by have := m.2; omega⟩ hm1
        have hme : (⟨(m.val - 1) + 1, hm1⟩ : Fin (r + K)) = m := Fin.ext (by simp only; omega)
        rw [hme] at h2
        exact le_trans h2 (ih (by omega) _)

theorem beA_le (H : HypT N n0 r K LL B od bb a La p) : (beA n0 B : ℝ) ≤ 2 * a * (N : ℝ) := by
  unfold beA
  push_cast
  have ha : (0 : ℝ) ≤ 2 * a := by have := H.a3; linarith
  calc ∑ i : Fin N, (if i.val < n0 then (B i : ℝ) else 0) ≤ ∑ _i : Fin N, 2 * a := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases hi : i.val < n0
        · rw [ite_eq_left hi]; exact (H.H1 i hi).2
        · rw [ite_eq_right hi]; exact ha
    _ = 2 * a * (N : ℝ) := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end

def code (N r K : ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Fin N × Fin (2 * N) → ℕ := fun v =>
  if h : v.2.val < N ∧ v.2.val < r + K then (μ v.1.succ ⟨v.2.val, h.2⟩).toNat
  else if h' : r + K - 2 * N + v.2.val < r + K then (-μ v.1.succ ⟨r + K - 2 * N + v.2.val, h'⟩).toNat else 0

theorem path_count_finite : PathCountFinite := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  have hK := two_N_lt_K H
  set M := beA n0 B with hM
  let t : Finset (Fin N × Fin (2 * N) → ℕ) := Fintype.piFinset fun _ => Finset.range (M + 1)
  have hshape : ∀ μ ∈ SP (r := r) (K := K) LL n0 B, ∀ (s : Fin (N + 1)) (m : Fin (r + K)),
      (m.val + N < r + K → 0 ≤ μ s m) ∧ (N ≤ m.val → μ s m ≤ 0) ∧ μ s m ≤ (M : ℤ) ∧ -(M : ℤ) ≤ μ s m := by
    rintro μ ⟨dd, hP⟩ s m
    obtain ⟨P, rfl⟩ := hP.path
    refine ⟨fun h => mu_nonneg P s.val s.2 m (by have := s.2; omega),
      fun h => mu_nonpos P s.val s.2 m (by have := s.2; omega), path_le_beA H P hP s.val s.2 m, ?_⟩
    refine le_trans ?_ (neg_dminus_le_mu P s.val s.2 m)
    have := dminus_le_beA H hP.degs s.val
    linarith
  have hmaps : ∀ μ ∈ SP (r := r) (K := K) LL n0 B, code N r K μ ∈ (t : Set (Fin N × Fin (2 * N) → ℕ)) := by
    intro μ hμ
    simp only [t, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range]
    intro v
    unfold code
    split_ifs with h h'
    · have := (hshape μ hμ v.1.succ ⟨v.2.val, h.2⟩).2.2.1
      omega
    · have := (hshape μ hμ v.1.succ ⟨r + K - 2 * N + v.2.val, h'⟩).2.2.2
      omega
    · omega
  have hinj : Set.InjOn (code N r K) (SP (r := r) (K := K) LL n0 B) := by
    intro μ hμ μ' hμ' hc
    funext s m
    induction s using Fin.cases with
    | zero =>
      obtain ⟨dd, hP⟩ := hμ
      obtain ⟨dd', hP'⟩ := hμ'
      obtain ⟨P, rfl⟩ := hP.path
      obtain ⟨P', rfl⟩ := hP'.path
      rw [P.zero, P'.zero]
    | succ i =>
      have h1 := hshape μ hμ i.succ m
      have h2 := hshape μ' hμ' i.succ m
      by_cases hm : m.val < N
      · have hcv := congrFun hc (i, ⟨m.val, by omega⟩)
        unfold code at hcv
        rw [dite_eq_left ⟨hm, m.2⟩, dite_eq_left ⟨hm, m.2⟩] at hcv
        have e1 := h1.1 (by omega)
        have e2 := h2.1 (by omega)
        have hcv' : (μ i.succ m).toNat = (μ' i.succ m).toNat := hcv
        omega
      · by_cases hm2 : m.val + N < r + K
        · have e1 := h1.1 hm2
          have e2 := h2.1 hm2
          have e3 := h1.2.1 (by omega)
          have e4 := h2.2.1 (by omega)
          omega
        · have hidx : m.val - (r + K - 2 * N) < 2 * N := by have := m.2; omega
          have hcv := congrFun hc (i, ⟨m.val - (r + K - 2 * N), hidx⟩)
          unfold code at hcv
          have hn1 : ¬ ((m.val - (r + K - 2 * N)) < N ∧ (m.val - (r + K - 2 * N)) < r + K) := by omega
          have hn2 : r + K - 2 * N + (m.val - (r + K - 2 * N)) < r + K := by have := m.2; omega
          rw [dite_eq_right hn1, dite_eq_right hn1, dite_eq_left hn2, dite_eq_left hn2] at hcv
          have hme : (⟨r + K - 2 * N + (m.val - (r + K - 2 * N)), hn2⟩ : Fin (r + K)) = m :=
            Fin.ext (by simp only; omega)
          rw [hme] at hcv
          have hcv' : (-μ i.succ m).toNat = (-μ' i.succ m).toNat := hcv
          have e3 := h1.2.1 (by omega)
          have e4 := h2.2.1 (by omega)
          omega
  have hfin : (SP (r := r) (K := K) LL n0 B).Finite :=
    Set.Finite.of_injOn (fun μ hμ => hmaps μ hμ) hinj t.finite_toSet
  refine ⟨hfin, ?_⟩
  have hle := Set.ncard_le_ncard_of_injOn (code N r K) hmaps hinj t.finite_toSet
  rw [Set.ncard_coe_finset] at hle
  have hcard : t.card = (M + 1) ^ (N * (2 * N)) := by
    simp [t, Fintype.card_piFinset]
  rw [hcard] at hle
  have hA : (0 : ℝ) < 1 + 2 * a * (N : ℝ) := by
    have := H.a3
    nlinarith
  have hM1 : ((M + 1 : ℕ) : ℝ) ≤ 1 + 2 * a * (N : ℝ) := by
    have := beA_le H
    push_cast
    linarith
  calc ((SP (r := r) (K := K) LL n0 B).ncard : ℝ) ≤ (((M + 1) ^ (N * (2 * N)) : ℕ) : ℝ) := by exact_mod_cast hle
    _ = ((M + 1 : ℕ) : ℝ) ^ (N * (2 * N)) := by push_cast; rfl
    _ ≤ (1 + 2 * a * (N : ℝ)) ^ (N * (2 * N)) := pow_le_pow_left₀ (Nat.cast_nonneg _) hM1 _
    _ = Real.exp (2 * (N : ℝ) ^ 2 * ell0 N a) := by
        unfold ell0
        rw [← Real.exp_log hA, ← Real.exp_nat_mul, Real.log_exp]
        congr 1
        push_cast
        ring
end

section
open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem finite_St {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) : ({I | IsSt mu I} : Set (ℤ → Finset (Fin n))).Finite := by
  classical
  refine Set.Finite.of_injOn (f := fun I (c : colRange mu) => I c.1) (t := Set.univ) (fun _ _ => Set.mem_univ _) ?_
    Set.finite_univ
  intro I hI I' hI' h
  funext c
  by_cases hc : c ∈ colRange mu
  · exact congrFun h ⟨c, hc⟩
  · rw [hI.1 c hc, hI'.1 c hc]

theorem wt_eq (D : Formalism.BasicNotions.D7) (h3 : admB3 D) {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (hd : Dominant (pEnd mu)) :
    ({I | IsSt mu I} : Set (ℤ → Finset (Fin n))).ncard = stCount n (pEnd mu) := by
  have h1 := h3 n N mu hd
  have h2 := h3 n 0 (fun _ => pEnd mu) hd
  have h4 : ((Nat.card {I : ℤ → Finset (Fin n) // IsSt mu I} : ℕ) : ℚ) = ((stCount n (pEnd mu) : ℕ) : ℚ) := by
    rw [h1]; unfold stCount; rw [h2]; rfl
  rw [← Nat.card_coe_set_eq]
  exact_mod_cast h4

theorem stCount_zero (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (n : ℕ) : stCount n (0 : Fin n → ℤ) = 1 := by
  have h2 := h3 n 0 (fun _ => (0 : Fin n → ℤ)) (fun _ _ _ => le_rfl)
  have h4 : ((stCount n (0 : Fin n → ℤ) : ℕ) : ℚ) = 1 := by
    unfold stCount
    rw [h2]
    refine Finset.prod_eq_one fun i _ => Finset.prod_eq_one fun j _ => ?_
    split_ifs with hij
    · have : ((j : ℕ) : ℚ) - ((i : ℕ) : ℚ) ≠ 0 := by
        have h5 : ((i : ℕ) : ℚ) < ((j : ℕ) : ℚ) := by exact_mod_cast hij
        linarith
      simp only [pEnd, Pi.zero_apply, Int.cast_zero, sub_zero, zero_add]
      exact div_self this
    · rfl
  exact_mod_cast h4

theorem stCount_cast {n n' : ℕ} (h : n = n') (la : Fin n' → ℤ) :
    stCount n (fun l => la (Fin.cast h l)) = stCount n' la := by
  subst h; rfl

open Classical in
theorem pieri_vec (D : Formalism.BasicNotions.D7) (h5 : GenericProjectionCriterion D) (n : ℕ) (hn : 0 < n) (ν : Fin n → ℤ) (b : ℕ) (hd : Dominant ν) :
    stCount n ν * Nat.choose (b + n - 1) (n - 1) =
      ∑ μ ∈ (Fintype.piFinset fun i : Fin n => Finset.Icc (ν i) (ν i + b)).filter (fun μ => HStrip ν μ b),
        stCount n μ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (h5 m ν b hd).1

open Classical in
theorem pieri_cov (D : Formalism.BasicNotions.D7) (h5 : GenericProjectionCriterion D) (n : ℕ) (hn : 0 < n) (ν : Fin n → ℤ) (b : ℕ) (hd : Dominant ν) :
    stCount n ν * Nat.choose (b + n - 1) (n - 1) =
      ∑ μ ∈ (Fintype.piFinset fun i : Fin n => Finset.Icc (ν i - b) (ν i)).filter (fun μ => HStrip μ ν b),
        stCount n μ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact (h5 m ν b hd).2

variable {N r K : ℕ}

def StepOK (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (i : Fin N) (la la' : Fin (r + K) → ℤ) : Prop :=
  (i.val < n0 → if LL.vec i then HStrip la la' (B i) else HStrip la' la (B i)) ∧
  (n0 ≤ i.val → (∃ d : ℕ, HStrip la la' d) ∧ ∀ m : Fin (r + K), m.val ≤ i.val - n0 → la' m = (beA n0 B : ℤ))

def VP (LL : Letters (Fin N)) (n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) : Prop :=
  μ 0 = 0 ∧ (∀ t : Fin (N + 1), t.val ≤ s → Dominant (μ t)) ∧
    ∀ i : Fin N, i.val < s → StepOK LL n0 B i (μ i.castSucc) (μ i.succ)

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem sp_iff (H : HypT N n0 r K LL B od bb a La p) (μ : Fin (N + 1) → Fin (r + K) → ℤ) :
    μ ∈ SP (r := r) (K := K) LL n0 B ↔ VP LL n0 B N μ := by
  classical
  constructor
  · rintro ⟨dd, hP⟩
    obtain ⟨P, rfl⟩ := hP.path
    refine ⟨P.zero, fun t _ => P.dom t, fun i _ => ⟨fun hi => ?_, fun hi => ⟨⟨dd i, ?_⟩, fun m hm => hP.head i m hi hm⟩⟩⟩
    · have := P.step i
      rwa [hP.degs i hi] at this
    · exact step_vec P i (H.vec_true_of_late i (by omega))
  · rintro ⟨h0, hd, hs⟩
    have hex : ∀ i : Fin N, ∃ d : ℕ, (i.val < n0 → d = B i) ∧
        if LL.vec i then HStrip (μ i.castSucc) (μ i.succ) d else HStrip (μ i.succ) (μ i.castSucc) d := by
      intro i
      by_cases hi : i.val < n0
      · exact ⟨B i, fun _ => rfl, (hs i i.2).1 hi⟩
      · obtain ⟨d, hd'⟩ := ((hs i i.2).2 (by omega)).1
        refine ⟨d, fun h => absurd h hi, ?_⟩
        rw [ite_eq_left (H.vec_true_of_late i (by omega))]
        exact hd'
    choose dd hdd using hex
    exact ⟨dd, ⟨⟨μ, h0, fun t => hd t (by have := t.2; omega), fun i => (hdd i).2⟩, rfl⟩, fun i hi => (hdd i).1 hi,
      fun i m hi hm => ((hs i i.2).2 hi).2 m hm⟩

theorem vp_le_dplus {s : ℕ} {μ : Fin (N + 1) → Fin (r + K) → ℤ} (h : VP LL n0 B s μ) :
    ∀ (t : ℕ) (ht : t < N + 1), t ≤ s → t ≤ n0 → ∀ m, μ ⟨t, ht⟩ m ≤ (dplus LL B t : ℤ) := by
  intro t
  induction t with
  | zero =>
    intro ht _ _ m
    have h0 : (⟨0, ht⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, h.1]; simp
  | succ t ih =>
    intro ht hts htn m
    have htN : t < N := by omega
    have ih' := ih (by omega) (by omega) (by omega) m
    have hst := (h.2.2 ⟨t, htN⟩ (by simp only; omega)).1 (by simp only; omega)
    have hd : dplus LL B (t + 1) = dplus LL B t + if LL.vec ⟨t, htN⟩ = true then B ⟨t, htN⟩ else 0 :=
      dsum_succ (fun l => LL.vec l = true) B t htN
    rw [hd]
    cases hv : LL.vec ⟨t, htN⟩ with
    | true =>
      rw [ite_eq_left hv] at hst
      have h' : μ ⟨t + 1, ht⟩ m ≤ μ ⟨t, by omega⟩ m + (B ⟨t, htN⟩ : ℤ) := strip_le_add hst m
      simp only [ite_true]
      push_cast
      linarith
    | false =>
      rw [ite_eq_right (by simp [hv])] at hst
      have h' : μ ⟨t + 1, ht⟩ m ≤ μ ⟨t, by omega⟩ m := hst.1 m
      simp
      linarith

theorem dplus_le_beA' (t : ℕ) (ht : t ≤ n0) : dplus LL B t ≤ beA n0 B :=
  Finset.sum_le_sum fun l _ => by
    by_cases hl : l.val < t ∧ LL.vec l = true
    · rw [ite_eq_left hl, ite_eq_left (by omega)]
    · rw [ite_eq_right hl]; exact Nat.zero_le _

theorem vp_le {s : ℕ} {μ : Fin (N + 1) → Fin (r + K) → ℤ} (h : VP LL n0 B s μ) :
    ∀ (t : ℕ) (ht : t < N + 1), t ≤ s → ∀ m, μ ⟨t, ht⟩ m ≤ (beA n0 B : ℤ) := by
  intro t
  induction t with
  | zero =>
    intro ht _ m
    have h0 : (⟨0, ht⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, h.1]; simp
  | succ t ih =>
    intro ht hts m
    by_cases htn : t + 1 ≤ n0
    · refine le_trans (vp_le_dplus h (t + 1) ht hts htn m) ?_
      exact_mod_cast dplus_le_beA' (t + 1) htn
    · have htN : t < N := by omega
      obtain ⟨⟨d, hst⟩, hhead⟩ := (h.2.2 ⟨t, htN⟩ (by simp only; omega)).2 (by simp only; omega)
      by_cases hm : m.val = 0
      · exact le_of_eq (hhead m (by omega))
      · have hm1 : (m.val - 1) + 1 < r + K := by have := m.2; omega
        have h2 := hst.2.1 ⟨m.val - 1, by have := m.2; omega⟩ hm1
        have hme : (⟨(m.val - 1) + 1, hm1⟩ : Fin (r + K)) = m := Fin.ext (by simp only; omega)
        rw [hme] at h2
        exact le_trans h2 (ih (by omega) (by omega) _)

open Classical in
theorem vp_update {s : ℕ} (hs : s < N) {μ : Fin (N + 1) → Fin (r + K) → ℤ} (h : VP LL n0 B s μ)
    (la' : Fin (r + K) → ℤ) (hd : Dominant la')
    (hst : StepOK LL n0 B ⟨s, hs⟩ (μ (⟨s, hs⟩ : Fin N).castSucc) la') :
    VP LL n0 B (s + 1) (Function.update μ (⟨s, hs⟩ : Fin N).succ la') := by
  have hne : ∀ t : Fin (N + 1), t.val ≤ s → t ≠ (⟨s, hs⟩ : Fin N).succ := by
    intro t ht he
    rw [he] at ht
    simp at ht
  refine ⟨?_, ?_, ?_⟩
  · rw [Function.update_of_ne (hne 0 (by simp))]; exact h.1
  · intro t ht
    by_cases he : t = (⟨s, hs⟩ : Fin N).succ
    · rw [he, Function.update_self]; exact hd
    · rw [Function.update_of_ne he]
      refine h.2.1 t ?_
      have : t.val ≠ s + 1 := fun hv => he (Fin.ext (by simpa using hv))
      omega
  · intro i hi
    by_cases he : i.val = s
    · have hi' : i = ⟨s, hs⟩ := Fin.ext he
      subst hi'
      rw [Function.update_self, Function.update_of_ne (hne _ (by simp))]
      exact hst
    · rw [Function.update_of_ne (hne _ (by simp; omega)), Function.update_of_ne (hne _ (by simp; omega))]
      exact h.2.2 i (by omega)

end
end

section
open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def tailT (t : ℕ) (la : Fin (r + K) → ℤ) : Fin (K + t) → ℤ := fun l =>
  if h : (r - t) + l.val < r + K then la ⟨(r - t) + l.val, h⟩ else 0

def glueT (t : ℕ) (be : ℤ) (τ : Fin (K + t) → ℤ) : Fin (r + K) → ℤ := fun m =>
  if h : m.val < r - t then be else if h' : m.val - (r - t) < K + t then τ ⟨m.val - (r - t), h'⟩ else 0

theorem tailT_glueT (t : ℕ) (ht : t ≤ r) (be : ℤ) (τ : Fin (K + t) → ℤ) : tailT (r := r) t (glueT t be τ) = τ := by
  funext l
  have hl := l.2
  have h1 : (r - t) + l.val < r + K := by omega
  simp only [tailT, glueT, dite_eq_left h1]
  simp

theorem tailT_apply (t : ℕ) (ht : t ≤ r) (la : Fin (r + K) → ℤ) (l : Fin (K + t)) :
    tailT t la l = la ⟨(r - t) + l.val, by have := l.2; omega⟩ := by
  unfold tailT; rw [dite_eq_left]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem finite_SAll [NeZero r] [NeZero K] (H : HypT N n0 r K LL B od bb a La p) :
    (SAll (r := r) (K := K) LL n0 B).Finite := by
  have hS : (SP (r := r) (K := K) LL n0 B).Finite := by
    refine (Set.Finite.pi (t := fun _ : Fin (N + 1) => Set.pi Set.univ fun _ : Fin (r + K) => Set.Icc (-(beA n0 B : ℤ)) (beA n0 B)) fun _ => Set.Finite.pi fun _ => Set.finite_Icc _ _).subset ?_
    rintro μ ⟨dd, hpa⟩
    obtain ⟨P, rfl⟩ := hpa.path
    simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const]
    intro s m
    exact ⟨le_trans (neg_le_neg (by exact_mod_cast dminus_le_beA H hpa.degs s.val)) (neg_dminus_le_mu P s.val s.2 m), path_le_beA H P hpa s.val s.2 m⟩
  refine (hS.biUnion fun μ _ => (Set.finite_singleton μ).prod (finite_St (tanPart μ))).subset ?_
  rintro ⟨μ, I⟩ ⟨h1, h2⟩
  exact Set.mem_biUnion h1 ⟨rfl, h2⟩

open Classical in
def Af (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) :
    Finset (QT N r K) :=
  hfin.toFinset.filter fun q => ∀ t : Fin (N + 1), t.val ≤ s → q.1 t = μ0 t

open Classical in
theorem Af_fiber (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ) (hs : s < N)
    (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) (la' : Fin (r + K) → ℤ) :
    (Af hfin s μ0).filter (fun q => q.1 (⟨s, hs⟩ : Fin N).succ = la') =
      Af hfin (s + 1) (Function.update μ0 (⟨s, hs⟩ : Fin N).succ la') := by
  ext q
  simp only [Af, Finset.mem_filter]
  constructor
  · rintro ⟨⟨hq, h⟩, h'⟩
    refine ⟨hq, fun t ht => ?_⟩
    by_cases e : t = (⟨s, hs⟩ : Fin N).succ
    · subst e
      rw [Function.update_apply, ite_eq_left rfl]
      exact h'
    · rw [Function.update_of_ne e]
      apply h
      have : t.val ≠ s + 1 := fun h2 => e (Fin.ext (by simp [h2]))
      omega
  · rintro ⟨hq, h⟩
    refine ⟨⟨hq, fun t ht => ?_⟩, ?_⟩
    · have e : t ≠ (⟨s, hs⟩ : Fin N).succ := by
        rintro rfl
        simp at ht
      rw [h t (by omega), Function.update_of_ne e]
    · rw [h _ (by simp)]
      simp

theorem Af_step (H : HypT N n0 r K LL B od bb a La p) (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ)
    (hs : s < N) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) (q : QT N r K) (hq : q ∈ Af hfin s μ0) :
    Dominant (q.1 (⟨s, hs⟩ : Fin N).succ) ∧
      StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) (q.1 (⟨s, hs⟩ : Fin N).succ) := by
  classical
  simp only [Af, Finset.mem_filter, Set.Finite.mem_toFinset] at hq
  obtain ⟨⟨hsp, -⟩, hμ⟩ := hq
  obtain ⟨dd, hpa⟩ := hsp
  obtain ⟨P, hP⟩ := hpa.path
  have hc : q.1 (⟨s, hs⟩ : Fin N).castSucc = μ0 (⟨s, hs⟩ : Fin N).castSucc := hμ _ (by simp)
  rw [← hc]
  have hstep := P.step ⟨s, hs⟩
  rw [hP] at hstep
  refine ⟨by rw [← hP]; exact P.dom _, fun hlt => ?_, fun hge => ⟨⟨dd ⟨s, hs⟩, ?_⟩, fun m hm => hpa.head _ m hge hm⟩⟩
  · rwa [← hpa.degs _ hlt]
  · have hv : LL.vec ⟨s, hs⟩ = true := H.vec_true_of_late _ (Nat.le_add_right_of_le hge)
    rwa [ite_eq_left hv] at hstep

open Classical in
theorem Af_card_sum (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) (s : ℕ) (hs : s < N)
    (μ0 : Fin (N + 1) → Fin (r + K) → ℤ) (E : Finset (Fin (r + K) → ℤ))
    (hE : ∀ q ∈ Af hfin s μ0, q.1 (⟨s, hs⟩ : Fin N).succ ∈ E) :
    (Af hfin s μ0).card = ∑ la' ∈ E, (Af hfin (s + 1) (Function.update μ0 (⟨s, hs⟩ : Fin N).succ la')).card := by
  rw [Finset.card_eq_sum_card_fiberwise hE]
  refine Finset.sum_congr rfl fun la' _ => ?_
  rw [Af_fiber hfin s hs]

end
end

end Formalism.MainNotions.SelectionLemmas.Pf.T

namespace Formalism.MainNotions.SelectionLemmas.Pf.TE

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace Formalism.MainNotions.SelectionLemmas.Pf.T

section Num61

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem six_le_Ns (hX : X.Hyp p K) : 6 ≤ X.Ns := by
  have hV := hX.valid
  have hr2 := hX.r2
  have hg : X.F.fr 0 (r - 1) < X.F.fr 1 0 := by
    have h0 := hV.2.2.2.1 0
    simpa using h0
  have hle : ∀ j : ℤ, ∀ i, i < r → X.F.fr j 0 ≤ X.F.fr j i := fun j i hi => fr_le hV j 0 i (Nat.zero_le _) hi
  have hleT : ∀ j : ℤ, ∀ i, i < r → X.F.fr j i ≤ X.F.fr j (r - 1) := fun j i hi => fr_le hV j i (r - 1) (by omega) (by omega)
  have hinj : ∀ j : ℤ, Set.InjOn (fun i => X.F.fr j i) (Finset.range r) := by
    intro j a ha b hb hab
    simp only [Finset.coe_range, Set.mem_Iio] at ha hb
    simp only at hab
    rcases lt_trichotomy a b with h | h | h
    · have h2 := fr_lt hV j a b h hb
      omega
    · exact h
    · have h2 := fr_lt hV j b a h ha
      omega
  have hAc : ((Finset.range r).image (fun i => X.F.fr 0 i)).card = r := by
    rw [Finset.card_image_of_injOn (hinj 0), Finset.card_range]
  have hCc : ((Finset.range r).image (fun i => X.F.fr 1 i)).card = r := by
    rw [Finset.card_image_of_injOn (hinj 1), Finset.card_range]
  have hBc : r ≤ (X.F.LLset 1).card := (hV.2.2.2.2.2.2.1 1).1
  have hsub : (Finset.range r).image (fun i => X.F.fr 0 i) ∪ X.F.LLset 1 ∪
      (Finset.range r).image (fun i => X.F.fr 1 i) ⊆ X.F.letters 1 := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_image, Finset.mem_range] at hx
    simp only [Frames.letters, sub_self, Finset.mem_filter, Finset.mem_Icc]
    rcases hx with (⟨i, hi, rfl⟩ | hB) | ⟨i, hi, rfl⟩
    · refine ⟨⟨hle 0 i hi, ?_⟩, (hV.2.2.2.2.1 0 i hi).1⟩
      have h1 := hleT 0 i hi
      have h2 := hle 1 (r - 1) (by omega)
      omega
    · simp only [Frames.LLset, sub_self, Finset.mem_filter, Finset.mem_Ioo] at hB
      refine ⟨⟨?_, ?_⟩, hB.2⟩
      · have h1 := hle 0 (r - 1) (by omega)
        omega
      · have h1 := hle 1 (r - 1) (by omega)
        omega
    · refine ⟨⟨?_, hleT 1 i hi⟩, (hV.2.2.2.2.1 1 i hi).1⟩
      have h1 := hle 0 (r - 1) (by omega)
      have h2 := hle 1 i hi
      omega
  have hdAB : Disjoint ((Finset.range r).image (fun i => X.F.fr 0 i)) (X.F.LLset 1) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    simp only [Finset.mem_image, Finset.mem_range] at hxA
    obtain ⟨i, hi, rfl⟩ := hxA
    simp only [Frames.LLset, sub_self, Finset.mem_filter, Finset.mem_Ioo] at hxB
    have h1 := hleT 0 i hi
    omega
  have hdABC : Disjoint ((Finset.range r).image (fun i => X.F.fr 0 i) ∪ X.F.LLset 1)
      ((Finset.range r).image (fun i => X.F.fr 1 i)) := by
    rw [Finset.disjoint_left]
    intro x hx hxC
    simp only [Finset.mem_image, Finset.mem_range] at hxC
    obtain ⟨i, hi, rfl⟩ := hxC
    have h1 := hle 1 i hi
    rcases Finset.mem_union.mp hx with hxA | hxB
    · simp only [Finset.mem_image, Finset.mem_range] at hxA
      obtain ⟨i', hi', he⟩ := hxA
      have h2 := hleT 0 i' hi'
      omega
    · simp only [Frames.LLset, sub_self, Finset.mem_filter, Finset.mem_Ioo] at hxB
      omega
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdABC, Finset.card_union_of_disjoint hdAB, hAc, hCc] at hcard
  have h3 := hX.card 1
  omega

theorem a_big (hX : X.Hyp p K) : 416 * (X.Ns : ℝ) ≤ X.a := by
  have hp : (13 : ℝ) ≤ p := by exact_mod_cast hX.p13
  have hY := hX.Y1
  have hk : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) := by
    have h0 := hX.r2
    exact_mod_cast (by omega : 1 ≤ r + K)
  have hmem := frj_mem hX.valid 1 0 (by have := hX.r2; omega)
  have hQ : 1 ≤ X.Q := (one_le_pow₀ (by linarith : (1 : ℝ) ≤ p)).trans (hX.twist 1 _ hmem)
  have hE : (1 : ℝ) ≤ (X.E₀ : ℝ) + X.mStar + 1 := by
    linarith
  calc 416 * (X.Ns : ℝ) = 32 * 13 * 1 * 1 ^ 2 * X.Ns * 1 ^ 2 * 1 := by ring
    _ ≤ 32 * p * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns * X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) := by
      gcongr
    _ ≤ X.a := hX.P3

theorem four_hundred_sixteen_le_a (hX : X.Hyp p K) : 416 ≤ X.a := by
  have h2 : (6 : ℝ) ≤ X.Ns := by exact_mod_cast six_le_Ns hX
  linarith [a_big hX]

theorem log_a_ge (hX : X.Hyp p K) : 1 ≤ Real.log X.a := by
  have h := four_hundred_sixteen_le_a hX
  rw [Real.le_log_iff_exp_le (by linarith)]
  linarith [Real.exp_one_lt_d9]

theorem k_big (hX : X.Hyp p K) (hk : 1088 ≤ X.Ck) : 1088 * (X.Ns : ℝ) ^ 2 ≤ ((r + K : ℕ) : ℝ) := by
  have hl := log_a_ge hX
  have hP1 := hX.P1
  have hN : (0 : ℝ) ≤ (X.Ns : ℝ) ^ 2 := by positivity
  have hC : (0 : ℝ) ≤ X.Ck := by linarith
  have h1 : 0 ≤ X.Ck * (X.Ns : ℝ) ^ 2 := mul_nonneg hC hN
  nlinarith [mul_le_mul_of_nonneg_left hl h1, mul_le_mul_of_nonneg_right hk hN]

theorem c_bounds (hX : X.Hyp p K) (h41 : ∀ t ∈ X.F.TT, (9 / 10 : ℝ) * (X.deg t : ℝ) ≤ (X.a' p K t : ℝ))
    (j y : ℤ) (hy : y ∈ X.F.letters j) :
    (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j) ≤
        (X.a' p K (posOf n' y) : ℝ) ∧
      (9 / 10 : ℝ) * X.a ≤ (X.a' p K (posOf n' y) : ℝ) ∧ (X.a' p K (posOf n' y) : ℝ) ≤ 2 * X.a := by
  have hV := hX.valid
  have hr2 := hX.r2
  have hp1 : (1 : ℝ) ≤ p := by have := hX.p13; exact_mod_cast (by omega : 1 ≤ p)
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hy
  obtain ⟨⟨hy1, hy2⟩, hyT⟩ := hy
  have hdeg := hX.degs _ hyT
  have h41y := h41 _ hyT
  have ha'le : (X.a' p K (posOf n' y) : ℝ) ≤ X.deg (posOf n' y) := by
    have h0 : X.a' p K (posOf n' y) ≤ X.deg (posOf n' y) := by
      unfold Dat.a' Dat.d
      rw [ite_eq_left hyT]
      omega
    exact_mod_cast h0
  refine ⟨?_, by linarith [hdeg.1], by linarith [hdeg.2]⟩
  have hwL : X.F.fr (j - 1) 0 ∈ X.F.letters j := by
    simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_refl _, ?_⟩, (hV.2.2.2.2.1 (j - 1) 0 (by omega)).1⟩
    have hg := hV.2.2.2.1 (j - 1)
    rw [sub_add_cancel] at hg
    have h1 := fr_le hV (j - 1) 0 (r - 1) (Nat.zero_le _) (by omega)
    have h2 := fr_le hV j 0 (r - 1) (Nat.zero_le _) (by omega)
    omega
  have hdist : X.F.dist j y ≤ X.F.dist j (X.F.fr (j - 1) 0) := by
    unfold Frames.dist
    exact Int.toNat_le_toNat (by omega)
  have hQ0 : (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) ≤ X.Q := hX.twist j _ hwL
  have hQ1 : 1 ≤ X.Q := (one_le_pow₀ hp1).trans hQ0
  have hY := hX.Y1
  have hNs : (6 : ℝ) ≤ X.Ns := by exact_mod_cast six_le_Ns hX
  have hk1 : (1 : ℝ) ≤ ((r + K : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r + K)
  have hE : (1 : ℝ) ≤ (X.E₀ : ℝ) + X.mStar + 1 := by
    have h1 : (0 : ℝ) ≤ X.E₀ := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ X.mStar := Nat.cast_nonneg _
    linarith
  have hkdef : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  set D0 := X.F.dist j (X.F.fr (j - 1) 0) with hD0
  set Dn := 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ D0 with hDnd
  have hYk : 0 ≤ X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns :=
    mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (Nat.cast_nonneg _)
  have hDn : 0 < Dn := by
    rw [hDnd, hkdef]
    have h1 : (0 : ℝ) < (p : ℝ) ^ D0 := pow_pos (by linarith) _
    have h2 : (0 : ℝ) < X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns := by
      have h3 : (0 : ℝ) < ((r + K : ℕ) : ℝ) ^ 2 := by positivity
      positivity
    nlinarith
  have hDa : Dn ≤ X.a := by
    have h1 : (8 : ℝ) ≤ 32 * p := by linarith
    have h2 : (p : ℝ) ^ D0 ≤ X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) := by
      nlinarith [mul_le_mul_of_nonneg_left hE (sq_nonneg X.Q)]
    have h3 := mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (by positivity) (by linarith)) hYk
    calc Dn = 8 * (p : ℝ) ^ D0 * (X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns) := by rw [hDnd, hkdef]; ring
      _ ≤ 32 * p * (X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1)) * (X.Y * ((r + K : ℕ) : ℝ) ^ 2 * X.Ns) := h3
      _ = 32 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Q ^ 2 *
          ((X.E₀ : ℝ) + X.mStar + 1) := by ring
      _ ≤ X.a := hX.P3
  have hfl1 : ⌊X.a / Dn⌋₊ ≠ 0 := by
    have h1 : 1 ≤ ⌊X.a / Dn⌋₊ := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hDn]; linarith)
    omega
  have hRjdef : X.Rj p K j = Nat.log p ⌊X.a / Dn⌋₊ := rfl
  have hRj : (p : ℝ) ^ (X.Rj p K j) ≤ X.a / Dn := by
    have h1 : p ^ (X.Rj p K j) ≤ ⌊X.a / Dn⌋₊ := by rw [hRjdef]; exact Nat.pow_log_le_self p hfl1
    calc (p : ℝ) ^ (X.Rj p K j) = ((p ^ X.Rj p K j : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (⌊X.a / Dn⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ X.a / Dn := Nat.floor_le (div_nonneg (by linarith) hDn.le)
  have hpd : (p : ℝ) ^ (X.F.dist j y) ≤ (p : ℝ) ^ D0 := pow_le_pow_right₀ hp1 hdist
  have hA : 0 ≤ (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
    rw [hkdef]
    have := hYk
    nlinarith
  have e : (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j) ≤
      (9 / 10) * X.a := by
    rw [pow_add]
    calc (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ X.F.dist j y * (p : ℝ) ^ X.Rj p K j)
        ≤ (36 / 5 : ℝ) * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * ((p : ℝ) ^ D0 * (X.a / Dn)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hpd hRj (by positivity) (by positivity)) hA
      _ = (9 / 10) * X.a := by
          have hk0 : Dat.k (r := r) K ≠ 0 := by rw [hkdef]; linarith
          have hY0 : X.Y ≠ 0 := by linarith
          have hN0 : (X.Ns : ℝ) ≠ 0 := by linarith
          have hpD : (p : ℝ) ^ D0 ≠ 0 := pow_ne_zero _ (by linarith)
          rw [hDnd]
          field_simp
          ring
  linarith [hdeg.1, h41y]

theorem Bdeg_bounds (hX : X.Hyp p K)
    (j : ℤ) (b : ℤ → ℕ) (hA : X.AdmLL p K j b) (x : ℤ) (hx : x ∈ X.F.letters j) (hlt : x < X.F.fr j 0) :
    (X.a' p K (posOf n' x) : ℝ) / (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) - 2 * Dat.k (r := r) K * (X.Ns : ℝ) ≤
        (X.Bdeg p K j (X.restr j b) x : ℝ) ∧
      (X.Bdeg p K j (X.restr j b) x : ℝ) ≤
        (X.a' p K (posOf n' x) : ℝ) / (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
  have hr2 := hX.r2
  have hNs : (6 : ℝ) ≤ X.Ns := by exact_mod_cast six_le_Ns hX
  have hkdef : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  have hpp : 0 < p ^ (X.F.dist j x + X.Rj p K j) := pow_pos hX.prime.pos _
  have hPc : ((p ^ (X.F.dist j x + X.Rj p K j) : ℕ) : ℝ) = (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
    push_cast
    ring
  have hP0 : (0 : ℝ) < (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by rw [← hPc]; exact_mod_cast hpp
  unfold Dat.Bdeg
  by_cases hW : X.F.IsW j x
  · rw [ite_eq_left hW]
    unfold Dat.Bw Dat.m0
    set A := X.a' p K (posOf n' x) with hAdef
    set pp := p ^ (X.F.dist j x + X.Rj p K j) with hppdef
    have hq1 : ((A / pp : ℕ) : ℝ) ≤ (A : ℝ) / (pp : ℝ) := Nat.cast_div_le
    have hq2 : (A : ℝ) / (pp : ℝ) < ((A / pp : ℕ) : ℝ) + 1 := by
      have hmod := Nat.div_add_mod A pp
      have hlt := Nat.mod_lt A hpp
      have hppR : (0 : ℝ) < (pp : ℝ) := by exact_mod_cast hpp
      rw [div_lt_iff₀ hppR]
      have e1 : (A : ℝ) = (pp : ℝ) * ((A / pp : ℕ) : ℝ) + ((A % pp : ℕ) : ℝ) := by exact_mod_cast hmod.symm
      have e2 : ((A % pp : ℕ) : ℝ) < (pp : ℝ) := by exact_mod_cast hlt
      nlinarith
    rw [← hPc]
    set z : ℤ := ((A / pp : ℕ) : ℤ) - ((r + K + r + 1 : ℕ) : ℤ) - (((r + K) * X.Ns + 1 : ℕ) : ℤ) with hz
    have hzR : (z : ℝ) = ((A / pp : ℕ) : ℝ) - ((r + K + r + 1 : ℕ) : ℝ) - (((r + K) * X.Ns + 1 : ℕ) : ℝ) := by
      simp only [hz, Int.cast_sub, Int.cast_natCast]
    have hc1 : ((r + K + r + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + K + 1 := by push_cast; ring
    have hc2 : (((r + K) * X.Ns + 1 : ℕ) : ℝ) = ((r : ℝ) + K) * X.Ns + 1 := by push_cast; ring
    rw [hc1, hc2] at hzR
    have hzt1 : (z : ℝ) ≤ ((z.toNat : ℕ) : ℝ) := by
      have h1 : z ≤ (z.toNat : ℤ) := Int.self_le_toNat z
      exact_mod_cast h1
    have hzt2 : ((z.toNat : ℕ) : ℝ) ≤ max (z : ℝ) 0 := by
      rcases le_or_gt 0 z with h | h
      · have h1 : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg h
        have h2 : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by exact_mod_cast h1
        rw [h2]
        exact le_max_left _ _
      · rw [Int.toNat_of_nonpos h.le]
        simp
    have hApos : (0 : ℝ) ≤ (A : ℝ) / (pp : ℝ) := by positivity
    have hkc : ((r + K : ℕ) : ℝ) = (r : ℝ) + K := by push_cast; ring
    rw [hkdef, hkc]
    have hrR : (2 : ℝ) ≤ r := by exact_mod_cast hr2
    have hprod : ((r : ℝ) + K) * 6 ≤ ((r : ℝ) + K) * X.Ns :=
      mul_le_mul_of_nonneg_left hNs (by linarith)
    constructor
    · linarith
    · have h1 : max (z : ℝ) 0 ≤ (A : ℝ) / (pp : ℝ) := by
        apply max_le
        · rw [hzR]
          have h2 : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg _
          have h3 : (0 : ℝ) ≤ (K : ℝ) := Nat.cast_nonneg _
          have h4 : (0 : ℝ) ≤ ((r : ℝ) + K) * X.Ns := by positivity
          linarith
        · exact hApos
      linarith
  · rw [ite_eq_right hW]
    have hxl := hx
    simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hxl
    have hlate : x ∈ X.toLate j := by
      unfold Dat.toLate
      simp only [Finset.mem_filter]
      exact ⟨hx, hW⟩
    unfold Dat.restr
    rw [ite_eq_left hlate]
    have hLL : x ∈ X.F.LLset j := by
      simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo]
      unfold Frames.IsW at hW
      push Not at hW
      exact ⟨⟨hW, hlt⟩, hxl.2⟩
    obtain ⟨h1, h2⟩ := hA x hLL
    have hPz : ((X.Pz p K j x : ℕ) : ℝ) = (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
      unfold Dat.Pz
      push_cast
      ring
    rw [hPz] at h1 h2
    rw [hkdef] at h1 ⊢
    have h3 : (0 : ℝ) ≤ ((r + K : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 : ((r + K : ℕ) : ℝ) ≤ 2 * ((r + K : ℕ) : ℝ) * (X.Ns : ℝ) := by nlinarith
    constructor
    · linarith
    · exact h2

end Num61

end Formalism.MainNotions.SelectionLemmas.Pf.TE

namespace Formalism.MainNotions.SelectionLemmas.Pf
section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

section Kill

variable {R σ : Type} [CommRing R] (S : Set σ)

open Classical in
def kill : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun v => if v ∈ S then 0 else MvPolynomial.X v

open Classical in
def scaleS : MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
  aeval fun v => if v ∈ S then Polynomial.X * Polynomial.C (MvPolynomial.X v) else Polynomial.C (MvPolynomial.X v)

open Classical in
def offDeg : (σ →₀ ℕ) →+ ℕ := Finsupp.liftAddHom fun v => if v ∈ S then AddMonoidHom.id ℕ else 0

theorem scaleS_monomial (m : σ →₀ ℕ) :
    scaleS (R := R) S (monomial m 1) = Polynomial.C (monomial m 1) * Polynomial.X ^ offDeg S m := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have : (monomial (f + g) (1 : R)) = monomial f 1 * monomial g 1 := by
      rw [monomial_mul, one_mul]
    rw [this, map_mul, hf, hg, map_add (f := _), pow_add, map_mul]
    ring
  | single v k =>
    rw [← MvPolynomial.X_pow_eq_monomial, map_pow]
    by_cases hv : v ∈ S
    · have h1 : scaleS (R := R) S (MvPolynomial.X v) = Polynomial.X * Polynomial.C (MvPolynomial.X v) := by
        simp [scaleS, hv]
      have h2 : offDeg S (Finsupp.single v k) = k := by simp [offDeg, hv]
      rw [h1, h2, mul_pow, Polynomial.C_pow, mul_comm]
    · have h1 : scaleS (R := R) S (MvPolynomial.X v) = Polynomial.C (MvPolynomial.X v) := by
        simp [scaleS, hv]
      have h2 : offDeg S (Finsupp.single v k) = 0 := by simp [offDeg, hv]
      rw [h1, h2, pow_zero, mul_one, Polynomial.C_pow]

theorem scaleS_coeff_zero (f : MvPolynomial σ R) : (scaleS S f).coeff 0 = kill S f := by
  classical
  have h : (Polynomial.constantCoeff.comp (scaleS (R := R) S : MvPolynomial σ R →+* Polynomial (MvPolynomial σ R))) =
      (kill (R := R) S : MvPolynomial σ R →+* MvPolynomial σ R) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [scaleS, kill, MvPolynomial.algebraMap_eq]
    · intro v
      by_cases hv : v ∈ S <;> simp [scaleS, kill, hv]
  have := congrArg (fun g => g f) h
  simpa [Polynomial.constantCoeff_apply] using this

theorem li_of_kill {ι : Type} (m : ι → σ →₀ ℕ) (w : ι → MvPolynomial σ R)
    (h : LinearIndependent R fun q => monomial (m q) (1 : R) * kill S (w q)) :
    LinearIndependent R fun q => monomial (m q) (1 : R) * w q := by
  classical
  rw [linearIndependent_iff'] at h ⊢
  intro s a hsum
  by_contra hne
  push Not at hne
  obtain ⟨q0, hq0s, hq0⟩ := hne
  let s' := s.filter fun q => a q ≠ 0
  have hs' : s'.Nonempty := ⟨q0, Finset.mem_filter.mpr ⟨hq0s, hq0⟩⟩
  obtain ⟨q1, hq1, hmin⟩ := Finset.exists_min_image s' (fun q => offDeg S (m q)) hs'
  set δ := offDeg S (m q1) with hδ
  have hsum' : ∑ q ∈ s', a q • (monomial (m q) (1 : R) * w q) = 0 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro q hq hq'
    have : a q = 0 := by
      by_contra hh
      exact hq' (Finset.mem_filter.mpr ⟨hq, hh⟩)
    rw [this, zero_smul]
  have hΘ := congrArg (fun P => (scaleS S P).coeff δ) hsum'

  simp only [map_sum, map_smul, map_mul, scaleS_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
  map_zero, Polynomial.coeff_zero] at hΘ
  have hterm : ∀ q ∈ s', (Polynomial.C (monomial (m q) (1 : R)) * Polynomial.X ^ offDeg S (m q) *
      scaleS S (w q)).coeff δ = if offDeg S (m q) = δ then monomial (m q) (1 : R) * kill S (w q) else 0 := by
    intro q hq
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    have hle := hmin q hq
    split_ifs with h1 h2 h2
    · rw [h2, Nat.sub_self, scaleS_coeff_zero]
    · exact absurd (le_antisymm h1 hle) h2
    · exact absurd (le_of_eq h2) h1
    · rw [mul_zero]
  rw [Finset.sum_congr rfl fun q hq => by rw [hterm q hq]] at hΘ
  have hΘ' : ∑ q ∈ s'.filter (fun q => offDeg S (m q) = δ), a q • (monomial (m q) (1 : R) * kill S (w q)) = 0 := by
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) hΘ
    split_ifs <;> simp
  have := h _ a hΘ' q1 (Finset.mem_filter.mpr ⟨hq1, rfl⟩)
  exact (Finset.mem_filter.mp hq1).2 this

end Kill

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ)

omit [NeZero n'] in
def offSet (j : ℤ) : Set (ℤ × Fin (r + K)) :=
  {v | ∃ t c : Fin r, c ≠ Fin.rev t ∧ v = (X.F.fr j t.val, Fin.castAdd K c)}

omit [NeZero n'] in
def monTau (j : ℤ) (u : Fin r × Fin r → ℕ) : ℤ × Fin (r + K) →₀ ℕ :=
  ∑ v : Fin r × Fin r, Finsupp.single (X.F.fr j v.1.val, Fin.castAdd K v.2) (u v)

def wordEl (O : Type) [CommRing O] (j : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) : SegRing O r K :=
  segRen X.F j O (r + K) (PsiPl O (plPart q.1) (Ican (plPart q.1)) * PsiTan O (tanPart q.1) q.2.1)

end Dat

def RestKey (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b →
      LinearIndependent O fun q : X.Idx p K j (X.restr j b) =>
        monomial (X.monTau K j q.1.2.2) (1 : O) * kill (X.offSet K j) (X.wordEl K O j q.1)

theorem fr_injective {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) :
    Function.Injective fun a : Fin r => F.fr j a.val :=
  fun a b hab => Fin.ext (TE.fr_inj hV j a.val b.val a.isLt b.isLt hab)

theorem plEmb_injective (O : Type) [CommRing O] (r K : ℕ) : Function.Injective (plEmb O r K) := by
  apply rename_injective
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.castAdd_injective _ _ h.2)

theorem restInd_of (C₀ : ℝ) (hK : RestKey C₀) : RestInd C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hB
  have h1 := li_of_kill (X.offSet K j) (fun q : X.Idx p K j (X.restr j b) => X.monTau K j q.1.2.2)
    (fun q => X.wordEl K O j q.1) (hK p n' r K X O S hX hLa hk j b hB)
  set c0 : MvPolynomial (ℤ × Fin r) O := X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat) with hc0
  have hD : X.Dw O j ≠ 0 := Formalism.MainNotions.G.Joints.StandardMonomialSpace.detX_ne_zero _ (fr_injective X.F hX.valid (j - 1))
  have hc0ne : c0 ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ hD) (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (X_ne_zero _))
  have hc : plEmb O r K c0 ≠ 0 := (map_ne_zero_iff _ (plEmb_injective O r K)).mpr hc0ne
  have h2 := h1.map' (LinearMap.mulLeft O (plEmb O r K c0))
    (LinearMap.ker_eq_bot.mpr fun x y hxy => mul_left_cancel₀ hc hxy)
  have heq : (fun q : X.Idx p K j (X.restr j b) => X.famEl p K O j b q.1) =
      (⇑(LinearMap.mulLeft O ((plEmb O r K) c0)) ∘
        fun q : X.Idx p K j (X.restr j b) => (monomial (X.monTau K j q.1.2.2)) (1 : O) * X.wordEl K O j q.1) := by
    funext q
    simp only [Function.comp, LinearMap.mulLeft_apply]
    unfold Dat.famEl Dat.wordEl Dat.monTau
    rw [map_mul, ← hc0, mul_assoc]
    congr 2
    rw [MvPolynomial.monomial_sum_one, map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_pow, ← MvPolynomial.X_pow_eq_monomial]
    simp [plEmb]
  rw [heq]
  exact h2

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs

variable {R : Type} [CommRing R] {N r : ℕ}

def stg (ν : Fin (N + 1) → Fin r → ℤ) (i : ℕ) : Fin r → ℤ := if h : i < N + 1 then ν ⟨i, h⟩ else 0

theorem stg_eq (ν : Fin (N + 1) → Fin r → ℤ) (i : ℕ) (h : i < N + 1) : ν ⟨i, h⟩ = stg ν i := by
  simp [stg, h]

theorem Kcol_succ (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (j : ℕ) (h : j < N) :
    Kcol R ν c (j + 1) =
      colStep c (colH (stg ν j) c) (colH (stg ν (j + 1)) c) (letVec R ⟨j, h⟩) (Kcol R ν c j) := by
  rw [Kcol, dite_eq_left h, stg_eq ν j (by omega), stg_eq ν (j + 1) (by omega)]

def offN (n0 : ℕ) : Set (Fin N × Fin r) := {v | n0 ≤ v.1.val ∧ v.2.val + (v.1.val - n0) + 1 ≠ r}

theorem kill_colStep (S : Set (Fin N × Fin r)) (c : ℤ) (hP hN : ℕ) (x : Fin r → MvPolynomial (Fin N × Fin r) R)
    (Kf : Finset (Fin r) → MvPolynomial (Fin N × Fin r) R) (J : Finset (Fin r)) :
    kill S (colStep c hP hN x Kf J) = colStep c hP hN (fun m => kill S (x m)) (fun J => kill S (Kf J)) J :=
  lift_colStep_map (kill (R := R) S : MvPolynomial (Fin N × Fin r) R →+* MvPolynomial (Fin N × Fin r) R) c hP hN x Kf J

theorem kill_X_not (S : Set (Fin N × Fin r)) (v : Fin N × Fin r) (hv : v ∉ S) :
    kill (R := R) S (MvPolynomial.X v) = MvPolynomial.X v := by
  simp [kill, hv]

theorem kill_X_mem (S : Set (Fin N × Fin r)) (v : Fin N × Fin r) (hv : v ∈ S) :
    kill (R := R) S (MvPolynomial.X v) = 0 := by
  simp [kill, hv]

theorem kill_Kcol_low (n0 : ℕ) (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ n0, ∀ J, kill (offN n0) (Kcol R ν c j J) = Kcol R ν c j J := by
  intro j
  induction j with
  | zero =>
    intro _ J
    exact lift_extOne_map (kill (R := R) (offN (N := N) (r := r) n0) :
      MvPolynomial (Fin N × Fin r) R →+* MvPolynomial (Fin N × Fin r) R) J
  | succ j ih =>
    intro hj J
    have hjN : j < N := by omega
    rw [Kcol_succ ν c j hjN, kill_colStep]
    have e1 : (fun m => kill (offN n0) (letVec R (N := N) (n := r) ⟨j, hjN⟩ m)) = letVec R ⟨j, hjN⟩ := by
      funext m
      apply kill_X_not
      intro hv
      have : n0 ≤ j := hv.1
      omega
    have e2 : (fun J => kill (offN n0) (Kcol R ν c j J)) = Kcol R ν c j := funext (ih (by omega))
    rw [e1, e2]

variable (n0 : ℕ) (hN : n0 + r = N)

def tauI (m : Fin r) : Fin N := ⟨n0 + (r - 1 - m.val), by have := m.isLt; omega⟩

def rises (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (i : ℕ) : Prop := colH (stg ν i) c < colH (stg ν (i + 1)) c

open Classical in
def riseA (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : ℕ) : Finset (Fin r) :=
  Finset.univ.filter fun m => r - 1 - m.val < t ∧ rises ν c (n0 + (r - 1 - m.val))

theorem kill_Kcol_tau (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (hc : 1 ≤ c)
    (hmono : ∀ t < r, colH (stg ν (n0 + t)) c ≤ colH (stg ν (n0 + t + 1)) c) :
    ∀ t ≤ r, ∀ J, riseA n0 ν c t ⊆ J → ∃ e : ℕ, kill (offN n0) (Kcol R ν c (n0 + t) J) =
      (-1) ^ e * (∏ m ∈ riseA n0 ν c t, MvPolynomial.X (tauI n0 hN m, m)) * Kcol R ν c n0 (J \ riseA n0 ν c t) := by
  classical
  intro t
  induction t with
  | zero =>
    intro _ J _
    refine ⟨0, ?_⟩
    have : riseA n0 ν c 0 = ∅ := by
      simp [riseA]
    rw [this]
    simp only [add_zero, pow_zero, Finset.prod_empty, mul_one, one_mul, Finset.sdiff_empty]
    exact kill_Kcol_low n0 (by omega) ν c n0 le_rfl J
  | succ t ih =>
    intro ht J hJ
    have htr : t < r := by omega
    have hjN : n0 + t < N := by omega
    let mt : Fin r := ⟨r - 1 - t, by omega⟩
    have hmt : r - 1 - mt.val = t := by simp only [mt]; omega
    have hval : ∀ m : Fin r, r - 1 - m.val = t → m = mt := by
      intro m hm
      apply Fin.ext
      have := m.isLt
      simp only [mt]; omega
    rw [show n0 + (t + 1) = n0 + t + 1 by ring, Kcol_succ ν c (n0 + t) hjN, kill_colStep]
    by_cases hr : rises ν c (n0 + t)
    · have hA : riseA n0 ν c (t + 1) = insert mt (riseA n0 ν c t) := by
        ext m
        simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases h3 : r - 1 - m.val = t
          · exact Or.inl (hval m h3)
          · exact Or.inr ⟨by omega, h2⟩
        · rintro (h | ⟨h1, h2⟩)
          · subst h
            rw [hmt]; exact ⟨by omega, hr⟩
          · exact ⟨by omega, h2⟩
      have hnot : mt ∉ riseA n0 ν c t := by
        simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h; rw [hmt] at h; omega
      have hmJ : mt ∈ J := hJ (by rw [hA]; exact Finset.mem_insert_self _ _)
      have hsub : riseA n0 ν c t ⊆ J.erase mt := by
        intro m hm
        refine Finset.mem_erase.mpr ⟨fun h => hnot (h ▸ hm), hJ (by rw [hA]; exact Finset.mem_insert_of_mem hm)⟩
      obtain ⟨e, he⟩ := ih (by omega) (J.erase mt) hsub
      have hstep : colStep c (colH (stg ν (n0 + t)) c) (colH (stg ν (n0 + t + 1)) c)
          (fun m => kill (offN n0) (letVec R (N := N) (n := r) ⟨n0 + t, hjN⟩ m))
          (fun J => kill (offN n0) (Kcol R ν c (n0 + t) J)) J =
          (-1) ^ (J.filter fun j => mt < j).card * MvPolynomial.X (tauI n0 hN mt, mt) *
            kill (offN n0) (Kcol R ν c (n0 + t) (J.erase mt)) := by
        have hr' : colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c := hr
        unfold colStep
        rw [ite_eq_left hr', ite_eq_left hc]
        unfold wedgeR
        rw [Finset.sum_eq_single mt]
        · congr 2
          have : (tauI n0 hN mt : Fin N) = ⟨n0 + t, hjN⟩ := by
            apply Fin.ext; simp only [tauI]; omega
          rw [this]
          apply kill_X_not
          intro hv
          apply hv.2
          simp only [mt]; omega
        · intro m _ hm
          have : kill (offN n0) (letVec R (N := N) (n := r) ⟨n0 + t, hjN⟩ m) = 0 := by
            apply kill_X_mem
            refine ⟨by simp, ?_⟩
            intro h
            apply hm
            apply hval
            simp only [add_tsub_cancel_left] at h
            omega
          beta_reduce
          rw [this]; ring
        · intro h; exact absurd hmJ h
      rw [hstep, he, hA, Finset.prod_insert hnot]
      refine ⟨(J.filter fun j => mt < j).card + e, ?_⟩
      have hset : J.erase mt \ riseA n0 ν c t = J \ insert mt (riseA n0 ν c t) := by
        ext m
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
        tauto
      rw [hset, pow_add]
      ring
    · have hA : riseA n0 ν c (t + 1) = riseA n0 ν c t := by
        ext m
        simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases h3 : r - 1 - m.val = t
          · rw [h3] at h2; exact absurd h2 hr
          · exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
      have heq : colH (stg ν (n0 + t)) c = colH (stg ν (n0 + t + 1)) c :=
        le_antisymm (hmono t htr) (not_lt.mp hr)
      rw [hA] at hJ ⊢
      obtain ⟨e, he⟩ := ih (by omega) J hJ
      refine ⟨e, ?_⟩
      unfold colStep
      rw [heq, ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]
      exact he

end Abs

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs2

variable {R : Type} [CommRing R] {N r : ℕ}

theorem colStep_same (c : ℤ) (h : ℕ) (x : Fin r → MvPolynomial (Fin N × Fin r) R)
    (Kf : Finset (Fin r) → MvPolynomial (Fin N × Fin r) R) : colStep c h h x Kf = Kf := by
  unfold colStep
  rw [ite_eq_right (lt_irrefl _), ite_eq_right (lt_irrefl _)]

theorem Kcol_const (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ N, (∀ i < j, colH (stg ν i) c = colH (stg ν (i + 1)) c) → Kcol R ν c j = extOne := by
  intro j
  induction j with
  | zero => intro _ _; rw [Kcol]
  | succ j ih =>
    intro hj h
    rw [Kcol_succ ν c j (by omega), h j (by omega), colStep_same]
    exact ih (by omega) fun i hi => h i (by omega)

def cutPath (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) : Fin (N + 1) → Fin r → ℤ := fun i => stg ν (min i.val n0)

theorem stg_cut (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (i : ℕ) (hi : i ≤ N) :
    stg (cutPath n0 ν) i = stg ν (min i n0) := by
  have : i < N + 1 := by omega
  simp [stg, cutPath, this]

theorem Kcol_cut (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ N, Kcol R (cutPath n0 ν) c j = Kcol R ν c (min j n0) := by
  intro j
  induction j with
  | zero => intro _; rw [Nat.zero_min, Kcol, Kcol]
  | succ j ih =>
    intro hj
    rw [Kcol_succ _ c j (by omega), stg_cut n0 ν j (by omega), stg_cut n0 ν (j + 1) hj, ih (by omega)]
    by_cases h : j + 1 ≤ n0
    · rw [min_eq_left h, min_eq_left (by omega : j ≤ n0), Kcol_succ ν c j (by omega)]
    · rw [min_eq_right (by omega : n0 ≤ j + 1), min_eq_right (by omega : n0 ≤ j), colStep_same]

theorem colH_all {μ : Fin r → ℤ} {c : ℤ} (h : ∀ m, c ≤ μ m) : colH μ c = r := by
  unfold colH
  rw [Finset.filter_true_of_mem fun m _ => h m, Finset.card_univ, Fintype.card_fin]

theorem colH_none {μ : Fin r → ℤ} {c : ℤ} (h : ∀ m, μ m < c) : colH μ c = 0 := by
  unfold colH
  rw [Finset.filter_false_of_mem fun m _ => not_le.mpr (h m), Finset.card_empty]

theorem colH_anti (μ : Fin r → ℤ) {c c' : ℤ} (h : c ≤ c') : colH μ c' ≤ colH μ c := by
  unfold colH
  exact Finset.card_le_card fun m hm => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    omega

structure PlHyp (n0 : ℕ) (be : ℤ) (ν : Fin (N + 1) → Fin r → ℤ) : Prop where
  rng : ∀ i ≤ N, ∀ m, 0 ≤ stg ν i m ∧ stg ν i m ≤ be
  fin : ∀ m, stg ν N m = be
  up : ∀ t < r, ∀ c, colH (stg ν (n0 + t)) c ≤ colH (stg ν (n0 + t + 1)) c ∧
    colH (stg ν (n0 + t + 1)) c ≤ colH (stg ν (n0 + t)) c + 1

def mT (t : ℕ) (ht : t < r) : Fin r := ⟨r - 1 - t, by omega⟩

theorem riseA_succ_pos (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : ℕ) (ht : t < r)
    (hr : rises ν c (n0 + t)) :
    riseA n0 ν c (t + 1) = insert (mT t ht) (riseA n0 ν c t) ∧ mT t ht ∉ riseA n0 ν c t := by
  classical
  have hmt : r - 1 - (mT t ht).val = t := by simp only [mT]; omega
  constructor
  · ext m
    simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : r - 1 - m.val = t
      · left
        apply Fin.ext
        have := m.isLt
        simp only [mT]; omega
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · subst h
        rw [hmt]; exact ⟨by omega, hr⟩
      · exact ⟨by omega, h2⟩
  · simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro h; rw [hmt] at h; omega

theorem riseA_succ_neg (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : ℕ)
    (hr : ¬ rises ν c (n0 + t)) : riseA n0 ν c (t + 1) = riseA n0 ν c t := by
  classical
  ext m
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h3 : r - 1 - m.val = t
    · rw [h3] at h2; exact absurd h2 hr
    · exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

theorem card_riseA {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    ∀ t ≤ r, colH (stg ν n0) c + (riseA n0 ν c t).card = colH (stg ν (n0 + t)) c := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    have : riseA n0 ν c 0 = ∅ := by simp [riseA]
    rw [this]; simp
  | succ t ih =>
    intro ht
    have htr : t < r := by omega
    have h := ih (by omega)
    obtain ⟨u1, u2⟩ := H.up t htr c
    by_cases hr : rises ν c (n0 + t)
    · obtain ⟨hA, hnot⟩ := riseA_succ_pos n0 ν c t htr hr
      rw [hA, Finset.card_insert_of_notMem hnot]
      have hr' : colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c := hr
      rw [show n0 + (t + 1) = n0 + t + 1 by ring]
      omega
    · rw [riseA_succ_neg n0 ν c t hr]
      have hr' : ¬ colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c := hr
      rw [show n0 + (t + 1) = n0 + t + 1 by ring]
      omega

theorem pEnd_eq (ν : Fin (N + 1) → Fin r → ℤ) : pEnd ν = stg ν N := by
  unfold pEnd
  rw [← stg_eq ν N (by omega)]
  rfl

theorem Ican_eq [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    Ican ν c = if 1 ≤ c ∧ c ≤ be then Finset.univ else ∅ := by
  classical
  have hbe : 0 ≤ be := by
    have := (H.rng N le_rfl 0).1
    rwa [H.fin] at this
  unfold Ican
  rw [pEnd_eq]
  by_cases h1 : 1 ≤ c
  · rw [ite_eq_left h1]
    by_cases h2 : c ≤ be
    · rw [ite_eq_left ⟨h1, h2⟩, colH_all fun m => by rw [H.fin]; exact h2]
      exact Finset.filter_true_of_mem fun m _ => m.isLt
    · rw [ite_eq_right (fun h => h2 h.2), colH_none fun m => by rw [H.fin]; omega]
      exact Finset.filter_false_of_mem fun m _ => by omega
  · rw [ite_eq_right h1, ite_eq_right (fun h => h1 h.1), colH_all fun m => by rw [H.fin]; omega]
    exact Finset.filter_false_of_mem fun m _ => by have := m.isLt; omega

def Icut (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) : ℤ → Finset (Fin r) := fun c => Ican ν c \ riseA n0 ν c r

theorem Kcol_inactive {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ)
    (hc : ¬ (1 ≤ c ∧ c ≤ be)) (j : ℕ) (hj : j ≤ N) : Kcol R ν c j = extOne := by
  apply Kcol_const ν c j hj
  intro i hi
  by_cases h1 : 1 ≤ c
  · have h2 : be < c := by
      by_contra h; exact hc ⟨h1, by omega⟩
    rw [colH_none fun m => lt_of_le_of_lt (H.rng i (by omega) m).2 h2,
      colH_none fun m => lt_of_le_of_lt (H.rng (i + 1) (by omega) m).2 h2]
  · rw [colH_all fun m => le_trans (by omega) (H.rng i (by omega) m).1,
      colH_all fun m => le_trans (by omega) (H.rng (i + 1) (by omega) m).1]

theorem extOne_empty {P : Type} [CommRing P] : (extOne (n := r) (P := P) ∅) = 1 := by
  simp [extOne]

theorem mem_colRange_of_le_entry (μ : Fin (N + 1) → Fin r → ℤ) (i : Fin (N + 1)) (m : Fin r) {c : ℤ} (h1 : 0 ≤ c)
    (h2 : c ≤ μ i m) : c ∈ colRange μ := by
  unfold colRange
  have hT : |μ i m| ≤ ∑ i, ∑ m, |μ i m| := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ m, |μ i m|)
      (fun i _ => Finset.sum_nonneg fun m _ => abs_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun m => |μ i m|) (fun m _ => abs_nonneg _) (Finset.mem_univ m)
  have := le_abs_self (μ i m)
  simp only [Finset.mem_Icc]
  constructor <;> omega

theorem Psi_full [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    Psi R ν (Ican ν) = ∏ c ∈ Finset.Icc 1 be, Kcol R ν c N Finset.univ := by
  classical
  unfold Psi
  symm
  have hsub : Finset.Icc 1 be ⊆ colRange ν := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    refine mem_colRange_of_le_entry ν (Fin.last N) 0 (by omega) ?_
    have := H.fin 0
    rw [← stg_eq ν N (by omega)] at this
    have h' : ν (Fin.last N) 0 = be := this
    rw [h']; exact hc.2
  rw [← Finset.prod_subset hsub]
  · refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_Icc] at hc
    rw [Ican_eq H, ite_eq_left hc]
  · intro c _ hc
    rw [Finset.mem_Icc] at hc
    rw [Ican_eq H, ite_eq_right hc, Kcol_inactive H c hc N le_rfl, extOne_empty]

theorem Psi_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    Psi R (cutPath n0 ν) (Icut n0 ν) = ∏ c ∈ Finset.Icc 1 be, Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r) := by
  classical
  unfold Psi
  have hterm : ∀ c, Kcol R (cutPath n0 ν) c N (Icut n0 ν c) =
      if 1 ≤ c ∧ c ≤ be then Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r) else 1 := by
    intro c
    rw [Kcol_cut n0 ν c N le_rfl, min_eq_right (by omega : n0 ≤ N)]
    unfold Icut
    rw [Ican_eq H]
    split_ifs with h
    · rfl
    · rw [Finset.empty_sdiff, Kcol_inactive H c h n0 (by omega), extOne_empty]
  rw [Finset.prod_congr rfl fun c _ => hterm c]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one]

  have hsub : (colRange (cutPath n0 ν)).filter (fun c => 1 ≤ c ∧ c ≤ be) ⊆ Finset.Icc 1 be := by
    intro c hc
    rw [Finset.mem_filter] at hc
    exact Finset.mem_Icc.mpr hc.2
  refine Finset.prod_subset hsub ?_
  intro c hc hnot
  rw [Finset.mem_Icc] at hc
  have hout : c ∉ colRange (cutPath n0 ν) := fun h => hnot (Finset.mem_filter.mpr ⟨h, hc⟩)
  have hlow : ∀ i ≤ n0, ∀ m, stg ν i m < c := by
    intro i hi m
    by_contra hge
    apply hout
    refine mem_colRange_of_le_entry (cutPath n0 ν) ⟨i, by omega⟩ m (by omega) ?_
    have : cutPath n0 ν ⟨i, by omega⟩ m = stg ν i m := by
      simp [cutPath, min_eq_left hi]
    rw [this]; omega
  have h0 : colH (stg ν n0) c = 0 := colH_none (hlow n0 le_rfl)
  have hcard := card_riseA H c r le_rfl
  rw [h0, hN, colH_all fun m => by rw [H.fin]; exact hc.2, zero_add] at hcard
  have hall : riseA n0 ν c r = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard, Fintype.card_fin]
  rw [hall, Finset.sdiff_self, Kcol_const ν c n0 (by omega) fun i hi => by
    rw [colH_none (hlow i (by omega)), colH_none (hlow (i + 1) (by omega))], extOne_empty]

theorem kill_Psi [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    ∃ e : ℕ, kill (offN n0) (Psi R ν (Ican ν)) =
      (-1) ^ e * (∏ c ∈ Finset.Icc 1 be, ∏ m ∈ riseA n0 ν c r, MvPolynomial.X (tauI n0 hN m, m)) *
        Psi R (cutPath n0 ν) (Icut n0 ν) := by
  classical
  rw [Psi_full H, Psi_cut hN H, map_prod]
  have hcol : ∀ c ∈ Finset.Icc 1 be, ∃ e : ℕ, kill (offN n0) (Kcol R ν c N Finset.univ) =
      (-1) ^ e * (∏ m ∈ riseA n0 ν c r, MvPolynomial.X (tauI n0 hN m, m)) *
        Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    have := kill_Kcol_tau (R := R) n0 hN ν c hc.1 (fun t ht => (H.up t ht c).1) r le_rfl Finset.univ
      (Finset.subset_univ _)
    rwa [hN] at this
  choose! e he using hcol
  refine ⟨∑ c ∈ Finset.Icc 1 be, e c, ?_⟩
  rw [Finset.prod_congr rfl he, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

end Abs2

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Dict

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ}

theorem kfr_le (hV : F.Valid L₁ N₁) (j : ℤ) {a b : ℕ} (hab : a ≤ b) (hb : b < r) : F.fr j a ≤ F.fr j b :=
  TE.fr_le hV j a b hab hb

theorem k_fr_mem_letters (hV : F.Valid L₁ N₁) (j : ℤ) {t : ℕ} (ht : t < r) : F.fr j t ∈ F.letters j :=
  letI : NeZero r := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt ht)⟩
  TE.frj_mem hV j t ht

theorem k_r_le_segN (hV : F.Valid L₁ N₁) (hr : 0 < r) (j : ℤ) : r ≤ segN F j :=
  letI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  TE.r_le_segN hV j

theorem segE_eq_fr_iff (hV : F.Valid L₁ N₁) (j : ℤ) (i : Fin (segN F j)) {t : ℕ} (ht : t < r) :
    segE F j i = F.fr j t ↔ i.val = segN F j - r + t :=
  letI : NeZero r := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt ht)⟩
  TE.dict_tau hV i ⟨t, ht⟩

theorem segE_lt_fr_iff (hV : F.Valid L₁ N₁) (hr : 0 < r) (j : ℤ) (i : Fin (segN F j)) :
    segE F j i < F.fr j 0 ↔ i.val < segN F j - r :=
  letI : NeZero r := ⟨Nat.ne_of_gt hr⟩
  TE.dict_early hV i

end Dict

section Supp

variable {R : Type} [CommRing R] {N r : ℕ}

theorem Kcol_supported (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ N, ∀ J, Kcol R ν c j J ∈ supported R {v : Fin N × Fin r | v.1.val < j} := by
  intro j
  induction j with
  | zero =>
    intro _ J
    rw [Kcol.eq_1]
    unfold extOne
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ j ih =>
    intro hj J
    have hS : ∀ J', Kcol R ν c j J' ∈ supported R {v : Fin N × Fin r | v.1.val < j + 1} := by
      intro J'
      refine supported_mono (fun v hv => ?_) (ih (by omega) J')
      simp only [Set.mem_setOf_eq] at hv ⊢
      omega
    have hx : ∀ m, letVec R ⟨j, by omega⟩ m ∈ supported R {v : Fin N × Fin r | v.1.val < j + 1} := by
      intro m
      show X ((⟨j, by omega⟩ : Fin N), m) ∈ Algebra.adjoin R (X '' _)
      exact Algebra.subset_adjoin ⟨((⟨j, by omega⟩ : Fin N), m), by simp, rfl⟩
    rw [Kcol_succ ν c j (by omega)]
    unfold colStep wedgeR contrR
    split_ifs <;> first
      | exact hS J
      | exact sum_mem (fun m _ => mul_mem (mul_mem (pow_mem (neg_mem (one_mem _)) _) (hx m)) (hS _))

theorem Psi_cut_supported (n0 : ℕ) (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) (I : ℤ → Finset (Fin r)) :
    Psi R (cutPath n0 ν) I ∈ supported R {v : Fin N × Fin r | v.1.val < n0} := by
  unfold Psi
  refine prod_mem (fun c _ => ?_)
  rw [Kcol_cut n0 ν c N le_rfl, min_eq_right hn]
  exact Kcol_supported ν c n0 hn (I c)

end Supp

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Gen6

variable {N r : ℕ}

theorem stg_castSucc (ν : Fin (N + 1) → Fin r → ℤ) (l : Fin N) : ν l.castSucc = stg ν l.val := by
  unfold stg
  rw [dite_eq_left (by have := l.isLt; omega)]
  rfl

theorem stg_succ (ν : Fin (N + 1) → Fin r → ℤ) (l : Fin N) : ν l.succ = stg ν (l.val + 1) := by
  unfold stg
  rw [dite_eq_left (by have := l.isLt; omega)]
  rfl

theorem stg_plPart {K : ℕ} (μ : Fin (N + 1) → Fin (r + K) → ℤ) (i : ℕ) (m : Fin r) :
    stg (plPart μ) i m = stg μ i (Fin.castAdd K m) := by
  unfold stg
  split_ifs <;> rfl

theorem colH_step {ν ν' : Fin r → ℤ} (hν : Antitone ν) (hν' : Antitone ν') (ha : ∀ a, ν a ≤ ν' a)
    (hb : ∀ (a : Fin r) (h : a.val + 1 < r), ν' ⟨a.val + 1, h⟩ ≤ ν a) (c : ℤ) :
    colH ν c ≤ colH ν' c ∧ colH ν' c ≤ colH ν c + 1 := by
  constructor
  · unfold colH
    apply Finset.card_le_card
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    exact le_trans hm (ha m)
  · unfold colH
    set S := Finset.univ.filter fun m => c ≤ ν m with hS
    set S' := Finset.univ.filter fun m => c ≤ ν' m with hS'
    have hsub : S'.image Fin.val ⊆ insert 0 (S.image fun a => a.val + 1) := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, S', S, Finset.mem_insert] at hx ⊢
      obtain ⟨m, hm, rfl⟩ := hx
      rcases Nat.eq_zero_or_pos m.val with h0 | hpos
      · left
        exact h0
      · right
        have hlt : m.val - 1 < r := by omega
        have h1 : (m.val - 1) + 1 < r := by omega
        have hm' : (⟨(m.val - 1) + 1, h1⟩ : Fin r) = m := Fin.ext (by simp; omega)
        refine ⟨⟨m.val - 1, hlt⟩, ?_, by simp; omega⟩
        have h2 := hb ⟨m.val - 1, hlt⟩ h1
        rw [hm'] at h2
        exact le_trans hm h2
    calc S'.card = (S'.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
      _ ≤ (insert 0 (S.image fun a => a.val + 1)).card := Finset.card_le_card hsub
      _ ≤ (S.image fun a => a.val + 1).card + 1 := Finset.card_insert_le _ _
      _ ≤ S.card + 1 := by
        have := Finset.card_image_le (s := S) (f := fun a : Fin r => a.val + 1)
        omega

theorem cut_ppath {LL : Letters (Fin N)} {b' : Fin N → ℕ} (P1 : PPath r N LL b') (n0 : ℕ) :
    ∃ bc, ∃ Pc : PPath r N LL bc, Pc.mu = cutPath n0 P1.mu := by
  classical
  have hdom : ∀ k, k < N + 1 → Antitone (stg P1.mu k) := by
    intro k hk
    rw [← stg_eq P1.mu k hk]; exact P1.dom _
  refine ⟨fun i => if i.val < n0 then b' i else 0, ⟨cutPath n0 P1.mu, ?_, ?_, ?_⟩, rfl⟩
  · show stg P1.mu (min (0 : Fin (N + 1)).val n0) = 0
    simp only [Fin.val_zero, Nat.zero_min]
    rw [← stg_eq P1.mu 0 (by omega)]
    exact P1.zero
  · intro i
    exact hdom _ (lt_of_le_of_lt (min_le_left _ _) i.isLt)
  · intro i
    have hi := i.isLt
    by_cases h : i.val < n0
    · have e1 : cutPath n0 P1.mu i.castSucc = P1.mu i.castSucc := by
        show stg P1.mu (min i.val n0) = _
        rw [min_eq_left (by omega), stg_castSucc P1.mu]
      have e2 : cutPath n0 P1.mu i.succ = P1.mu i.succ := by
        show stg P1.mu (min (i.val + 1) n0) = _
        rw [min_eq_left (by omega), stg_succ P1.mu]
      rw [e1, e2]
      simp only [h, ite_true]
      exact P1.step i
    · have e1 : cutPath n0 P1.mu i.castSucc = stg P1.mu n0 := by
        show stg P1.mu (min i.val n0) = _
        rw [min_eq_right (by omega)]
      have e2 : cutPath n0 P1.mu i.succ = stg P1.mu n0 := by
        show stg P1.mu (min (i.val + 1) n0) = _
        rw [min_eq_right (by omega)]
      rw [e1, e2]
      simp only [h, ite_false]
      have hs : HStrip (stg P1.mu n0) (stg P1.mu n0) 0 :=
        ⟨fun _ => le_rfl, fun a h' => hdom n0 (by omega) (by rw [Fin.le_def]; simp), by simp⟩
      split_ifs <;> exact hs

theorem joinPT_parts {K : ℕ} (μ : Fin (N + 1) → Fin (r + K) → ℤ) : joinPT (plPart μ) (tanPart μ) = μ := by
  funext i
  exact Fin.append_castAdd_natAdd

end Gen6

section Dat6

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

theorem dplus_le_beS (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) (s : ℕ) (hs : s ≤ segN X.F j - r) :
    T.dplus (segLL X.F j) dd s ≤ X.beS p K j b := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  unfold T.dplus Dat.beS
  have himg : (X.F.letters j).filter (· < X.F.fr j 0) =
      (Finset.univ.filter fun l : Fin (segN X.F j) => l.val < segN X.F j - r).image (segE X.F j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨i, rfl⟩ := segE_surj X.F j hx
      exact ⟨i, (segE_lt_fr_iff X.F hV hr j i).mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨segE_mem X.F j i, (segE_lt_fr_iff X.F hV hr j i).mpr hi⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.sum_filter]
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs with h1 h2 h2
  · rw [hP.degs l ((segE_lt_fr_iff X.F hV hr j l).mpr h2)]
  · omega
  · exact Nat.zero_le _
  · exact le_rfl

theorem plHyp_of (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) :
    PlHyp (segN X.F j - r) (X.beS p K j b : ℤ) (plPart μ) := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  obtain ⟨P, hPμ⟩ := hP.path
  have hrN : r ≤ segN X.F j := k_r_le_segN X.F hV hr j
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK

  have htau : ∀ t (ht : t < r), ∃ l : Fin (segN X.F j), l.val = segN X.F j - r + t ∧
      segE X.F j l = X.F.fr j t ∧ HStrip (stg μ (segN X.F j - r + t)) (stg μ (segN X.F j - r + t + 1)) (dd l) := by
    intro t ht
    let l : Fin (segN X.F j) := ⟨segN X.F j - r + t, by omega⟩
    have hl : segE X.F j l = X.F.fr j t := (segE_eq_fr_iff X.F hV j l ht).mpr rfl
    have hvec : (segLL X.F j).vec l = true := by
      rw [comb_vec, hl]; exact (hV.2.2.2.2.1 j t ht).2
    have hs := T.step_vec P l hvec
    rw [hPμ, stg_castSucc μ, stg_succ μ] at hs
    exact ⟨l, rfl, hl, hs⟩
  have hlow : ∀ i ≤ segN X.F j - r, ∀ m, stg μ i m ≤ (X.beS p K j b : ℤ) := by
    intro i hi m
    have h1 := T.mu_le_dplus P i (by omega) m
    rw [hPμ, stg_eq μ i (by omega)] at h1
    have h2 := dplus_le_beS X p K hX j b μ dd hP i hi
    exact le_trans h1 (by exact_mod_cast h2)
  have hup : ∀ t ≤ r, ∀ m, stg μ (segN X.F j - r + t) m ≤ (X.beS p K j b : ℤ) := by
    intro t
    induction t with
    | zero => intro _ m; exact hlow _ le_rfl m
    | succ t ih =>
      intro ht m
      obtain ⟨l, hlv, hl, hs⟩ := htau t (by omega)
      rw [show segN X.F j - r + (t + 1) = segN X.F j - r + t + 1 by ring]
      by_cases hm : m.val = 0
      · have := hP.head l ⟨t, by omega⟩ hl m (by omega)
        rw [stg_succ μ, hlv] at this
        rw [this]
      · have hm' := m.isLt
        have h2 := hs.2.1 ⟨m.val - 1, by omega⟩ (by simp only []; omega)
        have e : (⟨(⟨m.val - 1, by omega⟩ : Fin (r + K)).val + 1, by simp only []; omega⟩ : Fin (r + K)) = m :=
          Fin.ext (by simp only []; omega)
        rw [e] at h2
        exact le_trans h2 (ih (by omega) _)
  have hdom : ∀ k, k < segN X.F j + 1 → Antitone (stg (plPart μ) k) := by
    intro k hk a a' haa
    rw [stg_plPart, stg_plPart, ← stg_eq μ k hk, ← hPμ]
    exact P.dom _ (by rw [Fin.le_def]; simpa using haa)
  refine ⟨?_, ?_, ?_⟩
  · intro i hi m
    rw [stg_plPart]
    constructor
    · have h1 := T.mu_nonneg P i (by omega) (Fin.castAdd K m) (by
        have := m.isLt
        simp only [Fin.val_castAdd]; omega)
      rwa [hPμ, stg_eq μ i (by omega)] at h1
    · by_cases h : i ≤ segN X.F j - r
      · exact hlow i h _
      · have := hup (i - (segN X.F j - r)) (by omega) (Fin.castAdd K m)
        rwa [show segN X.F j - r + (i - (segN X.F j - r)) = i by omega] at this
  · intro m
    rw [stg_plPart]
    obtain ⟨l, hlv, hl, -⟩ := htau (r - 1) (by omega)
    have := hP.head l ⟨r - 1, by omega⟩ hl (Fin.castAdd K m) (by
      have := m.isLt
      simp only [Fin.val_castAdd]; omega)
    rw [stg_succ μ, hlv, show segN X.F j - r + (r - 1) + 1 = segN X.F j by omega] at this
    exact this
  · intro t ht c
    obtain ⟨l, hlv, hl, hs⟩ := htau t ht
    refine colH_step (hdom _ (by omega)) (hdom _ (by omega)) ?_ ?_ c
    · intro a
      rw [stg_plPart, stg_plPart]
      exact hs.1 _
    · intro a h
      rw [stg_plPart, stg_plPart]
      have := hs.2.1 (Fin.castAdd K a) (by simp only [Fin.val_castAdd]; omega)
      exact this

end Dat6

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

def BetaRatioBound (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b → 4 * X.Y * (X.beS p K j (X.restr j b) : ℝ) ≤ (X.Qc p K j : ℝ)

def TauDegreeOnPathBound : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K →
    ∀ (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) (dd : Fin (segN X.F j) → ℕ),
      X.IsPATH p K j b μ dd → ∀ i, X.F.fr j 0 ≤ segE X.F j i → dd i ≤ 2 * X.beS p K j b

def ResidueClassCount : Prop :=
  ∀ (r Q be c ρ : ℕ), 2 ≤ r → 2 * be < Q →
    (Q : ℝ) ^ (r - 1) * (1 - 2 * r * be / Q) ≤
      (((Fintype.piFinset fun _ : Fin r => Finset.range (Q - 2 * be)).filter
        fun w => (c + ∑ i, w i) % Q = ρ % Q).card : ℝ)

section Congr

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ) [NeZero K]

theorem Bdeg_congr (j : ℤ) {b b' : ℤ → ℕ} (x : ℤ) (h : b x = b' x) : X.Bdeg p K j b x = X.Bdeg p K j b' x := by
  unfold Dat.Bdeg
  rw [h]

theorem beS_congr (j : ℤ) {b b' : ℤ → ℕ} (h : ∀ x, x < X.F.fr j 0 → b x = b' x) :
    X.beS p K j b = X.beS p K j b' := by
  unfold Dat.beS
  refine Finset.sum_congr rfl fun x hx => ?_
  exact Bdeg_congr X p K j x (h x (Finset.mem_filter.mp hx).2)

theorem IsPATH_congr (j : ℤ) {b b' : ℤ → ℕ} (h : ∀ x, x < X.F.fr j 0 → b x = b' x)
    {μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ} {dd : Fin (segN X.F j) → ℕ} (hP : X.IsPATH p K j b μ dd) :
    X.IsPATH p K j b' μ dd :=
  ⟨hP.path, fun i hi => by rw [hP.degs i hi]; exact Bdeg_congr X p K j _ (h _ hi),
    fun i i' hi m hm => by rw [hP.head i i' hi m hm, beS_congr X p K j h]⟩

theorem IsGood_congr (hX : X.Hyp p K) (j : ℤ) {b b' : ℤ → ℕ} (h : ∀ x, x < X.F.fr j 0 → b x = b' x)
    {μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ} (hG : X.IsGood p K j b μ) : X.IsGood p K j b' μ := by
  classical
  intro i hi
  have hlate : segE X.F j i ∈ X.toLate j := Finset.mem_filter.mpr ⟨segE_mem X.F j i, hi⟩
  have hold := (oldest_letter_in_segment p n' r K X hX j _ hlate).2
  have hth : X.thc p K j b' (segE X.F j i) = X.thc p K j b (segE X.F j i) := by
    unfold Dat.thc
    split_ifs with hW
    · rfl
    · have hLL := hold hW
      unfold Frames.LLset at hLL
      have hlt := (Finset.mem_Ioo.mp (Finset.mem_filter.mp hLL).1).2
      rw [h _ hlt]
  rw [hth]
  exact hG i hi

theorem restr_setTau_low (j : ℤ) (b : ℤ → ℕ) (e : Fin r → ℕ) (x : ℤ) (hx : x < X.F.fr j 0) :
    X.restr j b x = X.restr j (X.setTau j b e) x := by
  unfold Dat.restr Dat.setTau
  have : ¬ (X.F.fr j 0 ≤ x ∧ x ≤ X.F.fr j (r - 1)) := fun h => by omega
  simp only [this, ite_false]

theorem restr_setTau_tau (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (e : Fin r → ℕ) (i' : Fin r) :
    X.restr j (X.setTau j b e) (X.F.fr j i'.val) = e i' := by
  classical
  have hV := hX.valid
  have hmem := k_fr_mem_letters X.F hV j i'.isLt
  have h4 := hV.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h4
  have a2 := kfr_le X.F hV j (Nat.zero_le i'.val) i'.isLt
  have a3 := kfr_le X.F hV j (by have := i'.isLt; omega : i'.val ≤ r - 1) (by have := i'.isLt; omega)
  have hlate : X.F.fr j i'.val ∈ X.toLate j := by
    refine Finset.mem_filter.mpr ⟨hmem, ?_⟩
    unfold Frames.IsW
    omega
  unfold Dat.restr Dat.setTau
  rw [ite_eq_left hlate, ite_eq_left ⟨a2, a3⟩, Finset.sum_eq_single i']
  · simp
  · intro i _ hne
    rw [ite_eq_right]
    intro h
    exact hne (fr_injective X.F hV j h).symm
  · intro h; exact absurd (Finset.mem_univ _) h

end Congr

theorem restMon_of (C₀ : ℝ) (h61 : BetaRatioBound C₀) (h21 : TauDegreeOnPathBound) (h63 : ResidueClassCount) : RestMon C₀ := by
  intro p n' r K _ _ _ X hX hLa hk j b hA hfin ρ
  classical
  have hV := hX.valid
  have hr : 0 < r := NeZero.pos r
  have hY : (1 : ℝ) ≤ X.Y := hX.Y1
  have hrhs : (0 : ℝ) ≤ ∑ e ∈ Fintype.piFinset fun i : Fin r =>
      (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j,
        (Nat.card (X.Idx p K j (X.restr j (X.setTau j b e))) : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  rcases le_or_gt (1 - (r : ℝ) / (2 * X.Y)) 0 with hneg | hpos
  · rw [max_eq_left hneg, mul_zero, zero_pow hr.ne', mul_zero]
    exact hrhs
  rw [max_eq_right hpos.le]
  set be := X.beS p K j (X.restr j b) with hbe
  set Q := X.Qc p K j with hQ
  have hQpos : 0 < Q := by
    rw [hQ]; unfold Dat.Qc
    exact pow_pos hX.prime.pos _
  have hbeQ : 4 * X.Y * (be : ℝ) ≤ (Q : ℝ) := h61 p n' r K X hX hLa hk j b hA
  have hbeQ' : 4 * be ≤ Q := by
    have : (4 : ℝ) * (be : ℝ) ≤ (Q : ℝ) := by nlinarith [Nat.cast_nonneg (α := ℝ) be]
    exact_mod_cast this
  obtain ⟨T, hT⟩ : ∃ T, Q = T + 2 * be := ⟨Q - 2 * be, by omega⟩
  have hTpos : 0 < T := by omega
  have hrN := k_r_le_segN X.F hV hr j
  let idxT : Fin r → Fin (segN X.F j) := fun i' => ⟨segN X.F j - r + i'.val, by have := i'.isLt; omega⟩
  have hidx : ∀ i', segE X.F j (idxT i') = X.F.fr j i'.val := fun i' =>
    (segE_eq_fr_iff X.F hV j _ i'.isLt).mpr rfl
  have := Fintype.ofFinite (X.Tset p K j (X.restr j b))
  let ddOf : X.Tset p K j (X.restr j b) → Fin (segN X.F j) → ℕ := fun τ => Classical.choose τ.2
  have hdd : ∀ τ : X.Tset p K j (X.restr j b), X.IsPATH p K j (X.restr j b) τ.1.1 (ddOf τ) ∧
      X.IsGood p K j (X.restr j b) τ.1.1 ∧ IsSt (tanPart τ.1.1) τ.1.2 := fun τ => Classical.choose_spec τ.2
  let dtau : X.Tset p K j (X.restr j b) → Fin r → ℕ := fun τ i' => ddOf τ (idxT i')
  have hdtau : ∀ τ i', dtau τ i' ≤ 2 * be := by
    intro τ i'
    refine h21 p n' r K X hX j _ _ _ (hdd τ).1 (idxT i') ?_
    rw [hidx]
    exact kfr_le X.F hV j (Nat.zero_le _) i'.isLt
  let Wfin : Finset (Fin r → ℕ) := Fintype.piFinset fun _ : Fin r => Finset.range T
  let Ufin : Finset (Fin r × Fin r → ℕ) := Fintype.piFinset fun _ : Fin r × Fin r => Finset.range T
  let φ : X.Tset p K j (X.restr j b) × (Fin r × Fin r → ℕ) → Fin r → ℕ := fun x i' =>
    dtau x.1 i' + ∑ c, x.2 (i', c)
  let A : Finset (X.Tset p K j (X.restr j b) × (Fin r × Fin r → ℕ)) :=
    ((Finset.univ : Finset (X.Tset p K j (X.restr j b))) ×ˢ Ufin).filter fun x => ∀ i', φ x i' % Q = ρ i' % Q
  set E := Fintype.piFinset fun i : Fin r => (Finset.range (r * Q)).filter fun e => e % Q = ρ i % Q with hE
  set cst : ℝ := (Q : ℝ) ^ (r - 1) * (1 - (r : ℝ) / (2 * X.Y)) with hcst
  have hcst0 : 0 ≤ cst := by positivity

  have hφE : ∀ x ∈ A, φ x ∈ E := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    have hu := (Finset.mem_product.mp hx1).2
    rw [Fintype.mem_piFinset] at hu
    rw [hE, Fintype.mem_piFinset]
    intro i'
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hx2 i'⟩
    have h1 : ∑ c, x.2 (i', c) ≤ r * (T - 1) := by
      have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin r)) (fun c => x.2 (i', c)) (T - 1) (by
        intro c _
        have := Finset.mem_range.mp (hu (i', c))
        omega)
      simpa using this
    have h2 := hdtau x.1 i'
    have h3 : r * (T - 1) + r = r * T := by
      obtain ⟨T', rfl⟩ : ∃ T', T = T' + 1 := ⟨T - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; ring
    have h4 : 2 * be ≤ r * (2 * be) := Nat.le_mul_of_pos_left _ hr
    have h5 : r * Q = r * T + r * (2 * be) := by rw [hT]; ring
    show dtau x.1 i' + ∑ c, x.2 (i', c) < r * Q
    omega

  have hfib : ∀ e ∈ E, (A.filter fun x => φ x = e).card ≤ Nat.card (X.Idx p K j (X.restr j (X.setTau j b e))) := by
    intro e _
    have hlow := restr_setTau_low X j b e
    have hbe' : X.beS p K j (X.restr j (X.setTau j b e)) = be := (beS_congr X p K j hlow).symm
    have hfinI : Finite (X.Idx p K j (X.restr j (X.setTau j b e))) := by
      let g : X.Idx p K j (X.restr j (X.setTau j b e)) →
          X.Tset p K j (X.restr j b) × (Fin r × Fin r → Fin Q) := fun q =>
        (⟨(q.1.1, q.1.2.1), by
          obtain ⟨dd, h1, h2, h3, -⟩ := q.2
          exact ⟨dd, IsPATH_congr X p K j (fun x hx => (hlow x hx).symm) h1,
            IsGood_congr X p K hX j (fun x hx => (hlow x hx).symm) h2, h3⟩⟩,
          fun v => ⟨q.1.2.2 v, by
            obtain ⟨dd, -, -, -, h4, -⟩ := q.2
            have := h4 v
            omega⟩)
      refine Finite.of_injective g ?_
      intro q q' hqq
      have h1 : q.1.1 = q'.1.1 := congrArg (fun z => z.1.1.1) hqq
      have h2 : q.1.2.1 = q'.1.2.1 := congrArg (fun z => z.1.1.2) hqq
      refine Subtype.ext (Prod.ext h1 (Prod.ext h2 ?_))
      funext v
      exact congrArg (fun z => (z.2 v).val) hqq
    let g : {x // x ∈ A.filter fun x => φ x = e} → X.Idx p K j (X.restr j (X.setTau j b e)) := fun x =>
      ⟨(x.1.1.1.1, x.1.1.1.2, x.1.2), by
        obtain ⟨hxA, hxe⟩ := Finset.mem_filter.mp x.2
        obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hxA
        have hu := (Finset.mem_product.mp hx1).2
        rw [Fintype.mem_piFinset] at hu
        refine ⟨ddOf x.1.1, IsPATH_congr X p K j hlow (hdd x.1.1).1, IsGood_congr X p K hX j hlow (hdd x.1.1).2.1,
          (hdd x.1.1).2.2, ?_, ?_⟩
        · intro v
          rw [hbe']
          have := Finset.mem_range.mp (hu v)
          show x.1.2 v + 2 * be < Q
          omega
        · intro i i' hi
          have hii : i = idxT i' := (segE_strictMono X.F j).injective (hi.trans (hidx i').symm)
          rw [restr_setTau_tau X p K hX j b e i', hii]
          exact congrFun hxe i'⟩
    have hg : Function.Injective g := by
      intro x x' hxx
      have h1 : x.1.1.1.1 = x'.1.1.1.1 := congrArg (fun z => z.1.1) hxx
      have h2 : x.1.1.1.2 = x'.1.1.1.2 := congrArg (fun z => z.1.2.1) hxx
      have h3 : x.1.2 = x'.1.2 := congrArg (fun z => z.1.2.2) hxx
      exact Subtype.ext (Prod.ext (Subtype.ext (Prod.ext h1 h2)) h3)
    have := Nat.card_le_card_of_injective g hg
    rwa [Nat.card_eq_fintype_card, Fintype.card_coe] at this

  have hcount : ∀ τ : X.Tset p K j (X.restr j b), cst ^ r ≤ ((A.filter fun x => x.1 = τ).card : ℝ) := by
    intro τ
    have h1 : ∀ i' : Fin r, cst ≤ ((Wfin.filter fun w => (dtau τ i' + ∑ c, w c) % Q = ρ i' % Q).card : ℝ) := by
      intro i'
      have h63' := h63 r Q be (dtau τ i') (ρ i') hX.r2 (by omega)
      rw [show Q - 2 * be = T by omega] at h63'
      refine le_trans ?_ h63'
      rw [hcst]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hQr : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast hQpos
      have : 2 * (r : ℝ) * (be : ℝ) / Q ≤ (r : ℝ) / (2 * X.Y) := by
        rw [div_le_div_iff₀ hQr (by positivity)]
        nlinarith
      linarith
    have h2 : (Fintype.piFinset fun i' : Fin r =>
        Wfin.filter fun w => (dtau τ i' + ∑ c, w c) % Q = ρ i' % Q).card ≤ (A.filter fun x => x.1 = τ).card := by
      refine Finset.card_le_card_of_injOn (fun w => (τ, fun v : Fin r × Fin r => w v.1 v.2)) ?_ ?_
      · intro w hw
        have hw' := Fintype.mem_piFinset.mp (Finset.mem_coe.mp hw)
        refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_univ _, Fintype.mem_piFinset.mpr fun v => ?_⟩, fun i' => ?_⟩, rfl⟩)
        · exact Fintype.mem_piFinset.mp (Finset.mem_filter.mp (hw' v.1)).1 v.2
        · exact (Finset.mem_filter.mp (hw' i')).2
      · intro w _ w' _ hww
        simp only [Prod.mk.injEq, true_and] at hww
        funext a c
        exact congrFun hww (a, c)
    rw [Fintype.card_piFinset] at h2
    have h3 : cst ^ r ≤ ∏ i' : Fin r, ((Wfin.filter fun w => (dtau τ i' + ∑ c, w c) % Q = ρ i' % Q).card : ℝ) := by
      have : cst ^ r = ∏ _i' : Fin r, cst := by simp
      rw [this]
      exact Finset.prod_le_prod₀ (fun _ _ => hcst0) fun i' _ => h1 i'
    refine le_trans h3 ?_
    exact_mod_cast h2
  have hA1 : A.card = ∑ τ : X.Tset p K j (X.restr j b), (A.filter fun x => x.1 = τ).card :=
    Finset.card_eq_sum_card_fiberwise fun x _ => Finset.mem_coe.mpr (Finset.mem_univ _)
  have hA2 : A.card = ∑ e ∈ E, (A.filter fun x => φ x = e).card :=
    Finset.card_eq_sum_card_fiberwise fun x hx => Finset.mem_coe.mpr (hφE x (Finset.mem_coe.mp hx))
  have hstep1 : (Nat.card (X.Tset p K j (X.restr j b)) : ℝ) * cst ^ r ≤ (A.card : ℝ) := by
    rw [hA1, Nat.card_eq_fintype_card]
    push_cast
    have : (Fintype.card (X.Tset p K j (X.restr j b)) : ℝ) * cst ^ r =
        ∑ _τ : X.Tset p K j (X.restr j b), cst ^ r := by
      simp
    rw [this]
    exact Finset.sum_le_sum fun τ _ => hcount τ
  refine le_trans hstep1 ?_
  rw [hA2]
  push_cast
  exact Finset.sum_le_sum fun e he => by exact_mod_cast hfib e he

end
end Formalism.MainNotions.SelectionLemmas.Pf

section
open scoped BigOperators TensorProduct
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

def ResidueClassLowerBound : Prop :=
  ∀ (r Q be c : ℕ), 2 ≤ r → 2 * be < Q →
    (Q : ℝ) ^ (r - 1) * (1 - 2 * r * be / Q) ≤
      (((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter
        (fun u => (∑ l, (u l : ℕ)) % Q = c % Q)).card : ℝ)

end Formalism.InvariantFactorPaths.BranchingDimensions
end

section
open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.BranchingDimensions

section Residue

def cnt (T Q r c : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin r → Fin T)).filter (fun u => (∑ l, (u l : ℕ)) % Q = c % Q)).card

lemma shift_iff (Q a s c : ℕ) (hQ : 1 ≤ Q) :
    (a + s) % Q = c % Q ↔ s % Q = (c + (Q - 1) * a) % Q := by
  obtain ⟨R, rfl⟩ : ∃ R, Q = R + 1 := ⟨Q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  constructor
  · intro h
    have h0 : Nat.ModEq (R + 1) (a + s) c := h
    have h1 : Nat.ModEq (R + 1) (a + s + R * a) (c + R * a) := h0.add_right (R * a)
    have h2 : a + s + R * a = s + (R + 1) * a := by ring
    rw [h2] at h1
    have h3 : (s + (R + 1) * a) % (R + 1) = (c + R * a) % (R + 1) := h1
    rw [Nat.add_mul_mod_self_left] at h3
    exact h3
  · intro h
    have h0 : Nat.ModEq (R + 1) s (c + R * a) := h
    have h1 : Nat.ModEq (R + 1) (a + s) (a + (c + R * a)) := h0.add_left a
    have h2 : a + (c + R * a) = c + (R + 1) * a := by ring
    rw [h2] at h1
    have h3 : (a + s) % (R + 1) = (c + (R + 1) * a) % (R + 1) := h1
    rw [Nat.add_mul_mod_self_left] at h3
    exact h3

lemma cnt_succ (T Q r c : ℕ) (hQ : 1 ≤ Q) :
    cnt T Q (r + 1) c = ∑ a : Fin T, cnt T Q r (c + (Q - 1) * a) := by
  have hbij : Function.Bijective
      (fun p : Fin T × (Fin r → Fin T) => (Fin.cons p.1 p.2 : Fin (r + 1) → Fin T)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun u => (u 0, Fin.tail u), fun p => ?_, fun u => ?_⟩
    · simp
    · simp
  simp only [cnt, Finset.card_filter]
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective _ hbij _ _ (fun p => ?_)
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  exact if_congr (shift_iff _ _ _ _ hQ).symm rfl rfl

lemma cnt_one (T Q c : ℕ) (hT : T ≤ Q) : cnt T Q 1 c = if c % Q < T then 1 else 0 := by
  have hbij : Function.Bijective (fun a : Fin T => (fun _ : Fin 1 => a)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun u => u 0, fun a => rfl, fun u => ?_⟩
    funext i
    rw [Subsingleton.elim i 0]
  have step : (∑ u : Fin 1 → Fin T, if (∑ l, (u l : ℕ)) % Q = c % Q then 1 else 0) =
      ∑ a : Fin T, if (a : ℕ) = c % Q then 1 else 0 := by
    symm
    refine Fintype.sum_bijective _ hbij _ _ (fun a => ?_)
    simp only [Fin.sum_univ_one]
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le a.isLt hT)]
  unfold cnt
  rw [Finset.card_filter, step]
  by_cases h : c % Q < T
  · rw [ite_eq_left h, Finset.sum_eq_single (⟨c % Q, h⟩ : Fin T)]
    · simp
    · intro b _ hb
      exact ite_eq_right (fun e => hb (Fin.ext e))
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  · rw [ite_eq_right h]
    apply Finset.sum_eq_zero
    intro a _
    exact ite_eq_right (fun e => h (lt_of_eq_of_lt e.symm a.isLt))

private theorem eq_of_add_pred_mul_mod_eq_of_lt (Q c a b : ℕ) (hQ : 1 ≤ Q) (ha : a < Q) (hb : b < Q)
    (h : (c + (Q - 1) * a) % Q = (c + (Q - 1) * b) % Q) : a = b := by
  have h1 : (a + (c + (Q - 1) * a) % Q) % Q = c % Q :=
    (shift_iff Q a _ c hQ).2 (Nat.mod_mod _ _)
  have h2 : (b + (c + (Q - 1) * a) % Q) % Q = c % Q :=
    (shift_iff Q b _ c hQ).2 (by rw [Nat.mod_mod, h])
  have h3 : Nat.ModEq Q (a + (c + (Q - 1) * a) % Q) (b + (c + (Q - 1) * a) % Q) :=
    h1.trans h2.symm
  have h4 : Nat.ModEq Q a b := Nat.ModEq.add_right_cancel' _ h3
  have h5 : a % Q = b % Q := h4
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h5

lemma cnt_two (T Q c : ℕ) (hQ : 1 ≤ Q) (hT : T ≤ Q) : T - (Q - T) ≤ cnt T Q 2 c := by
  have h2 : cnt T Q 2 c = ∑ a : Fin T, cnt T Q 1 (c + (Q - 1) * a) :=
    cnt_succ T Q 1 c hQ
  rw [h2]
  simp only [cnt_one T Q _ hT]
  have hsplit : (∑ a : Fin T, if (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) +
      ((Finset.univ : Finset (Fin T)).filter
        (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card = T := by
    rw [Finset.card_filter, ← Finset.sum_add_distrib]
    have hone : ∀ a : Fin T, ((if (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) +
        (if ¬ (c + (Q - 1) * (a : ℕ)) % Q < T then 1 else 0) : ℕ) = 1 := by
      intro a
      by_cases h : (c + (Q - 1) * (a : ℕ)) % Q < T <;> simp [h]
    simp only [hone, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  have hle : ((Finset.univ : Finset (Fin T)).filter
      (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card ≤ Q - T := by
    have hc : ((Finset.univ : Finset (Fin T)).filter
        (fun a : Fin T => ¬ (c + (Q - 1) * (a : ℕ)) % Q < T)).card ≤ (Finset.Ico T Q).card := by
      apply Finset.card_le_card_of_injOn (fun a : Fin T => (c + (Q - 1) * (a : ℕ)) % Q)
      · intro a ha
        have ha' : T ≤ (c + (Q - 1) * (a : ℕ)) % Q := by simpa using ha
        simp only [Finset.mem_coe, Finset.mem_Ico]
        exact ⟨ha', Nat.mod_lt _ (by omega)⟩
      · intro a _ b _ hab
        exact Fin.ext (eq_of_add_pred_mul_mod_eq_of_lt Q c a b hQ (lt_of_lt_of_le a.isLt hT)
          (lt_of_lt_of_le b.isLt hT) hab)
    rw [Nat.card_Ico] at hc
    exact hc
  omega

lemma cnt_ge (T Q : ℕ) (hQ : 1 ≤ Q) (hT : T ≤ Q) (s : ℕ) :
    ∀ c, T ^ s * (T - (Q - T)) ≤ cnt T Q (s + 2) c := by
  induction s with
  | zero =>
    intro c
    rw [pow_zero, one_mul]
    exact cnt_two T Q c hQ hT
  | succ s ih =>
    intro c
    rw [show s + 1 + 2 = (s + 2) + 1 by omega, cnt_succ T Q (s + 2) c hQ]
    calc T ^ (s + 1) * (T - (Q - T)) = ∑ _a : Fin T, T ^ s * (T - (Q - T)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
          ring
      _ ≤ ∑ a : Fin T, cnt T Q (s + 2) (c + (Q - 1) * a) :=
          Finset.sum_le_sum (fun a _ => ih _)

private theorem pow_mul_sub_natCast_add_two_mul_le_sub_pow_mul (q b : ℝ) (hb : 0 ≤ b) (hbq : b ≤ q) :
    ∀ m : ℕ, q ^ m * (q - ((m : ℝ) + 2) * b) ≤ (q - b) ^ m * (q - 2 * b) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hq : 0 ≤ q := le_trans hb hbq
    have h1 : (q - b) * (q ^ m * (q - ((m : ℝ) + 2) * b)) ≤ (q - b) * ((q - b) ^ m * (q - 2 * b)) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h2 : 0 ≤ q ^ m * (((m : ℝ) + 2) * b ^ 2) :=
      mul_nonneg (pow_nonneg hq m) (by positivity)
    calc q ^ (m + 1) * (q - (((m + 1 : ℕ) : ℝ) + 2) * b)
        = (q - b) * (q ^ m * (q - ((m : ℝ) + 2) * b)) - q ^ m * (((m : ℝ) + 2) * b ^ 2) := by
          push_cast
          ring
      _ ≤ (q - b) * ((q - b) ^ m * (q - 2 * b)) := by linarith
      _ = (q - b) ^ (m + 1) * (q - 2 * b) := by ring

theorem residueClassLowerBound : ResidueClassLowerBound := by
  intro r Q be c hr hQ
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  have hQpos : (0 : ℝ) < (Q : ℝ) := by exact_mod_cast (show 0 < Q by omega)
  have hQne : (Q : ℝ) ≠ 0 := ne_of_gt hQpos
  have key := cnt_ge (Q - 2 * be) Q (by omega) (by omega) m c
  have key' := (Nat.cast_le (α := ℝ)).mpr key
  refine le_trans ?_ key'
  have eq1 : (Q : ℝ) ^ (m + 1) * (1 - 2 * ((m + 2 : ℕ) : ℝ) * (be : ℝ) / (Q : ℝ)) =
      (Q : ℝ) ^ m * ((Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ))) := by
    have h : (Q : ℝ) ^ (m + 1) * (1 - 2 * ((m + 2 : ℕ) : ℝ) * (be : ℝ) / (Q : ℝ)) =
        (Q : ℝ) ^ m * (Q : ℝ) - (Q : ℝ) ^ m * (((m : ℝ) + 2) * (2 * (be : ℝ))) * ((Q : ℝ) / (Q : ℝ)) := by
      push_cast
      ring
    rw [h, div_self hQne, mul_one]
    ring
  rw [show m + 2 - 1 = m + 1 by omega]
  refine le_trans (le_of_eq eq1) ?_
  by_cases h4 : 2 * (2 * be) ≤ Q
  · have e1 : (Q - 2 * be) - (Q - (Q - 2 * be)) = Q - 2 * (2 * be) := by omega
    have c1 : ((Q - 2 * be : ℕ) : ℝ) = (Q : ℝ) - 2 * (be : ℝ) := by
      rw [Nat.cast_sub (show 2 * be ≤ Q by omega)] <;> push_cast <;> ring
    have c2 : ((Q - 2 * (2 * be) : ℕ) : ℝ) = (Q : ℝ) - 2 * (2 * (be : ℝ)) := by
      rw [Nat.cast_sub h4] <;> push_cast <;> ring
    rw [Nat.cast_mul, Nat.cast_pow, e1, c1, c2]
    exact pow_mul_sub_natCast_add_two_mul_le_sub_pow_mul (Q : ℝ) (2 * (be : ℝ)) (by positivity) (by exact_mod_cast hQ.le) m
  · have hneg : (Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ)) ≤ 0 := by
      have h1 : (Q : ℝ) ≤ 2 * (2 * (be : ℝ)) := by
        exact_mod_cast (show Q ≤ 2 * (2 * be) by omega)
      have h2 : (0 : ℝ) ≤ (m : ℝ) * (be : ℝ) := by positivity
      nlinarith
    have hp : (0 : ℝ) ≤ (Q : ℝ) ^ m := by positivity
    have hle : (Q : ℝ) ^ m * ((Q : ℝ) - ((m : ℝ) + 2) * (2 * (be : ℝ))) ≤ 0 := by
      nlinarith [mul_nonneg hp (neg_nonneg.mpr hneg)]
    exact le_trans hle (Nat.cast_nonneg _)

end Residue

end Formalism.InvariantFactorPaths.BranchingDimensions
end

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem residue_class_count : ResidueClassCount := by
  classical
  intro r Q be c ρ hr hQ
  have hQ0 : 0 < Q := by omega
  have hcore := Formalism.InvariantFactorPaths.BranchingDimensions.residueClassLowerBound r Q be (ρ % Q + (Q - c % Q)) hr hQ
  refine le_trans hcore ?_
  have hle : ((Finset.univ : Finset (Fin r → Fin (Q - 2 * be))).filter
      (fun u => (∑ l, (u l : ℕ)) % Q = (ρ % Q + (Q - c % Q)) % Q)).card ≤
      ((Fintype.piFinset fun _ : Fin r => Finset.range (Q - 2 * be)).filter
        fun w => (c + ∑ i, w i) % Q = ρ % Q).card := by
    refine Finset.card_le_card_of_injOn (fun u => fun l => (u l : ℕ)) ?_ ?_
    · intro u hu
      have hu' := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun l =>
        Finset.mem_range.mpr (u l).isLt, ?_⟩)
      have h1 : (∑ l, (u l : ℕ)) ≡ ρ % Q + (Q - c % Q) [MOD Q] := hu'
      have h2 : c + ∑ l, (u l : ℕ) ≡ c + (ρ % Q + (Q - c % Q)) [MOD Q] := Nat.ModEq.add_left c h1
      have h3 : c + (ρ % Q + (Q - c % Q)) ≡ ρ [MOD Q] := by
        have hc : c % Q < Q := Nat.mod_lt _ hQ0
        have e1 : c + (ρ % Q + (Q - c % Q)) = (c - c % Q + Q) + ρ % Q := by
          have := Nat.mod_le c Q
          omega
        rw [e1]
        have e2 : c - c % Q + Q ≡ 0 [MOD Q] := by
          have hd : Q ∣ c - c % Q := Nat.dvd_sub_mod c
          exact (Nat.modEq_zero_iff_dvd.mpr (Dvd.dvd.add hd (dvd_refl Q)))
        have e3 : ρ % Q ≡ ρ [MOD Q] := Nat.mod_modEq ρ Q
        simpa using e2.add e3
      exact h2.trans h3
    · intro u _ u' _ huu
      funext l
      exact Fin.ext (congrFun huu l)
  exact_mod_cast hle

theorem tele_le : ∀ (n : ℕ) (hn : 0 < n) (f g : Fin n → ℤ),
    (∀ (a : Fin n) (h : a.val + 1 < n), f ⟨a.val + 1, h⟩ ≤ g a) →
    ∑ a, (f a - g a) ≤ f ⟨0, hn⟩ - g ⟨n - 1, by omega⟩ := by
  intro n hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  intro f g h
  rw [Finset.sum_sub_distrib, Fin.sum_univ_succ f, Fin.sum_univ_castSucc g]
  have h1 : ∑ i : Fin m, f i.succ ≤ ∑ i : Fin m, g i.castSucc :=
    Finset.sum_le_sum fun i _ => h i.castSucc (by simp)
  have e : (⟨m + 1 - 1, by omega⟩ : Fin (m + 1)) = Fin.last m := Fin.ext (by simp)
  rw [e]
  have e0 : (⟨0, hn⟩ : Fin (m + 1)) = 0 := rfl
  rw [e0]
  linarith

section D21

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

theorem dminus_le_beS (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) (hP : X.IsPATH p K j b μ dd) (s : ℕ) :
    T.dminus (segLL X.F j) dd s ≤ X.beS p K j b := by
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  unfold T.dminus Dat.beS
  have himg : (X.F.letters j).filter (· < X.F.fr j 0) =
      (Finset.univ.filter fun l : Fin (segN X.F j) => l.val < segN X.F j - r).image (segE X.F j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      obtain ⟨i, rfl⟩ := segE_surj X.F j hx
      exact ⟨i, (segE_lt_fr_iff X.F hV hr j i).mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨segE_mem X.F j i, (segE_lt_fr_iff X.F hV hr j i).mpr hi⟩
  rw [himg, Finset.sum_image (fun a _ b _ h => (segE_strictMono X.F j).injective h), Finset.sum_filter]
  refine Finset.sum_le_sum fun l _ => ?_
  split_ifs with h1 h2 h2
  · rw [hP.degs l ((segE_lt_fr_iff X.F hV hr j l).mpr h2)]
  · exfalso
    have hl := l.isLt
    have ht : l.val - (segN X.F j - r) < r := by omega
    have hseg : segE X.F j l = X.F.fr j (l.val - (segN X.F j - r)) :=
      (segE_eq_fr_iff X.F hV j l ht).mpr (by omega)
    have hvec : (segLL X.F j).vec l = true := by
      rw [comb_vec, hseg]; exact (hV.2.2.2.2.1 j _ ht).2
    rw [hvec] at h1
    exact absurd h1.2 (by simp)
  · exact Nat.zero_le _
  · exact le_rfl

end D21

theorem tau_degree_on_path_bound : TauDegreeOnPathBound := by
  intro p n' r K _ _ _ X hX j b μ dd hP i hi
  classical
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  obtain ⟨P, hPμ⟩ := hP.path
  have hil := i.isLt
  have hnot : ¬ i.val < segN X.F j - r := fun h => by
    have := (segE_lt_fr_iff X.F hV hr j i).mpr h
    omega
  have ht : i.val - (segN X.F j - r) < r := by omega
  have hseg : segE X.F j i = X.F.fr j (i.val - (segN X.F j - r)) :=
    (segE_eq_fr_iff X.F hV j i ht).mpr (by omega)
  have hvec : (segLL X.F j).vec i = true := by
    rw [comb_vec, hseg]; exact (hV.2.2.2.2.1 j _ ht).2
  have hs := T.step_vec P i hvec
  rw [hPμ] at hs
  have hn : 0 < r + K := by omega
  have h1 := tele_le (r + K) hn (μ i.succ) (μ i.castSucc) hs.2.1
  rw [hs.2.2] at h1
  have h2 : μ i.succ ⟨0, hn⟩ = (X.beS p K j b : ℤ) :=
    hP.head i ⟨i.val - (segN X.F j - r), ht⟩ hseg ⟨0, hn⟩ (Nat.zero_le _)
  have h3 := T.neg_dminus_le_mu P i.val (by omega) ⟨r + K - 1, by omega⟩
  rw [hPμ] at h3
  have h4 := dminus_le_beS X p K hX j b μ dd hP i.val
  have h5 : μ i.castSucc = μ ⟨i.val, by omega⟩ := rfl
  rw [h2, h5] at h1
  have : (dd i : ℤ) ≤ 2 * (X.beS p K j b : ℤ) := by linarith
  exact_mod_cast this

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs3

variable {N r : ℕ}

theorem Icut_eq [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    Icut n0 ν c = if 1 ≤ c ∧ c ≤ be then Finset.univ \ riseA n0 ν c r else ∅ := by
  classical
  unfold Icut
  rw [Ican_eq H]
  split_ifs
  · rfl
  · exact Finset.empty_sdiff _

theorem pEnd_cut {n0 : ℕ} (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) : pEnd (cutPath n0 ν) = stg ν n0 := by
  rw [pEnd_eq, stg_cut n0 ν N le_rfl, min_eq_right hn]

theorem riseA_filter (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : Fin r) :
    (riseA n0 ν c r).filter (· ≤ t) = riseA n0 ν c r \ riseA n0 ν c (r - 1 - t.val) := by
  classical
  ext m
  have hm := m.isLt
  have ht := t.isLt
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, fun h4 => ?_⟩
    have : m.val ≤ t.val := h3
    omega
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    by_contra h4
    exact h3 (by omega) h2

theorem riseA_mono (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) {s t : ℕ} (h : s ≤ t) :
    riseA n0 ν c s ⊆ riseA n0 ν c t := by
  classical
  intro m
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨h1, h2⟩
  exact ⟨by omega, h2⟩

theorem card_Icut_filter [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ}
    (H : PlHyp n0 be ν) (c : ℤ) (hc : 1 ≤ c ∧ c ≤ be) (t : Fin r) :
    ((Finset.univ \ riseA n0 ν c r).filter (· ≤ t)).card + r =
      t.val + 1 + colH (stg ν (n0 + (r - 1 - t.val))) c := by
  classical
  have ht := t.isLt
  have h1 : ((Finset.univ \ riseA n0 ν c r).filter (· ≤ t)).card + ((riseA n0 ν c r).filter (· ≤ t)).card =
      t.val + 1 := by
    rw [← Finset.card_union_of_disjoint]
    · have : (Finset.univ \ riseA n0 ν c r).filter (· ≤ t) ∪ (riseA n0 ν c r).filter (· ≤ t) = Finset.Iic t := by
        ext m
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_Iic]
        tauto
      rw [this, Fin.card_Iic]
    · rw [Finset.disjoint_left]
      intro m hm hm'
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm hm'
      exact hm.1 hm'.1
  have h2 : ((riseA n0 ν c r).filter (· ≤ t)).card + (riseA n0 ν c (r - 1 - t.val)).card = (riseA n0 ν c r).card := by
    rw [riseA_filter, Finset.card_sdiff_add_card_eq_card (riseA_mono n0 ν c (by omega))]
  have h3 := card_riseA H c r le_rfl
  have h4 := card_riseA H c (r - 1 - t.val) (by omega)
  have hNr : colH (stg ν N) c = r := colH_all fun m => by rw [H.fin]; exact hc.2
  rw [hN, hNr] at h3
  omega

theorem isSt_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    IsSt (cutPath n0 ν) (Icut n0 ν) := by
  classical
  have hcard : ∀ c, (Icut n0 ν c).card =
      if 1 ≤ c then colH (pEnd (cutPath n0 ν)) c else r - colH (pEnd (cutPath n0 ν)) c := by
    intro c
    rw [pEnd_cut (by omega), Icut_eq H]
    by_cases h1 : 1 ≤ c
    · rw [ite_eq_left h1]
      by_cases h2 : c ≤ be
      · rw [ite_eq_left ⟨h1, h2⟩, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        have h3 := card_riseA H c r le_rfl
        have hNr : colH (stg ν N) c = r := colH_all fun m => by rw [H.fin]; exact h2
        rw [hN, hNr] at h3
        omega
      · rw [ite_eq_right fun h => h2 h.2, Finset.card_empty,
          colH_none fun m => lt_of_le_of_lt (H.rng n0 (by omega) m).2 (by omega)]
    · rw [ite_eq_right h1, ite_eq_right fun h => h1 h.1, Finset.card_empty,
        colH_all fun m => le_trans (by omega) (H.rng n0 (by omega) m).1]
      omega
  refine ⟨?_, hcard, ?_⟩
  · intro c hc
    by_cases h : 1 ≤ c ∧ c ≤ be
    · rw [← Finset.card_eq_zero, hcard c, ite_eq_left h.1, pEnd_cut (by omega)]
      apply colH_none
      intro m
      by_contra hge
      apply hc
      refine mem_colRange_of_le_entry (cutPath n0 ν) ⟨n0, by omega⟩ m (by omega) ?_
      have : cutPath n0 ν ⟨n0, by omega⟩ m = stg ν n0 m := by simp [cutPath]
      rw [this]; omega
    · rw [Icut_eq H, ite_eq_right h]
  · intro c t
    unfold tabCol
    by_cases h1 : 1 ≤ c
    · rw [ite_eq_left h1, ite_eq_left (by omega : (1 : ℤ) ≤ c + 1), Icut_eq H, Icut_eq H]
      by_cases h2 : c + 1 ≤ be
      · rw [ite_eq_left ⟨by omega, h2⟩, ite_eq_left ⟨h1, by omega⟩]
        have e1 := card_Icut_filter hN H (c + 1) ⟨by omega, h2⟩ t
        have e2 := card_Icut_filter hN H c ⟨h1, by omega⟩ t
        have e3 := colH_anti (stg ν (n0 + (r - 1 - t.val))) (by omega : c ≤ c + 1)
        omega
      · rw [ite_eq_right fun h => h2 h.2]
        simp
    · rw [ite_eq_right h1]
      have hc0 : Icut n0 ν c = ∅ := by rw [Icut_eq H, ite_eq_right fun h => h1 h.1]
      rw [hc0, Finset.sdiff_empty]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

theorem le_iff_lt_colH {μ : Fin r → ℤ} (hμ : Antitone μ) (c : ℤ) (m : Fin r) : c ≤ μ m ↔ m.val < colH μ c := by
  first | (apply UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption)

theorem eq_of_colH {μ μ' : Fin r → ℤ} (hμ : Antitone μ) (hμ' : Antitone μ') (h : ∀ c, colH μ c = colH μ' c) :
    μ = μ' := by
  funext m
  apply le_antisymm
  · rw [le_iff_lt_colH hμ', ← h, ← le_iff_lt_colH hμ]
  · rw [le_iff_lt_colH hμ, h, ← le_iff_lt_colH hμ']

theorem riseA_eq_filter (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) {t : ℕ} (ht : t ≤ r) :
    riseA n0 ν c t = (riseA n0 ν c r).filter fun m => r - 1 - m.val < t := by
  classical
  ext m
  have := m.isLt
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, h1⟩
  · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩

theorem path_eq_of_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν ν' : Fin (N + 1) → Fin r → ℤ}
    (H : PlHyp n0 be ν) (H' : PlHyp n0 be ν') (hd : ∀ i, Antitone (ν i)) (hd' : ∀ i, Antitone (ν' i))
    (hcut : cutPath n0 ν = cutPath n0 ν') (hI : Icut n0 ν = Icut n0 ν') : ν = ν' := by
  classical
  have hlow : ∀ i ≤ n0, stg ν i = stg ν' i := by
    intro i hi
    have h1 := stg_cut n0 ν i (by omega)
    have h2 := stg_cut n0 ν' i (by omega)
    rw [min_eq_left hi] at h1 h2
    rw [← h1, ← h2, hcut]
  have hrise : ∀ c, 1 ≤ c ∧ c ≤ be → riseA n0 ν c r = riseA n0 ν' c r := by
    intro c hc
    have h1 := congrFun hI c
    rw [Icut_eq H, Icut_eq H', ite_eq_left hc, ite_eq_left hc] at h1
    have := congrArg (fun s => Finset.univ \ s) h1
    simpa [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] using this
  funext i
  rw [stg_eq ν i.val i.isLt, stg_eq ν' i.val i.isLt]
  by_cases hi : i.val ≤ n0
  · exact hlow i.val hi
  · obtain ⟨t, ht⟩ : ∃ t, i.val = n0 + t := ⟨i.val - n0, by omega⟩
    have htr : t ≤ r := by omega
    apply eq_of_colH
    · rw [← stg_eq ν i.val i.isLt]; exact hd i
    · rw [← stg_eq ν' i.val i.isLt]; exact hd' i
    intro c
    rw [ht]
    by_cases hc : 1 ≤ c ∧ c ≤ be
    · rw [← card_riseA H c t htr, ← card_riseA H' c t htr, hlow n0 le_rfl, riseA_eq_filter n0 ν c htr,
        riseA_eq_filter n0 ν' c htr, hrise c hc]
    · by_cases h1 : 1 ≤ c
      · have h2 : be < c := by
          by_contra h; exact hc ⟨h1, by omega⟩
        rw [colH_none fun m => lt_of_le_of_lt (H.rng _ (by omega) m).2 h2,
          colH_none fun m => lt_of_le_of_lt (H'.rng _ (by omega) m).2 h2]
      · rw [colH_all fun m => le_trans (by omega) (H.rng _ (by omega) m).1,
          colH_all fun m => le_trans (by omega) (H'.rng _ (by omega) m).1]

end Abs3

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem kill_rename {R σ τ : Type} [CommRing R] (f : σ → τ) (S : Set τ) (P : MvPolynomial σ R) :
    kill S (rename f P) = rename f (kill (f ⁻¹' S) P) := by
  have h : (kill S).comp (rename f) = (rename f).comp (kill (f ⁻¹' S) : MvPolynomial σ R →ₐ[R] _) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, rename_X, kill, aeval_X]
    by_cases h1 : f i ∈ S
    · have h2 : i ∈ f ⁻¹' S := h1
      rw [ite_eq_left h1, ite_eq_left h2, map_zero]
    · have h2 : i ∉ f ⁻¹' S := h1
      rw [ite_eq_right h1, ite_eq_right h2, rename_X]
  exact AlgHom.congr_fun h P

theorem kill_of_empty {R σ : Type} [CommRing R] (S : Set σ) (hS : S = ∅) (P : MvPolynomial σ R) : kill S P = P := by
  subst hS
  have h : (kill (∅ : Set σ) : MvPolynomial σ R →ₐ[R] _) = AlgHom.id R _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [kill]
  rw [h]
  rfl

theorem li_mono_words {R σ ι α : Type} [CommRing R] [IsDomain R] (Tset : Set σ) (w : α → MvPolynomial σ R)
    (hw : LinearIndependent R w) (M : ι → σ →₀ ℕ) (x : ι → α) (hM : ∀ q, ∀ v, M q v ≠ 0 → v ∈ Tset)
    (hsup : ∀ q, w (x q) ∈ supported R Tsetᶜ) (hinj : ∀ q q', M q = M q' → x q = x q' → q = q') :
    LinearIndependent R fun q => monomial (M q) (1 : R) * w (x q) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum q₀ hq₀
  obtain ⟨Φ, hΦmono⟩ : ∃ Φ : MvPolynomial σ R →ₗ[R] MvPolynomial σ R, ∀ (n : σ →₀ ℕ) (a : R),
      Φ (monomial n a) = if n.filter (· ∈ Tset) = M q₀ then monomial (n.filter (· ∉ Tset)) a else 0 := by
    refine ⟨(MvPolynomial.basisMonomials σ R).constr R (fun n : σ →₀ ℕ =>
      if n.filter (· ∈ Tset) = M q₀ then monomial (n.filter (· ∉ Tset)) (1 : R) else 0), fun n a => ?_⟩
    have e : monomial n a = a • (MvPolynomial.basisMonomials σ R) n := by
      simp only [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    rw [e, map_smul, Module.Basis.constr_basis]
    split_ifs
    · rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
    · rw [smul_zero]
  have hkey : ∀ q, Φ (monomial (M q) (1 : R) * w (x q)) = if M q = M q₀ then w (x q) else 0 := by
    intro q
    have hwsup := hsup q
    rw [mem_supported] at hwsup
    have hT : ∀ n ∈ (w (x q)).support, (M q + n).filter (· ∈ Tset) = M q ∧
        (M q + n).filter (· ∉ Tset) = n := by
      intro n hn
      have hnv : ∀ v, n v ≠ 0 → v ∉ Tset := fun v hv =>
        hwsup ((mem_vars_iff_mem_support v).2 ⟨n, hn, Finsupp.mem_support_iff.2 hv⟩)
      constructor
      · ext v
        rw [Finsupp.filter_apply, Finsupp.add_apply]
        by_cases hv : v ∈ Tset
        · rw [ite_eq_left hv]
          have : n v = 0 := by
            by_contra h
            exact hnv v h hv
          rw [this, add_zero]
        · rw [ite_eq_right hv]
          by_contra h
          exact hv (hM q v (Ne.symm h))
      · ext v
        rw [Finsupp.filter_apply, Finsupp.add_apply]
        by_cases hv : v ∈ Tset
        · rw [ite_eq_right (not_not.2 hv)]
          by_contra h
          exact hnv v (Ne.symm h) hv
        · rw [ite_eq_left hv]
          have : M q v = 0 := by
            by_contra h
            exact hv (hM q v h)
          rw [this, zero_add]
    conv_lhs => rw [(w (x q)).as_sum]

    rw [Finset.mul_sum, map_sum]
    simp only [monomial_mul, one_mul, hΦmono]
    split_ifs with hMq
    · conv_rhs => rw [(w (x q)).as_sum]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [(hT n hn).1, (hT n hn).2, ite_eq_left hMq]
    · refine Finset.sum_eq_zero fun n hn => ?_
      rw [(hT n hn).1, ite_eq_right hMq]
  have hxinj : Function.Injective (fun q : {q // M q = M q₀} => x q.1) := by
    intro a b h
    exact Subtype.ext (hinj a.1 b.1 (a.2.trans b.2.symm) h)
  have hfib : LinearIndependent R (w ∘ fun q : {q // M q = M q₀} => x q.1) := hw.comp _ hxinj
  have h2 : ∑ q ∈ s, g q • (if M q = M q₀ then w (x q) else 0) = 0 := by
    have h := congrArg Φ hsum

    rw [map_sum, map_zero] at h
    calc ∑ q ∈ s, g q • (if M q = M q₀ then w (x q) else 0)
        = ∑ q ∈ s, Φ (g q • (monomial (M q) (1 : R) * w (x q))) :=
          Finset.sum_congr rfl fun q _ => by rw [map_smul, hkey]
      _ = 0 := h
  have h3 : ∑ q ∈ s.subtype (fun q => M q = M q₀), g q.1 • (w ∘ fun q : {q // M q = M q₀} => x q.1) q = 0 := by
    simp only [Function.comp_apply]
    rw [Finset.sum_subtype_eq_sum_filter (f := fun q => g q • w (x q)), Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) h2
    split_ifs <;> simp
  exact linearIndependent_iff'.1 hfib (s.subtype (fun q => M q = M q₀)) (fun q => g q.1) h3 ⟨q₀, rfl⟩
    (Finset.mem_subtype.2 hq₀)

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem rename_mem_supported {R σ τ : Type} [CommRing R] {f : σ → τ} {S : Set σ} {S' : Set τ}
    (h : ∀ v ∈ S, f v ∈ S') {P : MvPolynomial σ R} (hP : P ∈ supported R S) : rename f P ∈ supported R S' := by
  classical
  rw [mem_supported] at hP ⊢
  intro v hv
  have h1 := vars_rename f P (Finset.mem_coe.mp hv)
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h1
  exact h u (hP (Finset.mem_coe.mpr hu))

theorem sum_single_apply_zero {σ ι : Type} (s : Finset ι) (a : ι → σ) (k : ι → ℕ) (v : σ) (h : ∀ i ∈ s, a i ≠ v) :
    (∑ i ∈ s, Finsupp.single (a i) (k i)) v = 0 := by
  classical
  rw [Finsupp.finsetSum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finsupp.single_apply, ite_eq_right (h i hi)]

section Fin7

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (K : ℕ)

def gp (j : ℤ) : Fin (segN X.F j) × Fin r → ℤ × Fin (r + K) := fun v => (segE X.F j v.1, Fin.castAdd K v.2)

def gt (j : ℤ) : Fin (segN X.F j) × Fin K → ℤ × Fin (r + K) := fun v => (segE X.F j v.1, Fin.natAdd r v.2)

theorem segRen_PsiPl (O : Type) [CommRing O] (j : ℤ) (ν : Fin (segN X.F j + 1) → Fin r → ℤ)
    (I : ℤ → Finset (Fin r)) :
    segRen X.F j O (r + K) (PsiPl O ν I) = rename (gp X K j) (Psi O ν I) := by
  unfold segRen PsiPl
  rw [rename_rename]
  rfl

theorem segRen_PsiTan (O : Type) [CommRing O] (j : ℤ) (κ : Fin (segN X.F j + 1) → Fin K → ℤ)
    (I : ℤ → Finset (Fin K)) :
    segRen X.F j O (r + K) (PsiTan O κ I) = rename (gt X K j) (Psi O κ I) := by
  unfold segRen PsiTan
  rw [rename_rename]
  rfl

def tauSet (j : ℤ) : Set (ℤ × Fin (r + K)) := {v | ∃ t c : Fin r, v = (X.F.fr j t.val, Fin.castAdd K c)}

theorem castAdd_ne_natAdd (a : Fin r) (c : Fin K) : Fin.castAdd K a ≠ Fin.natAdd r c := by
  intro h
  have := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at this
  have := a.isLt
  omega

theorem gp_preimage {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j : ℤ) :
    (gp X K j) ⁻¹' (X.offSet K j) = offN (segN X.F j - r) := by
  have hrN := k_r_le_segN X.F hV (NeZero.pos r) j
  ext v
  have hv1 := v.1.isLt
  constructor
  · rintro ⟨t, c, hc, hv⟩
    simp only [gp, Prod.mk.injEq] at hv
    have h1 := (segE_eq_fr_iff X.F hV j v.1 t.isLt).mp hv.1
    have h2 : v.2 = c := Fin.castAdd_injective _ _ hv.2
    refine ⟨by omega, fun h3 => hc ?_⟩
    apply Fin.ext
    rw [Fin.val_rev, ← h2]
    omega
  · rintro ⟨h1, h2⟩
    have ht : v.1.val - (segN X.F j - r) < r := by omega
    refine ⟨⟨v.1.val - (segN X.F j - r), ht⟩, v.2, ?_, ?_⟩
    · intro h3
      apply h2
      have := congrArg Fin.val h3
      rw [Fin.val_rev] at this
      simp only [] at this
      omega
    · simp only [gp, Prod.mk.injEq, and_true]
      exact (segE_eq_fr_iff X.F hV j v.1 ht).mpr (by omega)

theorem gt_preimage (j : ℤ) : (gt X K j) ⁻¹' (X.offSet K j) = ∅ := by
  ext v
  simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  rintro ⟨t, c, -, hv⟩
  simp only [gt, Prod.mk.injEq] at hv
  exact castAdd_ne_natAdd K c v.2 hv.2.symm

def dgT (j : ℤ) (n0 : ℕ) (hN : n0 + r = segN X.F j) (be : ℤ) (ν : Fin (segN X.F j + 1) → Fin r → ℤ) :
    ℤ × Fin (r + K) →₀ ℕ :=
  ∑ c ∈ Finset.Icc 1 be, ∑ m ∈ riseA n0 ν c r, Finsupp.single (gp X K j (tauI n0 hN m, m)) 1

theorem kill_wordEl (O : Type) [CommRing O] {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j : ℤ)
    (hN : segN X.F j - r + r = segN X.F j) (be : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ))
    (H : PlHyp (segN X.F j - r) be (plPart q.1)) :
    ∃ e : ℕ, kill (X.offSet K j) (X.wordEl K O j q) =
      (-1) ^ e * monomial (dgT X K j (segN X.F j - r) hN be (plPart q.1)) (1 : O) *
        segRen X.F j O (r + K) (PsiPl O (cutPath (segN X.F j - r) (plPart q.1)) (Icut (segN X.F j - r) (plPart q.1)) *
          PsiTan O (tanPart q.1) q.2.1) := by
  classical
  obtain ⟨e, he⟩ := kill_Psi (R := O) hN H
  refine ⟨e, ?_⟩
  unfold Dat.wordEl
  rw [map_mul, map_mul, map_mul, segRen_PsiPl, segRen_PsiTan, segRen_PsiPl, kill_rename, kill_rename,
    gp_preimage X K hV j, kill_of_empty _ (gt_preimage X K j), he]
  simp only [map_mul, map_pow, map_neg, map_one, map_prod, rename_X]
  unfold dgT
  rw [MvPolynomial.monomial_sum_one]
  have : ∀ c ∈ Finset.Icc 1 be,
      monomial (∑ m ∈ riseA (segN X.F j - r) (plPart q.1) c r,
        Finsupp.single (gp X K j (tauI (segN X.F j - r) hN m, m)) 1) (1 : O) =
      ∏ m ∈ riseA (segN X.F j - r) (plPart q.1) c r, MvPolynomial.X (gp X K j (tauI (segN X.F j - r) hN m, m)) := by
    intro c _
    rw [MvPolynomial.monomial_sum_one]
    rfl
  rw [Finset.prod_congr rfl this]
  ring

theorem monTau_apply {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j : ℤ) (u : Fin r × Fin r → ℕ) (t c : Fin r) :
    X.monTau K j u (X.F.fr j t.val, Fin.castAdd K c) = u (t, c) := by
  classical
  unfold Dat.monTau
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single (t, c)]
  · simp
  · intro v _ hv
    rw [Finsupp.single_apply, ite_eq_right]
    intro h
    simp only [Prod.mk.injEq] at h
    exact hv (Prod.ext (fr_injective X.F hV j h.1) (Fin.castAdd_injective _ _ h.2))
  · intro h; exact absurd (Finset.mem_univ _) h

end Fin7

theorem restKey_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) : RestKey C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hB
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hr : 0 < r := NeZero.pos r
  have hV := hX.valid
  have hrN := k_r_le_segN X.F hV hr j
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have hN : segN X.F j - r + r = segN X.F j := Nat.sub_add_cancel hrN
  have h10 : BracketPolynomialSpan D := hAdm.2.2.2.2.2.2.2.2.2.1
  have h12 : NestedTypeBound D := hAdm.2.2.2.2.2.2.2.2.2.2.2.1
  have hw := (h12 p O S n' r K X.F X.L₁ X.N₁ j (fun _ => 0) (fun _ => 0) (fun _ => 0) hV hNK
    (fun _ => le_rfl)).2.1
  have hH : ∀ q : X.Idx p K j (X.restr j b),
      PlHyp (segN X.F j - r) (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) := by
    intro q
    obtain ⟨dd, hP, -⟩ := q.2
    exact plHyp_of X p K hX j _ _ dd hP
  have hpair : ∀ q : X.Idx p K j (X.restr j b), ∃ b' b'' : Fin (segN X.F j) → ℕ,
      (∃ P1 : PPath r (segN X.F j) (segLL X.F j) b', P1.mu = plPart q.1.1) ∧
      (∃ P2 : PPath K (segN X.F j) (segLL X.F j) b'', P2.mu = tanPart q.1.1) := by
    intro q
    obtain ⟨dd, hP, -⟩ := q.2
    obtain ⟨P, hPμ⟩ := hP.path
    obtain ⟨b', b'', -, h1, h2, -⟩ := (h10 (segN X.F j) r K (segLL X.F j) dd hNK (plPart q.1.1) (tanPart q.1.1)).mp
      ⟨P, by rw [hPμ, joinPT_parts]⟩
    exact ⟨b', b'', h1, h2⟩
  have hx : ∀ q : X.Idx p K j (X.restr j b),
      ((cutPath (segN X.F j - r) (plPart q.1.1), tanPart q.1.1) ∈ segPairsAll X.F j K) ∧
      IsSt (cutPath (segN X.F j - r) (plPart q.1.1)) (Icut (segN X.F j - r) (plPart q.1.1)) ∧
      IsSt (tanPart q.1.1) q.1.2.1 := by
    intro q
    obtain ⟨b', b'', ⟨P1, h1⟩, h2⟩ := hpair q
    obtain ⟨bc, Pc, hPc⟩ := cut_ppath P1 (segN X.F j - r)
    obtain ⟨dd, -, -, hSt, -⟩ := q.2
    exact ⟨⟨bc, b'', ⟨Pc, by rw [hPc, h1]⟩, h2⟩, isSt_cut hN (hH q), hSt⟩
  let x : X.Idx p K j (X.restr j b) →
      {x : ((Fin (segN X.F j + 1) → Fin r → ℤ) × (Fin (segN X.F j + 1) → Fin K → ℤ)) ×
        ((ℤ → Finset (Fin r)) × (ℤ → Finset (Fin K))) //
        x.1 ∈ segPairsAll X.F j K ∧ IsSt x.1.1 x.2.1 ∧ IsSt x.1.2 x.2.2} := fun q =>
    ⟨((cutPath (segN X.F j - r) (plPart q.1.1), tanPart q.1.1),
      (Icut (segN X.F j - r) (plPart q.1.1), q.1.2.1)), hx q⟩
  let M : X.Idx p K j (X.restr j b) → (ℤ × Fin (r + K) →₀ ℕ) := fun q =>
    X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1)
  have htauI : ∀ m : Fin r, gp X K j (tauI (segN X.F j - r) hN m, m) ∈ tauSet X K j := by
    intro m
    have hm := m.isLt
    refine ⟨⟨r - 1 - m.val, by omega⟩, m, ?_⟩
    simp only [gp, Prod.mk.injEq, and_true]
    exact (segE_eq_fr_iff X.F hV j _ (by omega)).mpr rfl
  have hM : ∀ q, ∀ v, M q v ≠ 0 → v ∈ tauSet X K j := by
    intro q v hv
    by_contra hnot
    apply hv
    show (X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q.1.1)) v = 0
    rw [Finsupp.add_apply]
    have h1 : X.monTau K j q.1.2.2 v = 0 := by
      unfold Dat.monTau
      exact sum_single_apply_zero _ _ _ v fun i _ h => hnot ⟨i.1, i.2, h.symm⟩
    have h2 : dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1) v = 0 := by
      unfold dgT
      rw [Finsupp.finsetSum_apply]
      refine Finset.sum_eq_zero fun c _ => ?_
      exact sum_single_apply_zero _ _ _ v fun m _ h => hnot (h ▸ htauI m)
    rw [h1, h2]
  have hsup : ∀ q, segRen X.F j O (r + K) (PsiPl O (x q).1.1.1 (x q).1.2.1 * PsiTan O (x q).1.1.2 (x q).1.2.2) ∈
      supported O (tauSet X K j)ᶜ := by
    intro q
    rw [map_mul, segRen_PsiPl, segRen_PsiTan]
    refine Subalgebra.mul_mem _ ?_ ?_
    · refine rename_mem_supported ?_ (Psi_cut_supported (segN X.F j - r) (by omega) (plPart q.1.1) _)
      rintro v hv ⟨t, c, h⟩
      simp only [gp, Prod.mk.injEq] at h
      have := (segE_eq_fr_iff X.F hV j v.1 t.isLt).mp h.1
      have hv' : v.1.val < segN X.F j - r := hv
      omega
    · refine rename_mem_supported (S := Set.univ) ?_ (by rw [supported_univ]; exact Algebra.mem_top)
      rintro v - ⟨t, c, h⟩
      simp only [gt, Prod.mk.injEq] at h
      exact castAdd_ne_natAdd K c v.2 h.2.symm
  have hinj : ∀ q q', M q = M q' → x q = x q' → q = q' := by
    intro q q' hMq hxq
    have hx' := congrArg Subtype.val hxq
    simp only [x, Prod.mk.injEq] at hx'
    obtain ⟨⟨hcut, hκ⟩, hI, hI''⟩ := hx'
    obtain ⟨b1, -, ⟨P1, h1⟩, -⟩ := hpair q
    obtain ⟨b2, -, ⟨P2, h2⟩, -⟩ := hpair q'
    have hν : plPart q.1.1 = plPart q'.1.1 :=
      path_eq_of_cut hN (hH q) (hH q') (fun i => by rw [← h1]; exact P1.dom i) (fun i => by rw [← h2]; exact P2.dom i)
        hcut hI
    have hμ : q.1.1 = q'.1.1 := by
      rw [← joinPT_parts q.1.1, ← joinPT_parts q'.1.1, hν, hκ]
    have hu0 : X.monTau K j q.1.2.2 = X.monTau K j q'.1.2.2 := by
      have h3 : X.monTau K j q.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q.1.1) =
          X.monTau K j q'.1.2.2 + dgT X K j (segN X.F j - r) hN _ (plPart q'.1.1) := hMq
      rw [hν] at h3
      exact add_right_cancel h3
    have hu : q.1.2.2 = q'.1.2.2 := by
      funext v
      rw [← monTau_apply X K hV j q.1.2.2 v.1 v.2, ← monTau_apply X K hV j q'.1.2.2 v.1 v.2, hu0]
    exact Subtype.ext (Prod.ext hμ (Prod.ext hI'' hu))
  have hli := li_mono_words (tauSet X K j) _ hw M x hM hsup hinj
  have hkill := fun q : X.Idx p K j (X.restr j b) =>
    kill_wordEl X K O hV j hN (X.beS p K j (X.restr j b) : ℤ) q.1 (hH q)
  choose e he using hkill
  have hli2 := hli.units_smul fun q => (-1 : Oˣ) ^ e q
  have heq : (fun q : X.Idx p K j (X.restr j b) =>
      monomial (X.monTau K j q.1.2.2) (1 : O) * kill (X.offSet K j) (X.wordEl K O j q.1)) =
      ((fun q => (-1 : Oˣ) ^ e q) • fun q => monomial (M q) (1 : O) *
        segRen X.F j O (r + K) (PsiPl O (x q).1.1.1 (x q).1.2.1 * PsiTan O (x q).1.1.2 (x q).1.2.2)) := by
    funext q
    rw [he q]
    simp only [Pi.smul_apply']
    rw [Units.smul_def, MvPolynomial.smul_eq_C_mul]
    have hmm : monomial (M q) (1 : O) = monomial (X.monTau K j q.1.2.2) (1 : O) *
        monomial (dgT X K j (segN X.F j - r) hN (X.beS p K j (X.restr j b) : ℤ) (plPart q.1.1)) (1 : O) := by
      rw [monomial_mul, one_mul]
    rw [hmm]
    simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, map_pow, map_neg, map_one]
    ring
  rw [heq]
  exact hli2

end
end Formalism.MainNotions.SelectionLemmas.Pf
