module

public import Formalism.GL3MeanSquares.SecondEstimateOfIntervalHypothesis
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.CountSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MeanSquareHypWIff
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBoundRight
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ReLtOneOfZero

@[expose] public section

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

private theorem aux (Q : ℝ) (M : ℕ) [NeZero M] (ψ : DirichletCharacter ℂ M) (hp : ψ.IsPrimitive) (hM : (M : ℝ) ≤ Q)
    (hz : ¬ ZeroFreeBox Q ψ) :
    ∃ p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)), p.1 + 1 = M ∧ p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, M = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne M)
  refine ⟨⟨k, ψ⟩, rfl, hp, hM, ?_⟩
  unfold ZeroFreeBox at hz
  push Not at hz
  exact hz

private theorem zero_density_box :
    Formalism.HermitianLattices.Ext.PrimitiveCharacterCasts.ZeroDensityBox := by
  classical
  obtain ⟨C, -, hC⟩ := GlobalTheory.ZeroDensityMult.zero_density_mult
  refine ⟨C, fun Q S hQ hS => ?_⟩
  have hex := fun p hp => (hS p hp).2.2
  choose! z hz using hex
  let g : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)) → (Σ N : ℕ, DirichletCharacter ℂ (N + 1) × ℂ) :=
    fun p => ⟨p.1, p.2, z p⟩
  have hinj : Function.Injective g :=
    Function.LeftInverse.injective (g := fun q => ⟨q.1, q.2.1⟩) fun _ => rfl
  have h1 := hC Q hQ (S.image g) (by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨(hS p hp).2.1, (hS p hp).1, (hz p hp).2.2, (hz p hp).1.le, (hz p hp).2.1⟩)
  rw [Finset.sum_image hinj.injOn] at h1
  refine le_trans ?_ h1
  have h2 : S.card ≤ ∑ p ∈ S, analyticOrderNatAt (DirichletCharacter.LFunction (g p).2.1) (g p).2.2 := by
    rw [Finset.card_eq_sum_ones]
    refine Finset.sum_le_sum fun p hp => ?_
    have hre := GlobalTheory.ZeroDensityMult.re_lt_one_of_zero p.2 (hS p hp).1 (hz p hp).2.2
    exact GlobalTheory.GoodHeight.one_le_order p.2 (fun h : z p = 1 => by simp [h] at hre) (hz p hp).2.2
  exact_mod_cast h2

theorem count_bad_core :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Q F : ℝ) (S : Finset ℕ), 3 ≤ Q →
      (∀ q ∈ S, q.Prime ∧ F < q ∧ ∃ (N f : ℕ) (_ : NeZero N) (ψ : DirichletCharacter ℂ N),
        N = f * q ∧ (f : ℝ) ≤ F ∧ ψ.IsPrimitive ∧ (N : ℝ) ≤ Q ∧ ¬ ZeroFreeBox Q ψ) →
      (S.card : ℝ) ≤ C * Q ^ (1 / 4 : ℝ) := by
  classical
  obtain ⟨C, hC⟩ := zero_density_box
  refine ⟨max C 0, le_max_right _ _, fun Q F S hQ hS => ?_⟩
  have key : ∀ q : ℕ, ∃ p : (Σ N : ℕ, DirichletCharacter ℂ (N + 1)), q ∈ S →
      (∃ f : ℕ, p.1 + 1 = f * q ∧ (f : ℝ) ≤ F) ∧ p.2.IsPrimitive ∧ ((p.1 + 1 : ℕ) : ℝ) ≤ Q ∧
      ∃ s : ℂ, 1 - 1 / 400 < s.re ∧ |s.im| ≤ Q ∧ DirichletCharacter.LFunction p.2 s = 0 := by
    intro q
    by_cases hq : q ∈ S
    · obtain ⟨-, -, N, f, _, ψ, hN, hf, hp, hNQ, hz⟩ := hS q hq
      obtain ⟨p, h1, h2⟩ := aux Q N ψ hp hNQ hz
      exact ⟨p, fun _ => ⟨⟨f, h1.trans hN, hf⟩, h2⟩⟩
    · exact ⟨⟨0, 1⟩, fun h => absurd h hq⟩
  choose g hg using key
  have hinj : Set.InjOn g S := by
    intro q hq q' hq' h
    obtain ⟨⟨f, hf, -⟩, -⟩ := hg q hq
    obtain ⟨⟨f', hf', hF'⟩, -⟩ := hg q' hq'
    have hpq := (hS q hq).1
    have hpq' := (hS q' hq').1
    have hlt := (hS q hq).2.1
    have he : f * q = f' * q' := by rw [← hf, ← hf', h]
    have hd : q ∣ f' * q' := ⟨f, by rw [← he, mul_comm]⟩
    rcases (Nat.Prime.dvd_mul hpq).1 hd with h1 | h1
    · have hpos : 0 < f' := by
        rcases Nat.eq_zero_or_pos f' with h0 | h0
        · rw [h0] at hf'; simp at hf'
        · exact h0
      have : (q : ℝ) ≤ f' := by exact_mod_cast Nat.le_of_dvd hpos h1
      linarith
    · exact (Nat.prime_dvd_prime_iff_eq hpq hpq').1 h1
  have h1 := hC Q (S.image g) hQ (by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hp
    exact (hg q hq).2)
  rw [Finset.card_image_of_injOn hinj] at h1
  refine h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ?_)
  exact Real.rpow_nonneg (by linarith) _

end QH
