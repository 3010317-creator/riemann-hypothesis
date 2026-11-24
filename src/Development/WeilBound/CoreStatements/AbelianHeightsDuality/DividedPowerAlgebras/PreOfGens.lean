module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPreDividedPowersOfGenerators
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

open PowerSeries Finset

variable {B : Type} [CommRing B]

def IsExp (f : B⟦X⟧) : Prop := ∀ m n, coeff m f * coeff n f = ((m + n).choose m : B) * coeff (m + n) f

theorem IsExp.mul {f g : B⟦X⟧} (hf : IsExp f) (hg : IsExp g) : IsExp (f * g) := by
  intro m n
  simp only [coeff_mul]
  have e : ((m + n).choose m : B) * ∑ p ∈ HasAntidiagonal.antidiagonal (m + n), coeff p.1 f * coeff p.2 g =
      ∑ i ∈ HasAntidiagonal.antidiagonal m, ∑ p ∈ HasAntidiagonal.antidiagonal (m + n),
        (p.1.choose i.1 : B) * (p.2.choose i.2 : B) * (coeff p.1 f * coeff p.2 g) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.1 hp, Nat.add_choose_eq, ← Finset.sum_mul]
    push_cast
    rfl
  rw [e, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi' := Finset.HasAntidiagonal.mem_antidiagonal.1 hi
  rw [Finset.mul_sum]
  refine Finset.sum_of_injOn (fun k : ℕ × ℕ ↦ (i.1 + k.1, i.2 + k.2)) ?_ ?_ ?_ ?_
  · intro k _ l _ h
    simp only [Prod.mk.injEq, add_right_inj] at h
    exact Prod.ext h.1 h.2
  · intro k hk
    have := Finset.HasAntidiagonal.mem_antidiagonal.1 hk
    exact Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only; omega)
  · intro p hp hn
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h1 : p.1 < i.1
    · simp [Nat.choose_eq_zero_of_lt h1]
    by_cases h2 : p.2 < i.2
    · simp [Nat.choose_eq_zero_of_lt h2]
    refine absurd ⟨(p.1 - i.1, p.2 - i.2), Finset.mem_coe.2 (Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only; omega)), ?_⟩ hn
    exact Prod.ext (by simp only; omega) (by simp only; omega)
  · intro k _
    have a := hf i.1 k.1
    have b := hg i.2 k.2
    simp only
    linear_combination (coeff i.2 g * coeff k.2 g) * a + (((i.1 + k.1).choose i.1 : B) * coeff (i.1 + k.1) f) * b

end FubiniStudyChowHeightFormula₂.Adr
