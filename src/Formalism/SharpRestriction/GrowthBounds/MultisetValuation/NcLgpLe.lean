module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Finset

theorem nc_lgp_le (p : ℕ) (hp : 2 ≤ p) (x : ℤ) (A : ℝ) (c : ℕ) (hx : (x : ℝ) ≤ A ^ c)
    (hl : 1 ≤ Real.logb p A) : (lgp p x : ℝ) ≤ (c + 1) * Real.logb p A := by
  unfold lgp
  split_ifs with h
  · push_cast
    have : 0 ≤ Real.logb p A := by linarith
    nlinarith
  · push_cast
    have hx0 : 0 < x := by omega
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
    have h1 : (Nat.log p x.toNat : ℝ) ≤ Real.logb p (x.toNat : ℝ) := Real.natLog_le_logb _ _
    have h2 : ((x.toNat : ℕ) : ℝ) = (x : ℝ) := by
      have : ((x.toNat : ℕ) : ℤ) = x := Int.toNat_of_nonneg hx0.le
      exact_mod_cast this
    rw [h2] at h1
    have h3 : Real.logb p (x : ℝ) ≤ Real.logb p (A ^ c) :=
      Real.logb_le_logb_of_le hp1 (by exact_mod_cast hx0) hx
    rw [Real.logb_pow] at h3
    nlinarith

variable {n' k1 : ℕ}

end Formalism.MainNotions.FormalGroupSystem.Pf
