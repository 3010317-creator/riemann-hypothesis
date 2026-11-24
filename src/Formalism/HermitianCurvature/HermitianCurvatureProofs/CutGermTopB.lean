module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTop
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Lam1
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousInvUpper
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsCompactRoots
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.OneSubPowLe
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBTAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtEntryAppendStart
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.StandardPairingDecay
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeightProductGermIndep
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateSplit

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.GermRateSplit Finset Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

def l1T (m : ℕ) : ℂ := (-1) ^ (m + 3) / Complex.I ^ (m + 2)

def l2T (m : ℕ) : ℂ := Complex.I * l1T m

theorem norm_l1T (m : ℕ) : ‖l1T m‖ = 1 := by
  simp [l1T]

theorem top_base_ne_zero (m : ℕ) : l1T m ≠ 0 := by
  intro h
  simpa [h] using norm_l1T m

theorem norm_l2T (m : ℕ) : ‖l2T m‖ = 1 := by
  rw [l2T, norm_mul, Complex.norm_I, norm_l1T, one_mul]

theorem top_root_ne_zero (m : ℕ) : l2T m ≠ 0 := by
  intro h
  simpa [h] using norm_l2T m

theorem top_root_pow_eq (m : ℕ) : l2T m ^ (m + 2) = (-1) ^ (m + 3) * l1T m ^ (m + 1) := by
  have hI : Complex.I ^ (m + 2) ≠ 0 := pow_ne_zero _ Complex.I_ne_zero
  have h1 : Complex.I ^ (m + 2) * l1T m = (-1) ^ (m + 3) := by
    rw [l1T, mul_div_cancel₀ _ hI]
  calc l2T m ^ (m + 2) = (Complex.I ^ (m + 2) * l1T m) * l1T m ^ (m + 1) := by
        rw [l2T]
        ring
    _ = (-1) ^ (m + 3) * l1T m ^ (m + 1) := by rw [h1]

theorem psi_l (m : ℕ) (w : ℂ) : G.psi U.betaU (l2T m / l1T m * w) = conj (G.psi ((2 : ℝ) : ℂ) w) := by
  have hl : l2T m / l1T m = Complex.I := by
    rw [l2T, mul_div_assoc, div_self (top_base_ne_zero m), mul_one]
  have key : U.betaU * (Complex.I * w) = -(((2 : ℝ) : ℂ) * w) := by
    simp only [U.betaU, Formalism.QuantumDeterminants.cStd]
    push_cast
    linear_combination (2 * w) * Complex.I_sq
  rw [hl, G.psi, G.psi, key, ← Complex.exp_conj]
  congr 1
  apply Complex.ext <;> simp

end

end Formalism.FourierDecayAlt.P.CutBP.GT
