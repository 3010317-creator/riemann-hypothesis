module

import CompanionTheory.RealGroups.FormalDegrees.ArchimedeanFormalDegrees.FormalDegreeFormula.ModelFunctionsMultiply
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.ModelTau
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ProdSubLtEqFactorial
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.HcParamGapGeIndex
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Unique

@[expose] public section

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 ReciprocityTheory.ChartRestriction.DS.HW

variable {n : ℕ}

def CkModel : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (m : Fin n → ℤ) (hm : NonnegDom ε m) (k : KG ε),
    cK (modelKType ε hm) k = ‖f0K ε m k‖

def CkTwist : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (Λ : Fin n → ℝ) (T : KType ε Λ) (c : ℤ),
    ∃ T' : KType ε (fun a => Λ a + (c : ℝ)), ∀ k, cK T' k = cK T k

def ModelFunctionsMultiply : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (m₁ m₂ : Fin n → ℤ), NonnegDom ε m₁ → NonnegDom ε m₂ → ∀ k : KG ε,
    f0K ε (m₁ + m₂) k = f0K ε m₁ k * f0K ε m₂ k

theorem coefPow_of (hM : CkModel) (hT : CkTwist) (hF : ModelFunctionsMultiply) : CoefPow := by
  apply CompanionTheory.RgFd.coefPow_of <;> assumption

end PositivityTheory.RgFd
