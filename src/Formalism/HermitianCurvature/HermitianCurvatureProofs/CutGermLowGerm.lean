module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtSizePtG
public import Formalism.HermitianCurvature.StatementTBB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AeNeZeroComplex
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEX_UwTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyZeroNear
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGCongr
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGInt
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbGermRateLowBOfParts
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

namespace GLG

def PP (m : ℕ) (h : C.LPt) (x Dv : ℂ) : Option ℂ → C.LPt
  | none => h ++ [(m + 1, x⁻¹), (1, x ^ (m + 1) * Dv)]
  | some z => h ++ [(m + 2, z)]

end GLG

namespace GLG

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def lam (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (w : List C.Letter) (a : C.LPt) : ℝ :=
  √(TBB.nPt P.k P.r (TBB.TTp p) a) / √(TBB.normC nn w)

end GLG


end

end Formalism.FourierDecayAlt.P.CutBP
