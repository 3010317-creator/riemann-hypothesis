module

public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalDataRealPlace
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix MeasureTheory NumberField Filter Topology

noncomputable section

namespace Formalism.MainNotions.S.LocalFrameAxioms

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

def LocMatch (D : D7) (T T' : ℝ) (x : LocalDataRealPlace D) (B : LocBessel D.R.k D.R.rS) : Prop :=
  B.lam = x.lam ∧ B.u = x.u ∧ B.u' = x.u' ∧ Tz D.R.k D.R.rS B.z = T ∧ Tz D.R.k D.R.rS B.z' = T' ∧
    B.ε = epsSH D.R

def FrameAx (D : D7) (δ : D.host.E) (L : LatticeDataWithDual D) (B : D.what₂.Tau → LocBessel D.R.k D.R.rS) : Prop :=
  ∃ ϱ : ℝ, IsFrameScale D L ϱ ∧ ∀ v, (B v).c = cPsi D δ v / (ϱ : ℂ)

def PsiAx (D : D7) (δ : D.host.E) : Prop :=
  δ ≠ 0 ∧ ((∀ v, (plEmb D v δ).re = 0) ∨ ∀ v, (plEmb D v δ).im = 0)

theorem k_le_nS (D : D7) : D.R.k ≤ 2 * D.R.rS + D.R.k + 1 := by omega

def Nlet (D : D7) (Kst : ℕ) : ℝ := 4 * (Kst : ℝ) * ((D.R.rS : ℝ) + 1)

section Arith

open scoped ComplexOrder

variable (D : D7)

variable {D}

end Arith

end Formalism.MainNotions.S.LocalFrameAxioms

end
