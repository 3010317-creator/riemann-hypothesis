module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.CardCellsEqSumRowLen
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.CoreTermLe
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Expand
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.HeartPderivMinor
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.Vanish
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

theorem entAtD_of (hX : PExpCoeff) (hB : PBridge) (hC : PLapComm) (hM : PMinorAff) (hS : PSDegMul)
    (hF : PLapForms) : PI.EntAtD.EntAtD :=
  entAtD_of_core (core_of (expand_of hX) (vanish_of hB hC (lapZero_of hM hS hF)))

theorem entAtD_of_all_rows (hX : PExpCoeff) (hB : PBridge) (hC : PLapComm) : PI.EntAtD.EntAtD := by
  apply entAtD_of_core
  intro H _ _ N0 N1 p _ nu Th hTh
  have h := core_of_rowContractionBound (expand_of hX) hB hC H N0 N1 p nu Th hTh
  have hsum : (∑ t : H, (rowContractionBound (nu (false, t)) (nu (true, t)) : ℝ)) ≤
      ∑ t : H, (cPr (nu (false, t)) (nu (true, t)) : ℝ) :=
    Finset.sum_le_sum fun t _ => by exact_mod_cast rowContractionBound_le_cPr (nu (false, t)) (nu (true, t))
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  intro I m
  refine (h I m).trans ?_
  apply Real.rpow_le_rpow_of_exponent_le hp
  linarith

end PI.EntAtD.W
