module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitary
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionsLieRationalWeightsCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantKernelStableAndAdmissible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockCoinvariantsHighestWeightCyclicMultiplicityOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockSecondActionQuadraticIdentityModCoinvariants
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegTransposeFockSecondActionQuadraticModCoinvari
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem fock_pack : ∀ (P Q R S : ℕ) (x : ℂ), Pack (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  obtain ⟨-, hLie, -, hWt, -⟩ := _root_.GlobalTheory.HoweR.fock_lie_wts_comm P Q R S
  obtain ⟨hStab, hAdm⟩ := _root_.GlobalTheory.HoweR.coinv_stab_adm P Q R S x
  obtain ⟨α, β, hq⟩ := _root_.GlobalTheory.HoweR.SecondQuad.qop_mem_coinv P Q R S x
  obtain ⟨α', β', hqt⟩ := _root_.GlobalTheory.HoweR.QuadT.negT_fockAct2_quad P Q R S x
  refine ⟨⟨hLie, hWt, _root_.GlobalTheory.HoweR.fock_locU P Q R S⟩, hStab, ⟨α, β, α', β', fun a b v _ => ⟨hq a b v, hqt a b v⟩⟩, hAdm, _root_.GlobalTheory.HoweR.coinv_cycMod P Q R S x⟩

end GlobalTheory.HoweR
