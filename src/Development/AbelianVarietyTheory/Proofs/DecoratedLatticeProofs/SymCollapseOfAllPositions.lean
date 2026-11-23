module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContrFactor
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnIndicatorPureAtSymmetricPosition
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatColumnSupportOfOneIndexAtSymPositionStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatRowIndicatorOfSymLevelExchange
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelDoubleStepOfFlatColumnFlatRow
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricLevelChainPatternIterated
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

namespace GlobalTheory.LocFlat

theorem symCollapse_of_allPositions : AllPositions → GlobalTheory.LocFlat.SymCollapse := by
  intro hA k _ _ _ _ _ _ ν hν s κ S t _ _
  obtain ⟨hO, hE⟩ := hA k ν hν s κ S t
  have hP : S.Pattern t := GlobalTheory.SymChain.pattern_iter k s κ S t
  have hC := _root_.GlobalTheory.LocFlat.pureCol_of_pattern k ν hν s κ S t hP hE
  have hR := _root_.GlobalTheory.LocFlat.pureRow_of_exchange k ν hν s κ S t hP hE
  exact ⟨GlobalTheory.T.flatColumnSupport_of_oneIndexAt_symPosition k ν hν s κ S t hO, hC, hR, _root_.GlobalTheory.LocFlat.doubleStep_of_pureCol_pureRow k ν hν s κ S t hP hO hC hR⟩

end GlobalTheory.LocFlat
