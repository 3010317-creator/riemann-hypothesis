module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceMultGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedAway
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedAwayZariski
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceReducedGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceUnmixedGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveBranchLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CurveBranchLengthHolds
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBranches
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SliceBranchesHolds
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalOrder
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceBundleRadicalAway
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceLength
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceMultGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedAwayZariski
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceUnmixedGeneral
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTransverseSliceGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimDomain
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceReducedAway
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.BranchInverseOffHypersurfaceHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.InjectiveHolomorphicJacobianNeZeroHolds
import GroundTheory.HeightsAndTheta.Heights.LocalFiniteness.RegularLocusIdentityHolds
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Heights.BranchOrder

open GroundTheory.Heights₂.Heights

theorem sliceReducedAwayZariski : SliceReducedAwayZariski.Statement :=
  @SliceReducedAwayZariski.proof AutoClose.GenericFibreRadicalAway SliceBundleRadicalAway.proof

theorem sliceReducedAway : SliceReducedAway.Statement :=
  @SliceReducedAway.proof sliceReducedAwayZariski

theorem sliceUnmixedGeneral : SliceUnmixedGeneral.Statement :=
  @SliceUnmixedGeneral.proof AutoClose.CMHeightOneGeneral LocalDimDomain.proof
    AutoClose.SliceLocalDimGeneral AutoClose.SliceCMUnmixed

theorem sliceReducedGeneral : SliceReducedGeneral.Statement :=
  @SliceReducedGeneral.proof sliceUnmixedGeneral sliceReducedAway

theorem sliceMultGeneral : SliceMultGeneral.Statement :=
  @SliceMultGeneral.proof AutoClose.CMGeneralPoint TransverseSliceGeneral.proof AutoClose.LengthTransverseSlice

theorem sliceLength : SliceLength.Statement :=
  @SliceLength.proof IndefiniteRowSideFullHecke.ComplexSets.VanishNearPoint.full sliceReducedGeneral sliceMultGeneral

theorem localOrder : LocalOrder.Statement :=
  LocalOrder.proof sliceLength _root_.GlobalTheory.CompanionTheory.Ar.SliceBranch.sliceBranches _root_.GlobalTheory.CompanionTheory.Heights.CurveBranch.curveBranchLength

end GlobalTheory.CompanionTheory.Heights.BranchOrder
