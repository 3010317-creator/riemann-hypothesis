module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CubeTheorem
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.LBSpreads
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CubeTheoremOfPerfect
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasModelOfSpreading
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.CubeTheorem.SchemeModels
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsProperSpreadsOut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LbSpreads
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectOfModels
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchemeModelsSpread
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothSpreadsOut
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

@[expose] public section

set_option autoImplicit false

namespace GlobalTheory.SpreadingModels

theorem cubeTheorem_holds : GlobalTheory.Published.CubeTheorem :=
  _root_.GlobalTheory.CompanionTheory.CubePerf.cubeTheorem_of_perfAll (_root_.GlobalTheory.CompanionTheory.SpreadingModels.perfAll_of_hasModel (_root_.GlobalTheory.CompanionTheory.CubeModels.hasModel_of_spreads _root_.GlobalTheory.CompanionTheory.NoethApprox.schemeModels _root_.GlobalTheory.CompanionTheory.SmoothSpread.smooth_spreads _root_.GlobalTheory.CompanionTheory.SpreadingModels.properSpreads _root_.GlobalTheory.CompanionTheory.LBLimit.lbSpreads))

end GlobalTheory.SpreadingModels
