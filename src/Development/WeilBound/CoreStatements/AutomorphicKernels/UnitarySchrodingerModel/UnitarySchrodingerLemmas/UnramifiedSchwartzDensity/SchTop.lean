module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.Reduce
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.SchCut
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanCoordinates
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanFamilyContinuity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanScaling
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanSection
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DensityIntegralStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePartOpen
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.UnramifiedSchwartzDensity.Assemble
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

theorem PositivityTheory.PfSWUS.SchInf.schwartzDensInf : PositivityTheory.PfSWUS.HMass.SchwartzDensInf :=
  PositivityTheory.PfSWUS.SchInf.schwartzDensInf_of _root_.GlobalTheory.CompanionTheory.PushFam.integrable_continuousAt_of_linear_push _root_.GlobalTheory.CompanionTheory.SecInf.secInf _root_.GlobalTheory.CompanionTheory.SW.CoordR.coordInf _root_.GlobalTheory.CompanionTheory.SW.HaarScale.scaleInf _root_.GlobalTheory.CompanionTheory.SW.FinOpenGram.finOpen
    GlobalTheory.T.density_integral
