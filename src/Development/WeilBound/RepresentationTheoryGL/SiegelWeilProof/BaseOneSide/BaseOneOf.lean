module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Pieces
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterSideEquidistribution
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormulaOfComponents
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Equidistribution
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistenceTestFunctions
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrincipleHermitian
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianExistencePrinciple
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionSideEquidistribution
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFormulaOfTotalMassOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityOfMassOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalDensityRatioFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarFibrationFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilRankOneBaseCase
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeOfScalarFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateIntegralFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIdentityOfLocalDensities
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.MassOneBase.MassOne
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.PlugInf
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

namespace PositivityTheory.Rg.Base1

theorem baseOne_of (hM : PositivityTheory.SiegelWeilFormula.Densx.MassOne) : PositivityTheory.SiegelWeilFormula.Densx.BaseOne :=
  _root_.GlobalTheory.CompanionTheory.Base1.baseOne_of_parts (_root_.GlobalTheory.CompanionTheory.Mass.Rank.mass_formula_of_total_mass_one hM) (_root_.GlobalTheory.CompanionTheory.SW.BaseSimil.simil _root_.GlobalTheory.CompanionTheory.RgBase.ScalFib.scal) _root_.GlobalTheory.CompanionTheory.SW.BaseHasse.hasse
    (_root_.GlobalTheory.CompanionTheory.RgBaseCnt.cnt_of _root_.GlobalTheory.CompanionTheory.TateRes.tate (_root_.GlobalTheory.CompanionTheory.BasePsi.psiSide_of_equi _root_.GlobalTheory.CompanionTheory.Equi.equi) _root_.GlobalTheory.CompanionTheory.RatioBase.ratio _root_.GlobalTheory.CompanionTheory.RgBase.hEx _root_.GlobalTheory.CompanionTheory.SW.BaseTest.testEx _root_.GlobalTheory.CompanionTheory.SW.RankOne.dens
      (_root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.lside _root_.GlobalTheory.CompanionTheory.Equi.equi) (_root_.GlobalTheory.CompanionTheory.RgBase.Theta.thetaId _root_.GlobalTheory.CompanionTheory.RgBase.ScalFib.scal (_root_.GlobalTheory.CompanionTheory.RankOneLoc.locR _root_.GlobalTheory.CompanionTheory.RgBase.ScalFib.scal hM)))

theorem baseOne : PositivityTheory.SiegelWeilFormula.Densx.BaseOne := baseOne_of PositivityTheory.SiegelWeilFormula.BaseOne.massOne

theorem densEq : PositivityTheory.SiegelWeilFormula.Gen.DensEq := PositivityTheory.SiegelWeilFormula.Densx.densEq_of_one baseOne PositivityTheory.SiegelWeilFormula.BaseOne.massOne

end PositivityTheory.Rg.Base1
