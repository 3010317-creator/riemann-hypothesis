module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.SiegelDensitiesLowAOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Cocompactness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Equidistribution
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HassePrinciple
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftSideFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalMassFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanValueFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormThetaMul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneVectorFormulaOfParts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeInvariance
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VectorLengthFormulaOfParts
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.SingleRowSide.Srside
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

namespace PositivityTheory.Rg.Mass

theorem e1 : E1 :=
  _root_.GlobalTheory.CompanionTheory.Mass.anisotropic_binary_one_vector_formula (_root_.GlobalTheory.CompanionTheory.Mass.One.vector_length_formula_up_to_constant _root_.GlobalTheory.CompanionTheory.MassCocompact.coCpt _root_.GlobalTheory.CompanionTheory.SW.LocBin.locMass) _root_.GlobalTheory.CompanionTheory.SW.MassSimil.simil _root_.GlobalTheory.CompanionTheory.SW.MassHasse.hasse
    (_root_.GlobalTheory.CompanionTheory.RgMass.cnt _root_.GlobalTheory.CompanionTheory.SW.MassTest.testEx (_root_.GlobalTheory.CompanionTheory.SW.LS.lside _root_.GlobalTheory.CompanionTheory.Equi.equi _root_.GlobalTheory.CompanionTheory.MassCocompact.coCpt)
      (PositivityTheory.Rg.Mass.LiteralAutomorphy.srside (_root_.GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd _root_.GlobalTheory.CompanionTheory.Equi.equi _root_.GlobalTheory.CompanionTheory.MassCount.countBd) _root_.GlobalTheory.CompanionTheory.SW.LocBin.locMass))

theorem oneVecBinary : PositivityTheory.PfSWUS.HMass.OneVecBinary := by
  intro F E _ _ _ _ _ σ hc M J hJ hM hA T hT hd
  subst hM
  exact e1 F E σ hc J hJ (fun x hx => by_contra fun h => hA x h hx) T hT hd

end PositivityTheory.Rg.Mass
