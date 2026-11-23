module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteCutoffBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AbsoluteFourierCoefficientsStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CasimirOperatorFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureOperatorFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactSobolevEmbedding
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcentrationTimeBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenseDomainFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FriedrichsExtensionFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusCurve
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusFirstAssumption
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelLocalization
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelRegularity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelWeightFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PaleyWienerDecay
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionNormBound
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothOperatorFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevOperatorFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSpacePreserved
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WvAlg
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.AsmKerOneOfSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevIntegrationByParts
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

namespace PositivityTheory.RgBcC.Fc

open PositivityTheory.RgBcC

theorem calcSteps : CalcSteps :=
  ⟨GlobalTheory.T.absolute_fourier_coefficients, _root_.GlobalTheory.CompanionTheory.FcCut.absCut, _root_.GlobalTheory.CompanionTheory.WaveCurve.fcurve, GlobalTheory.CompanionTheory.WaveFc.wvAlg, _root_.GlobalTheory.CompanionTheory.FcCls.clsFacts, _root_.GlobalTheory.CompanionTheory.SobOpsPf.sobOps, _root_.GlobalTheory.CompanionTheory.CptSobProof.cptSob,
    _root_.GlobalTheory.CompanionTheory.SecBd.secBound_main, _root_.GlobalTheory.CompanionTheory.PresSobA.presSob, _root_.GlobalTheory.CompanionTheory.FcConcT.concT, _root_.GlobalTheory.CompanionTheory.CurveJ.curveJoint, _root_.GlobalTheory.CompanionTheory.FriedrichsFc.friedrichs, _root_.GlobalTheory.CompanionTheory.Casimir.omFormula, _root_.GlobalTheory.CompanionTheory.FcCalc.Ibp.ibpSob,
    GlobalTheory.T.dense_domain_facts⟩

theorem asmCpt : AsmCpt :=
  _root_.GlobalTheory.CompanionTheory.WaveFc.Asm.asm1 GlobalTheory.T.absolute_fourier_coefficients _root_.GlobalTheory.CompanionTheory.FcCut.absCut _root_.GlobalTheory.CompanionTheory.WaveCurve.fcurve GlobalTheory.CompanionTheory.WaveFc.wvAlg _root_.GlobalTheory.CompanionTheory.FcCls.clsFacts _root_.GlobalTheory.CompanionTheory.SobOpsPf.sobOps _root_.GlobalTheory.CompanionTheory.CptSobProof.cptSob
    _root_.GlobalTheory.CompanionTheory.SecBd.secBound_main _root_.GlobalTheory.CompanionTheory.PresSobA.presSob _root_.GlobalTheory.CompanionTheory.FcConcT.concT _root_.GlobalTheory.CompanionTheory.CurveJ.curveJoint _root_.GlobalTheory.CompanionTheory.FriedrichsFc.friedrichs _root_.GlobalTheory.CompanionTheory.Casimir.omFormula _root_.GlobalTheory.CompanionTheory.FcCalc.Ibp.ibpSob _root_.GlobalTheory.CompanionTheory.DenseCpt.denseD

theorem asmKerOne : AsmKerOne :=
  asmKerOne_of_steps asmCpt calcSteps _root_.GlobalTheory.CompanionTheory.FcSmooth.smoothOp _root_.GlobalTheory.CompanionTheory.WaveCurve.Decay.pwdecay _root_.GlobalTheory.CompanionTheory.KerFc.kerCore _root_.GlobalTheory.CompanionTheory.WaveLoc.kerLoc _root_.GlobalTheory.CompanionTheory.KerWord.kerW

end PositivityTheory.RgBcC.Fc
