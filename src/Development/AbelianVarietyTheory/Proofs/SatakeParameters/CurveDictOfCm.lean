module

public import Formalism.LocalToGlobal.InertKernelTheory.DefsRepDict
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.CM4
public import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BetaModelCoefficientsInvertL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoboundaryIntegralLawRespectsSimeq
public import Formalism.LocalToGlobal.InertKernelTheory.DefsSigma
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CurveLatticeSigmaTwoAlgebraicOfInvariantsAlgebra
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InverseSeriesFormalGroupIsoIntegral
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogCoordinatesExponentIsCoboundary
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhEquivShortWeierstrassModel
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaUnitFunctionShortModelIntegral
public import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.StatementW
public import Formalism.SharpRestriction.AdmissibleParameterJoins.GandSp
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnramifiedWeierstrassCurveTransformCoefficientsW
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe
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

namespace GlobalTheory.CurveDictionary

theorem curveDict_of_cm : Formalism.L2.Th1.CM.CM2 → Formalism.L2.Th1.CM.CM3 → Formalism.L2.Th1.CM.CM4 →
    Formalism.L2.KerInert.Rep.CurveDict := fun hGood _ hTor =>
  curveDict_of_inputs hGood hTor _root_.GlobalTheory.CurveSigmaAlg.secondEisensteinAlgebraic_of_invAlg _root_.GlobalTheory.CoefWfUnram.coefWf_phW _root_.GlobalTheory.BeCoefficients.beCoef _root_.GlobalTheory.CobExactProof.cobExact _root_.GlobalTheory.CobSimeqProof.cobSimeq
    _root_.GlobalTheory.ShortModelTie.phTie _root_.GlobalTheory.ShortModelTheta.thetaTie_holds _root_.GlobalTheory.InverseSeriesIntegral.v_integral

end GlobalTheory.CurveDictionary
