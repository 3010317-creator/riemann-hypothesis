module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExist
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmNormalizedThetaJetsIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaFunctionsOverTwoUnitAndIntegral
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaValuesVanishAtOddSplitPrime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisDataExists
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertPrimeOrderParitySignRadicalIntegralForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTaylorCoeffsAlgebraicAtComplexMultiplicatio
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumNormConjCmPointsAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaComplexConjugationCompatible
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTorsionTranslateIntegralSeries
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationVacuumSignInertPlaces
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

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum

theorem inp_all : ∀ D, Inp D := fun D =>
  { g1 := (_root_.GlobalTheory.InducedType.induced_type D).1
    perm := (_root_.GlobalTheory.InducedType.induced_type D).2
    uni := _root_.GlobalTheory.theta_translation_intertwiner_unitary D
    mu := _root_.GlobalTheory.TripleIntertwiner.triple_constant D
    curve := _root_.GlobalTheory.ConjCurve.galCurve_holds D
    gal := _root_.GlobalTheory.GalTheta.gal_all D
    galEx := _root_.GlobalTheory.GalExist.galEx_all D
    t0Ex := _root_.GlobalTheory.TwoTorsionPt.exists_point D
    use1 := _root_.GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D
    alg := _root_.GlobalTheory.ThetaAlgebraic.taylor_algebraic D
    conj := _root_.GlobalTheory.ThetaConj.useConj_all D
    nrm := _root_.GlobalTheory.ConjNorm.useNorm_all D
    bar := _root_.GlobalTheory.ThetaConj.useBar_holds D
    odd3 := _root_.GlobalTheory.InertSign.vacuum_inert D
    odd4 := _root_.GlobalTheory.VacuumScalar.vacuum_scalar D
    rep := _root_.GlobalTheory.NormSum.exists_rep_trivial_at D
    model := _root_.GlobalTheory.UnitModel.modelEx_holds D
    transl := _root_.GlobalTheory.ThetaTransl.transl_holds D
    two := _root_.GlobalTheory.EvenTheta.atTwo D
    jets := _root_.GlobalTheory.ThetaJets.jetsPh_all D
    split := _root_.GlobalTheory.ThetaSplit.splitZero D
    eqv := GlobalTheory.OddRank.exact_equivariance D }

end GlobalTheory.NormSum
