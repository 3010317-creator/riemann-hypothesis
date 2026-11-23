module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingIdentityOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityInert
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermStar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchLeviWordsOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOf
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RegularPowerTorus
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparablePowerTorus
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

@[expose] public section

namespace PositivityTheory.Rg.BcB.F.MLM

theorem matchLMIdOf : MatchLMIdOf := _root_.GlobalTheory.CompanionTheory.MatchId.matchLMIdOf
theorem matchLMUnitOf : MatchLMUnitOf := _root_.GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf

theorem muInert : MuInert := _root_.GlobalTheory.CompanionTheory.MuInertPlace.muInert
theorem regPowT : RegPowT := _root_.GlobalTheory.CompanionTheory.RegPow.regPowT
theorem sepPowT : SepPowT := _root_.GlobalTheory.CompanionTheory.SepPow.sepPowT
theorem ctStar : CtStar := _root_.GlobalTheory.CompanionTheory.CtAdj.ctStar
theorem matchLMWordSOf : MatchLMWordSOf := _root_.GlobalTheory.CompanionTheory.LeviMatchingWords.matchLMWordSOf

end PositivityTheory.Rg.BcB.F.MLM
