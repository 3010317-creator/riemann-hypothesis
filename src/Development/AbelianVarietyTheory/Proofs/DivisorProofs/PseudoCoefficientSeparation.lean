module

public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSide
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleRepHasTraceFiniteAdelicPureTensorFunctStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TestDataHaarFactorization
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspMultiplicityCompletionEqDiscreteSeriesModelStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleUnitaryCompletionFiniteTimesDSStatement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryEquivIffFinitePartEquivDiscreteSeriesStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesMultiplicity
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumEqSumOfMatchingFamily
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
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryRepEqFiniteSmoothPartTensorDisStatement
import Mathlib.Tactic.Linter.HaveILetI

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSideStatement, Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissibleStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTerms, Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTermsStatement, Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientSeparation

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSideStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSideStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSide\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSideStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissibleStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissibleStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissible\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissibleStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTerms =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTerms", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule\nimport Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleRepHasTraceFiniteAdelicPureTensorFunctStatement\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TestDataHaarFactorization\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSideStatement\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartIrreducibleAdmissibleStatement\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleUnitaryRepEqFiniteSmoothPartTensorDisStatement\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTerms =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTermsStatement =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTermsStatement", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTerms\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTermsStatement =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientSeparation =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientSeparation", "h": "module\n\npublic import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.IsClosedEmbeddingOfLocallyCompact\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing\npublic import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsStandardIndModule\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteSeriesModelTraceTermsStatement\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspMultiplicityCompletionEqDiscreteSeriesModelStatement\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIrreducibleUnitaryCompletionFiniteTimesDSStatement\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryEquivIffFinitePartEquivDiscreteSeriesStatement\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.EllipticPartTestData\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesMultiplicity\npublic import Mathlib.Analysis.CStarAlgebra.Classes\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumEqSumOfMatchingFamily\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.TestDataHaarFactorization\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SpecTraceProof

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}


open Classical in
theorem isCopyFinDS_of_equiv {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ρ : GA D V →* (H →L[ℂ] H)} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    {σ : Representation ℂ (GfC V) W} {σ' : Representation ℂ (GfC V) W'} (f : σ.Equiv σ')
    (h : IsCopyFinDS σ M ρ ⊤) : IsCopyFinDS σ' M ρ ⊤ := by
  obtain ⟨T, hT, hinj, hspan⟩ := h
  refine ⟨T ∘ₗ f.symm.toLinearEquiv.toLinearMap, ?_, hinj.comp f.symm.toLinearEquiv.injective, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := mem_homTensorPi.1 hT
    refine mem_homTensorPi.2 ⟨fun _ _ => Submodule.mem_top, fun g w y => ?_, fun i g w y => h3 i g _ y⟩
    have e : f.symm.toLinearEquiv (σ' g w) = σ g (f.symm.toLinearEquiv w) :=
      LinearMap.congr_fun (f.symm.isIntertwining' g) w
    have h2' := h2 g (f.symm.toLinearEquiv w) y
    rw [← e] at h2'
    exact h2'
  · rw [← hspan]
    congr 2
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, Set.mem_setOf_eq]
    exact ⟨fun ⟨w, y, hv⟩ => ⟨_, y, hv⟩, fun ⟨w, y, hv⟩ => ⟨f.toLinearEquiv w, y, by simpa using hv⟩⟩


open Classical in
theorem isCopyFinDS_of_uEquiv {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {ρ : GA D V →* (H →L[ℂ] H)} {ρ' : GA D V →* (H' →L[ℂ] H')} {W : Type} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (GfC V) W} (hρ : UEquiv ρ ρ')
    (h : IsCopyFinDS σ M ρ ⊤) : IsCopyFinDS σ M ρ' ⊤ := by
  obtain ⟨A, hA⟩ := hρ
  obtain ⟨T, hT, hinj, hspan⟩ := h
  let C := (ContinuousLinearMap.compContinuousMultilinearMapL ℂ M.H H H'
    (A.toContinuousLinearEquiv : H →L[ℂ] H')).toLinearMap
  have hC : ∀ w y, (C ∘ₗ T) w y = A (T w y) := fun _ _ => rfl
  refine ⟨C ∘ₗ T, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3⟩ := mem_homTensorPi.1 hT
    refine mem_homTensorPi.2 ⟨fun _ _ => Submodule.mem_top, fun g w y => ?_, fun i g w y => ?_⟩
    · rw [hC, hC, h2, hA]
    · rw [hC, hC, h3, hA]
  · intro w w' e
    refine hinj (ContinuousMultilinearMap.ext fun y => A.injective ?_)
    rw [← hC, ← hC, e]
  · have hS : {v | ∃ w y, v = (C ∘ₗ T) w y} = A '' {v | ∃ w y, v = T w y} := by
      ext v
      simp only [hC, Set.mem_setOf_eq, Set.mem_image]
      exact ⟨fun ⟨w, y, hv⟩ => ⟨_, ⟨w, y, rfl⟩, hv.symm⟩, fun ⟨_, ⟨w, y, rfl⟩, hv⟩ => ⟨w, y, hv.symm⟩⟩
    rw [hS]
    have hd : Dense ((Submodule.span ℂ {v | ∃ w y, v = T w y} : Submodule ℂ H) : Set H) :=
      Submodule.dense_iff_topologicalClosure_eq_top.2 hspan
    refine Submodule.dense_iff_topologicalClosure_eq_top.1 ?_
    have e2 : (Submodule.span ℂ ((A.toLinearEquiv : H →ₗ[ℂ] H') '' {v | ∃ w y, v = T w y}) : Set H') =
        (A.toLinearEquiv : H →ₗ[ℂ] H') '' (Submodule.span ℂ {v | ∃ w y, v = T w y} : Set H) := by
      rw [Submodule.span_image, Submodule.map_coe]
    have e3 : (A.toLinearEquiv : H →ₗ[ℂ] H') '' {v | ∃ w y, v = T w y} = A '' {v | ∃ w y, v = T w y} := rfl
    rw [← e3, e2]
    exact A.surjective.denseRange.dense_image A.continuous hd

theorem not_isIntegralOp_zero {G W : Type} [Group G] [MeasurableSpace G] [AddCommGroup W] [Module ℂ W]
    {ν : Measure G} {σ : Representation ℂ G W} {F : G → ℂ} {c : ℂ}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ F c) (hc : c ≠ 0) : ¬ GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ F 0 := by
  intro h0
  obtain ⟨A, hA, -, rfl⟩ := h
  obtain rfl := hA.unique h0
  refine hc ?_
  have e : (LinearMap.restrict (0 : W →ₗ[ℂ] W) (p := LinearMap.range (0 : W →ₗ[ℂ] W))
      (q := LinearMap.range (0 : W →ₗ[ℂ] W)) fun v _ => LinearMap.mem_range_self _ v) = 0 :=
    LinearMap.ext fun x => Subtype.ext rfl
  rw [e, map_zero]

end GlobalTheory.SpecTraceProof

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoefficientSeparation =====
