module

public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CohomologyShapeOfTateDualityEuler
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrFiniteOverPadicTopologiesExist
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinIsoDualLatticeOfLocalTateDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHomModuloUnramifiedShapeOfLocalDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralLocalDualityOfLocalTateDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvIsoOfLocalTateDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalCohomologySevenElementaryFacts
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalLocalDualityOfLocalTateDuality
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOfLocalCohomologyShape
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedGaloisHomsBoundedClassNumberOfArtinRec
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedPadicDecompositionHomExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatInvIsoOfLocalTateDualityCyclotomicTwist
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

namespace GlobalTheory

theorem langRecCore_of_artinReciprocity (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hT : Formalism.GaloisCohomology.LocalTateDualityK)
    (hE : Formalism.GaloisCohomology.LocalEulerCharK) : ReciprocityTheory.ChartRestriction.T2.Core :=
  { dec := _root_.GlobalTheory.DecLocal.decEquiv,
    inv := _root_.GlobalTheory.InvColim.inv_iso hT,
    fin := _root_.GlobalTheory.FinIsoDualLattice.finIso_of_localTateDuality hT,
    rat := _root_.GlobalTheory.ratIso_of_localTateDuality hT,
    int := _root_.GlobalTheory.LocDualInt.int_iso_of_localTateDuality hT,
    jspan := _root_.GlobalTheory.jSpan_holds,
    nat := _root_.GlobalTheory.natInvIso_of_localTateDuality hT,
    shape := _root_.GlobalTheory.ShapeNeg.shapeG_of_localDuality hT hE,
    shapeUnr := _root_.GlobalTheory.ShapeUnrTriv.shapeUnr_of_localDuality hT hE,
    unr := _root_.GlobalTheory.UnrChar.unrDec,
    vhE := _root_.GlobalTheory.UnramifiedClassBound.vhE_of_globalArtinReciprocity hA,
    top := _root_.GlobalTheory.PadicTop.topEx,
    elem := _root_.GlobalTheory.LocElem.elem }

end GlobalTheory
