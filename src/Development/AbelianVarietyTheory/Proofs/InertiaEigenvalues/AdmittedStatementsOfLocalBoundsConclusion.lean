module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleTableOfLocalBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesConditionTwoThree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRamifiedTypePrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesRowsAndBand
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionFive
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesSizeConditionSix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalBoundTableAllPrimesVanishingExcluded
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

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.NLink

theorem admittedStatements_of_localBoundsConclusion : ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (X : KillingConditions.HubData D) (C : ℝ),
    Concl L P X C → ∃ tb : TwistedPlaces.Tab L, TwistedPlaces.AdmT L tb C P := by
  intro D L P X C h
  obtain ⟨tf, hF, h23⟩ := h.two
  refine ⟨tab L X tf C, ?_⟩
  have h2 : TwistedPlaces.adm2 L := fun j hj w hw _ => h.mult j hj w hw
  obtain ⟨hA, hB, hC, hD, hBand⟩ := _root_.GlobalTheory.NLink.localBoundTableAllPrimes_rowsAndBand D L P X C tf h
  obtain ⟨hE, hExc⟩ := _root_.GlobalTheory.NLink.largePrimeLengthVanishing_and_exceptionalBounded_tab D L P X C tf h
  obtain ⟨hG, hH⟩ := _root_.GlobalTheory.NLink.localBoundTableAllPrimes_ramified_typePrimes D L P X C tf h
  exact ⟨h.pass, h2, h.rank, _root_.GlobalTheory.NLink.admissible_table_of_conclusion D L P X C tf h h23, _root_.GlobalTheory.NLink.adm5_tab D L P X C tf h,
    _root_.GlobalTheory.NLink.adm6_tab D L P X C tf h, hA, hB, hC, hD, hBand, hE, hExc,
    _root_.GlobalTheory.NLinkAdmF.localBoundTableAllPrimes_conditionTwoThree D L P X C tf h hF, hG, hH, h.par⟩

end GlobalTheory.NLink
