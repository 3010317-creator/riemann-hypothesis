module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfIntegralGaugedFormalGroupLaw
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugeDerivEqPairingOfIntegralGaugedLaw
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GaugedFormalGroupKernelSmallOfSecond
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsSelfConjugatePlace
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndSelfConjugatePlace
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IntegralGermsIndependentOfCurveSystem
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsIntegralGaugedFormalGroupLawSelfConjugateSquar
import Formalism.LocalToGlobal.CharacterGerms.RowTieAxes
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

@[expose] public section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem formal_statements_selfConj :
    CartSelfSt ∧ AxesSelfSt ∧ GermZeroSelfConjugate ∧ CEqSelfSt ∧ IndependenceBoundSelfConjugate := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact _root_.GlobalTheory.RowLaw.cartHyp_of_rlaw C V d _ _ _ (_root_.GlobalTheory.RowLawSquare.rlaw_rawSelf C V O dd Y d I0 p) (_root_.GlobalTheory.ProjSelf.hasProj_self C V O dd Y d I0 p)
      (_root_.GlobalTheory.hasTeich_selfData C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    have h := _root_.GlobalTheory.RowLawSquare.rlaw_rawSelf C V O dd Y d I0 p
    exact RawChart.axes_of _ h.exc h.axes
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact intGerm_indep_of_rlaw C V d _ _ _ (_root_.GlobalTheory.RowLawSquare.rlaw_rawSelf C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p _
    exact _root_.GlobalTheory.RowLaw.cEqSt_of_rLaw C V d _ _ _ (_root_.GlobalTheory.RowLawSquare.rlaw_rawSelf C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact _root_.GlobalTheory.RowKernel.independenceBoundCondition_of_rankMaximalCondition C V d _ _ _ (_root_.GlobalTheory.RowLawSquare.rlaw_rawSelf C V O dd Y d I0 p)

end GlobalTheory.RowLaw
