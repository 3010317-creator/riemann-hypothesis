module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsPullbackMetricFlagRefinement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopFormSignedMeasureEqAtlasPart
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeEqChernFormIntegralOfComplexCase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleFibreIntegralPullbackMulFibreClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGradedMetricsWeightsOnLineBundles
public import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolyEqIntersectionNumber
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormsEqEsymmGradedFormsFlag
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormEvalRealPolyChernFormsFlaggedMetric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackRealPolynomialEvenFormFields
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgAtlasAtlasOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlaggedBundleMetricPullGramRefinement
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

@[expose] public section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

theorem GlobalTheory.ChernCalc.chernWeilNumbers_of_chernDegreeComplex :
    GlobalTheory.Published.ChernDegreeComplex → GlobalTheory.Published.ChernWeilNumbers := by
  intro h F _ σ X Y ι _ m E E' φ f gr hR hG H hH R
  have hD : GlobalTheory.Published.ChernDegree := _root_.GlobalTheory.ChernDegreeBaseChange.chernDegree_of_complex h
  have hf : f ≫ X.str = Y.str := hR.hom.inducedModelMorphism_comp_structureMap
  have hform := _root_.GlobalTheory.ChernCalc.isForm_evalF_chernF F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH) R
  have hM := _root_.GlobalTheory.ChernCalc.isMetricFr_pullGram F σ X Y ι m E E' φ f hf hR H hH
  have hu : ptsIn X.str σ ⊤ = Set.univ := Set.eq_univ_of_forall fun _ => mem_ptsIn_top
  choose L r ψ h1 h2 h3 using _root_.GlobalTheory.ChernCalc.graded_weight F σ Y ι m E' _ gr hG hM
  have e : grF E' (pullGram E H φ f hf) = fun x => c1W (ψ x) := funext fun x => (h3 x).symm
  unfold HasChernIntegral
  rw [hu]
  simp only [_root_.GlobalTheory.ChernCalc.chernTopPart_eq_part F σ X ι m E H R]
  refine ⟨fun ε => ?_, ?_⟩
  · have := (_root_.GlobalTheory.LineForm.wInt_props _ _ (atlas X σ)).1 _ hform ε
    exact measure_ne_top _ _
  · refine (_root_.GlobalTheory.ChernCalc.fibre_integral F σ X Y ι m E E' φ f hf hR H hH _ hform).symm.trans ?_
    rw [_root_.GlobalTheory.LineForm.pullback_evalF _ _ _ _ _ _ _ _ _ _ (_root_.GlobalTheory.ChernCalc.pullback_chernF F σ X Y ι m E E' φ f hf hR H hH) R,
      _root_.GlobalTheory.ChernCalc.integral_chernF_mul_grF F σ Y ι m E' _ hM, e]
    exact _root_.GlobalTheory.ChernLine.integral_evalF_c1W_eq_interPoly hD F σ Y _ gr L r ψ (fun a => ⟨h1 a, h2 a⟩) _
