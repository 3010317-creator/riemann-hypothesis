module

public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimAtAuxiliaryPrimePlaces
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionComparisonAdmissibleEveryPlaceOver
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontainePropertiesAllPlacesAlt
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralTateH2Top
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalFieldsAtAuxiliaryPrimes
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAOfBlochKatoTateDualityEulerC
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfAdmittedHypotheses
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedHomsBoundedByClassNumberOfArtin
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachHypothesisCrystallineLattices
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtension
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatum
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedForms
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistedPlaceBound

theorem closing : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 2080 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → (∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.TameGeneratorConditions i) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D ∧ EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  intro hGAR hBKL hLTD hLEC D HW F Cm r ρ large₂ ep C Qp hC hQ hN5 hG1 hG2 hG3 hG4 hG5 hG6 hSet hKill hJump hFon hG5x hPar
  have hUsed := _root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm
  have hW : EmbeddingTypeJumps.admW (D := D) HW F := by
    intro i _ w hw Cf h
    exact _root_.GlobalTheory.WachHyp.hypW_crystalline D HW F Cm hUsed.1 hUsed.2 (GlobalTheory.crysOnCond_all D HW F) (D.nd.l i) _ 1 Cf.LL h
  have hA : EmbeddingTypeJumps.admA (D := D) 160 := _root_.GlobalTheory.theoremA_closing hBKL hLTD hLEC D HW F Cm 160 le_rfl
  have hTB : EmbeddingTypeJumps.admTB (D := D) HW F := _root_.GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar hBKL hLTD hLEC D HW F Cm
  have hBK : EmbeddingTypeJumps.admBK (D := D) := _root_.GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ hBKL hLTD hLEC D
  have hLit : EmbeddingTypeJumps.LiteratureHypotheses (D := D) := by
    intro i hi
    refine ⟨hG5x i hi, fun w hw Cf => ⟨?_, _root_.GlobalTheory.InertiaEigenvalues.DimAtQD.main hLTD hLEC D i hi w hw Cf⟩,
      GlobalTheory.BridgeTie.localCoefficientCompatibility D i, GlobalTheory.FontaineAdm.fontaineProperties_all_places D i, _root_.GlobalTheory.IntTateTop.admH2_of_duality hLTD D i,
      _root_.GlobalTheory.UnramifiedHomBound.unramified_homs_bounded_by_class_number_of_artin hGAR D i⟩
    exact Formalism.MainNotions.TruncatedSeriesCountingIdentities.tate_duality_h2_of_all_coefficients _ _ _
      (GlobalTheory.TateTop.tateH2_of_duality_loc hLTD (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw)
      (GlobalTheory.HTW.Rec.goodO_finExt_integers (D.nd.l i) Cf.LL)
  have h01 := _root_.GlobalTheory.LocalFieldsQD.main D
  refine ⟨h01.1, h01.2, ?_⟩
  exact _root_.GlobalTheory.TheoremB.theoremB_of_admitted D HW F r ρ large₂ ep 160 C Qp (by rw [max_eq_left (by norm_num)]; linarith) hQ hW hA
    hN5 hG1 hG2 hG3 hG4 hG5 hG6 hSet hTB hBK hKill hJump hFon hLit hPar

end GlobalTheory.TwistedPlaceBound
