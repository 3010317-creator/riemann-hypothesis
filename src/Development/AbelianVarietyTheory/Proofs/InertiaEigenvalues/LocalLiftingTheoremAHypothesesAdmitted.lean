module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ElementDenominatorAdm7
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisRest
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingBounds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremWachModuleLemmaHypothesesAdmitted
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictAdm
public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedForms
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.ArchimedeanSignatureMatchingOfLiftingTheory
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1fStatement
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AdmittedPartOne

theorem all_admitted : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ElementDenominator.Adm1 D HW F Cm 23 32 32 := by
  intro hBK hTD hEC D HW F Cm
  have hU := (_root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm).1
  have h54 := _root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hBK hTD hEC D HW F Cm
  have hA := (_root_.GlobalTheory.LiftAdmitted.all_admitted D HW F Cm).1
  refine ⟨hU.1, hU.2.2.1, GlobalTheory.T.restriction_corestriction_H1f D HW F, hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    GlobalTheory.AdmHerrLocal.main D HW F, hU.2.2.2, archimedean_signature_matching_of_liftingTheory D HW F 23 32 32 10 h54,
    lifting_input_five_of_lifting D HW F 10 23 32 32 h54, lifting_input_six_of_lifting D HW F 10 23 32 32 h54,
    _root_.GlobalTheory.elementDenominator_adm7 D, GlobalTheory.Per.FontaineAdm.fontaine_bounds D, GlobalTheory.Per.StrictAdm.strict_adm D, _root_.GlobalTheory.Per.ResFinite.adm12_elementDenominator D⟩

end GlobalTheory.AdmittedPartOne
