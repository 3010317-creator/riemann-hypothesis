module

public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimFormulaAllLocalSituations
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaSubOneDivUniformiserAtLetterOfConclusions
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGeneratorsAll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrExtensionClassFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrPartAEveryRecord
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedForms
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.HerrDescriptionH1OfHerr
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHold
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

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.TheoremCAdm

theorem admissible_ranks_of_CMDatum : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      RamifiedCoefficientChains.admitted D HW F Cm 10 23 32 32 := by
  intro hBK hTD hEC D HW F Cm
  have hU := (_root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm).1
  have h54 := _root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hBK hTD hEC D HW F Cm
  have h6a := GlobalTheory.HerrFull.herr_part_a_every_record D HW F
  exact ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2,
    RamifiedCoefficientChains.sizes_bound_of_log_estimates D HW F h54, RamifiedCoefficientChains.restriction_dimension_of_division D HW F h54, RamifiedCoefficientChains.level_tools_of_admitted D HW F h54, RamifiedCoefficientChains.lemma_M_prime_hypothesis D HW F h54,
    RamifiedCoefficientChains.crystalline_lift_of_theorem_c D HW F h54, RamifiedCoefficientChains.lifting_bounds_of_theorem_c D HW F h54,
    _root_.GlobalTheory.Per.DcrisExact.fontaine_dcris D, _root_.GlobalTheory.blochKatoDim_at_every_local_situation D, _root_.GlobalTheory.h1f_generators_of_record D,
    Formalism.MainNotions.N.herr_description_H1_of_herr D HW F h6a, _root_.GlobalTheory.ExtCrysCrit.blochKato_ext_all D,
    GlobalTheory.HerrExtClass.herr_extension_class_formula D HW F,
    Formalism.MainNotions.HerrComplexNaturality.herr_naturality_theorem_holds D HW F h6a,
    _root_.GlobalTheory.adm18_of_N1used D HW F Cm (_root_.GlobalTheory.NL.wach_used_clauses D HW F Cm),
    _root_.GlobalTheory.GenCountUnram.admGenL_all D⟩

end GlobalTheory.TheoremCAdm
