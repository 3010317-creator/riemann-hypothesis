module

public import Formalism.GaloisCohomology.LocalTateDualityK
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
public import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationSaturationKiller
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleArcDatumGivesArcProperty
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ArcTheoremToolsOfWachModuleConclusions
public import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterion
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClassSplittingAlongArcsOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineUniversalPartCaseA
public import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DDeRhamEqDCrisOfUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisExactStrictElementwiseCrystalline
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFullFaithfulExactPsi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fGenerationUnramified
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrExtensionClassFormula
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JumpsExactAdm
public import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatements
public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleLocalConclusionsUsedForms
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachRelayLemmaArcCoordinateHypotheses
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineDcris
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeLaterClausesHold
import Formalism.SharpRestriction.LevelLetterCocycles.DivisibilityInvariantMulLinear
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

namespace GlobalTheory.TheoremBAdm

theorem admissible_ranks_of_CMDatum : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
      ArcLiftingSetup.admitted D HW F Cm 10 23 32 32 8 := by
  intro hBK hTD hEC D HW F Cm
  have hN1 := _root_.GlobalTheory.NL.wach_used_clauses D HW F Cm
  obtain ⟨hP1, -, -, -, -, hP6, -, hP8, hP9, -⟩ := hN1
  have h54 := _root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hBK hTD hEC D HW F Cm
  obtain ⟨-, ⟨hWX, -⟩, hW1, -, -, hH, -, -⟩ := h54
  have hB := _root_.GlobalTheory.ArcTools.arc_tools_from_clauses D HW F Cm
  obtain ⟨hSat, -, hSatP, hPi0, hKL, hKill, -, hF1, -⟩ := hB
  obtain ⟨hRelay, hArcAdm⟩ := _root_.GlobalTheory.NQ.relay_and_arc_inputs hBK hTD hEC D HW F Cm
  have hA11 := _root_.GlobalTheory.Per.DcrisExact.fontaine_dcris D
  have hArc := _root_.GlobalTheory.admissibleArcDatum_gives_arcProperty D HW F Cm hArcAdm hP1 hA11
  have hJ := (GlobalTheory.jumps_exact_adm D HW F).2
  have hExt := GlobalTheory.HerrExtClass.herr_extension_class_formula D HW F
  have hAdm9 := _root_.GlobalTheory.dcris_exact_strict_elementwise D
  have hSplit := _root_.GlobalTheory.classSplitAlongArcs D HW F Cm ⟨hP8, hP9, hW1, hJ, hExt, hF1, hRelay, hArc⟩ hArcAdm hP1 hP6 hWX
    (_root_.GlobalTheory.fontaine_litFont_assembled D HW F) hJ hAdm9 hA11
  have hUniv := _root_.GlobalTheory.universalPart_caseA D HW F Cm ⟨hSat, hKL, hPi0, hArc⟩ hP9 hH (_root_.GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange D)
  exact ⟨(_root_.GlobalTheory.NL.usedLocalConclusion_and_prvE D HW F Cm).1, _root_.GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt hBK hTD hEC D HW F Cm, hSat, hSatP, hKill,
    ArcLiftingSetup.content_divisibility_clause D, _root_.GlobalTheory.GenCountUnram.admGenL_all D, hRelay, hArc, hSplit, hUniv, hAdm9, _root_.GlobalTheory.ExtCrysCrit.blochKato_ext_all D⟩

end GlobalTheory.TheoremBAdm
