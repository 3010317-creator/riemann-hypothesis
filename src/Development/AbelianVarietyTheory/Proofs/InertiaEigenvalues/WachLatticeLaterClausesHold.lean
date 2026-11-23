module

public import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
public import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CokernelCrystallineSurjectionKilledByXPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineExtensionIntegralCocycleAllPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefectTorsionSecondCohomologyKernel
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LettersFree
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHolds
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemH1fIffResMem
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeComparisonDcris
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeExpansionAtLowLevelPoints
public import Formalism.SharpRestriction.LevelLetterCocycles.GammaSemisimpleLocalOfConsequences
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleConsequencesPoleQuotient
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleDescentToTameSubextension
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleSaturatedExactnessCrystalline
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonOfWachBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocyclePolesFrobeniusQCrystalline
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrH1Description
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachIntegralComplexCocycleClassFinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachModuleUniquenessCharacterisation
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

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL

theorem wach_used_clauses (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) : DeltaInvariantNormBound D HW F Cm := by
  unfold DeltaInvariantNormBound
  refine ⟨GlobalTheory.NL.LetterFree.letters_free D HW F, GlobalTheory.NL.WachLatticeTrivialModUniformizer.wachLattice_galois_trivial_mod_uniformizer D HW F Cm,
    GlobalTheory.NL.CmpCris.wachLattice_comparison_dcris D HW F Cm, _root_.GlobalTheory.NL.LatLevel.lattice_at_level D HW F Cm, _root_.GlobalTheory.NL.Heights.heights_from_jumps D HW F Cm,
    _root_.GlobalTheory.NL.Exact.exactness_of_N D HW F Cm, _root_.GlobalTheory.NL.PoleCrys.main D HW F, _root_.GlobalTheory.NL.NygaardFrobeniusPower.crystalline_extension_integral_cocycle_all_places D HW F Cm, _root_.GlobalTheory.NL.p9_statement D HW F,
    _root_.GlobalTheory.NL.FrobeniusMatrixUniqueness.main D HW F, _root_.GlobalTheory.NL.WachModulePoleQuotient.wachModule_consequences_poleQuotient D HW F Cm, GlobalTheory.NL.HerrComplexH1.herr_H1_description D HW F,
    GlobalTheory.NL.FiniteRestrictionH1f.mem_H1f_iff_res_mem D HW F, _root_.GlobalTheory.NL.IntComplex.main D HW F, _root_.GlobalTheory.NL.DefectTorsion.defect_torsion D HW F Cm,
    _root_.GlobalTheory.NL.CokerKill.X_pow_kills_coker D HW F Cm, ?_⟩
  unfold ConclusionE
  exact ⟨GlobalTheory.NL.NygaardExtension.main D HW F, _root_.GlobalTheory.NL.SandJumps.main D HW F Cm⟩

end GlobalTheory.NL
