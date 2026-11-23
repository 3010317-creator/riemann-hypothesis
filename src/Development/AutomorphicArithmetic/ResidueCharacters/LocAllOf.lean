module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AutomorphicArithmetic.ResidueCharacters.InvariantsKilledOverCyclotomicAlt
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoLocalAllOfTateDualityEulerChar
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrysOnCondOfEveryDatum
public import Formalism.SharpRestriction.LevelLetterCocycles.ElementDenominator
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineRestrictFiniteExtensionJumps
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineAtAll
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremTbOfLocalBlochKatoDualityEuler
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentKillsInvariantsNoJumpZero
public import Development.AutomorphicArithmetic.ResidueCharacters.InvariantsKilledOverCyclotomic
public import Development.AutomorphicArithmetic.ResidueCharacters.LiftKOf
public import Development.AutomorphicArithmetic.ResidueCharacters.TbKOf
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiesAndInputsOfDualityEuler
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

theorem UpperTheory.N.locAll_of (hbk : GlobalTheory.Published.BlochKatoLocal) (htd : Formalism.GaloisCohomology.LocalTateDualityK)
    (hec : Formalism.GaloisCohomology.LocalEulerCharK) (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (h54 : LiftingTheory.LiftTheoremAllCases D HW F 23 32 32)
    (hW : ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
      EmbeddingTypeJumps.WachHypothesisLocal (LocalSituation.sit D.loc HW l (D.locA l) K s LL h) ((F l).E K s LL h).tie) :
    UpperTheory.N.LiftK (D.loc l) ∧ UpperTheory.N.InvariantsKilledOverCyclotomic (D.loc l) ∧ UpperTheory.N.TBK (D.loc l) := by
  have hres : ElementDenominator.CrystallineRestrictionToExtension D.loc := _root_.GlobalTheory.Per.ResFinite.adm12_elementDenominator D
  have hF := GlobalTheory.FontaineAll.fontaineAt_all D l
  obtain ⟨_J, hA⟩ := GlobalTheory.LocInputs.ties_and_inputs_of_duality_euler htd hec D HW F
  exact ⟨UpperTheory.N.liftK_of D HW F l h54 hres hF,
    UpperTheory.N.invariants_killed_over_cyclotomic_subfield_of_admissible D HW F l hW (fun K s LL h => _root_.GlobalTheory.HubX.InvariantsNoJump.torsion_exponent_kills_invariants_no_jump_zero hbk htd hec D HW F Cm l K s LL h) hres hF,
    UpperTheory.N.tbK_of D HW F l (_root_.GlobalTheory.TheoremTBRecords.aux_of_blochKato_tateDuality_eulerChar hbk htd hec D HW F Cm) (_root_.GlobalTheory.crysOnCond_all D HW F) hW
      (UpperTheory.N.TwistK.tbe_all D HW F hA (_root_.GlobalTheory.BlochKatoLocalAllOfTateDualityEulerChar₂.aux_of_blochKato_tateDuality_eulerChar₂ hbk htd hec D) l) hres hF⟩
