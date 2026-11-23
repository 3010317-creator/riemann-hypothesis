module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BoundAtTwoThreeFamilyFon
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineLatticeWachModuleExistsProof
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DecompositionInvariantsCondition
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LenUnitInvariantsTwistedLatticeLeOfKillingExpone
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxLengthLocalInvariantsTwistedFractionModIntege
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionExponentKillsInvariantsNoJumpZero
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreExtraStatement
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

@[expose] public section



section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
namespace GlobalTheory.NSizes
theorem main_alt_alt : Hypotheses₂ → ∀ (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (nch : NChoice D) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (X : KillingConditions.HubData D) (C₂ : ℝ), _root_.GlobalTheory.NLink.SetupAlt L nch HW X C₂ → KillingConditions.InvariantsBoundsWithCoarseColumnConstant L X 120 := by
  intro hP D L P nch HW F Cm X C₂ hS
  have hb : ((0 : ℕ) : ℝ) ≤ L.sc.b := by
    simp only [Nat.cast_zero]
    exact (Real.exp_pos _).le
  have hub := _root_.GlobalTheory.T.split_bound_of_params_alt hP.font hP.fin GlobalTheory.Published.cheb_holds D L HW F (rowC C₂) nch X 120 0 hS.canon P
    (le_trans (by norm_num) hS.big) le_rfl hb (hS.facts.admJ L hS.par) hS.par67 hS.facts.toCore.admA
    hS.facts.Conclusion1.1 hS.facts.Conclusion1.2.2 hS.facts.Conclusion2.1 hS.facts.Conclusion2.2.2 hS.facts.rhoBar hS.facts.large.2.1
    hS.facts.large.2.2 hS.facts.nct hS.facts.trip hS.facts.same hS.facts.block hS.facts.muUnr hS.facts.depthG
  obtain ⟨-, -, -, -, hCB, hC0, ⟨M0, h0', hW⟩, -⟩ := hub
  intro i hT hg hR
  refine ⟨hCB i hT hg hR, ?_, ?_⟩
  · have h := _root_.GlobalTheory.InvariantsKO.main D i (X.dc i).col (fun h => hR.1 (Or.inl h)) (fun h => hR.2.1 (Or.inl h))
      (fun h => hR.2.1 (Or.inr h)) (fun u hu => ((X.dc i).cover u).1 (Or.inr hu))
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  · intro hsp u hu
    refine ⟨hC0 i hT hg hR hsp u hu, fun π hπ => ?_⟩
    obtain ⟨hu', s, hs, hc, hcrys, hJ, hnj, hcle⟩ := hW i hT hg hsp u hu π hπ
    have hWat := _root_.GlobalTheory.NLink.wAll_holds D HW F Cm (D.nd.l i) (D.nbr i u hu').Kw s (D.nbr i u hu').LL hs
    have hHW := hWat (GlobalTheory.HubX.wLat D i (X.ρ i) π u hu' hc) M0 h0' hcrys hJ
    have hkill := _root_.GlobalTheory.HubX.InvariantsNoJump.torsion_exponent_kills_invariants_no_jump_zero hP.bk hP.tate hP.euler D HW F Cm (D.nd.l i) (D.nbr i u hu').Kw s (D.nbr i u hu').LL hs
      M0 h0' (GlobalTheory.HubX.wLat D i (X.ρ i) π u hu' hc) hHW hnj
    have hlen := _root_.GlobalTheory.LengthH0Bound.main D HW i (X.ρ i) π u hu' s hs hc (X.c0 i u) _ rfl (by
      intro x hx
      have e := hkill x hx
      rw [← Nat.sub_add_cancel hcle, pow_add, mul_smul, e, smul_zero])
    have h1 := hC0 i hT hg hR hsp u hu
    have hr : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
    calc (Br.h0W i u (X.ρ i) π : ℝ) ≤ (D.R.r : ℝ) * (X.c0 i u : ℕ) := hlen
      _ ≤ (D.R.r : ℝ) * (120 * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L) := mul_le_mul_of_nonneg_left h1 hr
      _ = 120 * D.R.r * D.R.n * D.R.nV * Formalism.MainNotions.TwistedPlaces.large₂ L := by ring
end GlobalTheory.NSizes
end
