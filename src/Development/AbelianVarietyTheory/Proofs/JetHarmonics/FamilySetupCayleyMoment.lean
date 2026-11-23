module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyWeightedStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FixesWedgeAndForm
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFRepDualStandardUnitaryRep
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LenEqOfUnitriangular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NumericalFamilyShapeGaps
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuotientMeasureAeMemAndMeasurableBesselModelStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormSqHermTranslatesOrthonormalStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorBesselTransferStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGlProjectionLevelSumSqLeStatement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomentStep

theorem lintegral_le_of_le_sum {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι] (ν : Measure Ω) (f : Ω → ℝ)
    (g : ι → ι → Ω → ℝ) (C : ℝ) (N : ι → ι → ℝ) (hC : 0 ≤ C) (hg0 : ∀ d s x, 0 ≤ g d s x)
    (hm : ∀ d s, AEMeasurable (g d s) ν) (hpt : ∀ᵐ x ∂ν, f x ≤ C * ∑ d, ∑ s, g d s x)
    (hN : ∀ d s, 0 ≤ N d s) (hint : ∀ d s, ∫⁻ x, ENNReal.ofReal (g d s x) ∂ν ≤ ENNReal.ofReal (N d s)) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂ν ≤ ENNReal.ofReal (C * ∑ d, ∑ s, N d s) := by
  calc ∫⁻ x, ENNReal.ofReal (f x) ∂ν
      ≤ ∫⁻ x, ENNReal.ofReal C * ∑ d, ∑ s, ENNReal.ofReal (g d s x) ∂ν := by
        refine lintegral_mono_ae (hpt.mono fun x hx => ?_)
        refine (ENNReal.ofReal_le_ofReal hx).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg fun d _ => Finset.sum_nonneg fun s _ => hg0 d s x]
        congr 1
        exact Finset.sum_congr rfl fun d _ => ENNReal.ofReal_sum_of_nonneg fun s _ => hg0 d s x
    _ = ENNReal.ofReal C * ∑ d, ∑ s, ∫⁻ x, ENNReal.ofReal (g d s x) ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun d _ => Finset.aemeasurable_fun_sum _ fun s _ => (hm d s).ennreal_ofReal]
        congr 1
        exact Finset.sum_congr rfl fun d _ => lintegral_finsetSum' _ fun s _ => (hm d s).ennreal_ofReal
    _ ≤ ENNReal.ofReal C * ∑ d, ∑ s, ENNReal.ofReal (N d s) := by
        gcongr with d _ s _
        exact hint d s
    _ = _ := by
        rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_sum_of_nonneg fun d _ => Finset.sum_nonneg fun s _ => hN d s]
        congr 1
        exact (Finset.sum_congr rfl fun d _ => ENNReal.ofReal_sum_of_nonneg fun s _ => hN d s).symm

theorem norm_sum_smul_sq_le {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (c : ι → ℂ)
    (v : ι → V) : ‖∑ s, c s • v s‖ ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ s, ‖c s‖ ^ 2 * ‖v s‖ ^ 2 := by
  have h1 : ‖∑ s, c s • v s‖ ≤ ∑ s, ‖c s‖ * ‖v s‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun s _ => norm_smul _ _))
  have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun s => ‖c s‖ * ‖v s‖)
  simp only [mul_pow, Finset.card_univ] at h2
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem pointwise_le {V ι : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [Fintype ι] (L D A : ℝ) (q : ℕ)
    (a β : ι → ℂ) (Ds : ι → ℝ) (v : V) (y : ι → ι → V) (hD : 0 ≤ D) (hL : ∑ d, ‖a d‖ ^ 2 = L ^ 2)
    (he : ∀ d, a d • v = ∑ s, β s • y d s) (hβ : ∀ s, ‖β s‖ ^ 2 * D ≤ A * Ds s) :
    L ^ (2 * (q + 1)) * (D * ‖v‖ ^ 2) ≤
      ((Fintype.card ι : ℝ) * A) * ∑ d, ∑ s, L ^ (2 * q) * (Ds s * ‖y d s‖ ^ 2) := by
  have hP : 0 ≤ L ^ (2 * q) := by rw [pow_mul]; positivity
  have e1 : L ^ (2 * (q + 1)) * (D * ‖v‖ ^ 2) = ∑ d, L ^ (2 * q) * (D * ‖a d • v‖ ^ 2) := by
    rw [mul_add, pow_add, mul_one, ← hL, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [norm_smul]; ring
  rw [e1, Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [he d]
  calc L ^ (2 * q) * (D * ‖∑ s, β s • y d s‖ ^ 2)
      ≤ L ^ (2 * q) * (D * ((Fintype.card ι : ℝ) * ∑ s, ‖β s‖ ^ 2 * ‖y d s‖ ^ 2)) := by
        gcongr
        exact norm_sum_smul_sq_le β (y d)
    _ = ∑ s, (Fintype.card ι : ℝ) * L ^ (2 * q) * ‖y d s‖ ^ 2 * (‖β s‖ ^ 2 * D) := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring
    _ ≤ ∑ s, (Fintype.card ι : ℝ) * L ^ (2 * q) * ‖y d s‖ ^ 2 * (A * Ds s) := by
        exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hβ s) (by positivity)
    _ = _ := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring

theorem lOneNorm_sub_single_one_le {n : ℕ} (ν : Fin n → ℤ) (s : Fin n) : n1 (ν - Pi.single s 1) ≤ n1 ν + 1 := by
  have h1 : ∑ i, ((Pi.single s 1 : Fin n → ℤ) i).natAbs = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  unfold n1
  rw [← h1, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => Int.natAbs_sub_le _ _

theorem param_sub_single {n : ℕ} (lam : Fin n → ℝ) (ν : Fin n → ℤ) (s : Fin n) :
    (fun a => lam a + (((ν - Pi.single s 1) : Fin n → ℤ) a : ℝ)) =
      (fun a => lam a + (ν a : ℝ)) - Pi.single s 1 := by
  funext a
  by_cases h : a = s
  · subst h; simp; ring
  · simp [h]

end GlobalTheory.MomentStep
