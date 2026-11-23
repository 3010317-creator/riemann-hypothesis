module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzHadamardLemma
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationCharacterInvariantFormStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationInvariantFormConstL2Statement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzEqZeroOfWrongSignGaussianRelation
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Ring.IsFormallyReal
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

noncomputable section
open scoped Classical
namespace GlobalTheory.ArchInvForm

theorem trace_half {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)]
    (z : mixedEmbedding.mixedSpace F) :
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (⅟(2 : mixedEmbedding.mixedSpace F) * z) =
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F) z / 2 := by
  have h : (2 : ℝ) • (⅟(2 : mixedEmbedding.mixedSpace F) * z) = z := by
    rw [Algebra.smul_def, map_ofNat, ← mul_assoc, mul_invOf_self, one_mul]
  have h2 := congrArg (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)) h
  rw [map_smul, smul_eq_mul] at h2
  linarith

theorem schr_eq_schrF {F : Type} [Field F] [NumberField F] [Invertible (2 : mixedEmbedding.mixedSpace F)] {κ : Type} [Fintype κ]
    (ψ : AddChar (mixedEmbedding.mixedSpace F) ℂ)
    (hψ : ∀ a, ψ a = Complex.exp (-(2 * Real.pi * Complex.I) * (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) a : ℝ)))
    (w : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) :
    schr ψ w φ = GlobalTheory.ArchUniq.schrF (GlobalTheory.ArchUniq.trP F κ) w φ := by
  funext x
  simp only [schr, GlobalTheory.ArchUniq.schrF, hψ]
  congr 3
  rw [map_add (f := _), trace_half]
  rfl

theorem int_phase_shift {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (μ : @Measure V (borel V)) (hμ : @Measure.IsAddHaarMeasure V _ _ (borel V) μ)
    (u v p : V → ℂ) (hp : ∀ x, ‖p x‖ = 1) (a : V) :
    @integral V ℂ _ _ (borel V) μ (fun x => (p x * u (x + a)) * starRingEnd ℂ (p x * v (x + a))) =
      @integral V ℂ _ _ (borel V) μ (fun x => u x * starRingEnd ℂ (v x)) := by
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  have e : (fun x => (p x * u (x + a)) * starRingEnd ℂ (p x * v (x + a))) = fun x => u (x + a) * starRingEnd ℂ (v (x + a)) := by
    funext x
    have h1 : p x * starRingEnd ℂ (p x) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hp x]; simp
    rw [map_mul]
    linear_combination (u (x + a) * starRingEnd ℂ (v (x + a))) * h1
  rw [e]
  exact integral_add_right_eq_self (μ := μ) (fun x => u x * starRingEnd ℂ (v x)) a

end GlobalTheory.ArchInvForm
