module

public import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Mathlib.RingTheory.HahnSeries.Summable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FnHahnSeriesInvConverges
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesEqOfQExpansionSumAboveEventuallyEq
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveMul
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneEqZeroOfVanishAboveIm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasCommonExponentDenominatorRingOperations
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionSumAboveBasicProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNExp

theorem up_add (f f' : ℍ → ℂ) : up (f + f') = up f + up f' := rfl
theorem up_sub (f f' : ℍ → ℂ) : up (f - f') = up f - up f' := rfl
theorem up_mul (f f' : ℍ → ℂ) : up (f * f') = up f * up f' := rfl
theorem up_inv (f : ℍ → ℂ) : up f⁻¹ = (up f)⁻¹ := rfl

theorem exp_props : ∀ (Ω : Type) [Field Ω] (ε : Ω →+* ℂ), (∀ (f f' : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f' h' → IsExp ε (f + f') (h + h') ∧ IsExp ε (f - f') (h - h') ∧ IsExp ε (f * f') (h * h')) ∧ (∀ (f : ℍ → ℂ) (h h' : HahnSeries ℚ Ω), IsExp ε f h → IsExp ε f h' → h = h') ∧ (∀ c : Ω, IsExp ε (fun _ => ε c) (HahnSeries.C c)) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → IsExp ε f (0 : HahnSeries ℚ Ω) → f = 0) ∧ ∀ (f : ℍ → ℂ) (h : HahnSeries ℚ Ω), h ≠ 0 → IsExp ε f h → IsExp ε f⁻¹ h⁻¹ := by
  intro Ω _ ε
  obtain ⟨hden, hsing⟩ := _root_.GlobalTheory.FN.den_ring Ω
  obtain ⟨hmono, hadd, hmon, hcongr⟩ := _root_.GlobalTheory.FNHS.hs_props Ω ε
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro f f' h h' ⟨hd, C, hC⟩ ⟨hd', C', hC'⟩
    obtain ⟨d1, d2, d3⟩ := hden h h' hd hd'
    have e1 : HS ε (max C C') (up f) h := hmono _ _ _ _ (le_max_left _ _) hC
    have e2 : HS ε (max C C') (up f') h' := hmono _ _ _ _ (le_max_right _ _) hC'
    obtain ⟨s1, s2⟩ := hadd _ _ _ _ _ e1 e2
    refine ⟨⟨d1, max C C', ?_⟩, ⟨d2, max C C', ?_⟩, ⟨d3, max C C', ?_⟩⟩
    · rw [up_add]; exact s1
    · rw [up_sub]; exact s2
    · rw [up_mul]; exact _root_.GlobalTheory.FNProd.hs_mul Ω ε _ _ _ _ _ e1 e2
  · rintro f h h' ⟨hd, C, hC⟩ ⟨hd', C', hC'⟩
    exact _root_.GlobalTheory.FN.hs_uniq Ω ε C C' 0 (up f) (up f) h h' hd hd' hC hC' (fun _ _ => rfl)
  · intro c
    have hC : HahnSeries.C c = (HahnSeries.single (0 : ℚ) c : HahnSeries ℚ Ω) := HahnSeries.C_apply c
    rw [hC]
    refine ⟨hsing 0 c, 0, ?_⟩
    refine hcongr 0 _ _ _ ?_ (hmon 0 0 c)
    intro z _
    simp [up]
  · rintro f hf ⟨_, C, hC⟩
    apply _root_.GlobalTheory.upperHalfPlane_eq_zero_of_vanish_high f C hf
    intro τ hτ
    have hz := hC (τ : ℂ) (by simpa using hτ)
    have h0 : (fun r : ℚ => ε ((0 : HahnSeries ℚ Ω).coeff r) * Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (τ : ℂ))) = fun _ => 0 := by
      funext r; simp
    rw [h0] at hz
    have := hz.unique hasSum_zero
    simpa [up, UpperHalfPlane.ofComplex_apply] using this
  · rintro f h hne ⟨hd, C, hC⟩
    obtain ⟨d, C', hC'⟩ := _root_.GlobalTheory.fn_hahnSeries_inv_converges Ω ε C (up f) h hd hne hC
    exact ⟨d, C', by rw [up_inv]; exact hC'⟩

end GlobalTheory.FNExp
