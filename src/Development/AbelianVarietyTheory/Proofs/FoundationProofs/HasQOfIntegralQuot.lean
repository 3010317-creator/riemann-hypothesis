module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelCoeffAndFunctionUnique
public import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQMdifferentiableAndIsBoundedAtImInfty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQVadd
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasQExpansionOfPeriodicBoundedHolomorphic
public import Mathlib.Analysis.Complex.Norm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonicRootNormLeOneAddSum
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.QuotientIntegralHolomorphic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicMulEqZeroIff
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem hasQ_periodic {N : ℕ} {f : ℍ → ℂ} {a : ℕ → ℂ} (hN : 0 < N) (h : HasQ N f a) (τ : ℍ) :
    f ((N : ℝ) +ᵥ τ) = f τ := by
  have h1 := hasQ_vadd N f a (N : ℝ) h
  have hc : (fun n : ℕ => a n * Complex.exp (2 * Real.pi * Complex.I * n * ((N : ℝ) : ℂ) / N)) = a := by
    funext n
    have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have : 2 * Real.pi * Complex.I * n * ((N : ℝ) : ℂ) / N = (n : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; field_simp
    rw [this, Complex.exp_nat_mul_two_pi_mul_I, mul_one]
  rw [hc] at h1
  exact congrFun (_root_.GlobalTheory.QFam.hasQ_unique_both.2 N _ _ a h1 h) τ

theorem hasQ_of_integral_quot : ∀ (N n : ℕ) (A D : ℍ → ℂ) (s : Fin n → ℍ → ℂ), 0 < N →
    (∃ a, HasQ N A a) → (∃ d, HasQ N D d) → (∀ j, ∃ c, HasQ N (s j) c) → D ≠ 0 →
    (∀ τ, A τ ^ n + ∑ j, s j τ * A τ ^ (j : ℕ) * D τ ^ (n - j) = 0) →
    ∃ (h : ℍ → ℂ) (b : ℕ → ℂ), HasQ N h b ∧ ∀ τ, A τ = h τ * D τ := by
  intro N n A D s hN ⟨a, hA⟩ ⟨d, hD⟩ hs hD0 heq
  choose c hc using hs
  obtain ⟨hAm, -⟩ := _root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N A a hN hA
  obtain ⟨hDm, -⟩ := _root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N D d hN hD
  have hsm : ∀ j, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (s j) ∧ UpperHalfPlane.IsBoundedAtImInfty (s j) :=
    fun j => _root_.GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty N (s j) (c j) hN (hc j)
  have hUo : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hUc : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ, D τ ≠ 0 := by
    by_contra hc'
    push_neg at hc'
    exact hD0 (funext hc')
  have hofc : ∀ z : ℂ, 0 < z.im → ((UpperHalfPlane.ofComplex z : ℍ) : ℂ) = z := fun z hz => by
    rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
  obtain ⟨h₀, hh₀d, hh₀A, hh₀p⟩ := _root_.GlobalTheory.quotient_integral_holomorphic {z : ℂ | 0 < z.im} n
    (A ∘ UpperHalfPlane.ofComplex) (D ∘ UpperHalfPlane.ofComplex)
    (fun j => s j ∘ UpperHalfPlane.ofComplex) hUo hUc (UpperHalfPlane.mdifferentiable_iff.1 hAm)
    (UpperHalfPlane.mdifferentiable_iff.1 hDm) (fun j => UpperHalfPlane.mdifferentiable_iff.1 (hsm j).1)
    ⟨(τ₀ : ℂ), τ₀.im_pos, by simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hτ₀⟩
    (fun z _ => heq _)
  set h : ℍ → ℂ := fun τ => h₀ τ with hdef
  have hAh : ∀ τ, A τ = h τ * D τ := fun τ => by
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hh₀A (τ : ℂ) τ.im_pos
  have hhp : ∀ τ, h τ ^ n + ∑ j, s j τ * h τ ^ (j : ℕ) = 0 := fun τ => by
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using hh₀p (τ : ℂ) τ.im_pos
  have hhm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) h := by
    refine UpperHalfPlane.mdifferentiable_iff.2 (hh₀d.congr fun z hz => ?_)
    simp only [Function.comp_apply, hdef, hofc z hz]
  have hhNm : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun τ => h ((N : ℝ) +ᵥ τ)) := by
    have hd : DifferentiableOn ℂ (fun z : ℂ => h₀ (((N : ℝ) : ℂ) + z)) {z : ℂ | 0 < z.im} :=
      hh₀d.comp ((differentiableOn_const _).add differentiableOn_id) fun z hz => by
        show 0 < (((N : ℝ) : ℂ) + z).im
        simpa using hz
    refine UpperHalfPlane.mdifferentiable_iff.2 (hd.congr fun z hz => ?_)
    simp only [Function.comp_apply, hdef, UpperHalfPlane.coe_vadd, hofc z hz]
  have hper : ∀ τ : ℍ, h ((N : ℝ) +ᵥ τ) = h τ := by
    have hz : ∀ τ, (fun τ => h ((N : ℝ) +ᵥ τ) - h τ) τ * D τ = 0 := fun τ => by
      have e1 := hAh ((N : ℝ) +ᵥ τ)
      rw [hasQ_periodic hN hA, hasQ_periodic hN hD, hAh τ] at e1
      simp only
      linear_combination -e1
    rcases _root_.GlobalTheory.fn_mul_eq_zero_dom _ D (hhNm.sub hhm) hDm hz with h0 | h0
    · exact fun τ => sub_eq_zero.1 (congrFun h0 τ)
    · exact absurd h0 hD0
  have hbd : UpperHalfPlane.IsBoundedAtImInfty h := by
    have hS : (fun τ => ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := by
      have hb : ∀ j ∈ (Finset.univ : Finset (Fin n)),
          (fun τ => ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := fun j _ => by
        have : (s j) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) := (hsm j).2
        exact this.norm_left
      exact (Asymptotics.IsBigO.sum hb).congr_left fun τ => Finset.sum_apply _ _ _
    have h1 : (fun τ => 1 + ∑ j, ‖s j τ‖) =O[UpperHalfPlane.atImInfty] (1 : ℍ → ℝ) :=
      ((Asymptotics.isBigO_refl (1 : ℍ → ℝ) _).add hS).congr_left fun τ => rfl
    have h2 : h =O[UpperHalfPlane.atImInfty] (fun τ => 1 + ∑ j, ‖s j τ‖) := by
      refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun τ => ?_)
      have hb := _root_.GlobalTheory.monic_root_norm_le_one_add_sum n (fun j => s j τ) (h τ) (hhp τ)
      have hnn : (0 : ℝ) ≤ 1 + ∑ j, ‖s j τ‖ := by positivity
      rw [Real.norm_of_nonneg hnn, one_mul]
      exact hb
    exact h2.trans h1
  obtain ⟨b, hb⟩ := _root_.GlobalTheory.FN.hasQ_of_periodic_bounded N h hN hhm hper hbd
  exact ⟨h, b, hb, hAh⟩

end GlobalTheory.FN
