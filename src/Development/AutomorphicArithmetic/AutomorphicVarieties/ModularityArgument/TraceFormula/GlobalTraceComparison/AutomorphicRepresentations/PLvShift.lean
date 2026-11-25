module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportOutFinite
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.AutomorphicRepresentations.SlotBasic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open GlobalTheory.BCT GlobalTheory.PRep
open GlobalTheory.TraceLevel (mem_fixed_iff support_out_finite levOp_id_apply)

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

section SlopeTestRemainingChoices

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

private theorem reindex (K : Subgroup G) (σ : G ⧸ K ≃ G ⧸ K) (a : G → G)
    (hσ : ∀ g : G, σ (g : G ⧸ K) = (a g : G ⧸ K)) (ψ₁ ψ₂ : G → V)
    (hi : ∀ g, ∀ k ∈ K, ψ₁ (g * k) = ψ₁ g) (ha : ∀ g, ψ₁ (a g) = ψ₂ g) :
    ∑ᶠ q : G ⧸ K, ψ₁ q.out = ∑ᶠ q : G ⧸ K, ψ₂ q.out := by
  refine (finsum_comp_equiv σ (f := fun q : G ⧸ K => ψ₁ q.out)).symm.trans (finsum_congr fun q => ?_)
  have e : ((a q.out : G) : G ⧸ K) = ((σ q).out : G) := by
    rw [← hσ, QuotientGroup.out_eq', QuotientGroup.out_eq']
  have hk : (a q.out)⁻¹ * (σ q).out ∈ K := QuotientGroup.eq.1 e
  show ψ₁ (σ q).out = ψ₂ q.out
  rw [← ha, ← hi (a q.out) _ hk, mul_inv_cancel_left]

private def rEquiv (K : Subgroup G) (u : G) (h₁ : ∀ x ∈ K, u * x * u⁻¹ ∈ K)
    (h₂ : ∀ x ∈ K, u⁻¹ * x * u ∈ K) : G ⧸ K ≃ G ⧸ K where
  toFun := Quotient.map' (· * u) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have := h₂ _ hab
    convert this using 1
    group)
  invFun := Quotient.map' (· * u⁻¹) (by
    intro a b hab
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    have := h₁ _ hab
    convert this using 1
    group)
  left_inv := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      show ((g * u * u⁻¹ : G) : G ⧸ K) = g
      rw [mul_inv_cancel_right]
  right_inv := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      show ((g * u⁻¹ * u : G) : G ⧸ K) = g
      rw [inv_mul_cancel_right]

end SlopeTestRemainingChoices

theorem lvShift_pf : LvShift := by
  intro G V _ _ _ _ _ ρ K hKo hKc u hu h hh
  have hc : ∀ x ∈ K, u * x * u⁻¹ ∈ K := fun x hx => (hu x).1 hx
  have hc' : ∀ x ∈ K, u⁻¹ * x * u ∈ K := fun x hx => (hu _).2 (by
    have e : u * (u⁻¹ * x * u) * u⁻¹ = x := by group
    rwa [e])
  have H1 : IsHecke K (fun g => h (g * u⁻¹)) := by
    refine ⟨hh.1.comp_homeomorph (Homeomorph.mulRight u⁻¹), fun k hk x => ⟨?_, ?_⟩⟩
    · show h (k * x * u⁻¹) = h (x * u⁻¹)
      rw [mul_assoc]
      exact (hh.2 k hk _).1
    · show h (x * k * u⁻¹) = h (x * u⁻¹)
      have e : x * k * u⁻¹ = x * u⁻¹ * (u * k * u⁻¹) := by group
      rw [e]
      exact (hh.2 _ (hc k hk) _).2
  have H2 : IsHecke K (fun g => h (u⁻¹ * g)) := by
    refine ⟨hh.1.comp_homeomorph (Homeomorph.mulLeft u⁻¹), fun k hk x => ⟨?_, ?_⟩⟩
    · show h (u⁻¹ * (k * x)) = h (u⁻¹ * x)
      have e : u⁻¹ * (k * x) = u⁻¹ * k * u * (u⁻¹ * x) := by group
      rw [e]
      exact (hh.2 _ (hc' k hk) _).1
    · show h (u⁻¹ * (x * k)) = h (u⁻¹ * x)
      rw [← mul_assoc]
      exact (hh.2 k hk _).2
  have H3 : IsHecke K ((K : Set G).indicator 1) := by
    refine ⟨?_, fun k hk x => ⟨?_, ?_⟩⟩
    · have e : Function.support ((K : Set G).indicator (1 : G → ℂ)) = (K : Set G) := by
        ext x
        by_cases hx : x ∈ (K : Set G) <;> simp [hx]
      show IsCompact (closure (Function.support ((K : Set G).indicator (1 : G → ℂ))))
      rw [e, (K.isClosed_of_isOpen hKo).closure_eq]
      exact hKc
    · have : k * x ∈ (K : Set G) ↔ x ∈ (K : Set G) := K.mul_mem_cancel_left hk
      by_cases hx : x ∈ (K : Set G)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]
        rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun c => hx (this.1 c))]
    · have : x * k ∈ (K : Set G) ↔ x ∈ (K : Set G) := K.mul_mem_cancel_right hk
      by_cases hx : x ∈ (K : Set G)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]
        rfl
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun c => hx (this.1 c))]
  refine ⟨H1, H2, H3, fun y hy => ?_⟩
  have hy' := (mem_fixed_iff ρ K y).1 hy
  have hm : ∀ (a b : G) (v : V), ρ (a * b) v = ρ a (ρ b v) := fun a b v => by
    rw [map_mul]
    rfl
  have hinv : ∀ (f : G → ℂ), (∀ k ∈ K, ∀ x, f (x * k) = f x) → ∀ g, ∀ k ∈ K,
      f (g * k) • ρ (g * k) y = f g • ρ g y := fun f hf g k hk => by
    rw [hf k hk, hm, hy' k hk]
  have h_lv : ∀ (f : G → ℂ), HasCompactSupport f → ∀ v : V,
      Lv ρ K f v = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v := fun f hf v => by
    simpa [Lv, Subgroup.relIndex_self] using
      levOp_id_apply ρ K K f (support_out_finite K hKo f hf) v
  refine ⟨(mem_fixed_iff ρ K _).2 fun k hk => ?_, ?_, ?_, ?_⟩
  · have e : k * u = u * (u⁻¹ * k * u) := by group
    rw [← hm, e, hm, hy' _ (hc' k hk)]
  · rw [h_lv _ H1.1 y, h_lv h hh.1 _]
    refine reindex K (rEquiv K u hc hc') (· * u) (fun g => rfl)
      (fun g => h (g * u⁻¹) • ρ g y) (fun g => h g • ρ g (ρ u y))
      (hinv (fun g => h (g * u⁻¹)) fun k hk x => (H1.2 k hk x).2) fun g => ?_
    show h (g * u * u⁻¹) • ρ (g * u) y = h g • ρ g (ρ u y)
    rw [mul_inv_cancel_right, hm]
  · have hs : (Function.support fun q : G ⧸ K => h q.out • ρ q.out y).Finite :=
      (support_out_finite K hKo _ hh.1).subset (by
        intro q hq hz
        apply hq
        simp [hz])
    rw [h_lv _ H2.1 y, h_lv h hh.1 y, map_finsum (ρ u) hs]
    simp only [map_smul]
    refine reindex K (MulAction.toPerm u) (u * ·) (fun g => rfl)
      (fun g => h (u⁻¹ * g) • ρ g y) (fun g => h g • ρ u (ρ g y))
      (hinv (fun g => h (u⁻¹ * g)) fun k hk x => (H2.2 k hk x).2) fun g => ?_
    show h (u⁻¹ * (u * g)) • ρ (u * g) y = h g • ρ u (ρ g y)
    rw [inv_mul_cancel_left, hm]
  · rw [h_lv _ H3.1 y]
    have h1 : ((1 : G) : G ⧸ K).out ∈ (K : Set G) := by
      have : ((((1 : G) : G ⧸ K).out : G) : G ⧸ K) = ((1 : G) : G ⧸ K) := QuotientGroup.out_eq' _
      have := QuotientGroup.eq.1 this
      simpa using this
    rw [finsum_eq_single _ ((1 : G) : G ⧸ K)]
    · rw [Set.indicator_of_mem h1, hy' _ h1]
      simp
    · intro q hq
      have : q.out ∉ (K : Set G) := fun c => hq (by
        rw [← QuotientGroup.out_eq' q]
        exact QuotientGroup.eq.2 (by simpa using K.inv_mem c))
      rw [Set.indicator_of_notMem this, zero_smul]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Pi

end
