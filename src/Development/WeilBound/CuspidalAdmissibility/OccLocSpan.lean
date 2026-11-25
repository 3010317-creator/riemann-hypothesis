module

public import GroundTheory.AutomorphicForms.TensorProductTheorem.Restricted
public import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open GroundTheory.Automorphic.RestrictedTensor
open scoped TensorProduct

namespace PositivityTheory.TfC.OccursIff.Span

theorem span_core {ι : Type} {W : ι → Type} [∀ v, AddCommGroup (W v)] [∀ v, Module ℂ (W v)] (ξ : ∀ v, W v)
    {C W₁ W₂ H : Type} [AddCommGroup C] [Module ℂ C] [AddCommGroup W₁] [Module ℂ W₁] [AddCommGroup W₂]
    [Module ℂ W₂] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (E : C ≃ₗ[ℂ] W₁ ⊗[ℂ] W₂)
    (Te : W₂ ≃ₗ[ℂ] restrictedTensor ξ) (Φ : C →ₗ[ℂ] H) (u : H)
    (h : ∀ a (x : ∀ v, W v) (hx : IsRestricted ξ x),
      inner ℂ (Φ (E.symm (a ⊗ₜ Te.symm ⟨PiTensorProduct.tprod ℂ x, tprod_mem_restrictedTensor hx⟩))) u = 0)
    (c : C) : inner ℂ (Φ c) u = 0 := by
  let ψ : W₁ ⊗[ℂ] W₂ →ₗ[ℂ] ℂ :=
    (innerₛₗ ℂ u).comp (Φ.comp E.symm.toLinearMap)
  suffices hψ : ψ = 0 from inner_eq_zero_symm.mp <| by
    simpa [ψ, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply] using
      LinearMap.congr_fun hψ (E c)
  refine TensorProduct.ext' fun a b => ?_
  let L : restrictedTensor ξ →ₗ[ℂ] ℂ :=
    ψ.comp ((TensorProduct.mk ℂ W₁ W₂ a).comp Te.symm.toLinearMap)
  obtain ⟨r, hr, hre⟩ :=
    (Submodule.span_le (p := (LinearMap.ker L).map (restrictedTensor ξ).subtype)).2
      (by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨⟨_, tprod_mem_restrictedTensor hx⟩,
          LinearMap.mem_ker.2 (inner_eq_zero_symm.mpr (h a x hx)), rfl⟩)
      (Te b).2
  have hL := LinearMap.mem_ker.1 hr
  rw [Subtype.ext hre] at hL
  simpa [L, LinearEquiv.coe_toLinearMap, LinearEquiv.symm_apply_apply] using hL

end PositivityTheory.TfC.OccursIff.Span
