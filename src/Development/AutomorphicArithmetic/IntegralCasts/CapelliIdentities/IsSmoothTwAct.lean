module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Mathlib.Topology.Algebra.OpenSubgroup

@[expose] public section

namespace UpperTheory.Reformulated.B.Gwa2

noncomputable def IsSmooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [TopologicalSpace G] (ρ : Representation k G V) : Prop :=
  ∀ v : V, IsOpen {g : G | ρ g v = v}

noncomputable def twKer {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    (ρ : Representation k G V) (N : Subgroup G) (ψ : N →* kˣ) : Submodule k V :=
  Submodule.span k {w : V | ∃ (n : N) (v : V), w = ρ n v - (ψ n : k) • v}

@[reducible] noncomputable def TwJacquet {k G V : Type} [Field k] [Group G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (N : Subgroup G) (ψ : N →* kˣ) : Type :=
  V ⧸ twKer ρ N ψ

theorem aux4 {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (N : Subgroup G) (θ : N →* ℂˣ) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ (h : s m * (n : G) * (s m)⁻¹ ∈ N), θ ⟨s m * n * (s m)⁻¹, h⟩ = θ n)
    (m : M) :
    Submodule.span ℂ {w : V | ∃ (n : N) (v : V), w = ρ n v - (θ n : ℂ) • v} ≤
      Submodule.comap (ρ (s m)) (twKer ρ N θ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨n, v, rfl⟩
  obtain ⟨h, hθ⟩ := hs m n
  refine Submodule.subset_span ⟨⟨_, h⟩, ρ (s m) v, ?_⟩
  have key : ρ (s m * (n : G) * (s m)⁻¹) (ρ (s m) v) = ρ (s m) (ρ (n : G) v) := by
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel_right, map_mul, mul_apply_eq_comp]
  rw [hθ, map_sub, map_smul, ← key]

theorem aux5 {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (N : Subgroup G) (θ : N →* ℂˣ) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ (h : s m * (n : G) * (s m)⁻¹ ∈ N), θ ⟨s m * n * (s m)⁻¹, h⟩ = θ n) :
    Submodule.span ℂ {w : V | ∃ (n : N) (v : V), w = ρ n v - (θ n : ℂ) • v} ≤
      Submodule.comap (ρ (s 1)) (twKer ρ N θ) := by
  exact aux4 ρ N θ s hs 1

theorem aux6 {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (N : Subgroup G) (θ : N →* ℂˣ) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ (h : s m * (n : G) * (s m)⁻¹ ∈ N), θ ⟨s m * n * (s m)⁻¹, h⟩ = θ n) :
    (twKer ρ N θ).mapQ (twKer ρ N θ) (ρ (s 1)) (aux5 ρ N θ s hs) =
      (1 : TwJacquet ρ N θ →ₗ[ℂ] TwJacquet ρ N θ) := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ρ (s 1) v) = Submodule.Quotient.mk v
  rw [map_one, map_one, one_apply_eq_self]

theorem aux7 {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (N : Subgroup G) (θ : N →* ℂˣ) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ (h : s m * (n : G) * (s m)⁻¹ ∈ N), θ ⟨s m * n * (s m)⁻¹, h⟩ = θ n)
    (a b : M) :
    Submodule.span ℂ {w : V | ∃ (n : N) (v : V), w = ρ n v - (θ n : ℂ) • v} ≤
      Submodule.comap (ρ (s (a * b))) (twKer ρ N θ) := by
  exact aux4 ρ N θ s hs (a * b)

theorem aux8 {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (N : Subgroup G) (θ : N →* ℂˣ) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ (h : s m * (n : G) * (s m)⁻¹ ∈ N), θ ⟨s m * n * (s m)⁻¹, h⟩ = θ n)
    (a b : M) :
    (twKer ρ N θ).mapQ (twKer ρ N θ) (ρ (s (a * b))) (aux7 ρ N θ s hs a b) =
      (twKer ρ N θ).mapQ (twKer ρ N θ) (ρ (s a)) (aux4 ρ N θ s hs a) *
        (twKer ρ N θ).mapQ (twKer ρ N θ) (ρ (s b)) (aux4 ρ N θ s hs b) := by
  refine LinearMap.ext fun x ↦ ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  change Submodule.Quotient.mk (ρ (s (a * b)) v) = Submodule.Quotient.mk (ρ (s a) (ρ (s b) v))
  rw [map_mul, map_mul, mul_apply_eq_comp]

noncomputable def twAct {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (N : Subgroup G) (θ : N →* ℂˣ) {M : Type} [Group M] (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ (h : s m * (n : G) * (s m)⁻¹ ∈ N), θ ⟨s m * n * (s m)⁻¹, h⟩ = θ n) :
    Representation ℂ M (TwJacquet ρ N θ) :=
  { toFun := fun m ↦ (twKer ρ N θ).mapQ (twKer ρ N θ) (ρ (s m)) (aux4 ρ N θ s hs m)
    map_one' := aux6 ρ N θ s hs
    map_mul' := aux8 ρ N θ s hs : M →* TwJacquet ρ N θ →ₗ[ℂ] TwJacquet ρ N θ }

private theorem isOpen_fixer {M W : Type} [Group M] [AddCommGroup W] [Module ℂ W]
    [TopologicalSpace M] [IsTopologicalGroup M] (τ : Representation ℂ M W) (x : W)
    (h : {m : M | τ m x = x} ∈ nhds (1 : M)) : IsOpen {m : M | τ m x = x} := by
  let H : Subgroup M :=
    { carrier := {m : M | τ m x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} (ha : τ a x = x) (hb : τ b x = x) ↦ show τ (a * b) x = x by
        rw [map_mul, mul_apply_eq_comp, hb, ha]
      inv_mem' := fun {a} (ha : τ a x = x) ↦ show τ a⁻¹ x = x by
        conv_lhs => rw [← ha]
        rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self] }
  exact H.isOpen_of_mem_nhds h

theorem isSmooth_twAct {G M V : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] (ρ : Representation ℂ G V)
    (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
    (hs : ∀ (m : M) (n : N), ∃ (h : s m * (n : G) * (s m)⁻¹ ∈ N), θ ⟨s m * n * (s m)⁻¹, h⟩ = θ n)
    (hc : Continuous s) (hρ : IsSmooth ρ) : IsSmooth (twAct ρ N θ s hs) := by
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine isOpen_fixer _ _ ?_
  have hU : IsOpen {m : M | ρ (s m) v = v} := (hρ v).preimage hc
  refine Filter.mem_of_superset (hU.mem_nhds (by simp)) fun m (hm : ρ (s m) v = v) ↦ ?_
  change Submodule.Quotient.mk (ρ (s m) v) = Submodule.Quotient.mk v
  rw [hm]

end UpperTheory.Reformulated.B.Gwa2
