module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LimitPairSpaces.TensorSpanEqPairSpace
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.LV

open PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.E

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem typeB_of_mem_typSp {N : ℕ} {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)}
    {U : Submodule ℂ (Sm E N)} {φ : Sm E N} (h : φ ∈ TypSp K W U) : TypeB K W φ := by
  induction h using Submodule.span_induction with
  | mem _ hx => exact hx.2
  | zero =>
    refine ⟨fun u _ g => rfl, fun g => ?_⟩
    have e : (fun k : Kinf E N => (0 : Sm E N).1 (g * infGL E N (Unitary.toUnits k))) = 0 := rfl
    rw [e]
    exact W.zero_mem
  | add x y _ _ hx hy =>
    refine ⟨fun u hu g => ?_, fun g => ?_⟩
    · show x.1 (g * finGL E N u) + y.1 (g * finGL E N u) = x.1 g + y.1 g
      rw [hx.1 u hu g, hy.1 u hu g]
    · have e : (fun k : Kinf E N => (x + y).1 (g * infGL E N (Unitary.toUnits k))) =
          (fun k : Kinf E N => x.1 (g * infGL E N (Unitary.toUnits k))) +
            fun k : Kinf E N => y.1 (g * infGL E N (Unitary.toUnits k)) := rfl
      rw [e]
      exact W.add_mem (hx.2 g) (hy.2 g)
  | smul c x _ hx =>
    refine ⟨fun u hu g => ?_, fun g => ?_⟩
    · show c * x.1 (g * finGL E N u) = c * x.1 g
      rw [hx.1 u hu g]
    · have e : (fun k : Kinf E N => (c • x).1 (g * infGL E N (Unitary.toUnits k))) =
          c • fun k : Kinf E N => x.1 (g * infGL E N (Unitary.toUnits k)) := rfl
      rw [e]
      exact W.smul_mem c (hx.2 g)

theorem typSp_le {N : ℕ} (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ))
    (U : Submodule ℂ (Sm E N)) : TypSp K W U ≤ U :=
  Submodule.span_le.2 fun _ h => h.1

theorem tensor_span_mono {a b : ℕ} {U₁ U₁' : Submodule ℂ (Sm E a)} {U₂ U₂' : Submodule ℂ (Sm E b)} (h₁ : U₁ ≤ U₁')
    (h₂ : U₂ ≤ U₂') : tens2 U₁ U₂ ≤ tens2 U₁' U₂' :=
  Submodule.span_mono fun _ ⟨φ₁, hφ₁, φ₂, hφ₂, e⟩ => ⟨φ₁, h₁ hφ₁, φ₂, h₂ hφ₂, e⟩

def prodBil {a b : ℕ} (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    U₁ →ₗ[ℂ] U₂ →ₗ[ℂ] (GA E a × GA E b → ℂ) :=
  LinearMap.mk₂ ℂ (fun φ₁ φ₂ m => φ₁.1.1 m.1 * φ₂.1.1 m.2)
    (fun x y z => by funext m; simp [add_mul])
    (fun c x z => by funext m; simp [mul_assoc])
    (fun x y z => by funext m; simp [mul_add])
    (fun c x z => by funext m; simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul]; ring)

theorem fd_tens2 {a b : ℕ} (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) [FiniteDimensional ℂ U₁]
    [FiniteDimensional ℂ U₂] : FiniteDimensional ℂ (tens2 U₁ U₂) := by
  refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range (TensorProduct.lift (prodBil U₁ U₂)))
    (Submodule.span_le.2 ?_)
  rintro _ ⟨φ₁, h₁, φ₂, h₂, rfl⟩
  exact ⟨(⟨φ₁, h₁⟩ : U₁) ⊗ₜ[ℂ] (⟨φ₂, h₂⟩ : U₂), by rw [TensorProduct.lift.tmul]; rfl⟩

theorem sep_left {X Y V : Type} [AddCommGroup V] [Module ℂ V] (j : V →ₗ[ℂ] (X → ℂ)) (hj : Function.Injective j)
    (A : Submodule ℂ V) {n : ℕ} (f : Fin n → V) (g : Fin n → Y → ℂ)
    (hs : ∀ y, ∃ χ ∈ A, j χ = fun x => ∑ i, j (f i) x * g i y) :
    ∃ f' : Fin n → V, (∀ i, f' i ∈ A) ∧ ∀ x y, ∑ i, j (f i) x * g i y = ∑ i, j (f' i) x * g i y := by
  have hinj : LinearMap.ker (j.comp A.subtype) = ⊥ :=
    LinearMap.ker_eq_bot.2 (hj.comp Subtype.val_injective)
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (j.comp A.subtype) hinj
  refine ⟨fun i => (L (j (f i)) : V), fun i => (L (j (f i))).2, fun x y => ?_⟩
  obtain ⟨χ, hχ, e⟩ := hs y
  have e1 : (fun x => ∑ i, j (f i) x * g i y) = ∑ i, g i y • j (f i) := by
    funext x
    simp [Finset.sum_apply, mul_comm]
  have e2 : (⟨χ, hχ⟩ : A) = ∑ i, g i y • L (j (f i)) := by
    have h3 : L ((j.comp A.subtype) ⟨χ, hχ⟩) = ⟨χ, hχ⟩ := LinearMap.congr_fun hL _

    rw [← h3, LinearMap.comp_apply, Submodule.subtype_apply, e, e1, map_sum]
    simp only [map_smul]
  have e3 := congrArg (fun v : A => j (v : V) x) e2

  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply,
  smul_eq_mul] at e3
  rw [← congrFun e x, e3]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem sep_right {X Y V : Type} [AddCommGroup V] [Module ℂ V] (j : V →ₗ[ℂ] (Y → ℂ)) (hj : Function.Injective j)
    (B : Submodule ℂ V) {n : ℕ} (g : Fin n → X → ℂ) (f : Fin n → V)
    (hs : ∀ x, ∃ χ ∈ B, j χ = fun y => ∑ i, g i x * j (f i) y) :
    ∃ f' : Fin n → V, (∀ i, f' i ∈ B) ∧ ∀ x y, ∑ i, g i x * j (f i) y = ∑ i, g i x * j (f' i) y := by
  obtain ⟨f', hf', e⟩ := sep_left (X := Y) (Y := X) j hj B f g fun x => by
    obtain ⟨χ, hχ, e⟩ := hs x
    exact ⟨χ, hχ, by rw [e]; funext y; exact Finset.sum_congr rfl fun i _ => mul_comm _ _⟩
  refine ⟨f', hf', fun x y => ?_⟩
  have := e y x
  calc ∑ i, g i x * j (f i) y = ∑ i, j (f i) y * g i x := Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = ∑ i, j (f' i) y * g i x := this
    _ = _ := Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem tens_typ {a b : ℕ} {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)}
    {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))} {W₁ : Submodule ℂ (Kinf E a → ℂ)}
    {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : GA E a × GA E b → ℂ} (hF : F ∈ tens2 U₁ U₂)
    (h₁ : ∀ y, TypF K₁ W₁ fun x => F (x, y)) (h₂ : ∀ x, TypF K₂ W₂ fun y => F (x, y)) :
    F ∈ tens2 (TypSp K₁ W₁ U₁) (TypSp K₂ W₂ U₂) := by
  obtain ⟨n, ψ₁, ψ₂, hψ₁, hψ₂, rfl⟩ := InducedTensorMap.tensor_pair_finite_sum hF
  obtain ⟨φ₁, hφ₁, e₁⟩ := sep_left (Sm E a).subtype Subtype.val_injective (TypSp K₁ W₁ U₁) ψ₁
    (fun i y => (ψ₂ i).1 y) fun y => by
      refine ⟨∑ i, (ψ₂ i).1 y • ψ₁ i, Submodule.subset_span ⟨Submodule.sum_mem _ fun i _ =>
        U₁.smul_mem _ (hψ₁ i), ?_⟩, ?_⟩
      · have e : (∑ i, (ψ₂ i).1 y • ψ₁ i).1 = fun x => ∑ i, (ψ₁ i).1 x * (ψ₂ i).1 y := by
          funext x
          simp [Finset.sum_apply, mul_comm]
        rw [typeB_iff, e]
        exact h₁ y
      · funext x
        simp [Finset.sum_apply, mul_comm]
  obtain ⟨φ₂, hφ₂, e₂⟩ := sep_right (Sm E b).subtype Subtype.val_injective (TypSp K₂ W₂ U₂)
    (fun i x => (φ₁ i).1 x) ψ₂ fun x => by
      refine ⟨∑ i, (φ₁ i).1 x • ψ₂ i, Submodule.subset_span ⟨Submodule.sum_mem _ fun i _ =>
        U₂.smul_mem _ (hψ₂ i), ?_⟩, ?_⟩
      · have e : (∑ i, (φ₁ i).1 x • ψ₂ i).1 = fun y => ∑ i, (ψ₁ i).1 x * (ψ₂ i).1 y := by
          funext y
          have h := e₁ x y
          simp only [Submodule.subtype_apply] at h
          rw [h]
          simp [Finset.sum_apply]
        rw [typeB_iff, e]
        exact h₂ x
      · funext y
        simp [Finset.sum_apply]
  have e : (fun m : GA E a × GA E b => ∑ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2) =
      fun m => ∑ i, (φ₁ i).1 m.1 * (φ₂ i).1 m.2 := by
    funext m
    exact (e₁ m.1 m.2).trans (e₂ m.1 m.2)
  rw [e]
  exact InducedTensorMap.A.sum_mem hφ₁ hφ₂

theorem pair_typ {a b : ℕ} {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)}
    {K₁ : Subgroup (GL (Fin a) (Af E))} {K₂ : Subgroup (GL (Fin b) (Af E))} {W₁ : Submodule ℂ (Kinf E a → ℂ)}
    {W₂ : Submodule ℂ (Kinf E b → ℂ)} {F : H E a b → ℂ} (hF : F ∈ pairSpace U₁ U₂) (hT : TypeH K₁ K₂ W₁ W₂ F) :
    F ∈ pairSpace (TypSp K₁ W₁ U₁) (TypSp K₂ W₂ U₂) := by
  have slices (f : Kinf E a × Kinf E b → ℂ)
      (hf : f ∈ Submodule.span ℂ {z | ∃ u ∈ W₁, ∃ v ∈ W₂, z = fun k => u k.1 * v k.2}) :
      (fun k => f (k, 1)) ∈ W₁ ∧ (fun k => f (1, k)) ∈ W₂ := by
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨u, hu, v, hv, rfl⟩ := hf
      exact ⟨by simpa [Pi.smul_def, smul_eq_mul, mul_comm] using W₁.smul_mem (v 1) hu,
        by simpa [Pi.smul_def, smul_eq_mul] using W₂.smul_mem (u 1) hv⟩
    | zero => exact ⟨W₁.zero_mem, W₂.zero_mem⟩
    | add _ _ _ _ h₁ h₂ => exact ⟨W₁.add_mem h₁.1 h₂.1, W₂.add_mem h₁.2 h₂.2⟩
    | smul c _ _ h => exact ⟨W₁.smul_mem c h.1, W₂.smul_mem c h.2⟩
  rw [tensor_span_eq_pair_space] at hF ⊢
  apply tens_typ hF
  · intro y
    constructor
    · intro u hu g
      simpa [map_one] using hT.1 u hu 1 (one_mem _) (g, y)
    · intro g
      simpa [map_one] using (slices _ (hT.2 (g, y))).1
  · intro x
    constructor
    · intro u hu g
      simpa [map_one] using hT.1 1 (one_mem _) u hu (x, g)
    · intro g
      simpa [map_one] using (slices _ (hT.2 (x, g))).2

end PositivityTheory.Rg.BcB.SpectralAccumulation.LV

end
