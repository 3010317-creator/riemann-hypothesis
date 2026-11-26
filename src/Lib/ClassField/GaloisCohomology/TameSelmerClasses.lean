module

public import Lib.ClassField.GaloisCohomology.Cohomology
public import Lib.ClassField.GaloisCohomology.TameSelmerCocycles

/-!
# Local classes at a tamely ramified place

`New.Selmer.length_localCocycles_le` bounds the module `New.Selmer.localCocycles ρ L A B` of
restrictions to the decomposition group `D_A` of the locally constant cocycles that obey the
relations `L`: its length is at most `length (B ^ n) + length ker (ρ γ - 1)` for inertial `γ`.
This file states the bound for cohomology classes. When `ρ` acts continuously on the discrete
module `B ^ n` of finite length, the classes in `H¹(D_A, B ^ n)` of those restrictions have length
at most `length ker (ρ γ - 1) + length H⁰(D_A, B ^ n)`. The coboundaries `B¹(D_A, B ^ n)` account
for the difference: `|B¹| · |H⁰| = |B ^ n|`.

* `New.Selmer.tameModule`: `B ^ n` with the action of `Gal(Ω/E)` through `ρ`, as a discrete module.
* `New.Selmer.localClasses`: the classes in `H¹(D_A, B ^ n)` of `New.Selmer.localCocycles ρ L A B`.
* `New.Selmer.length_localClasses_le`: the bound for classes.

Notions from other files:
* `New.Z1`, `New.B1`: continuous 1-cocycles and coboundaries.
* `New.DiscreteModule.restrictTo`, `New.DiscreteModule.π₁`, `New.DiscreteModule.H`: restriction to
  a subgroup, the class map onto `H¹` and the cohomology.

## Relation to the literature

An upper bound of the kind given by the local Euler characteristic formula and local duality,
`length H¹ ≤ length H⁰ + length H²`; see J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of
Number Fields*, Ch. VII, §2.
-/

@[expose] public section

noncomputable section

namespace New.Selmer

open Module Matrix.Module LinearMap

variable {ℓ : ℕ} {E : Type} {O n : Type} [Field E] [EmbeddedNumberField E] [CommRing O]
  [Fintype n] [DecidableEq n] {ρ : Gal(Ω/E) →* Matrix n n O} {L : Set (Gal(Ω/E) →₀ Matrix n n O)}
  {A : ClosurePlace} {B : Type} [AddCommGroup B] [Module O B] {M : ℕ} {P : FinPlace E} {m : ℕ}

variable (ρ B) in
/-- `B ^ n` with the discrete topology and the action of `Gal(Ω/E)` through `ρ`, when the orbit
maps are locally constant. -/
abbrev tameModule (hρ : ∀ b : n → B, IsLocallyConstant fun g : Gal(Ω/E) ↦ ρ g • b) :
    DiscreteModule O Gal(Ω/E) :=
  letI : TopologicalSpace B := ⊥
  haveI : DiscreteTopology B := ⟨rfl⟩
  .of (actionRep O (n → B) ρ) (continuous_prod_of_discrete_right.2 fun b ↦ (hρ b).continuous)

variable (hρ : ∀ b : n → B, IsLocallyConstant fun g : Gal(Ω/E) ↦ ρ g • b)

/-- The discrete topology on `B`, the one used by `New.Selmer.tameModule`. -/
local instance : TopologicalSpace B := ⊥

local instance : DiscreteTopology B := ⟨rfl⟩

variable (ρ L A B) in
/-- The module `B ^ n` restricted to the decomposition group at `A`. -/
abbrev localModule : DiscreteModule O (decompGroup Gal(Ω/E) A) :=
  (tameModule ρ B hρ).restrictTo (decompGroup Gal(Ω/E) A)

/-- Restrictions to the decomposition group of locally constant cocycles are continuous
1-cocycles of the decomposition group. -/
lemma localCocycles_le_Z1 : localCocycles ρ L A B ≤ Z1 (localModule ρ A B hρ).ρ := by
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨h_cocycle, -, -, h_lc⟩ := mem_selmerModule_iff.1 hy
  exact ⟨h_lc.continuous.comp continuous_subtypeVal, fun g h ↦ h_cocycle g h⟩

variable (ρ L A B) in
/-- The classes in `H¹(D_A, B ^ n)` of `localCocycles ρ L A B`. -/
abbrev localClasses : Submodule O ((localModule ρ A B hρ).H 1) :=
  ((localCocycles ρ L A B).comap (Z1 (localModule ρ A B hρ).ρ).subtype).map
    (localModule ρ A B hρ).π₁

/-- The restrictions of all locally constant cocycles contain the coboundaries of the decomposition
group: those are restrictions of coboundaries of `Gal(Ω/E)`. -/
lemma B1_le_localCocycles_empty :
    B1 (localModule ρ A B hρ).ρ ≤
      (localCocycles ρ ∅ A B).comap (Z1 (localModule ρ A B hρ).ρ).subtype := fun z hz ↦ by
  obtain ⟨b, hb⟩ := mem_B1_iff.1 hz
  refine ⟨fun g ↦ ρ g • b - b, mem_selmerModule_iff.2 ⟨fun g h ↦ ?_, fun g hg ↦ ?_,
    mem_obeying.2 fun _ hf ↦ hf.elim, (hρ b).sub (IsLocallyConstant.const b)⟩, ?_⟩
  · simp [map_mul, mul_smul, smul_sub]
  · obtain ⟨v, hv, -⟩ := hg
    exact absurd (Set.mem_univ v) hv
  · funext g
    exact hb g

/-- For a module `B ^ n` of finite length, the length of the coboundaries of the decomposition group
plus that of the invariants is the length of `B ^ n`. -/
lemma length_B1_add_length_H0 :
    length O (B1 (localModule ρ A B hρ).ρ) + length O ((localModule ρ A B hρ).H 0) =
      length O (n → B) := by
  have h_ker : ker (coboundaryZ1 (localModule ρ A B hρ).continuous_orbit) =
      (localModule ρ A B hρ).ρ.invariants := by
    ext b
    rw [mem_ker, Representation.mem_invariants, Subtype.ext_iff, funext_iff]
    exact forall_congr' fun g ↦ sub_eq_zero
  have h := relLength_add_length_inf (⊤ : Submodule O (n → B))
    (ker (coboundaryZ1 (localModule ρ A B hρ).continuous_orbit))
  rw [relLength_ker, Submodule.map_top, top_inf_eq, range_coboundaryZ1, h_ker, length_top] at h
  rw [(localModule ρ A B hρ).zeroEquiv.length_eq]
  exact h

/-- `New.Selmer.length_localCocycles_le` for classes. Let `A` be a place of `Ω` over `P`, let
`ℓ ^ M` kill `B`, let `ρ` act with locally constant orbit maps on `B ^ n` of finite length, be
trivial on inertia at `A` near `1` and on the `m`-th powers of inertia, and let `m * ℓ ^ M` be prime
to `A`. For inertial `γ`, the classes in `H¹(D_A, B ^ n)` of the restrictions to the decomposition
group of the cocycles obeying the relations `L` have length at most the length of the kernel of
`ρ γ - 1` on `B ^ n` plus the length of `H⁰(D_A, B ^ n)`. -/
theorem length_localClasses_le (h_fin : length O (n → B) ≠ ⊤) (hB : ∀ b : B, ℓ ^ M • b = 0)
    (hA : IsPlaceOver A P) (h_exp : ∀ i ∈ inertiaGroup Gal(Ω/E) A, ρ (i ^ m) = 1)
    (h_open : ∀ᶠ g : Gal(Ω/E) in nhds 1, g ∈ inertiaGroup Gal(Ω/E) A → ρ g = 1)
    (γ : inertiaGroup Gal(Ω/E) A) (h_prime : A.valuation (m * ℓ ^ M : ℕ) = 1) :
    length O (localClasses ρ L A B hρ) ≤
      length O (ker ((ρ γ - 1) • 1 : End O (n → B))) +
        length O ((localModule ρ A B hρ).H 0) := by
  set W := (localCocycles ρ ∅ A B).comap (Z1 (localModule ρ A B hρ).ρ).subtype
  -- The classes for `L` are among those for no relations.
  have h_mono : localClasses ρ L A B hρ ≤ W.map (localModule ρ A B hρ).π₁ :=
    Submodule.map_mono fun z hz ↦ by
      obtain ⟨y, hy, hyz⟩ := hz
      exact ⟨y, mem_selmerModule_of_subset hy (Set.empty_subset L) le_rfl, hyz⟩
  -- The cocycles for no relations contain `B¹`, and are no longer than
  -- `length (B ^ n) + length ker (ρ γ - 1)`.
  have h_split := (localModule ρ A B hρ).length_eq_length_map_π₁_add_length_inf_B1 W
  rw [inf_eq_right.2 (B1_le_localCocycles_empty hρ)] at h_split
  have h_W : length O W ≤ length O (n → B) + length O (ker ((ρ γ - 1) • 1 : End O (n → B))) := by
    rw [LinearEquiv.length_eq (R := O) (M := W) (N := localCocycles ρ ∅ A B)
      (Submodule.comapSubtypeEquivOfLe (localCocycles_le_Z1 (L := ∅) (A := A) hρ))]
    exact length_localCocycles_le hB hA h_exp h_open γ h_prime
  have hB0 := length_B1_add_length_H0 (A := A) hρ
  have h_B1 : length O (B1 (localModule ρ A B hρ).ρ) ≠ ⊤ :=
    ne_top_of_le_ne_top h_fin (le_self_add.trans hB0.le)
  have key : length O (B1 (localModule ρ A B hρ).ρ) + length O (W.map (localModule ρ A B hρ).π₁) ≤
      length O (B1 (localModule ρ A B hρ).ρ) + (length O (ker ((ρ γ - 1) • 1 : End O (n → B))) +
        length O ((localModule ρ A B hρ).H 0)) := by
    rw [add_comm, ← h_split, add_comm (length O (ker _)), ← add_assoc, hB0]
    exact h_W
  exact (length_mono h_mono).trans ((ENat.add_le_add_iff_left h_B1).1 key)

end New.Selmer

end
