module

public import Lib.ClassField.GaloisCohomology.Cohomology
public import Lib.Cyclotomic.Kolyvagin.ReciprocityComponentBounds

/-!
# The odd-part components as groups of cohomology classes

The component `New.OddPart.component l e ψ ν` is a module of cocycles `Gal(Ω/ℚ) → O / l ^ ν` for
the character `Υ⁻¹`, where `Υ = cyc ^ e ψ` (`New.cyclotomicPowDirichlet l e ψ`). It is cut out by
local conditions and by vanishing at the complex conjugation `New.cmConj`. When `Υ` is odd,
`cmConj` acts on `O / l ^ ν` by the scalar `-1`, and `-1 - 1 = -2` is a unit when `2` is. Then the
component meets the coboundaries `B¹` only in `0` and maps isomorphically onto the classes, in
`H¹(Gal(Ω/ℚ), O / l ^ ν (Υ⁻¹))`, of the cocycles cut out by the local conditions alone. Those
cocycles contain `B¹`, since `Υ` is trivial on the elements where the local conditions ask for
vanishing. So the bounds on the component are bounds on cohomology classes.

* `New.OddPart.componentModule`: the discrete Galois module `O / l ^ ν` on which `g` acts by
  `Υ⁻¹(g)`.
* `New.OddPart.componentCocycles`: the component without the condition at `cmConj`, and
  `New.OddPart.componentClasses`, its module of classes in `H¹`.
* `New.OddPart.component_inf_B1_eq_bot`, `New.OddPart.componentEquivClasses`,
  `New.OddPart.card_component_eq_card_classes`, `New.OddPart.length_component_eq_length_classes`:
  for `Υ` odd and `2` a unit, the component is isomorphic to the module of classes.
* `New.OddPart.finite_componentClasses`, `New.OddPart.nsmul_componentClasses_eq_zero`,
  `New.OddPart.exists_detecting_points_componentClasses`: `New.OddPart.finite_component`,
  `New.OddPart.nsmul_component_eq_zero` and `New.OddPart.exists_detecting_points_component` for
  classes. A class is detected through `z (γ cmConj) - z (cmConj γ)`, which is
  `2 z(γ) + (Υ⁻¹(γ) - 1) z(cmConj)` for a representative `z` and does not depend on the
  representative.

Notions from other files:
* `New.Z1`, `New.B1`, `New.vanishingAt`: continuous 1-cocycles, coboundaries, and cocycles that
  vanish at a given element.
* `New.DiscreteModule.π₁`: the `O`-linear class map from `Z¹` onto `H¹`, with kernel `B¹`.

## Relation to the literature

Known: a cocycle that vanishes at an element acting by a scalar `ζ` with `ζ - 1` a unit is the
unique representative of its class with that property. The components are those of K. Rubin,
*Euler Systems*, 2000, III.4, read on cocycles normalised at complex conjugation.
-/

@[expose] public section

noncomputable section

namespace New.OddPart

open Module

variable {O : Type} [CommRing O] {N l e X : ℕ} [NeZero N] [L : Fact l.Prime]
  [PadicIntegerRing O l] {ψ : DirichletCharacter O N} {ν : ℕ}

variable (l e ψ) in
/-- The discrete Galois module `O / l ^ ν` on which `g` acts by `Υ⁻¹(g)`, for
`Υ = cyc ^ e ψ` (`New.cyclotomicPowDirichlet l e ψ`). The action factors through the Galois group
of `ℚ(μ_{N l ^ ν})`. -/
abbrev componentModule (ν : ℕ) : DiscreteModule O Gal(Ω/ℚ) :=
  letI : TopologicalSpace (QuotSpan (l ^ ν : O)) := ⊥
  haveI : DiscreteTopology (QuotSpan (l ^ ν : O)) := ⟨rfl⟩
  letI : MulAction Gal(Ω/ℚ) (QuotSpan (l ^ ν : O)) := .compHom _ (cyclotomicPowDirichlet l e ψ)⁻¹
  .of (charRep (QuotSpan (l ^ ν : O)) (cyclotomicPowDirichlet l e ψ)⁻¹)
    (continuousSMul_iff_stabilizer_isOpen.2 fun y ↦ Subgroup.isOpen_mono
      (fun g hg ↦ MulAction.mem_stabilizer_iff.2 (cyclotomicPowDirichlet_smul_eq_self (l := l)
        (e := e) (ψ := ψ) (m := l ^ ν) (g := g) hg (Selmer.nsmul_quot_eq_zero dvd_rfl y)).right)
      isOpen_ker_cyclotomicCharMod.out).1

/-- The discrete topology on `O / b`, the one used by `New.OddPart.componentModule`. -/
local instance (b : O) : TopologicalSpace (QuotSpan b) := ⊥

local instance (b : O) : DiscreteTopology (QuotSpan b) := ⟨rfl⟩

lemma componentModule_ρ_apply (g : Gal(Ω/ℚ)) (y : QuotSpan (l ^ ν : O)) :
    (componentModule l e ψ ν).ρ g y = ((cyclotomicPowDirichlet l e ψ)⁻¹ g).val • y :=
  rfl

variable (l e ψ) in
/-- The component `New.OddPart.component l e ψ ν` without the condition at `cmConj`: the locally
constant cocycles for `Υ⁻¹` with values in `O / l ^ ν` that vanish at the elements of
`New.cycloGalGroup N` lying in an inertia group at a place prime to `l` or in
`New.Selmer.shaLocalSet l ℚ 1`. -/
abbrev componentCocycles (ν : ℕ) : Submodule O (Gal(Ω/ℚ) → QuotSpan ((l : O) ^ ν)) :=
  vanishingCocycles (cyclotomicPowDirichlet l e ψ)⁻¹ (QuotSpan (l ^ ν : O))
    (cycloGalGroup N ∩ (inertiaAbove (placesDividing ℚ l)ᶜ ∪ Selmer.shaLocalSet l ℚ 1))

/-- The members of `componentCocycles` are continuous 1-cocycles of `componentModule`. -/
lemma componentCocycles_le_Z1 :
    componentCocycles l e ψ ν ≤ Z1 (componentModule l e ψ ν).ρ := fun _ hz ↦
  ⟨hz.1.continuous, hz.2.1⟩

variable (l e ψ) in
/-- `componentCocycles` as a module of continuous 1-cocycles of `componentModule`. -/
abbrev componentCocyclesZ1 (ν : ℕ) : Submodule O (Z1 (componentModule l e ψ ν).ρ) :=
  (componentCocycles l e ψ ν).comap (Z1 (componentModule l e ψ ν).ρ).subtype

variable (l e ψ) in
/-- The classes of `componentCocycles` in `H¹(Gal(Ω/ℚ), O / l ^ ν (Υ⁻¹))`. -/
abbrev componentClasses (ν : ℕ) : Submodule O ((componentModule l e ψ ν).H 1) :=
  (componentCocyclesZ1 l e ψ ν).map (componentModule l e ψ ν).π₁

variable (l e ψ ν) in
lemma component_le_Z1 : component l e ψ ν ≤ Z1 (componentModule l e ψ ν).ρ := fun _ hz ↦
  ⟨hz.1.continuous, hz.2.1⟩

variable (l e ψ ν) in
/-- The component as a module of continuous 1-cocycles: the members of `componentCocycles` that
vanish at `cmConj`. -/
lemma comap_component_eq :
    (component l e ψ ν).comap (Z1 (componentModule l e ψ ν).ρ).subtype =
      componentCocyclesZ1 l e ψ ν ⊓ vanishingAt (componentModule l e ψ ν).ρ cmConj := by
  ext z
  simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.mem_inf, mem_vanishingAt,
    component, componentCocycles, vanishingCocycles, Submodule.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq, Set.forall_mem_insert]
  tauto

/-- The character `Υ = cyc ^ e ψ` is trivial on the elements of `New.cycloGalGroup N` that lie in
an inertia group at a place prime to `l` or in `New.Selmer.shaLocalSet l ℚ 1`. -/
lemma cyclotomicPowDirichlet_eq_one {g : Gal(Ω/ℚ)}
    (hg : g ∈ (cycloGalGroup N : Set Gal(Ω/ℚ)) ∩
      (inertiaAbove (placesDividing ℚ l)ᶜ ∪ Selmer.shaLocalSet l ℚ 1)) :
    cyclotomicPowDirichlet l e ψ g = 1 := by
  obtain ⟨hN, hg⟩ := hg
  have h_cyc : cyclotomicChar Ω l g = 1 := by
    rcases hg with hg | ⟨A, -, hA⟩
    · obtain ⟨u, hu, B, hB, hgB⟩ := hg
      exact cyclotomicChar_eq_one_of_mem_inertiaGroup l hgB (hB.valuation_natCast_eq_one_iff.2 hu)
    · simpa using hA.2
  simp [cyclotomicPowDirichlet, h_cyc, MonoidHom.mem_ker.1 hN]

variable (l e ψ ν) in
/-- The component without the condition at `cmConj` contains the coboundaries: `Υ` is trivial on
the elements where it asks for vanishing. -/
lemma B1_le_componentCocyclesZ1 :
    B1 (componentModule l e ψ ν).ρ ≤ componentCocyclesZ1 l e ψ ν := fun z hz ↦ by
  obtain ⟨b, hb⟩ := mem_B1_iff.1 hz
  refine ⟨(IsLocallyConstant.iff_continuous _).2 z.2.1, z.2.2, fun g hg ↦ ?_⟩
  change (z : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)) g = 0
  rw [← hb, componentModule_ρ_apply, MonoidHom.inv_apply, cyclotomicPowDirichlet_eq_one hg,
    inv_one, Units.val_one, one_smul, sub_self]

/-- If `Υ` is odd (value `-1` at `cmConj`), then `cmConj` acts on `componentModule` by `-1`. -/
lemma componentModule_ρ_cmConj (hc : cyclotomicPowDirichlet l e ψ cmConj = -1)
    (y : QuotSpan (l ^ ν : O)) : (componentModule l e ψ ν).ρ cmConj y = (-1 : O) • y := by
  rw [componentModule_ρ_apply, MonoidHom.inv_apply, hc, inv_neg, inv_one, Units.val_neg,
    Units.val_one]

lemma isUnit_neg_one_sub_one {R : Type*} [CommRing R] (h_two : IsUnit (2 : R)) :
    IsUnit ((-1 : R) - 1) := by
  have h : (-1 : R) - 1 = -2 := by ring
  rw [h]
  exact h_two.neg

section Odd

variable (hc : cyclotomicPowDirichlet l e ψ cmConj = -1) (h_two : IsUnit (2 : O))
include hc h_two

/-- For `Υ` odd and `2` a unit, the component meets the coboundaries only in `0`. -/
theorem component_inf_B1_eq_bot :
    (component l e ψ ν).comap (Z1 (componentModule l e ψ ν).ρ).subtype ⊓
      B1 (componentModule l e ψ ν).ρ = ⊥ :=
  (Submodule.eq_bot_iff _).2 fun _ hz ↦ eq_zero_of_mem_B1_of_apply_eq_zero
    (componentModule_ρ_cmConj hc) (isUnit_neg_one_sub_one h_two) (Submodule.mem_inf.1 hz).2
    ((Submodule.mem_inf.1 ((comap_component_eq l e ψ ν) ▸ (Submodule.mem_inf.1 hz).1)).2)

/-- For `Υ` odd and `2` a unit, the component has the length of its module of classes
`componentClasses` in `H¹(Gal(Ω/ℚ), O / l ^ ν (Υ⁻¹))`. -/
theorem length_component_eq_length_classes :
    length O (component l e ψ ν) = length O (componentClasses l e ψ ν) := by
  have h_eq := LinearEquiv.length_eq (R := O)
    (M := (component l e ψ ν).comap (Z1 (componentModule l e ψ ν).ρ).subtype)
    (N := component l e ψ ν) (Submodule.comapSubtypeEquivOfLe (component_le_Z1 l e ψ ν))
  rw [← h_eq, comap_component_eq l e ψ ν]
  exact length_inf_vanishingAt_eq_length_map (componentModule_ρ_cmConj hc)
    (isUnit_neg_one_sub_one h_two) (componentModule l e ψ ν).continuous_orbit _
    (componentModule l e ψ ν).ker_π₁ (B1_le_componentCocyclesZ1 l e ψ ν)

/-- For `Υ` odd and `2` a unit, the component is isomorphic to the group of classes of
`componentCocycles` in Mathlib's `continuousCohomology 1`. -/
def componentEquivClasses :
    component l e ψ ν ≃+
      (componentCocyclesZ1 l e ψ ν).toAddSubgroup.map (componentModule l e ψ ν).classMap :=
  ((Submodule.comapSubtypeEquivOfLe (component_le_Z1 l e ψ ν)).symm.toAddEquiv.trans
    (AddEquiv.addSubgroupCongr
      (congrArg Submodule.toAddSubgroup (comap_component_eq l e ψ ν)))).trans <|
    infVanishingAtEquivMap (W := (componentCocyclesZ1 l e ψ ν).toAddSubgroup)
      (componentModule_ρ_cmConj hc) (isUnit_neg_one_sub_one h_two)
      (componentModule l e ψ ν).continuous_orbit _ (componentModule l e ψ ν).ker_classMap
      ((Submodule.toAddSubgroup_le _ _).2 (B1_le_componentCocyclesZ1 l e ψ ν))

/-- For `Υ` odd and `2` a unit, the component has as many elements as its group of classes. -/
theorem card_component_eq_card_classes :
    Nat.card (component l e ψ ν) = Nat.card
      ((componentCocyclesZ1 l e ψ ν).toAddSubgroup.map (componentModule l e ψ ν).classMap) :=
  Nat.card_congr (componentEquivClasses hc h_two).toEquiv

/-- For `Υ` odd and `2` a unit, every class of `componentCocycles` has a representative in the
component. -/
lemma exists_mem_component_π₁_eq {c : (componentModule l e ψ ν).H 1}
    (hc' : c ∈ componentClasses l e ψ ν) :
    ∃ z : Z1 (componentModule l e ψ ν).ρ,
      (z : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)) ∈ component l e ψ ν ∧
        (componentModule l e ψ ν).π₁ z = c := by
  unfold componentClasses at hc'
  rw [← map_inf_vanishingAt_eq_map_of_linear (componentModule_ρ_cmConj hc)
    (isUnit_neg_one_sub_one h_two) (componentModule l e ψ ν).continuous_orbit _
    (componentModule l e ψ ν).ker_π₁ (B1_le_componentCocyclesZ1 l e ψ ν),
    ← comap_component_eq l e ψ ν] at hc'
  obtain ⟨z, hz, rfl⟩ := hc'
  exact ⟨z, hz, rfl⟩

end Odd

/-- `New.OddPart.finite_component` for classes: the module of classes of `componentCocycles` is
finite. -/
theorem finite_componentClasses : Finite (componentClasses l e ψ ν) := by
  have h_fin : Finite (componentCocycles l e ψ ν) :=
    finite_vanishingCocycles (n := ν)
      (fun g y ↦ (cyclotomicPowDirichlet_smul_eq_self g.prop
        (Selmer.nsmul_quot_eq_zero dvd_rfl y)).right)
      fun _ ⟨h_fix, h_inertia⟩ ↦ ⟨h_fix, .inl h_inertia⟩
  have h_finZ : Finite (componentCocyclesZ1 l e ψ ν) :=
    .of_injective (fun z ↦ (⟨z.1.1, z.2⟩ : componentCocycles l e ψ ν)) fun z z' h ↦ by
      exact Subtype.ext (Subtype.ext (Subtype.mk.inj h))
  exact .of_surjective _ (LinearMap.submoduleMap_surjective _ _)

/-- `New.OddPart.nsmul_component_eq_zero` for classes. Let `X` have the Stickelberger property
`IsStickelbergerBound N e X`, let `Υ = cyc ^ e ψ` be odd, `e ≠ 0` and `2` a unit of `O`. Then
`4 X²` kills the module of classes of `componentCocycles` in `H¹(Gal(Ω/ℚ), O / l ^ ν (Υ⁻¹))`. -/
theorem nsmul_componentClasses_eq_zero (h_bound : IsStickelbergerBound N e X)
    (hc : cyclotomicPowDirichlet l e ψ cmConj = -1) (he_ne_zero : e ≠ 0)
    (h_two : IsUnit (2 : O)) {c : (componentModule l e ψ ν).H 1}
    (hc' : c ∈ componentClasses l e ψ ν) : (4 * X * X) • c = 0 := by
  obtain ⟨z, hz, rfl⟩ := exists_mem_component_π₁_eq hc h_two hc'
  have h_zero : (4 * X * X) • z = 0 :=
    Subtype.ext (nsmul_component_eq_zero h_bound hc he_ne_zero hz)
  rw [← map_nsmul, h_zero, map_zero]

/-- `New.OddPart.exists_detecting_points_component` for classes. Let `X ≠ 0` satisfy
`IsStickelbergerBound N e X`, let `Υ = cyc ^ e ψ` be odd, `e ≠ 0` and `l > N + e + 3`. Then there
are `v_l(X) + 1` elements `γ i` of the Galois group such that a class of `componentCocycles` in
`H¹(Gal(Ω/ℚ), O / l ^ ν (Υ⁻¹))` is zero when a representative `z` has
`z (γ i * cmConj) = z (cmConj * γ i)` for all `i`. The difference
`z (γ cmConj) - z (cmConj γ)` is `2 z(γ) + (Υ⁻¹(γ) - 1) z(cmConj)`, and it is the same for all
representatives of a class. -/
theorem exists_detecting_points_componentClasses (h_bound : IsStickelbergerBound N e X)
    (hc : cyclotomicPowDirichlet l e ψ cmConj = -1) (he_ne_zero : e ≠ 0) (hX : X ≠ 0)
    (hl : N + e + 3 < l) :
    ∃ γ : Fin (X.factorization l + 1) → Gal(Ω/ℚ),
      ∀ z ∈ componentCocyclesZ1 l e ψ ν,
        (∀ i, (z : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)) (γ i * cmConj) =
          (z : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)) (cmConj * γ i)) →
        (componentModule l e ψ ν).π₁ z = 0 := by
  have h_two : IsUnit (2 : O) :=
    isUnit_natCast_of_not_dvd (k := 2) fun h ↦ by have := Nat.le_of_dvd two_pos h; lia
  obtain ⟨γ, hγ⟩ := exists_detecting_points_component (ν := ν) h_bound hc he_ne_zero hX hl
  refine ⟨γ, fun z hz h_eq ↦ ?_⟩
  obtain ⟨b, hb, hzb⟩ := exists_sub_mem_B1_apply_eq_zero (componentModule_ρ_cmConj hc)
    (isUnit_neg_one_sub_one h_two) (componentModule l e ψ ν).continuous_orbit z
  have hz' : z - b ∈ componentCocyclesZ1 l e ψ ν ⊓ vanishingAt _ cmConj :=
    ⟨sub_mem hz (B1_le_componentCocyclesZ1 l e ψ ν hb), hzb⟩
  rw [← comap_component_eq l e ψ ν] at hz'
  -- A coboundary takes the same value at `γ cmConj` and at `cmConj γ`, as the action is abelian.
  obtain ⟨m, hm⟩ := mem_B1_iff.1 hb
  have h_comm (g : Gal(Ω/ℚ)) :
      (b : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)) (g * cmConj) =
        (b : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)) (cmConj * g) := by
    rw [← hm, ← hm, componentModule_ρ_apply, componentModule_ρ_apply, map_mul, map_mul,
      Units.val_mul, Units.val_mul, mul_comm (((cyclotomicPowDirichlet l e ψ)⁻¹ g).val)]
  -- So `z - b` vanishes at `cmConj` and takes the same value at `γ i cmConj` and `cmConj γ i`,
  -- which are `(z - b)(γ i)` and `-(z - b)(γ i)`; as `2` is a unit, `z - b` vanishes at `γ i`.
  have h_zero : z - b = 0 := by
    refine Subtype.ext (hγ _ hz' fun i ↦ h_two.smul_left_cancel.1 ?_)
    set w : Z1 (componentModule l e ψ ν).ρ := z - b
    have hw_c : (w : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)) cmConj = 0 := hzb
    have hw_eq : (w : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)) (γ i * cmConj) =
        (w : Gal(Ω/ℚ) → QuotSpan (l ^ ν : O)) (cmConj * γ i) := by
      simp only [w, Submodule.coe_sub, Pi.sub_apply, h_eq i, h_comm]
    rw [w.2.2, w.2.2, hw_c, map_zero, add_zero, componentModule_ρ_cmConj hc, zero_add] at hw_eq
    rw [smul_zero, two_smul]
    nth_rewrite 1 [hw_eq]
    rw [neg_one_smul, neg_add_cancel]
  rw [← sub_add_cancel z b, h_zero, zero_add, ← LinearMap.mem_ker,
    (componentModule l e ψ ν).ker_π₁]
  exact hb

end New.OddPart

end
