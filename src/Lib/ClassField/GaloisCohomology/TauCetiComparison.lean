import Lib.ClassField.Places.DecompositionCompletion
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
import TauCeti.RepresentationTheory.Homological.ContCohomology.CarryCocycle
import TauCeti.FieldTheory.KrullTopology

/-!
# Comparison of the Galois framework with Mathlib and Tau Ceti

This file compares the explicit Galois cohomology and the Galois groups of this library with
their counterparts in Mathlib and Tau Ceti. It changes nothing else: no file imports it yet. It is
the first step of moving the library onto the shared definitions.

## Main definitions and results

* `New.Z1_toAddSubgroup`, `New.Z2_toAddSubgroup`, `New.B2_toAddSubgroup`: for a representation `ρ`
  given by an action (`hρ : ρ g m = g • m`), the continuous cocycles and coboundaries `New.Z1 ρ`,
  `New.Z2 ρ`, `New.B2 ρ` are Tau Ceti's `TauCeti.ContCohomology.Z1`, `Z2`, `B2`.
* `New.H2AddEquiv`, `New.H2AddEquivContinuousCohomology`: `New.H2 ρ` is Tau Ceti's explicit `H²`,
  and so Mathlib's `continuousCohomology 2` of the discrete module, for a locally compact group.
* `New.QZ.carry_eq_characterCarry`, `New.H2AddEquiv_cyclicClass`: the carry of `New.QZ`, which is
  `AddCircle (1 : ℚ)`, is Tau Ceti's `characterCarry`, and `New.cyclicClass` is the class of
  `TauCeti.ContCohomology.characterCarryCocycle`.
* `New.galEquivAbsoluteGaloisGroup`: for an algebraic closure `Ω` of `K`, the Galois group
  `Gal(Ω/K)` used here is Mathlib's `Field.absoluteGaloisGroup K` as a topological group. For
  `New.Ω` over `ℚ` the two are equal by definition (`New.galΩ_eq_absoluteGaloisGroup`).
* `New.IsProGalois.toGalEquiv`: a group acting as the profinite Galois group of `Ω / K` is
  `Gal(Ω/K)` as a topological group.
* `New.IsCompletionEmb.decompGroupEquiv`: given completion data at a place `A` over `v`, the
  decomposition group of `A` is the absolute Galois group of the completion `LocField v`, which is
  `v.adicCompletion K`.
* `New.decompGroup_eq_decompositionSubgroup`, `New.mem_inertiaGroup_iff_mem_inertiaSubgroup`: for
  `Γ = Gal(L/K)`, `New.decompGroup` and `New.inertiaGroup` are Mathlib's
  `ValuationSubring.decompositionSubgroup` and `ValuationSubring.inertiaSubgroup`.

The coefficient ring `R` of `New.Z1 ρ` plays no part: Tau Ceti's groups are additive subgroups,
and the comparisons are for the underlying additive subgroups.
-/

noncomputable section

open TauCeti.ContCohomology

namespace New

/-! ### Cocycles and `H²` -/

section Cocycles

variable {R G M : Type*} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M]
  [Module R M] [TopologicalSpace M] [DiscreteTopology M] [DistribMulAction G M]
  {ρ : Representation R G M} (hρ : ∀ (g : G) (m : M), ρ g m = g • m)

include hρ

/-- The continuous 1-cocycles of `ρ` are Tau Ceti's continuous 1-cocycles of the action. -/
theorem Z1_toAddSubgroup : (Z1 ρ).toAddSubgroup = TauCeti.ContCohomology.Z1 G M := by
  ext f
  simp only [Submodule.mem_toAddSubgroup, mem_Z1_iff, groupCohomology.IsCocycle₁, ← hρ]
  exact and_congr Iff.rfl (forall₂_congr fun g h ↦ by rw [add_comm (f g)])

/-- The continuous 2-cocycles of `ρ` are Tau Ceti's continuous 2-cocycles of the action. -/
theorem Z2_toAddSubgroup : (Z2 ρ).toAddSubgroup = TauCeti.ContCohomology.Z2 G M := by
  ext f
  simp only [Submodule.mem_toAddSubgroup, mem_Z2_iff, groupCohomology.IsCocycle₂, ← hρ]
  refine and_congr Iff.rfl (forall₃_congr fun g h k ↦ ?_)
  constructor <;> intro h_eq
  · rw [h_eq]; abel
  · rw [eq_sub_of_add_eq h_eq]; abel

/-- The 2-coboundaries of `ρ` are Tau Ceti's 2-coboundaries, the images of continuous cochains. -/
theorem B2_toAddSubgroup : (B2 ρ).toAddSubgroup = TauCeti.ContCohomology.B2 G M := by
  ext f
  simp only [Submodule.mem_toAddSubgroup, mem_B2_iff]
  refine exists_congr fun c ↦ and_congr Iff.rfl ⟨fun h ↦ funext fun ⟨g, g'⟩ ↦ ?_, ?_⟩
  · rw [d1_apply, h g g', hρ]
  · rintro rfl g g'
    rw [d1_apply, hρ]

/-- The continuous 2-cocycles of `ρ`, as an additive group, are Tau Ceti's. -/
def Z2AddEquiv : Z2 ρ ≃+ TauCeti.ContCohomology.Z2 G M where
  toFun z := ⟨z.1, by rw [← Z2_toAddSubgroup hρ]; exact z.2⟩
  invFun z := ⟨z.1, by
    rw [← Submodule.mem_toAddSubgroup, Z2_toAddSubgroup hρ]; exact z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_Z2AddEquiv (z : Z2 ρ) : (Z2AddEquiv hρ z : G × G → M) = z := rfl

variable [IsTopologicalAddGroup M] [ContinuousMul G] [ContinuousSMul G M]

/-- `New.H2 ρ` is Tau Ceti's explicit `H²` of the action: both are continuous 2-cocycles modulo
the coboundaries of continuous 1-cochains. -/
def H2AddEquiv : H2 ρ ≃+ TauCeti.ContCohomology.H2 G M :=
  QuotientAddGroup.congr ((B2 ρ).comap (Z2 ρ).subtype).toAddSubgroup _ (Z2AddEquiv hρ) <| by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [AddSubgroup.mem_addSubgroupOf, ← B2_toAddSubgroup hρ]
      exact hw
    · intro hz
      refine ⟨(Z2AddEquiv hρ).symm z, ?_, (Z2AddEquiv hρ).apply_symm_apply z⟩
      rw [AddSubgroup.mem_addSubgroupOf, ← B2_toAddSubgroup hρ] at hz
      exact hz

/-- The class of a cocycle goes to the class of the same function. -/
@[simp]
theorem H2AddEquiv_mk (z : Z2 ρ) :
    H2AddEquiv hρ (Submodule.Quotient.mk z) = (Z2AddEquiv hρ z : TauCeti.ContCohomology.H2 G M) :=
  rfl

end Cocycles

section ContinuousCohomology

universe u

variable {R : Type*} {G M : Type u} [CommRing R] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
  {ρ : Representation R G M} (hρ : ∀ (g : G) (m : M), ρ g m = g • m)

/-- `New.H2 ρ` is Mathlib's continuous cohomology `continuousCohomology 2` of the discrete module
`M`, through Tau Ceti's explicit `H²`. The group `G` and the module `M` lie in one universe. -/
def H2AddEquivContinuousCohomology :
    H2 ρ ≃+ continuousCohomology 2 (TauCeti.ofDiscreteModule ℤ G M) :=
  (H2AddEquiv hρ).trans (explicitH2AddEquivContinuousCohomology G M)

end ContinuousCohomology

/-! ### The carry and the cyclic class -/

section Carry

variable {R G M : Type*} [CommRing R] [Group G] [TopologicalSpace G]

/-- A continuous character `G → ℚ/ℤ` as an additive homomorphism on `Additive G`, the form of
Tau Ceti's characters. -/
def QZChar.toAdditiveHom (χ : QZChar G) : Additive G →+ AddCircle (1 : ℚ) where
  toFun g := (χ : G → QZ) g.toMul
  map_zero' := show (χ : G → QZ) 1 = 0 by simpa using χ.prop.right 1 1
  map_add' g h := QZChar.apply_mul χ g.toMul h.toMul

@[simp]
theorem QZChar.toAdditiveHom_apply (χ : QZChar G) (g : G) :
    QZChar.toAdditiveHom χ (.ofMul g) = (χ : G → QZ) g := rfl

/-- The kernel of a continuous character into the discrete group `ℚ/ℤ` is open. -/
theorem QZChar.isOpen_ker_toAdditiveHom (χ : QZChar G) :
    IsOpen ((QZChar.toAdditiveHom χ).ker : Set (Additive G)) :=
  (isOpen_discrete ({0} : Set QZ)).preimage (χ.prop.left.comp continuous_toMul)

/-- The carry of the values of a character is Tau Ceti's `characterCarry`. -/
theorem QZ.carry_eq_characterCarry (χ : QZChar G) (g h : G) :
    ((χ : G → QZ) g).carry ((χ : G → QZ) h) = characterCarry (QZChar.toAdditiveHom χ) g h := rfl

variable [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] {ρ : Representation R G M} (hρ : ∀ (g : G) (m : M), ρ g m = g • m)
  [IsTopologicalAddGroup M] [ContinuousMul G] [ContinuousSMul G M]

/-- An invariant of `ρ` is a fixed point of the action. -/
def invariantsToH0 (w : ρ.invariants) : H0 G M :=
  ⟨w, fun g ↦ by rw [← hρ]; exact w.prop g⟩

/-- The cyclic class `(χ, w)` is the class of Tau Ceti's carry cocycle of `χ` and `w`. -/
theorem H2AddEquiv_cyclicClass (χ : QZChar G) (w : ρ.invariants) :
    H2AddEquiv hρ (cyclicClass ρ χ w) =
      (characterCarryCocycle (QZChar.toAdditiveHom χ) (QZChar.isOpen_ker_toAdditiveHom χ)
        (invariantsToH0 hρ w) : TauCeti.ContCohomology.H2 G M) :=
  rfl

end Carry

/-! ### Galois groups -/

section Galois

/-- The Galois group of `New.Ω` over `ℚ` is, by definition, Mathlib's absolute Galois group of
`ℚ`. -/
theorem galΩ_eq_absoluteGaloisGroup : Gal(Ω/ℚ) = Field.absoluteGaloisGroup ℚ := rfl

variable (K Ω : Type*) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

/-- For an algebraic closure `Ω` of `K`, the Galois group `Gal(Ω/K)` with its Krull topology is
Mathlib's absolute Galois group of `K`, through conjugation by an isomorphism of algebraic
closures. -/
def galEquivAbsoluteGaloisGroup : Gal(Ω/K) ≃ₜ* Field.absoluteGaloisGroup K :=
  let e : Ω ≃ₐ[K] AlgebraicClosure K := IsAlgClosure.equiv K Ω (AlgebraicClosure K)
  { e.autCongr with
    continuous_toFun := e.continuous_autCongr
    continuous_invFun := e.symm.continuous_autCongr }

variable {K Ω}

/-- The element of the absolute Galois group attached to `σ` is its conjugate by the chosen
isomorphism of algebraic closures. -/
theorem galEquivAbsoluteGaloisGroup_apply (σ : Gal(Ω/K)) :
    galEquivAbsoluteGaloisGroup K Ω σ = (IsAlgClosure.equiv K Ω (AlgebraicClosure K)).autCongr σ :=
  rfl


end Galois

section ProGalois

variable {Γ K Ω : Type*} [Group Γ] [TopologicalSpace Γ] [Field K] [Field Ω] [Algebra K Ω]
  [MulSemiringAction Γ Ω] [G : IsProGalois Γ K Ω]

variable (Γ K Ω) in
/-- A group `Γ` acting as the profinite Galois group of `Ω / K` (`New.IsProGalois`) is `Gal(Ω/K)`
as a topological group, through its action. -/
def IsProGalois.toGalEquiv : Γ ≃ₜ* Gal(Ω/K) :=
  let e : Γ ≃* Gal(Ω/K) := MulEquiv.ofBijective (MulSemiringAction.toAlgAut Γ K Ω)
    ⟨fun g g' h_eq ↦ G.faithful.eq_of_smul_eq_smul fun x ↦ DFunLike.congr_fun h_eq x,
      toAlgAut_surjective Γ⟩
  { e with
    continuous_toFun := continuous_of_equivariant_emb 1 fun _ _ ↦ rfl
    continuous_invFun := continuous_of_equivariant_emb (Γ' := Gal(Ω/K)) (L := K) 1 fun σ x ↦ by
      change e (e.symm σ) x = σ x
      rw [e.apply_symm_apply] }

@[simp]
theorem IsProGalois.toGalEquiv_apply (g : Γ) (x : Ω) : IsProGalois.toGalEquiv Γ K Ω g x = g • x :=
  rfl

end ProGalois

section Completion

open IsDedekindDomain

variable {K : Type*} [Field K] [EmbeddedNumberField K] {v : FinPlace K}
  {p : ℕ} [f : Fact (Nat.Prime p)]
  {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [MulSemiringAction Γ Ω] [IsProGalois Γ K Ω]
  {A : ClosurePlace} [a : Algebra (LocField v) (PadicAlgCl p)] {j : Ω →+* PadicAlgCl p}

/-- Given completion data at the place `A` over `v` (`New.IsCompletionEmb`), the decomposition
group of `A` is the absolute Galois group of the completion `LocField v = v.adicCompletion K`. It
acts on `ℚ̄_p`, an algebraic closure of the completion. This is the group-theoretic part of the
comparison between the henselian local fields of this library and complete local fields. -/
def IsCompletionEmb.decompGroupEquiv (h : IsCompletionEmb v p Γ A j) :
    decompGroup Γ A ≃ₜ* Field.absoluteGaloisGroup (LocField v) :=
  letI := h.toMulSemiringAction
  haveI := h.toIsLocalGalois.toIsProGalois
  haveI : IsAlgClosure (LocField v) (PadicAlgCl p) := ⟨inferInstance, inferInstance⟩
  (IsProGalois.toGalEquiv (decompGroup Γ A) (LocField v) (PadicAlgCl p)).trans
    (galEquivAbsoluteGaloisGroup (LocField v) (PadicAlgCl p))

end Completion

/-! ### Decomposition and inertia groups -/

section Decomposition

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (A : ValuationSubring L)

/-- For the Galois group `Gal(L/K)`, `New.decompGroup` is Mathlib's decomposition subgroup. -/
theorem decompGroup_eq_decompositionSubgroup :
    decompGroup Gal(L/K) A = A.decompositionSubgroup K := rfl

/-- For the Galois group `Gal(L/K)`, `σ` is in `New.inertiaGroup` exactly when it lies in the
decomposition subgroup and in Mathlib's inertia subgroup, the kernel of the action on the residue
field of `A`. -/
theorem mem_inertiaGroup_iff_mem_inertiaSubgroup (σ : Gal(L/K)) :
    σ ∈ inertiaGroup Gal(L/K) A ↔
      ∃ h : σ ∈ A.decompositionSubgroup K, (⟨σ, h⟩ : A.decompositionSubgroup K) ∈
        A.inertiaSubgroup K := by
  rw [mem_inertiaGroup_iff, IsFrob]
  simp only [pow_one]
  refine ⟨fun ⟨h, h_val⟩ ↦ ⟨h, ?_⟩, fun ⟨h, h_res⟩ ↦ ⟨h, fun x hx ↦ ?_⟩⟩
  · -- `σ` acts trivially on the residue field: `σ a - a` lies in the maximal ideal of `A`.
    refine MonoidHom.mem_ker.mpr (RingEquiv.ext fun x ↦ ?_)
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
    change (⟨σ, h⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A a = IsLocalRing.residue A a
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact h_val a (by rw [ValuationSubring.valuation_le_one_iff]; exact a.prop)
  · have hx : x ∈ A := by rwa [ValuationSubring.valuation_le_one_iff] at hx
    have h_eq : (⟨σ, h⟩ : A.decompositionSubgroup K) • IsLocalRing.residue A ⟨x, hx⟩ =
        IsLocalRing.residue A ⟨x, hx⟩ :=
      RingEquiv.congr_fun (MonoidHom.mem_ker.mp h_res) _
    rw [← IsLocalRing.ResidueField.residue_smul, ← sub_eq_zero, ← map_sub,
      IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff] at h_eq
    exact h_eq

end Decomposition

end New
