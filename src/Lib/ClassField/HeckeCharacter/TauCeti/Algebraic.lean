import Lib.ClassField.HeckeCharacter.TauCeti.Basic
import Lib.ClassField.Local.ArtinMap
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.Algebraic

/-!
# Our algebraic Hecke characters as Tau Ceti Hecke characters

An element `θ` of `New.AlgHeckeChar K` is a character `θ.character` of the finite ideles with open
kernel and an infinity type `θ.infinityType : (K →+* ℂ) → ℤ` with
`θ.character x = ∏ σ, σ x ^ (-θ.infinityType σ)` on `Kˣ`. This file builds the Tau Ceti Hecke
character `a ↦ θ(a_f) ∏_σ σ(a_σ) ^ (θ.infinityType σ)` of such a `θ` (with `σ(a_σ)` the extension of
`σ` to the completion at the place of `σ`) and shows that its Tau Ceti infinity type is the image
of `θ.infinityType` under `AlgebraicInfinityType.toContinuous`, with no change of sign. In
particular it is algebraic in Tau Ceti's sense.

## Main definitions and results

* `New.AlgHeckeChar.toHeckeCharacter`: the Tau Ceti Hecke character of `θ`.
* `New.AlgHeckeChar.finiteRestriction_toHeckeCharacter`,
  `New.AlgHeckeChar.finiteComponent_toHeckeCharacter`: its finite part is `θ.character`, and its
  component at a finite place `v` is `θ.character ∘ locIdele v`.
* `New.AlgHeckeChar.infinityType_toHeckeCharacter`: its infinity type is
  `AlgebraicInfinityType.toContinuous θ.infinityType`.
* `New.AlgHeckeChar.isAlgebraic_toHeckeCharacter`: it is algebraic.
-/

noncomputable section

open NumberField IsDedekindDomain TauCeti TauCeti.GlobalNumberFields InfinitePlace.Completion
  New.HeckeTC

namespace New

namespace AlgHeckeChar

variable {K : Type} [Field K] [NumberField K]

/-- The archimedean part at `w` of an algebraic Hecke character of infinity type `n`:
`z ↦ ∏ σ, σ(z) ^ n σ` over the complex embeddings `σ` that induce `w`, extended to `K_w`. -/
def infinityChar (n : (K →+* ℂ) → ℤ) (w : InfinitePlace K) : w.Completionˣ →ₜ* ℂˣ where
  toMonoidHom := ∏ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ ↦ InfinitePlace.mk σ = w),
    (completionEmbeddingUnits w σ : w.Completionˣ →* ℂˣ) ^ n σ
  continuous_toFun := by
    refine (continuous_finsetProd (f := fun σ z ↦ completionEmbeddingUnits w σ z ^ n σ)
      (Finset.univ.filter (fun σ : K →+* ℂ ↦ InfinitePlace.mk σ = w)) fun σ _ ↦
        (completionEmbeddingUnits w σ).continuous.zpow (n σ)).congr fun z ↦ ?_
    simp

lemma coe_infinityChar_apply (n : (K →+* ℂ) → ℤ) (w : InfinitePlace K) (z : w.Completionˣ) :
    (infinityChar n w z : ℂ) =
      ∏ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ ↦ InfinitePlace.mk σ = w),
        completionEmbedding w σ z ^ n σ := by
  simp [infinityChar, completionEmbeddingUnits]

/-- On `Kˣ`, the product over all infinite places of the archimedean parts of infinity type `n` is
`∏ σ, σ x ^ n σ`. -/
lemma prod_infinityChar_algebraMap (n : (K →+* ℂ) → ℤ) (x : Kˣ) :
    ∏ w, (infinityChar n w (Units.map (algebraMap K w.Completion).toMonoidHom x) : ℂ) =
      ∏ σ : K →+* ℂ, σ x ^ n σ := by
  simp_rw [coe_infinityChar_apply]
  rw [← Finset.prod_fiberwise Finset.univ (fun σ : K →+* ℂ ↦ InfinitePlace.mk σ)]
  refine Finset.prod_congr rfl fun w _ ↦ Finset.prod_congr rfl fun σ hσ ↦ ?_
  simp only [Units.coe_map, MonoidHom.coe_ofClass, RingHom.toMonoidHom_eq_coe]
  rw [completionEmbedding_algebraMap (Finset.mem_filter.1 hσ).2]

/-- The Tau Ceti Hecke character of an algebraic Hecke character `θ`: the character
`a ↦ θ(a_f) ∏_σ σ(a_σ) ^ (θ.infinityType σ)` of the idele class group. -/
def toHeckeCharacter (θ : AlgHeckeChar K) : HeckeCharacter K :=
  ofComponents θ.character θ.property.1 (infinityChar θ.infinityType) fun x ↦ by
    ext
    rw [Units.val_mul, Units.coe_prod, prod_infinityChar_algebraMap, θ.property.2 x, Units.val_one,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun σ _ ↦ ?_
    rw [← zpow_add₀ (by simp), neg_add_cancel, zpow_zero]

variable (θ : AlgHeckeChar K)

/-- The restriction of the Tau Ceti character of `θ` to the finite ideles is `θ.character`. -/
@[simp] lemma finiteRestriction_toHeckeCharacter :
    finiteRestriction θ.toHeckeCharacter = θ.character :=
  finiteRestriction_ofComponents ..

/-- The local component at a finite place `v` of the Tau Ceti character of `θ` is
`θ.character ∘ locIdele v`. -/
@[simp] lemma finiteComponent_toHeckeCharacter (v : FinPlace K) (x : (LocField v)ˣ) :
    θ.toHeckeCharacter.finiteComponent v x = θ.character (locIdele v x) :=
  ofComponents_finiteComponent ..

/-- The component at an infinite place `w` of the Tau Ceti character of `θ` is
`New.AlgHeckeChar.infinityChar θ.infinityType w`. -/
@[simp] lemma infiniteComponent_toHeckeCharacter (w : InfinitePlace K) :
    θ.toHeckeCharacter.infiniteComponent w = infinityChar θ.infinityType w :=
  ofComponents_infiniteComponent ..

/-- A product over the complex embeddings that induce a complex place `w` is the product of the
values at `w.embedding` and at its conjugate. -/
lemma prod_filter_mk_eq_of_isComplex {M : Type*} [CommMonoid M] {w : InfinitePlace K}
    (hw : w.IsComplex) (f : (K →+* ℂ) → M) :
    ∏ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ ↦ InfinitePlace.mk σ = w), f σ =
      f w.embedding * f (ComplexEmbedding.conjugate w.embedding) := by
  classical
  have h_ne : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun h ↦
    InfinitePlace.isComplex_iff.1 hw (ComplexEmbedding.isReal_iff.2 h.symm)
  have h_filter : Finset.univ.filter (fun σ : K →+* ℂ ↦ InfinitePlace.mk σ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      rcases InfinitePlace.mk_eq_iff.1 (h.trans (InfinitePlace.mk_embedding w).symm) with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by rw [← h']; exact (star_star σ).symm)
    · rintro (rfl | rfl)
      · exact InfinitePlace.mk_embedding w
      · rw [InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  rw [h_filter, Finset.prod_pair h_ne]

/-- A product over the complex embeddings that induce a real place `w` is the value at
`w.embedding`. -/
lemma prod_filter_mk_eq_of_isReal {M : Type*} [CommMonoid M] {w : InfinitePlace K}
    (hw : w.IsReal) (f : (K →+* ℂ) → M) :
    ∏ σ ∈ Finset.univ.filter (fun σ : K →+* ℂ ↦ InfinitePlace.mk σ = w), f σ = f w.embedding := by
  classical
  have h_real : ComplexEmbedding.conjugate w.embedding = w.embedding :=
    ComplexEmbedding.isReal_iff.1 (InfinitePlace.isReal_iff.1 hw)
  have h_filter : Finset.univ.filter (fun σ : K →+* ℂ ↦ InfinitePlace.mk σ = w) =
      {w.embedding} := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h
      rcases InfinitePlace.mk_eq_iff.1 (h.trans (InfinitePlace.mk_embedding w).symm) with h' | h'
      · exact h'
      · calc σ = ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) :=
            (star_star σ).symm
          _ = w.embedding := by rw [h', h_real]
    · rintro rfl
      exact InfinitePlace.mk_embedding w
  rw [h_filter, Finset.prod_singleton]

/-- At a real place `w`, the component of the Tau Ceti character of `θ` is `x ↦ x ^ n`, with `n`
the exponent of `θ` at `w.embedding`. -/
lemma realComponent_toHeckeCharacter (w : {w : InfinitePlace K // w.IsReal}) :
    θ.toHeckeCharacter.realComponent w =
      realUnitsCharacter (θ.infinityType w.val.embedding) (θ.infinityType w.val.embedding) := by
  ext x
  rw [HeckeCharacter.realComponent_apply, infiniteComponent_toHeckeCharacter,
    coe_infinityChar_apply, prod_filter_mk_eq_of_isReal w.property, completionEmbedding_embedding,
    coe_realUnitsCharacter_intCast,
    ← extensionEmbeddingOfIsReal_apply w.property, ← continuousMulEquivRealOfIsReal_apply]
  simp

/-- At a complex place `w`, the component of the Tau Ceti character of `θ` is `z ↦ z ^ a z̄ ^ b`,
with `a` and `b` the exponents of `θ` at `w.embedding` and at its conjugate. -/
lemma complexComponent_toHeckeCharacter (w : {w : InfinitePlace K // w.IsComplex}) :
    θ.toHeckeCharacter.complexComponent w =
      complexUnitsCharacter
        ((θ.infinityType w.val.embedding +
          θ.infinityType (ComplexEmbedding.conjugate w.val.embedding) : ℤ) : ℂ)
        (θ.infinityType w.val.embedding -
          θ.infinityType (ComplexEmbedding.conjugate w.val.embedding)) := by
  ext z
  have h_ne : ComplexEmbedding.conjugate w.val.embedding ≠ w.val.embedding := fun h ↦
    InfinitePlace.isComplex_iff.1 w.property (ComplexEmbedding.isReal_iff.2 h)
  rw [HeckeCharacter.complexComponent_apply, infiniteComponent_toHeckeCharacter,
    coe_infinityChar_apply, prod_filter_mk_eq_of_isComplex w.property,
    completionEmbedding_embedding, completionEmbedding_of_ne h_ne,
    coe_complexUnitsCharacter_intCast]
  simp

/-- **The infinity type of the Tau Ceti character of `θ` is `θ.infinityType`**, read as a continuous
infinity type by `AlgebraicInfinityType.toContinuous`. -/
theorem infinityType_toHeckeCharacter :
    θ.toHeckeCharacter.infinityType = AlgebraicInfinityType.toContinuous θ.infinityType := by
  refine HeckeCharacter.infinityType_eq_iff.2 ⟨fun w ↦ ?_, fun w ↦ ?_⟩
  · rw [realComponent_toHeckeCharacter]
    simp
  · rw [complexComponent_toHeckeCharacter]
    simp

/-- The Tau Ceti character of an algebraic Hecke character is algebraic. -/
theorem isAlgebraic_toHeckeCharacter : θ.toHeckeCharacter.IsAlgebraic := by
  rw [HeckeCharacter.IsAlgebraic, infinityType_toHeckeCharacter]
  exact ContinuousInfinityType.isAlgebraicOnIdentityComponent_toContinuous _

end AlgHeckeChar

end New
