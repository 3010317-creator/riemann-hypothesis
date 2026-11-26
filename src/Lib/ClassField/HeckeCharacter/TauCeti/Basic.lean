import Lib.ClassField.HeckeL.EulerProduct
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.FiniteComponent
import TauCeti.NumberTheory.NumberField.Global.HeckeCharacter.InfinityType

/-!
# Our Hecke characters as Tau Ceti Hecke characters

`New.IsHeckeOfType ψ n` describes a Hecke character through its finite part `ψ`, a character of
the finite ideles `(𝔸f K)ˣ` with open kernel, and its type `n`: on `Kˣ`,
`ψ x * ∏ w, (Φ w x / ‖Φ w x‖) ^ n w = 1`, with `Φ w` the complex embedding chosen at `w`
(`New.PlaceEmbedding`). Tau Ceti's `TauCeti.GlobalNumberFields.HeckeCharacter K` is a continuous
character of Mathlib's idele class group `IdeleClassGroup (𝓞 K) K`. This file builds the Tau Ceti
character of such a `ψ` and compares the two descriptions.

## Main definitions and results

* `New.HeckeTC.completionEmbedding w σ`: the extension to the completion `K_w` of a complex
  embedding `σ` inducing `w` (`w.embedding` extended, or its conjugate).
* `New.HeckeTC.ofComponents ψ hψ η h`: the Tau Ceti Hecke character `a ↦ ψ(a_f) ∏_w η_w(a_w)` built
  from a character `ψ` of the finite ideles with open kernel and characters `η w` of the `K_wˣ`,
  if their product is trivial on `Kˣ`; `New.HeckeTC.ofComponents_finiteComponent`,
  `New.HeckeTC.ofComponents_infiniteComponent` and `New.HeckeTC.ofComponents_ofFiniteIdele` give its
  components and its restriction to the finite ideles.
* `New.IsHeckeOfType.toHeckeCharacter`: the Tau Ceti character of `ψ`, unitary at infinity, with
  `ψ` as its finite part (`New.IsHeckeOfType.toHeckeCharacter_ofFiniteIdele`) and local components
  `ψ ∘ locIdele v` (`New.IsHeckeOfType.finiteComponent_toHeckeCharacter`).
* `New.IsHeckeOfType.infinityType_toHeckeCharacter`: its Tau Ceti infinity type: exponent `0`
  everywhere, parity `n w` at a real place, and angular frequency `n w` or `-n w` at a complex
  place,
  according as `Φ w` is `w.embedding` or its conjugate.
* `New.IsHeckeOfType.heckeCoeff_eq_finiteComponent`: the coefficients `New.heckeCoeff ψ S` of our
  Euler products are the values of the Tau Ceti local components at the chosen uniformisers.

## Conventions

No sign changes between the two sides: on `Kˣ` the finite part is the inverse of the archimedean
part on both sides, and the archimedean part of `New.IsHeckeOfType ψ n` at `w` is
`z ↦ (Φ_w z / |z|) ^ n w`, which in Tau Ceti's coordinate `w.embedding` at a complex place is the
angular character to the power `n w` or `-n w`.
-/

noncomputable section

open NumberField IsDedekindDomain TauCeti TauCeti.GlobalNumberFields InfinitePlace.Completion

namespace New

namespace HeckeTC

variable {K : Type*} [Field K]

/-! ### Embeddings of the completions at infinite places -/

/-- The extension to the completion `K_w` of the complex embedding `σ`: the extension of
`w.embedding` if `σ = w.embedding`, and its conjugate otherwise. If `σ` induces `w`, it extends `σ`
(`New.HeckeTC.completionEmbedding_algebraMap`). -/
def completionEmbedding (w : InfinitePlace K) (σ : K →+* ℂ) : w.Completion →+* ℂ :=
  open scoped Classical in
  if σ = w.embedding then extensionEmbedding w else (starRingEnd ℂ).comp (extensionEmbedding w)

lemma continuous_completionEmbedding (w : InfinitePlace K) (σ : K →+* ℂ) :
    Continuous (completionEmbedding w σ) := by
  unfold completionEmbedding
  split_ifs
  · exact (isometry_extensionEmbedding w).continuous
  · exact Complex.continuous_conj.comp (isometry_extensionEmbedding w).continuous

/-- If `σ` induces `w`, then `New.HeckeTC.completionEmbedding w σ` extends `σ`. -/
lemma completionEmbedding_algebraMap {w : InfinitePlace K} {σ : K →+* ℂ}
    (h : InfinitePlace.mk σ = w) (x : K) :
    completionEmbedding w σ (algebraMap K w.Completion x) = σ x := by
  have h_or : w.embedding = σ ∨ NumberField.ComplexEmbedding.conjugate w.embedding = σ := by
    rw [← InfinitePlace.mk_eq_iff, InfinitePlace.mk_embedding, h]
  unfold completionEmbedding
  split_ifs with h_eq
  · simp [h_eq, algebraMap_apply_eq_coe]
  · rcases h_or with h_or | h_or
    · exact absurd h_or.symm h_eq
    · simp [← h_or, algebraMap_apply_eq_coe]

/-- The embedding `w.embedding` itself extends to `extensionEmbedding w`. -/
lemma completionEmbedding_embedding (w : InfinitePlace K) :
    completionEmbedding w w.embedding = extensionEmbedding w := by
  simp [completionEmbedding]

/-- The conjugate of `w.embedding`, if different from it, extends to the conjugate of
`extensionEmbedding w`. -/
lemma completionEmbedding_of_ne {w : InfinitePlace K} {σ : K →+* ℂ} (h : σ ≠ w.embedding) :
    completionEmbedding w σ = (starRingEnd ℂ).comp (extensionEmbedding w) := by
  simp [completionEmbedding, h]

/-- The sign `1` if `σ = w.embedding` and `-1` otherwise. If `σ` induces the complex place `w`, the
angular character `z ↦ σ(z) / |z|` of `K_w` is `z ↦ (z / |z|) ^ embeddingSign w σ` in Tau Ceti's
coordinate `w.embedding`. -/
def embeddingSign (w : InfinitePlace K) (σ : K →+* ℂ) : ℤ :=
  open scoped Classical in
  if σ = w.embedding then 1 else -1

@[simp] lemma embeddingSign_embedding (w : InfinitePlace K) : embeddingSign w w.embedding = 1 := by
  simp [embeddingSign]

lemma embeddingSign_of_eq {w : InfinitePlace K} {σ : K →+* ℂ} (h : σ = w.embedding) :
    embeddingSign w σ = 1 := by
  simp [h]

lemma embeddingSign_of_ne {w : InfinitePlace K} {σ : K →+* ℂ} (h : σ ≠ w.embedding) :
    embeddingSign w σ = -1 := by
  simp [embeddingSign, h]

/-- The units of `K_w` mapped to `ℂˣ` by `New.HeckeTC.completionEmbedding w σ`, as a continuous
homomorphism. -/
def completionEmbeddingUnits (w : InfinitePlace K) (σ : K →+* ℂ) : w.Completionˣ →ₜ* ℂˣ :=
  ⟨Units.map (completionEmbedding w σ).toMonoidHom,
    Continuous.units_map _ (continuous_completionEmbedding w σ)⟩

variable [NumberField K]

/-! ### Ideles: the finite and the infinite parts

Tau Ceti's `IdeleGroup.toFiniteIdele` and `InfinitePlace.ideleInfiniteCoord` give the finite part of
an idele and its component at an infinite place; `IdeleGroup.ofFiniteIdele` reads a finite idele as
an idele with components `1` at the infinite places.
-/

lemma continuous_ideleInfiniteCoord (w : InfinitePlace K) :
    Continuous (w.ideleInfiniteCoord (R := 𝓞 K)) :=
  Continuous.units_map _ ((continuous_apply w).comp continuous_fst)

/-- Tau Ceti's principal finite ideles are ours. -/
@[simp] lemma unitEmbedding_eq_principalIdele (x : Kˣ) :
    FiniteAdeleRing.unitEmbedding (𝓞 K) K x = principalIdele x :=
  rfl

/-- Our local idele `locIdele v x` (component `x` at `v`, `1` elsewhere) is the finite part of
Mathlib's `IdeleGroup.ofAdicCompletion`. -/
lemma toFiniteIdele_ofAdicCompletion (v : FinPlace K) (x : (LocField v)ˣ) :
    IdeleGroup.toFiniteIdele (𝓞 K) K (IdeleGroup.ofAdicCompletion (𝓞 K) K v x) = locIdele v x := by
  refine Units.ext ?_
  apply RestrictedProduct.ext
  intro w
  change (FiniteAdeleRing.ofAdicCompletion K v (x : LocField v)) w = (locIdele v x : 𝔸f K) w
  by_cases h : w = v
  · subst h
    simp [locIdele_apply_self]
  · simp [locIdele_apply_of_ne h, h]

/-! ### Hecke characters from their finite and infinite parts -/

variable (ψ : (𝔸f K)ˣ →* ℂˣ) (hψ : ψ.ker.IsOpen) (η : ∀ w : InfinitePlace K, w.Completionˣ →ₜ* ℂˣ)
  (h : ∀ x : Kˣ, ψ (principalIdele x) *
    ∏ w, η w (Units.map (algebraMap K w.Completion).toMonoidHom x) = 1)

/-- The character `a ↦ ψ(a_f) ∏_w η_w(a_w)` of the ideles. -/
def idelesChar : IdeleGroup (𝓞 K) K →* ℂˣ :=
  ψ.comp (IdeleGroup.toFiniteIdele (𝓞 K) K) *
    ∏ w, (η w : w.Completionˣ →* ℂˣ).comp (w.ideleInfiniteCoord (R := 𝓞 K))

include hψ in
lemma continuous_idelesChar : Continuous (idelesChar ψ η) := by
  have hψc : Continuous ψ := MonoidHom.continuous_of_isOpen_ker ψ hψ
  refine (hψc.comp (IdeleGroup.continuous_toFiniteIdele (𝓞 K) K)).mul ?_
  have : ⇑(∏ w, (η w : w.Completionˣ →* ℂˣ).comp (w.ideleInfiniteCoord (R := 𝓞 K))) =
      fun a ↦ ∏ w, η w (w.ideleInfiniteCoord a) := by
    funext a
    simp 
  rw [this]
  exact continuous_finsetProd _ fun w _ ↦ (η w).continuous.comp (continuous_ideleInfiniteCoord w)

include h in
lemma principalSubgroup_le_ker_idelesChar :
    IdeleGroup.principalSubgroup (𝓞 K) K ≤ (idelesChar ψ η).ker := by
  rintro _ ⟨x, rfl⟩
  simpa [idelesChar] using h x

/-- The Tau Ceti Hecke character `a ↦ ψ(a_f) ∏_w η_w(a_w)` of `K`, for a character `ψ` of the finite
ideles with open kernel and characters `η w` of `K_wˣ` whose product is trivial on `Kˣ`. -/
def ofComponents : HeckeCharacter K where
  toMonoidHom := QuotientGroup.lift _ (idelesChar ψ η) (principalSubgroup_le_ker_idelesChar ψ η h)
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 (continuous_idelesChar ψ hψ η)

@[simp] lemma ofComponents_mk (a : IdeleGroup (𝓞 K) K) :
    ofComponents ψ hψ η h (a : IdeleClassGroup (𝓞 K) K) =
      ψ (IdeleGroup.toFiniteIdele (𝓞 K) K a) * ∏ w, η w (w.ideleInfiniteCoord a) := by
  simp [ofComponents, idelesChar]

/-- The Tau Ceti character built from `ψ` restricts to `ψ` on the finite ideles. -/
@[simp] lemma ofComponents_ofFiniteIdele (a : (𝔸f K)ˣ) :
    ofComponents ψ hψ η h (IdeleGroup.ofFiniteIdele (𝓞 K) K a : IdeleClassGroup (𝓞 K) K) = ψ a := by
  simp

/-- The local component at a finite place `v` of the Tau Ceti character built from `ψ` is
`ψ ∘ locIdele v`. -/
@[simp] lemma ofComponents_finiteComponent (v : FinPlace K) (x : (LocField v)ˣ) :
    (ofComponents ψ hψ η h).finiteComponent v x = ψ (locIdele v x) := by
  simp [HeckeCharacter.finiteComponent_apply, IdeleClassGroup.ofAdicCompletion,
    toFiniteIdele_ofAdicCompletion]

/-- The component at an infinite place `w` of the Tau Ceti character built from `ψ` and `η` is
`η w`. -/
@[simp] lemma ofComponents_infiniteComponent (w : InfinitePlace K) :
    (ofComponents ψ hψ η h).infiniteComponent w = η w := by
  ext x
  simp only [HeckeCharacter.infiniteComponent_apply, IdeleClassGroup.ofCompletion,
    MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply, ofComponents_mk,
    IdeleGroup.toFiniteIdele_ofCompletion, map_one, one_mul]
  rw [Finset.prod_eq_single w
    (fun w' _ hw' ↦ by rw [InfinitePlace.ideleInfiniteCoord_ofCompletion_of_ne w' hw', map_one])
    (by simp), InfinitePlace.ideleInfiniteCoord_ofCompletion_self]

/-- **A Tau Ceti Hecke character is determined by its finite and infinite parts**: by its values on
the finite ideles and its components at the infinite places. -/
theorem ext_of_ofFiniteIdele {χ χ' : HeckeCharacter K}
    (h_fin : ∀ a : (𝔸f K)ˣ, χ (IdeleGroup.ofFiniteIdele (𝓞 K) K a : IdeleClassGroup (𝓞 K) K) =
      χ' (IdeleGroup.ofFiniteIdele (𝓞 K) K a : IdeleClassGroup (𝓞 K) K))
    (h_inf : ∀ w, χ.infiniteComponent w = χ'.infiniteComponent w) : χ = χ' := by
  ext c
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (IdeleGroup.principalSubgroup (𝓞 K) K) c
  -- Split `a` into its components at the infinite places and its finite part.
  rw [← IdeleGroup.prod_ofCompletion_mul_ofFiniteIdele a]
  simp only [map_mul, map_prod]
  congr 2
  · refine Finset.prod_congr rfl fun w _ ↦ ?_
    exact DFunLike.congr_fun (h_inf w) (w.ideleInfiniteCoord a)
  · exact h_fin _

/-- The restriction of a Tau Ceti Hecke character to the finite ideles. -/
def finiteRestriction (χ : HeckeCharacter K) : (𝔸f K)ˣ →* ℂˣ :=
  (χ : IdeleClassGroup (𝓞 K) K →* ℂˣ).comp
    ((QuotientGroup.mk' _).comp (IdeleGroup.ofFiniteIdele (𝓞 K) K))

@[simp] lemma finiteRestriction_apply (χ : HeckeCharacter K) (a : (𝔸f K)ˣ) :
    finiteRestriction χ a = χ (IdeleGroup.ofFiniteIdele (𝓞 K) K a : IdeleClassGroup (𝓞 K) K) :=
  rfl

/-- The restriction of a Tau Ceti Hecke character to the finite ideles has open kernel. -/
lemma isOpen_ker_finiteRestriction (χ : HeckeCharacter K) : (finiteRestriction χ).ker.IsOpen := by
  -- `χ` is trivial on the finite parts of a congruence subgroup, which is open.
  obtain ⟨𝔪, h𝔪⟩ := χ.exists_modulus_finitePart_eq_one
  let U : Subgroup (𝔸f K)ˣ :=
    (ideleCongruenceSubgroup 𝔪).comap (IdeleGroup.ofFiniteIdele (𝓞 K) K)
  have hU : IsOpen (U : Set (𝔸f K)ˣ) :=
    (isOpen_ideleCongruenceSubgroup 𝔪).preimage (IdeleGroup.continuous_ofFiniteIdele _ _)
  refine Subgroup.isOpen_mono (H₁ := U) (fun a ha ↦ ?_) hU
  simpa using h𝔪 _ ha

/-- The local component at a finite place `v` of a Tau Ceti Hecke character is its finite
restriction composed with our `locIdele v`. -/
lemma finiteComponent_eq_finiteRestriction (χ : HeckeCharacter K) (v : FinPlace K)
    (x : (LocField v)ˣ) : χ.finiteComponent v x = finiteRestriction χ (locIdele v x) := by
  have h_fin : IdeleGroup.ofFiniteIdele (𝓞 K) K (locIdele v x) =
      IdeleGroup.ofAdicCompletion (𝓞 K) K v x := by
    rw [← toFiniteIdele_ofAdicCompletion]
    exact Units.ext rfl
  rw [finiteRestriction_apply, h_fin]
  rfl

/-- The restriction to the finite ideles of `New.HeckeTC.ofComponents ψ hψ η h` is `ψ`. -/
@[simp] lemma finiteRestriction_ofComponents : finiteRestriction (ofComponents ψ hψ η h) = ψ := by
  ext a
  simp

end HeckeTC

/-! ### The Tau Ceti character of a character of type `n` -/

namespace IsHeckeOfType

open HeckeTC

variable {K : Type*} [Field K] [NumberField K] [PlaceEmbedding K] {ψ : (𝔸f K)ˣ →* ℂˣ}
  {n : InfinitePlace K → ℤ}

/-- The archimedean part `z ↦ (Φ_w z / |Φ_w z|) ^ n w` at `w` of a Hecke character of type `n`
(`New.IsHeckeOfType.toHeckeCharacter`), a character of `K_wˣ`. -/
def infinityChar (n : InfinitePlace K → ℤ) (w : InfinitePlace K) : w.Completionˣ →ₜ* ℂˣ :=
  (complexUnitsCharacter 0 (n w)).comp (completionEmbeddingUnits w (Φ w))

omit [NumberField K] in
lemma coe_infinityChar_apply (w : InfinitePlace K) (z : w.Completionˣ) :
    (infinityChar n w z : ℂ) =
      (completionEmbedding w (Φ w) z / ‖completionEmbedding w (Φ w) z‖) ^ n w := by
  simp [infinityChar, completionEmbeddingUnits]

omit [NumberField K] in
/-- On `Kˣ`, the archimedean part at `w` of a character of type `n` is `(Φ_w x / |Φ_w x|) ^ n w`. -/
lemma coe_infinityChar_algebraMap (w : InfinitePlace K) (x : Kˣ) :
    (infinityChar n w (Units.map (algebraMap K w.Completion).toMonoidHom x) : ℂ) =
      (Φ w x.val / ‖Φ w x‖) ^ n w := by
  rw [coe_infinityChar_apply]
  simp [completionEmbedding_algebraMap (mk_Φ w)]

/-- The Tau Ceti Hecke character of a character `ψ` of the finite ideles of type `n`: the character
`a ↦ ψ(a_f) ∏_w (Φ_w(a_w) / |a_w|) ^ n w` of the idele class group. -/
def toHeckeCharacter (H : IsHeckeOfType ψ n) : HeckeCharacter K :=
  ofComponents ψ H.1 (infinityChar n) fun x ↦ by
    ext
    simp only [Units.val_mul, Units.coe_prod, coe_infinityChar_algebraMap, Units.val_one]
    exact H.2 x

variable (H : IsHeckeOfType ψ n)

/-- On the finite ideles, the Tau Ceti character of `ψ` is `ψ`. -/
@[simp] lemma toHeckeCharacter_ofFiniteIdele (a : (𝔸f K)ˣ) :
    H.toHeckeCharacter (IdeleGroup.ofFiniteIdele (𝓞 K) K a : IdeleClassGroup (𝓞 K) K) = ψ a :=
  ofComponents_ofFiniteIdele ..

/-- The local component at a finite place `v` of the Tau Ceti character of `ψ` is
`ψ ∘ locIdele v`. -/
@[simp] lemma finiteComponent_toHeckeCharacter (v : FinPlace K) (x : (LocField v)ˣ) :
    H.toHeckeCharacter.finiteComponent v x = ψ (locIdele v x) :=
  ofComponents_finiteComponent ..

/-- The component at an infinite place `w` of the Tau Ceti character of `ψ` is
`z ↦ (Φ_w z / |Φ_w z|) ^ n w`. -/
@[simp] lemma infiniteComponent_toHeckeCharacter (w : InfinitePlace K) :
    H.toHeckeCharacter.infiniteComponent w = infinityChar n w :=
  ofComponents_infiniteComponent ..

/-- The coefficient `New.heckeCoeff ψ S v` of our Euler products at `v ∉ S` is the value of the
Tau Ceti local component at `v` at the chosen uniformiser. -/
lemma heckeCoeff_eq_finiteComponent {S : Set (FinPlace K)} {v : FinPlace K} (hv : v ∉ S) :
    heckeCoeff ψ S v = (H.toHeckeCharacter.finiteComponent v (uniformizer v) : ℂ) := by
  rw [finiteComponent_toHeckeCharacter]
  simp [heckeCoeff, hv]

/-- `ψ` is unramified at `v` (`New.CharUnramifiedAt`) exactly when the local component of its Tau
Ceti character at `v` is trivial on the units of valuation `1`. -/
lemma charUnramifiedAt_iff (v : FinPlace K) :
    CharUnramifiedAt ψ v ↔
      ∀ u : (LocField v)ˣ, Valued.v u.val = 1 → H.toHeckeCharacter.finiteComponent v u = 1 := by
  simp only [CharUnramifiedAt, finiteComponent_toHeckeCharacter]

/-- At a real place `w`, the component of the Tau Ceti character of `ψ` is the power `n w` of the
sign character. -/
lemma realComponent_toHeckeCharacter (w : {w : InfinitePlace K // w.IsReal}) :
    H.toHeckeCharacter.realComponent w = realUnitsCharacter 0 (n w.val : ZMod 2) := by
  ext x
  rw [HeckeCharacter.realComponent_apply, infiniteComponent_toHeckeCharacter,
    coe_infinityChar_apply]
  set z := (Units.mapContinuousMulEquiv (continuousMulEquivRealOfIsReal w.property)).symm x
  -- Both extensions of the real embedding send `z` to `x`.
  have h_ext : extensionEmbedding w.val (z : w.val.Completion) = ((x : ℝ) : ℂ) := by
    rw [← extensionEmbeddingOfIsReal_apply w.property, ← continuousMulEquivRealOfIsReal_apply]
    simp [z]
  have h_emb : completionEmbedding w.val (Φ w.val) z = ((x : ℝ) : ℂ) := by
    unfold completionEmbedding
    split_ifs
    · exact h_ext
    · simp [h_ext]
  have h_sign : ((x : ℝ) : ℂ) / ‖((x : ℝ) : ℂ)‖ = (SignType.sign (x : ℝ) : ℂ) := by
    rcases lt_or_gt_of_ne x.ne_zero with hx | hx
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_neg hx, sign_neg hx]
      field_simp [hx.ne]
      simp
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx, sign_pos hx]
      field_simp [hx.ne']
      simp
  rw [h_emb, h_sign, coe_realUnitsCharacter_apply, Complex.cpow_zero, one_mul]
  rcases lt_or_gt_of_ne x.ne_zero with hx | hx
  · rw [sign_neg hx, SignType.coe_neg_one]
    rcases Int.even_or_odd (n w.val) with hk | hk
    · rw [ZMod.intCast_eq_zero_iff_even.mpr hk, ZMod.val_zero, pow_zero, hk.neg_one_zpow]
    · rw [ZMod.intCast_eq_one_iff_odd.mpr hk, ZMod.val_one, pow_one, hk.neg_one_zpow]
  · simp [sign_pos hx]

/-- At a complex place `w`, the component of the Tau Ceti character of `ψ` is `z ↦ (z / |z|) ^ n w`
in the coordinate `w.embedding` if `Φ w = w.embedding`, and `z ↦ (z / |z|) ^ (-n w)` otherwise. -/
lemma complexComponent_toHeckeCharacter (w : {w : InfinitePlace K // w.IsComplex}) :
    H.toHeckeCharacter.complexComponent w =
      complexUnitsCharacter 0 (embeddingSign w.val (Φ w.val) * n w.val) := by
  ext z
  rw [HeckeCharacter.complexComponent_apply, infiniteComponent_toHeckeCharacter]
  set y := (Units.mapContinuousMulEquiv (continuousMulEquivComplexOfIsComplex w.property)).symm z
  have h_ext : extensionEmbedding w.val (y : w.val.Completion) = z := by
    simp [y]
  by_cases h : Φ w.val = w.val.embedding
  · have : completionEmbeddingUnits w.val (Φ w.val) y = z := by
      ext
      simp [completionEmbeddingUnits, h, completionEmbedding_embedding, h_ext]
    rw [embeddingSign_of_eq h, one_mul]
    simp only [infinityChar, ContinuousMonoidHom.comp_toFun, this]
  · rw [embeddingSign_of_ne h, neg_one_mul]
    have : completionEmbeddingUnits w.val (Φ w.val) y =
        Units.map (starRingEnd ℂ : ℂ →* ℂ) z := by
      ext
      simp [completionEmbeddingUnits, completionEmbedding_of_ne h, h_ext]
    simp only [infinityChar, ContinuousMonoidHom.comp_toFun, this, complexUnitsCharacter_map_conj]

/-- **The infinity type of the Tau Ceti character of `ψ`.** All exponents are `0` (it is
unitary), the parity at a real place `w` is `n w`, and the angular frequency at a complex place `w`
is `n w` if `Φ w = w.embedding` and `-n w` if `Φ w` is the conjugate embedding
(`New.HeckeTC.embeddingSign`). -/
theorem infinityType_toHeckeCharacter :
    H.toHeckeCharacter.infinityType =
      { realExponent := 0
        realParity := fun w ↦ (n w.val : ZMod 2)
        complexExponent := 0
        complexAngularFrequency := fun w ↦ embeddingSign w.val (Φ w.val) * n w.val } :=
  HeckeCharacter.infinityType_eq_iff.2
    ⟨H.realComponent_toHeckeCharacter, H.complexComponent_toHeckeCharacter⟩

/-- The restriction of the Tau Ceti character of `ψ` to the finite ideles is `ψ`. -/
@[simp] lemma finiteRestriction_toHeckeCharacter : finiteRestriction H.toHeckeCharacter = ψ :=
  finiteRestriction_ofComponents ..

/-- **Conversely**, a Tau Ceti Hecke character whose components at the infinite places are those of
type `n` restricts on the finite ideles to a character of type `n`. -/
theorem _root_.New.HeckeTC.isHeckeOfType_finiteRestriction {χ : HeckeCharacter K}
    (hχ : ∀ w, χ.infiniteComponent w = infinityChar n w) :
    IsHeckeOfType (finiteRestriction χ) n := by
  refine ⟨isOpen_ker_finiteRestriction χ, fun x ↦ ?_⟩
  -- `χ` is trivial on the principal idele of `x`; split it into its finite and infinite parts.
  have h_one : χ (IdeleGroup.unitEmbedding (𝓞 K) K x : IdeleClassGroup (𝓞 K) K) = 1 := by
    have h_mem : IdeleGroup.unitEmbedding (𝓞 K) K x ∈ IdeleGroup.principalSubgroup (𝓞 K) K :=
      ⟨x, rfl⟩
    rw [(QuotientGroup.eq_one_iff _).2 h_mem, map_one]
  rw [← IdeleGroup.prod_ofCompletion_mul_ofFiniteIdele (IdeleGroup.unitEmbedding (𝓞 K) K x)]
    at h_one
  have h_inf (w : InfinitePlace K) :
      (χ (IdeleGroup.ofCompletion (𝓞 K) K w
        (w.ideleInfiniteCoord (IdeleGroup.unitEmbedding (𝓞 K) K x)) : IdeleClassGroup (𝓞 K) K) :
          ℂ) = (Φ w x.val / ‖Φ w x‖) ^ n w := by
    rw [← coe_infinityChar_algebraMap, ← hχ w]
    rfl
  have := congrArg Units.val h_one
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_prod, map_mul, map_prod, Units.val_mul,
    Units.coe_prod, h_inf, Units.val_one, IdeleGroup.toFiniteIdele_unitEmbedding,
    unitEmbedding_eq_principalIdele] at this
  simpa [mul_comm] using this

/-- The character of type `n` obtained from a Tau Ceti character `χ` with the components of type
`n` at infinity gives back `χ`. -/
theorem _root_.New.HeckeTC.toHeckeCharacter_finiteRestriction {χ : HeckeCharacter K}
    (hχ : ∀ w, χ.infiniteComponent w = infinityChar n w) :
    (HeckeTC.isHeckeOfType_finiteRestriction hχ).toHeckeCharacter = χ :=
  ext_of_ofFiniteIdele (fun a ↦ by simp) fun w ↦ by
    rw [infiniteComponent_toHeckeCharacter, hχ]

/-- With `n = 0`, the Tau Ceti character of a `ψ` of finite order has finite order. -/
theorem isFiniteOrder_toHeckeCharacter {ψ : (𝔸f K)ˣ →* ℂˣ} (H : IsHeckeOfType ψ 0)
    (hψ : IsOfFinOrder ψ) : H.toHeckeCharacter.IsFiniteOrder := by
  obtain ⟨m, hm, hψm⟩ := isOfFinOrder_iff_pow_eq_one.1 hψ
  refine (HeckeCharacter.isFiniteOrder_iff _).2 ⟨m, hm, fun c ↦ ?_⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (IdeleGroup.principalSubgroup (𝓞 K) K) c
  have h_trivial (w : InfinitePlace K) : infinityChar (0 : InfinitePlace K → ℤ) w = 1 := by
    ext z
    simp [infinityChar]
  have h_pow : ψ (IdeleGroup.toFiniteIdele (𝓞 K) K a) ^ m = 1 := by
    rw [← MonoidHom.pow_apply, hψm, MonoidHom.one_apply]
  simpa [toHeckeCharacter, h_trivial] using h_pow

end IsHeckeOfType

end New
