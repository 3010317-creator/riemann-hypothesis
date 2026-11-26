import Lib.ClassField.HeckeCharacter.TauCeti.Basic
import Lib.ClassField.HeckeCharacter.AlgebraicValues

/-!
# Our unitary Hecke characters on `New.𝔸` as Tau Ceti Hecke characters

`New.HeckeChar E` is the group of continuous circle-valued characters of the units of our adele
ring `New.𝔸 E = (InfinitePlace E → ℂ) × 𝔸f E` trivial on `Eˣ`, embedded by `New.toAdele` through the
embeddings `Φ w` of the CM type. This file reads Mathlib's adeles in `New.𝔸 E` through the same
embeddings (`New.HeckeTC.toOwnAdele`), which gives the Tau Ceti Hecke character of each element of
`New.HeckeChar E`.

## Main definitions and results

* `New.HeckeTC.toOwnAdele`: the map from Mathlib's `AdeleRing (𝓞 E) E` to `New.𝔸 E`, by
  `New.HeckeTC.completionEmbedding w (Φ w)` at each infinite place `w`; it extends `New.toAdele`
  (`New.HeckeTC.toOwnAdele_algebraMap`).
* `New.HeckeChar.toHeckeCharacter`: the Tau Ceti Hecke character of `χ : New.HeckeChar E`; its
  finite part is `χ.finPart` (`New.HeckeChar.finiteRestriction_toHeckeCharacter`) and its values at
  the local uniformisers are `χ.atUniformizer` (`New.HeckeChar.atUniformizer_eq_finiteComponent`).
* `New.HeckeChar.toHeckeCharacter_isHeckeOfType_finPart`: for `χ` of type `n` at infinity, it is the
  Tau Ceti character of the finite part `χ.finPart` of type `n`;
  `New.AutChar.HasWeight.toHeckeCharacter_isHeckeOfType` is the case of a base change
  `x ↦ ν (x / x̄)`.
-/

noncomputable section

open NumberField IsDedekindDomain TauCeti TauCeti.GlobalNumberFields New.HeckeTC

namespace New

namespace HeckeTC

variable {E : Type*} [Field E] [NumberField E] [PlaceEmbedding E]

/-- Mathlib's adeles read in `New.𝔸 E`: the component at an infinite place `w` is sent to `ℂ` by the
extension of the chosen embedding `Φ w`, the finite adeles are unchanged. -/
def toOwnAdele : AdeleRing (𝓞 E) E →+* 𝔸 E :=
  RingHom.prodMap
    (RingHom.pi fun w ↦ (completionEmbedding w (Φ w)).comp
      (Pi.evalRingHom (fun v : InfinitePlace E ↦ v.Completion) w))
    (RingHom.id (FiniteAdeleRing (𝓞 E) E))

lemma continuous_toOwnAdele : Continuous (toOwnAdele (E := E)) :=
  (continuous_pi fun w ↦ (continuous_completionEmbedding w (Φ w)).comp
    ((continuous_apply w).comp continuous_fst)).prodMk continuous_snd

/-- On `E`, `New.HeckeTC.toOwnAdele` is our diagonal embedding `New.toAdele`. -/
lemma toOwnAdele_algebraMap (x : E) : toOwnAdele (algebraMap E (AdeleRing (𝓞 E) E) x) = toAdele x :=
  Prod.ext (funext fun w ↦ completionEmbedding_algebraMap (mk_Φ w) x) rfl

/-- A finite idele with components `1` at the infinite places is read as the same finite idele. -/
lemma toOwnAdele_ofFiniteIdele (a : (𝔸f E)ˣ) :
    Units.map toOwnAdele.toMonoidHom (IdeleGroup.ofFiniteIdele (𝓞 E) E a) = finIdeleIncl a :=
  Units.ext (Prod.ext (funext fun w ↦ map_one (completionEmbedding w (Φ w))) rfl)

end HeckeTC

namespace HeckeChar

variable {E : Type*} [Field E] [CMType E] (χ : HeckeChar E)

/-- The character `a ↦ χ(a)` of Mathlib's ideles, with `a` read in `New.𝔸 E` through the embeddings
`Φ w`. -/
def idelesChar : IdeleGroup (𝓞 E) E →* ℂˣ :=
  (Circle.toUnits.comp χ.val.toMonoidHom).comp (Units.map toOwnAdele.toMonoidHom)

lemma principalSubgroup_le_ker_idelesChar :
    IdeleGroup.principalSubgroup (𝓞 E) E ≤ χ.idelesChar.ker := by
  rintro _ ⟨x, rfl⟩
  have h_one : χ.val (Units.map toOwnAdele.toMonoidHom (IdeleGroup.unitEmbedding (𝓞 E) E x)) = 1 :=
    χ.property _ ⟨x.val, (toOwnAdele_algebraMap x.val).symm⟩
  change Circle.toUnits (χ.val _) = 1
  rw [h_one, map_one]

/-- The Tau Ceti Hecke character of a unitary Hecke character `χ` on `New.𝔸 E`: the character
`a ↦ χ(a)` of the idele class group, with `a` read in `New.𝔸 E` through the embeddings `Φ w`. -/
def toHeckeCharacter : HeckeCharacter E where
  toMonoidHom := QuotientGroup.lift _ χ.idelesChar χ.principalSubgroup_le_ker_idelesChar
  continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 <|
    Units.isEmbedding_val₀.continuous_iff.2 <| continuous_subtypeVal.comp <|
      χ.val.continuous.comp (Continuous.units_map _ continuous_toOwnAdele)

@[simp] lemma toHeckeCharacter_mk (a : IdeleGroup (𝓞 E) E) :
    χ.toHeckeCharacter (a : IdeleClassGroup (𝓞 E) E) =
      Circle.toUnits (χ.val (Units.map toOwnAdele.toMonoidHom a)) :=
  rfl

/-- The finite part of the Tau Ceti character of `χ` is `χ.finPart`. -/
@[simp] lemma finiteRestriction_toHeckeCharacter :
    finiteRestriction χ.toHeckeCharacter = χ.finPart := by
  ext a
  change (Circle.toUnits (χ.val (Units.map toOwnAdele.toMonoidHom
    (IdeleGroup.ofFiniteIdele (𝓞 E) E a))) : ℂ) = (Circle.toUnits (χ.val (finIdeleIncl a)) : ℂ)
  rw [toOwnAdele_ofFiniteIdele]

/-- The value `χ.atUniformizer w` at the local idele of the chosen uniformiser is the value of the
local component at `w` of the Tau Ceti character of `χ`. -/
lemma atUniformizer_eq_finiteComponent (w : FinPlace E) :
    χ.atUniformizer w = (χ.toHeckeCharacter.finiteComponent w (uniformizer w) : ℂ) := by
  rw [finiteComponent_eq_finiteRestriction, finiteRestriction_toHeckeCharacter]
  rfl

/-- If `χ` is `z ↦ ∏ w, (z w / ‖z w‖) ^ n w` at infinity, its Tau Ceti character is that of its
finite part, of type `n` by `New.HeckeChar.isHeckeOfType_finPart`. -/
theorem toHeckeCharacter_isHeckeOfType_finPart {E : Type} [Field E] [CMType E] (χ : HeckeChar E)
    {n : InfinitePlace E → ℤ}
    (h_inf : ∀ z : (InfinitePlace E → ℂ)ˣ,
      χ.val (Units.map (MonoidHom.inl (InfinitePlace E → ℂ) (𝔸f E)) z) =
        ∏ w : InfinitePlace E, (z.val w / ‖z.val w‖) ^ n w) :
    (χ.isHeckeOfType_finPart h_inf).toHeckeCharacter = χ.toHeckeCharacter := by
  refine ext_of_ofFiniteIdele (fun a ↦ ?_) fun w ↦ ?_
  · rw [← finiteRestriction_apply, ← finiteRestriction_apply,
      IsHeckeOfType.finiteRestriction_toHeckeCharacter, finiteRestriction_toHeckeCharacter]
  · rw [IsHeckeOfType.infiniteComponent_toHeckeCharacter]
    ext z
    -- The idele concentrated at `w` is read in `New.𝔸 E` as the unit `y` of `InfinitePlace E → ℂ`
    -- with `Φ_w(z)` at `w` and `1` elsewhere, with finite part `1`.
    let f : w.Completion →* (InfinitePlace E → ℂ) :=
      (MonoidHom.fst _ _).comp (toOwnAdele.toMonoidHom.comp (AdeleRing.ofCompletion (𝓞 E) E w))
    have h_map : Units.map toOwnAdele.toMonoidHom (IdeleGroup.ofCompletion (𝓞 E) E w z) =
        Units.map (MonoidHom.inl (InfinitePlace E → ℂ) (𝔸f E)) (Units.map f z) :=
      Units.ext (Prod.ext rfl rfl)
    have h_f (v : InfinitePlace E) :
        f z v = if v = w then completionEmbedding w (Φ w) z else 1 := by
      classical
      change completionEmbedding v (Φ v) (Pi.mulSingle w (z : w.Completion) v) = _
      by_cases hv : v = w
      · subst hv
        rw [Pi.mulSingle_eq_same, ite_eq_left rfl]
      · rw [Pi.mulSingle_eq_of_ne hv, map_one, ite_eq_right hv]
    have h_val : (χ.toHeckeCharacter.infiniteComponent w z : ℂ) =
        (completionEmbedding w (Φ w) z / ‖completionEmbedding w (Φ w) z‖) ^ n w := by
      rw [HeckeCharacter.infiniteComponent_apply, IdeleClassGroup.ofCompletion,
        MonoidHom.comp_apply, QuotientGroup.mk'_apply, toHeckeCharacter_mk, h_map]
      simp only [Circle.toUnits_apply, Units.val_mk0, h_inf, Units.coe_map]
      rw [Finset.prod_eq_single w (fun v _ hv ↦ by simp [h_f, hv]) (by simp), h_f, ite_eq_left rfl]
    rw [h_val, IsHeckeOfType.coe_infinityChar_apply]

end HeckeChar

/-- For a character `ν` of `U(1)(𝔸)` of weight `e`, the Tau Ceti character of the finite part of its
base change `x ↦ ν (x / x̄)`, of type `2 e`, is the Tau Ceti character of the base change. -/
theorem AutChar.HasWeight.toHeckeCharacter_isHeckeOfType {E : Type} [Field E] [CMType E]
    {e : InfinitePlace E → ℤ} {ν : AutChar E} {ψ : (w : FinPlace E) → MulChar (ResField w) ℂ}
    [h : ν.HasWeight e ψ] :
    (AutChar.HasWeight.isHeckeOfType (h := h)).toHeckeCharacter =
      ν.baseChange.toHeckeCharacter :=
  ν.baseChange.toHeckeCharacter_isHeckeOfType_finPart h.baseChange_apply_inf

end New
