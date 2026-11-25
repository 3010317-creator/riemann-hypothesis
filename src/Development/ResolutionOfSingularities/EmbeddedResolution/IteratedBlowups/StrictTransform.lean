module

public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Mathlib.AlgebraicGeometry.Noetherian
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.OpenImmersionAppLE
public import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.ReducedSubscheme
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
public import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
public import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Mathlib.Tactic.Linter.Style

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def strictTransformOpens {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    ((D.comap π).subscheme).Opens :=
  (D.comap π).subschemeι ⁻¹ᵁ (Z.comap π).support.compl

theorem coe_strictTransformOpens {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    ((strictTransformOpens π Z D : ((D.comap π).subscheme).Opens) :
        Set ((D.comap π).subscheme)) =
      ⇑(D.comap π).subschemeι.base ⁻¹' ((Z.comap π).support.compl : Set X₁) := rfl

def strictTransformι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    (strictTransformOpens π Z D).toScheme ⟶ X₁ :=
  Scheme.Opens.ι (strictTransformOpens π Z D) ≫ (D.comap π).subschemeι

theorem strictTransformι_eq_ι_comp_subschemeι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    strictTransformι π Z D =
      Scheme.Opens.ι (strictTransformOpens π Z D) ≫ (D.comap π).subschemeι := rfl

theorem strictTransform_eq_ker_strictTransformι {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    Blowup.strictTransform π Z D = (strictTransformι π Z D).ker := rfl

theorem ker_eq_ker_of_isIso_comp {A B T : Scheme.{u}} (f : A ⟶ T) (g : B ⟶ T) (e : A ⟶ B)
    [IsIso e] (h : e ≫ g = f) : f.ker = g.ker := by
  subst h; exact Scheme.Hom.ker_comp_of_isIso e g

theorem ker_comap_ι_eq_ker_morphismRestrict {W T : Scheme.{u}} (m : W ⟶ T) [QuasiCompact m]
    (V : T.Opens) :
    (Scheme.Hom.ker m).comap (Scheme.Opens.ι V) = Scheme.Hom.ker (m ∣_ V) := by
  refine Scheme.IdealSheafData.ext (funext fun P => ?_)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion m (m ∣_ V) _ _ (isPullback_morphismRestrict m V)]

theorem ker_comap_ι_eq_ker_of_isIso_comp {W T S : Scheme.{u}} (m : W ⟶ T) [QuasiCompact m]
    (V : T.Opens) (n : S ⟶ V.toScheme) (e : S ⟶ (m ⁻¹ᵁ V).toScheme) [IsIso e]
    (h : e ≫ (m ∣_ V) = n) :
    (Scheme.Hom.ker m).comap (Scheme.Opens.ι V) = Scheme.Hom.ker n := by
  rw [ker_comap_ι_eq_ker_morphismRestrict m V, ker_eq_ker_of_isIso_comp n (m ∣_ V) e h]

theorem support_strictTransform_eq_closure_preimage {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z D)] :
    ((Blowup.strictTransform π Z D).support : Set X₁) =
      closure (⇑π.base ⁻¹' ((D.support : Set X) \ (Z.support : Set X))) := by
  have h1 : (((Z.comap π).support.compl : X₁.Opens) : Set X₁) =
      (⇑π.base ⁻¹' (Z.support : Set X))ᶜ := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have h2 : (((D.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (D.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  rw [strictTransform_eq_ker_strictTransformι, Scheme.Hom.support_ker]
  congr 1
  rw [strictTransformι_eq_ι_comp_subschemeι, _root_.AlgebraicGeometry.Scheme.Hom.range_comp_base, Scheme.Opens.range_ι,
    coe_strictTransformOpens, Set.image_preimage_eq_inter_range,
    Scheme.IdealSheafData.range_subschemeι, h1, h2]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage, Set.mem_sdiff]
  tauto

theorem support_strictTransform_eq_closure_sdiff {X X₁ : Scheme.{u}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData)
    [QuasiCompact (strictTransformι π Z D)] :
    ((Blowup.strictTransform π Z D).support : Set X₁) =
      closure (((D.comap π).support : Set X₁) \ ((Z.comap π).support : Set X₁)) := by
  have h1 : (((Z.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (Z.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have h2 : (((D.comap π).support : Closeds X₁) : Set X₁) =
      ⇑π.base ⁻¹' (D.support : Set X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  rw [support_strictTransform_eq_closure_preimage π Z D, h1, h2, Set.preimage_sdiff]

alias comap_le_strictTransform := _root_.FunctorialResolution.Blowup.comap_le_strictTransform

theorem strictTransform_top {X' X : Scheme.{u}} (f : X' ⟶ X) (Z : X.IdealSheafData) :
    Blowup.strictTransform f Z (⊤ : X.IdealSheafData) = ⊤ := by
  have h := comap_le_strictTransform f Z ⊤
  rw [Scheme.IdealSheafData.comap_top] at h
  exact le_antisymm le_top h

theorem comap_ker_subschemeι_comp {A B : Scheme.{u}} (K : A.IdealSheafData) (f : A ⟶ B)
    [IsOpenImmersion f] [QuasiCompact K.subschemeι] [QuasiCompact (K.subschemeι ≫ f)] :
    (K.subschemeι ≫ f).ker.comap f = K := by
  rw [Blowup.comap_ker_comp_of_isOpenImmersion, Scheme.IdealSheafData.ker_subschemeι]

private theorem ker_morphismRestrict_subschemeι {T : Scheme.{u}} (K : T.IdealSheafData) (V : T.Opens) :
    (K.subschemeι ∣_ V).ker = K.comap (Scheme.Opens.ι V) := by
  have h := isPullback_morphismRestrict K.subschemeι V
  have hfac : h.isoPullback.hom ≫ Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι
      = K.subschemeι ∣_ V := h.isoPullback_hom_fst
  show (K.subschemeι ∣_ V).ker = (Limits.pullback.fst (Scheme.Opens.ι V) K.subschemeι).ker
  rw [← hfac, Scheme.Hom.ker_comp_of_isIso]

private theorem exists_isIso_subschemeι_preimage_comap {T : Scheme.{u}} (K : T.IdealSheafData) (V : T.Opens) :
    ∃ e : (K.subschemeι ⁻¹ᵁ V).toScheme ⟶ (K.comap (Scheme.Opens.ι V)).subscheme,
      IsIso e ∧ e ≫ (K.comap (Scheme.Opens.ι V)).subschemeι = K.subschemeι ∣_ V := by
  have hk : (K.subschemeι ∣_ V).ker = (K.comap (Scheme.Opens.ι V)).subschemeι.ker := by
    rw [ker_morphismRestrict_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
  refine ⟨IsClosedImmersion.lift (K.comap (Scheme.Opens.ι V)).subschemeι
      (K.subschemeι ∣_ V) (le_of_eq hk.symm), ?_, IsClosedImmersion.lift_fac _ _ _⟩
  exact IsClosedImmersion.isIso_of_ker_eq (K.subschemeι ∣_ V)
    (K.comap (Scheme.Opens.ι V)).subschemeι _ (IsClosedImmersion.lift_fac _ _ _) hk

theorem ker_ι_preimage_comp_subschemeι_eq_ker_comap {T : Scheme.{u}} (K : T.IdealSheafData) (V : T.Opens) :
    (Scheme.Opens.ι (K.subschemeι ⁻¹ᵁ V) ≫ K.subschemeι).ker =
      ((K.comap (Scheme.Opens.ι V)).subschemeι ≫ Scheme.Opens.ι V).ker := by
  obtain ⟨e, he, hfac⟩ := exists_isIso_subschemeι_preimage_comap K V
  have := he
  rw [← morphismRestrict_ι K.subschemeι V, ← hfac, Category.assoc]
  exact Scheme.Hom.ker_comp_of_isIso e _

theorem isReduced_subscheme_strictTransform {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) (h : Blowup.IsBlowupAlongIdealSheaf π Z) [IsReduced D.subscheme]
    [QuasiCompact (strictTransformι π Z D)] :
    IsReduced (Blowup.strictTransform π Z D).subscheme := by
  have h1 := h.restrict Z.support.compl
  rw [Blowup.comap_ι_support_compl_eq_top Z] at h1
  have : IsIso (π ∣_ Z.support.compl) := h1.isIso_of_top
  have hsupp : (Z.comap π).support.compl = π ⁻¹ᵁ Z.support.compl := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hcc : (D.comap π).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))
      = (D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  obtain ⟨e₁, he₁, -⟩ := exists_isIso_subschemeι_preimage_comap (D.comap π) (π ⁻¹ᵁ Z.support.compl)
  obtain ⟨e₂, he₂, -⟩ :=
    Scheme.IdealSheafData.exists_iso_subscheme_comap_of_isIso (π ∣_ Z.support.compl)
      (D.comap (Scheme.Opens.ι Z.support.compl))
  obtain ⟨e₃, he₃, -⟩ := exists_isIso_subschemeι_preimage_comap D Z.support.compl
  have := he₁
  have := he₂
  have := he₃
  have : IsReduced (D.subschemeι ⁻¹ᵁ Z.support.compl).toScheme :=
    isReduced_of_isOpenImmersion (Scheme.Opens.ι (D.subschemeι ⁻¹ᵁ Z.support.compl))
  have : IsReduced (D.comap (Scheme.Opens.ι Z.support.compl)).subscheme :=
    isReduced_of_isOpenImmersion (inv e₃)
  have : IsReduced
      ((D.comap (Scheme.Opens.ι Z.support.compl)).comap (π ∣_ Z.support.compl)).subscheme :=
    isReduced_of_isOpenImmersion e₂
  have : IsReduced ((D.comap π).comap (Scheme.Opens.ι (π ⁻¹ᵁ Z.support.compl))).subscheme := by
    rw [hcc]; infer_instance
  have : IsReduced (strictTransformOpens π Z D).toScheme := by
    have hrw : strictTransformOpens π Z D
        = (D.comap π).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl) := by
      show (D.comap π).subschemeι ⁻¹ᵁ (Z.comap π).support.compl
          = (D.comap π).subschemeι ⁻¹ᵁ (π ⁻¹ᵁ Z.support.compl)
      rw [hsupp]
    rw [hrw]
    exact isReduced_of_isOpenImmersion e₁
  rw [strictTransform_eq_ker_strictTransformι]
  exact isReduced_subscheme_ker _

theorem strictTransform_eq_ker_restrict {X X₁ : Scheme.{u}} (f : X₁ ⟶ X)
    (W D₁ : X.IdealSheafData) :
    Blowup.strictTransform f W D₁ =
      (((D₁.comap (Scheme.Opens.ι W.support.compl)).comap
            (f ∣_ W.support.compl)).subschemeι ≫
          Scheme.Opens.ι (f ⁻¹ᵁ W.support.compl)).ker := by
  have hUV : (W.comap f).support.compl = f ⁻¹ᵁ W.support.compl := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  have hcomap : (D₁.comap f).comap (Scheme.Opens.ι (f ⁻¹ᵁ W.support.compl))
      = (D₁.comap (Scheme.Opens.ι W.support.compl)).comap (f ∣_ W.support.compl) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      morphismRestrict_ι]
  rw [strictTransform_eq_ker_strictTransformι, strictTransformι_eq_ι_comp_subschemeι]
  show (Scheme.Opens.ι ((D₁.comap f).subschemeι ⁻¹ᵁ (W.comap f).support.compl) ≫
      (D₁.comap f).subschemeι).ker = _
  rw [hUV, ker_ι_preimage_comp_subschemeι_eq_ker_comap, hcomap]

theorem strictTransform_congr_of_comap_ι_eq {X X₁ : Scheme.{u}} (f : X₁ ⟶ X)
    (W D₁ D₂ : X.IdealSheafData)
    (h : D₁.comap (Scheme.Opens.ι W.support.compl) =
      D₂.comap (Scheme.Opens.ι W.support.compl)) :
    Blowup.strictTransform f W D₁ = Blowup.strictTransform f W D₂ := by
  rw [strictTransform_eq_ker_restrict f W D₁, strictTransform_eq_ker_restrict f W D₂, h]

theorem isBlowupAlongIdealSheaf_of_isIso_comp {X A B : Scheme.{u}} (f : A ⟶ X) (g : B ⟶ X) (e : A ⟶ B)
    [IsIso e] (hfac : e ≫ g = f) (I : X.IdealSheafData) (hg : Blowup.IsBlowupAlongIdealSheaf g I) :
    Blowup.IsBlowupAlongIdealSheaf f I := by
  obtain ⟨hcart, huniv⟩ := hg
  have h1 : I.comap f = (I.comap g).comap e := by
    rw [← Scheme.IdealSheafData.comap_comp, hfac]
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact hcart.comap_of_isOpenImmersion e
  · intro Y q hq
    obtain ⟨t, ht, huniq⟩ := huniv Y q hq
    have ht' : t ≫ g = q := ht
    refine ⟨t ≫ inv e, ?_, ?_⟩
    · show (t ≫ inv e) ≫ f = q
      rw [← hfac, Category.assoc, IsIso.inv_hom_id_assoc]
      exact ht'
    · intro y hy
      have hy' : y ≫ f = q := hy
      have hye : y ≫ e = t := by
        refine huniq _ ?_
        show (y ≫ e) ≫ g = q
        rw [Category.assoc, hfac]
        exact hy'
      rw [← hye, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

theorem quasiCompact_strictTransformι_of_isLocallyNoetherian {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [IsLocallyNoetherian X₁] :
    QuasiCompact (strictTransformι π Z D) := by
  have : IsLocallyNoetherian (D.comap π).subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (D.comap π).subschemeι
  rw [strictTransformι_eq_ι_comp_subschemeι]
  infer_instance

instance instQuasiCompactStrictTransformMorphism {X X₁ : Scheme.{u}} (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) [IsLocallyNoetherian X₁] :
    QuasiCompact (strictTransformι π Z D) :=
  quasiCompact_strictTransformι_of_isLocallyNoetherian π Z D

end FunctorialResolution.EmbeddedResolution
