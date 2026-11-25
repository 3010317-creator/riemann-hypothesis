module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EtaleLocalizationAtPrimeTensorOfLowHeight
import Mathlib.Tactic.Linter.Style

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem lat_restrict_comap_span {Ω R E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [Semiring R] [SMul R Ω]
    [Module R E] [IsScalarTower R Ω E] (V : Submodule Ω E) {r : ℕ} (b : Fin r → V) :
    (Submodule.span R (Set.range fun i => (b i : E))).comap (V.subtype.restrictScalars R) =
      Submodule.span R (Set.range b) := by
  have h : (Set.range fun i => (b i : E)) = (V.subtype.restrictScalars R) '' Set.range b := by
    rw [← Set.range_comp]; rfl
  rw [h, ← Submodule.map_span, Submodule.comap_map_eq_of_injective]
  exact Subtype.val_injective

theorem Lat.restrict_isVBOn : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type)
    [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (V : Submodule Ω E),
    L.IsVBOn T r V → (L.comap V.subtype).IsVBOn T r ⊤ ∧
      ∀ p ∈ T, ((L.comap V.subtype).map V.subtype) p = L p := by
  intro X Ω _ ξ E _ _ L T r V h
  refine ⟨?_, ?_⟩
  · intro p hp
    obtain ⟨U, hpU, b, hb, hq⟩ := h p hp
    have hbV : ∀ i, b i ∈ V := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
    let b' : Fin r → V := fun i => ⟨b i, hbV i⟩
    have hval : (fun i => (b' i : E)) = b := rfl
    refine ⟨U, hpU, b', ?_, ?_⟩
    · apply Submodule.map_injective_of_injective (f := V.subtype) Subtype.val_injective
      have h1 : (Set.range b) = V.subtype '' Set.range b' := by
        rw [← Set.range_comp]; rfl
      rw [Submodule.map_span, ← h1, hb, Submodule.map_top, Submodule.range_subtype]
    · intro q hqT hqU
      obtain ⟨hli, hsp⟩ := hq q hqT hqU
      refine ⟨?_, ?_⟩
      · exact LinearIndependent.of_comp V.subtype hli
      · show (L q).comap (V.subtype.restrictScalars (regAt ξ q)) = _
        rw [hsp, ← hval]
        exact lat_restrict_comap_span V b'
  · intro p hp
    obtain ⟨U, hpU, b, hb, hq⟩ := h p hp
    obtain ⟨_, hsp⟩ := hq p hp hpU
    change Submodule.map (V.subtype.restrictScalars (regAt ξ p)) (Submodule.comap _ (L p)) = L p
    refine Submodule.map_comap_eq_self (hsp ▸ Submodule.span_le.2 ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨b i, hb ▸ Submodule.subset_span ⟨i, rfl⟩⟩, rfl⟩

end GlobalTheory.CompanionTheory.Ar
