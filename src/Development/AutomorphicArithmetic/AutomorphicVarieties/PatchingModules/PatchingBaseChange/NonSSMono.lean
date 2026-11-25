module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PairedDualFirstOrderDualMatrixSpace
public import Mathlib.RingTheory.Congruence.Hom

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.nonSS_mono :
    ∀ (R R' S G G' : Type) [CommRing R] [CommRing R'] [CommRing S] [Group G] [Group G'] (p : G' →* G) (I : Set (MonoidAlgebra R G)) (I' : Set (MonoidAlgebra R' G')) (φ : R →+* S) (φ' : R' →+* S) (Q : Ideal S), Function.Surjective p → (∀ z ∈ I', MonoidAlgebra.mapDomainRingHom S p (MonoidAlgebra.mapRingHom G' φ' z) ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G φ '' I)) → NonSS I φ Q → NonSS I' φ' Q := by
  intro R R' S G G' _ _ _ _ _ p I I' φ φ' Q hp hI ⟨κ, hκ, f, hf, hn⟩
  refine ⟨κ, hκ, f, hf, fun hs => hn ?_⟩
  set J := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G (f.comp φ) '' I) with hJ
  set J' := TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G' (f.comp φ') '' I') with hJ'
  let ψ : MonoidAlgebra κ G' →+* J.ringCon.Quotient :=
    J.ringCon.mk'.comp (MonoidAlgebra.mapDomainRingHom κ p)
  have hψs : Function.Surjective ψ := by
    refine (RingCon.mk'_surjective _).comp fun x => ?_
    obtain ⟨y, hy⟩ := Finsupp.mapDomain_surjective hp x.coeff
    exact ⟨MonoidAlgebra.ofCoeff y, MonoidAlgebra.coeff_injective hy⟩
  have hle : TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G φ '' I) ≤
      J.comap (MonoidAlgebra.mapRingHom G f) := by
    rw [TwoSidedIdeal.span_le]
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, ← RingHom.comp_apply,
      ← MonoidAlgebra.mapRingHom_comp]
    exact TwoSidedIdeal.subset_span ⟨y, hy, rfl⟩
  have hle' : J' ≤ J.comap (MonoidAlgebra.mapDomainRingHom κ p) := by
    rw [hJ', TwoSidedIdeal.span_le]
    rintro _ ⟨z, hz, rfl⟩
    rw [SetLike.mem_coe, TwoSidedIdeal.mem_comap, MonoidAlgebra.mapRingHom_comp,
      RingHom.comp_apply, ← RingHom.comp_apply (MonoidAlgebra.mapDomainRingHom κ p),
      ← MonoidAlgebra.mapRingHom_comp_mapDomainRingHom, RingHom.comp_apply,
      ← TwoSidedIdeal.mem_comap]
    exact hle (hI z hz)
  have hker : J'.ringCon ≤ RingCon.ker ψ := by
    intro a b hab
    rw [RingCon.ker_apply]
    have h1 : a - b ∈ J' := (TwoSidedIdeal.rel_iff _ _ _).1 hab
    have h2 := hle' h1
    rw [TwoSidedIdeal.mem_comap, map_sub] at h2
    exact (RingCon.eq _).2 ((TwoSidedIdeal.rel_iff _ _ _).2 h2)
  refine RingHom.isSemisimpleRing_of_surjective (RingCon.lift _ ψ hker) ?_
  intro y
  obtain ⟨x, rfl⟩ := hψs y
  exact ⟨(x : J'.ringCon.Quotient), rfl⟩
