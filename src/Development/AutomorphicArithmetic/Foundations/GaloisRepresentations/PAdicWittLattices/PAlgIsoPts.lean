module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
import Mathlib.Tactic.Linter.Style

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pAlgIsoPts :
    IsoPts → AlgIsoPts := by
  intro hI D E _ _ _ _ hpts
  let φ : CommRingCat.of D ⟶ CommRingCat.of E := CommRingCat.ofHom (algebraMap D E)
  have : Etale (Spec.map φ) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)
  have hiso : IsIso (Spec.map φ) := by
    refine hI (Spec.map φ) ?_
    intro Ω _ _ z
    obtain ⟨y, hy, hyu⟩ := hpts Ω (Spec.preimage z).hom
    refine ⟨Spec.map (CommRingCat.ofHom y), ?_, ?_⟩
    · show Spec.map (CommRingCat.ofHom y) ≫ Spec.map φ = z
      rw [← Spec.map_comp]
      conv_rhs => rw [← Spec.map_preimage z]
      congr 1
      ext d
      exact congrArg (fun f : D →+* Ω => f d) hy
    · intro w hw
      rw [← Spec.map_preimage w]
      congr 1
      ext e
      have hx : (Spec.preimage w).hom.comp (algebraMap D E) = (Spec.preimage z).hom := by
        have h2 : Spec.map (φ ≫ Spec.preimage w) = Spec.map (Spec.preimage z) := by
          rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage]
          exact hw
        have h3 := Spec.map_injective h2
        ext d
        exact congrArg (fun f => (CommRingCat.Hom.hom f) d) h3
      exact congrArg (fun f : E →+* Ω => f e) (hyu _ hx)
  have : IsIso (Scheme.Spec.map φ.op) := hiso
  have : IsIso φ.op := isIso_of_fully_faithful Scheme.Spec φ.op
  have : IsIso φ := isIso_of_op φ
  exact ConcreteCategory.bijective_of_isIso φ
