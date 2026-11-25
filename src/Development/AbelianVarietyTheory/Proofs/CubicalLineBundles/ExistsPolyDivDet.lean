module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Formalism.LocalToGlobal.CMDeterminantIdeals.StatementG
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointBaseChangeUniqueReflIff
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
public import Formalism.LocalToGlobal.ProjectiveLattices.AxHSupA
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsCyclotomicExtensionCyclotomicField28
import Formalism.LocalToGlobal.CMDeterminantIdeals.DetIdeal

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.RatFn

theorem exists_genericRing (F K : Type) [Field F] [Field K] [Algebra F K] (B : Type) [Fintype B] (m : B → ℕ) :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra F A) (π : K →ₐ[F] A) (X : ∀ b, Matrix (Fin (m b)) (Fin (m b)) A),
      _root_.IsReduced A ∧ (∀ b, IsUnit (X b).det) ∧ ∀ t : A, ∃ (P : MvPolynomial (FrVar m) K) (N : ℕ),
        ∀ (S : Type) [CommRing S] [Algebra F S] (φ : K →ₐ[F] S) (Y : ∀ b, Matrix (Fin (m b)) (Fin (m b)) S),
          (∀ b, IsUnit (Y b).det) → ∃ k : A →ₐ[F] S, k.comp π = φ ∧ (∀ b, (X b).map k = Y b) ∧
            (∏ b, (Y b).det) ^ N * k t = evalFr (MvPolynomial.map φ.toRingHom P) Y := by
  classical
  let X₀ : ∀ b, Matrix (Fin (m b)) (Fin (m b)) (MvPolynomial (FrVar m) K) :=
    fun b => Matrix.of fun i j => MvPolynomial.X ⟨b, (j, i)⟩
  let d : MvPolynomial (FrVar m) K := ∏ b, (X₀ b).det
  let A := Localization.Away d
  let jA : MvPolynomial (FrVar m) K →ₐ[F] A := IsScalarTower.toAlgHom F _ A
  have hd : IsUnit (algebraMap (MvPolynomial (FrVar m) K) A d) := IsLocalization.Away.algebraMap_isUnit d
  refine ⟨A, inferInstance, inferInstance, jA.comp (IsScalarTower.toAlgHom F K _),
    fun b => (X₀ b).map (algebraMap _ A), inferInstance, fun b => ?_, fun t => ?_⟩
  · beta_reduce
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_of_dvd_unit (map_dvd _ (Finset.dvd_prod_of_mem (fun b => (X₀ b).det) (Finset.mem_univ b))) hd
  · obtain ⟨N, P, hP⟩ := IsLocalization.Away.surj d t
    refine ⟨P, N, fun S _ _ φ Y hY => ?_⟩
    let e : MvPolynomial (FrVar m) K →+* S :=
      MvPolynomial.eval₂Hom φ.toRingHom (fun v : FrVar m => Y v.1 v.2.2 v.2.1)
    have heX : ∀ b, (X₀ b).map e = Y b := fun b => by
      ext i j
      simp [e, X₀]
    have hed : e d = ∏ b, (Y b).det := by
      simp only [d, map_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [RingHom.map_det, RingHom.mapMatrix_apply, heX]
    have hu : IsUnit (e d) := by
      rw [hed]
      exact IsUnit.prod_univ_iff.2 hY
    let k₀ : A →+* S := IsLocalization.Away.lift d hu
    have hk : ∀ p, k₀ (algebraMap _ A p) = e p := fun p => IsLocalization.Away.lift_eq d hu p
    have hC : ∀ x : K, e (algebraMap K _ x) = φ x := fun x => by simp [e]
    let k : A →ₐ[F] S :=
      { k₀ with
        commutes' := fun r => by
          change k₀ (algebraMap F A r) = _
          rw [IsScalarTower.algebraMap_apply F (MvPolynomial (FrVar m) K) A, hk,
            IsScalarTower.algebraMap_apply F K (MvPolynomial (FrVar m) K), hC, φ.commutes] }
    refine ⟨k, ?_, fun b => ?_, ?_⟩
    · ext x
      exact (hk _).trans (hC x)
    · rw [← heX b]
      ext i j
      exact hk _
    · have h := congrArg k₀ hP
      rw [map_mul, map_pow, hk, hk, hed] at h
      change _ * k₀ t = _
      rw [mul_comm, h, evalFr, MvPolynomial.eval_map]
      rfl

end GlobalTheory.LamT.RatFn
