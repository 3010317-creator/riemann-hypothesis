module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsFundSet
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GramMatrixConjugation
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

@[expose] public section

noncomputable section

namespace SheetDecomposition.Cj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped CategoryTheory.Obj ComplexOrder

section Val

variable {X : Scheme.{0}} {G : Over X} [GrpObj G]

theorem cj_cj (z : Sp ℂ ⟶ X) : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) ≫ z = z := by
  rw [← Category.assoc, GlobalTheory.ArchMetricCompare.cj_cj, Category.id_comp]

theorem eps_sq : spMap (dualMap (starRingEnd ℂ)) ≫ spMap (algebraMap ℂ (DualNumber ℂ)) =
    spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap (starRingEnd ℂ) := by
  have h2 : CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) ≫ CommRingCat.ofHom (dualMap (starRingEnd ℂ)) =
      CommRingCat.ofHom (starRingEnd ℂ) ≫ CommRingCat.ofHom (algebraMap ℂ (DualNumber ℂ)) :=
    CommRingCat.hom_ext (RingHom.ext fun a => GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.dualMap_algebraMap (starRingEnd ℂ) a)
  have h3 := congrArg Spec.map h2
  simpa only [Spec.map_comp] using h3

theorem isTangent_of_fibre {A : Over (Sp ℂ)} [GrpObj A] {z : Sp ℂ ⟶ X} {φ : A.left ⟶ G.left} (h : IsGrpPullback A G z φ)
    {v : epsAt z ⟶ G} (hv : IsTanAt G z v) {v' : epsR ℂ ⟶ A} (e : v'.left ≫ φ = v.left) : IsTangent v' := by
  refine h.1.hom_ext ?_ ?_
  · rw [Category.assoc, e]
    refine Eq.trans ?_ (GlobalTheory.PolBaseChange.eSec_comm h).symm
    refine Eq.trans hv ?_
    show (toUnit _ ≫ η[G]).left = _
    simp [eSec]
  · have z := congrArg (· ≫ A.hom) (GlobalTheory.ArchMetricCompare.isTangent_zero A)
    rw [← z, Category.assoc, Category.assoc, Over.w, Over.w]

end Val

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ} {Λ : Type} [AddCommGroup Λ]
  [Module (𝓞 E) Λ]

theorem fibreLatVec_conj {X : Scheme.{0}} (t : SAB H X) (z : Sp ℂ ⟶ X) (R R' : RiemLat E g Λ) {A₀ : Type}
    (x : A₀ → Fin g → ℂ) (v : A₀ → (epsAt z ⟶ t.G)) (hP : ∀ x, R'.P x = star (R.P x))
    (hH : R'.Hm = R.Hm.map (starRingEnd ℂ)) (hB : ∀ a x, R'.B a x = star (R.B a (star x)))
    (htan : ∀ a, IsTanAt t.G z (v a)) (hF : FibreLatVec t z R x v) :
    FibreLatVec t (spMap (starRingEnd ℂ) ≫ z) R' (fun a => star (x a)) (fun a => GlobalTheory.CompanionTheory.Ar.HodgeMetric.ConjPoint.conjVec z (v a)) := by
  obtain ⟨A, _, φ, u, χ, hpb, hAH, hact, hinj, hmem, hvec⟩ := hF
  have h := isGrpPullback_pullback A (spMap (starRingEnd ℂ))
  refine ⟨(Over.pullback (spMap (starRingEnd ℂ))).obj A, inferInstance, pullback.fst _ _ ≫ φ,
    GlobalTheory.ArchMetricCompare.cjUnif h u, fun l => star (χ ⟨star l.1, l.2⟩), h.comp hpb, ?_, fun a p => ?_, ?_,
    fun p => ?_, fun i => ?_⟩
  · rw [hH]
    exact GlobalTheory.ArchMetricCompare.cj_isAH h u hAH
  · show (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star (R'.B a p)))).left ≫ pullback.fst _ _ ≫ φ =
      (GlobalTheory.ArchMetricCompare.cjPt h (u.ex (star p))).left ≫ (pullback.fst _ _ ≫ φ) ≫ (t.act.act a).left
    rw [hB a p, star_star, GlobalTheory.ArchMetricCompare.cjPt_comp' h, Category.assoc, ← Category.assoc _ φ,
      ← Category.assoc _ (pullback.fst _ _ ≫ φ), GlobalTheory.ArchMetricCompare.cjPt_comp', hact a (star p)]
    simp only [Category.assoc]
  · intro x y e
    rw [hP, hP] at e
    exact hinj (star_injective e)
  · show star p ∈ u.Λ ↔ _
    rw [hmem]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by rw [hP, hx, star_star]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, by rw [hP, star_star]⟩
  · obtain ⟨v', e, hd⟩ := hvec i
    have sq : (spMap (dualMap (starRingEnd ℂ)) ≫ v'.left) ≫ A.hom = (epsR ℂ).hom ≫ spMap (starRingEnd ℂ) := by
      rw [Category.assoc, Over.w]
      exact eps_sq
    let t'' : epsR ℂ ⟶ (Over.pullback (spMap (starRingEnd ℂ))).obj A :=
      Over.homMk (h.1.lift _ _ sq) (h.1.lift_snd _ _ _)
    have e' : t''.left ≫ pullback.fst _ _ = spMap (dualMap (starRingEnd ℂ)) ≫ v'.left := h.1.lift_fst _ _ _
    refine ⟨t'', ?_, GlobalTheory.ArchMetricCompare.cj_isDiff h u (isTangent_of_fibre hpb (htan i) e) e' hd⟩
    rw [← Category.assoc, e', Category.assoc, e]
    rfl

theorem eqvBy_conj {R₁ R₂ R₁' R₂' : RiemLat E g Λ} (h₁ : ∀ x, R₁'.P x = star (R₁.P x))
    (h₂ : ∀ x, R₂'.P x = star (R₂.P x)) {gm : Λ ≃ₗ[𝓞 E] Λ} (h : R₁.EqvBy R₂ gm) : R₁'.EqvBy R₂' gm := by
  obtain ⟨k, hk⟩ := h
  refine ⟨{ toFun := fun x => star (k (star x))
            invFun := fun x => star (k.symm (star x))
            map_add' := fun x y => by simp
            map_smul' := fun a x => by simp
            left_inv := fun x => by simp
            right_inv := fun x => by simp }, fun x => ?_⟩
  show R₂'.P (gm x) = star (k (star (R₁'.P x)))
  rw [h₁, h₂, hk, star_star]

theorem autGrp_neg (f : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) : autGrp (E := E) (-f) = autGrp f := by
  ext gm
  show (∀ x y, (-f) (gm x) (gm y) = (-f) x y) ↔ ∀ x y, f (gm x) (gm y) = f x y
  simp

theorem star_mem_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} {q : Ψ × Fin j × Fin j' ≃ Fin n} {t : Fin n → ℂ}
    (ht : t ∈ ballDom q) : star t ∈ ballDom q := by
  intro τ
  have e : 1 - (ballMat q (star t) τ)ᴴ * ballMat q (star t) τ = (1 - (ballMat q t τ)ᴴ * ballMat q t τ)ᵀ := by
    ext a b
    simp [ballMat, Matrix.mul_apply, Matrix.one_apply, eq_comm, _root_.mul_comm]
  rw [e]
  exact (ht τ).transpose

theorem preimage_star_ballDom {Ψ : Type} [Fintype Ψ] {j j' n : ℕ} (q : Ψ × Fin j × Fin j' ≃ Fin n) :
    star ⁻¹' ballDom q = ballDom q := by
  ext t
  constructor
  · intro h
    have h' := star_mem_ballDom (q := q) (t := star t) h
    rwa [star_star] at h'
  · intro h
    exact star_mem_ballDom (q := q) (t := t) h

theorem analyticAt_star_star {n : ℕ} {f : (Fin n → ℂ) → Fin g → ℂ} {t₀ : Fin n → ℂ} (h : AnalyticAt ℂ f (star t₀)) :
    AnalyticAt ℂ (fun t => star (f (star t))) t₀ := by
  have h1 : ∀ᶠ t in 𝓝 t₀, AnalyticAt ℂ f (star t) :=
    (continuous_star.continuousAt (x := t₀)).tendsto.eventually h.eventually_analyticAt
  refine GlobalTheory.SCV.analyticAt_of_differentiableOn (s := {t | AnalyticAt ℂ f (star t)}) (fun t ht => ?_) h1
  have := (show AnalyticAt ℂ f (star t) from ht).differentiableAt.star_star
  rw [star_star] at this
  exact this.differentiableWithinAt

end SheetDecomposition.Cj
