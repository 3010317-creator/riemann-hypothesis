module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfSchroedingerTranslatesThetaSumZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicSchwartzNeZeroAtOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCompactSupportFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasRationalWeilOperatorLeviBlockStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenLatticePointAtPlaceLocalIdentity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergEigenProportionalLocalField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergLatticeSelfDualEveryFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowerUnipotentHasRationalWeilOperatorQuadraticChStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProduStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeInvariantVectorStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLocalImageLatticeSupportedAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedLeviLowerUnipotentWeylStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorLatticeLocalDarbouxCoordsBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenvalueThetaIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourierStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

noncomputable section

namespace GlobalTheory.RatWeilOp

open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F : Type} [Field F] [NumberField F]

theorem hasOp_of_symplectic (hF : IsTotallyReal F) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {κ : Type} [Fintype κ] [DecidableEq κ]
    (a : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (ha : aᵀ * Matrix.fromBlocks 0 1 (-1) 0 * a = Matrix.fromBlocks 0 1 (-1) 0) : HasOp ψ a :=
  GlobalTheory.T.symplecticGroup_generated_levi_lowerUnipotent_weyl F κ (HasOp ψ) (fun _ _ => HasOp.mul) (GlobalTheory.T.hasRationalWeilOperator_leviBlock F ψ κ) (GlobalTheory.T.lowerUnipotent_hasRationalWeilOperator_quadraticChar F ψ hψ κ) (GlobalTheory.T.weylElement_hasRationalWeilOperator_adelicFourier F hF ψ hψ κ) a ha

section Pure

variable {κ : Type} [Fintype κ]

theorem pure_mem (f : SInf F κ) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ schA F κ :=
  Submodule.subset_span ⟨f, fun y => ∏ᶠ v, φ v fun i => evalV F v (y i),
    ⟨GlobalTheory.WeilM.isLocallyConstant_finprod_evalV φ hφ.1 hφ.2, GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ hφ.1 hφ.2⟩, rfl⟩

theorem schA_le {N : Submodule ℂ ((κ → AF F) → ℂ)} (h : ∀ f φ, IsFam φ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ N) : schA F κ ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  replace hg := GlobalTheory.T.schwartzBruhat_finiteAdeles_mem_span_restrictedProducts F _ g hg
  induction hg using Submodule.span_induction with
  | zero => rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; exact N.zero_mem
  | add a b _ _ ha hb =>
    rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; exact N.add_mem ha hb
  | smul c a _ ha =>
    rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; exact N.smul_mem c ha
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    exact h f φ ⟨hφ, hs⟩

theorem IsFam.finite {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) (x : κ → AF F) :
    (Function.mulSupport fun v => φ v fun i => evFin F v (x i)).Finite := by
  have h : ∀ᶠ v in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F := eventually_all.2 fun i => (x i).2.2
  refine (eventually_cofinite.1 ?_)
  filter_upwards [h, hφ.2] with v h1 h2
  rw [h2, ind, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h1)]
  rfl

theorem pure_smul (f : SInf F κ) {φ : ∀ v : Pl F, (κ → Fv F v) → ℂ} (hφ : IsFam φ) (m : Pl F → ℂ) (h0 : ∀ v, m v ≠ 0)
    (h1 : ∀ᶠ v in cofinite, m v = 1) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((∏ᶠ v, m v) • f) (fun v => (m v)⁻¹ • φ v) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  have hm : (Function.mulSupport m).Finite := eventually_cofinite.1 h1
  have hm' : (Function.mulSupport fun v => (m v)⁻¹).Finite := hm.subset fun v hv h => hv (by simp only [h, inv_one])
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul, SchwartzMap.smul_apply]
  rw [finprod_mul_distrib hm' (hφ.finite x)]
  have : (∏ᶠ v, m v) * ∏ᶠ v, (m v)⁻¹ = 1 := by
    rw [← finprod_mul_distrib hm hm']
    exact finprod_eq_one_of_forall_eq_one fun v => mul_inv_cancel₀ (h0 v)
  linear_combination (f (fun i => evI F (x i)) * ∏ᶠ v, φ v fun i => evFin F v (x i)) * this

def schrL {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (w : (κ → R) × (κ → R)) :
    ((κ → R) → ℂ) →ₗ[ℂ] (κ → R) → ℂ where
  toFun := schr ψ w
  map_add' φ φ' := funext fun x => by simp only [schr, Pi.add_apply]; ring
  map_smul' a φ := funext fun x => by simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

variable {ψ : AddChar (AF F) ℂ} {a : Matrix (κ ⊕ κ) (κ ⊕ κ) F} {e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ} {c : ℂ}
  {ei : SInf F κ →L[ℂ] SInf F κ} {ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ}

theorem IsOp.maps (h : IsOp ψ a e c ei ev) : ∀ Φ ∈ schA F κ, e Φ ∈ schA F κ := fun _ hΦ =>
  schA_le (N := (schA F κ).comap e) (fun f φ hφ => by
    rw [Submodule.mem_comap, (h.2.2.2.2.2 f φ hφ).1]
    exact pure_mem _ (h.isFam hφ)) hΦ

theorem IsOp.Heisenberg₂ (h : IsOp ψ a e c ei ev) (w : (κ → AF F) × (κ → AF F)) :
    ∀ Φ ∈ schA F κ, e (schr ψ w Φ) = schr ψ (act (a.map (algebraMap F (AF F))) w) (e Φ) := fun _ hΦ =>
  schA_le (N := LinearMap.eqLocus (e ∘ₗ schrL ψ w) (schrL ψ (act (a.map (algebraMap F (AF F))) w) ∘ₗ e))
    (fun f φ hφ => (h.2.2.2.2.2 f φ hφ).2.1 w) hΦ

theorem IsOp.theta (h : IsOp ψ a e c ei ev) : ∀ Φ ∈ schA F κ, thetaSum F (e Φ) = c * thetaSum F Φ := fun _ hΦ =>
  (schA_le (N := {
      carrier := {Φ | Φ ∈ schA F κ ∧ thetaSum F (e Φ) = c * thetaSum F Φ}
      zero_mem' := ⟨zero_mem _, by simp [thetaSum]⟩
      add_mem' := fun {x y} hx hy => ⟨add_mem hx.1 hy.1, by
        rw [map_add (f := _), thetaSum_add F (h.maps _ hx.1) (h.maps _ hy.1), thetaSum_add F hx.1 hy.1, hx.2, hy.2, mul_add]⟩
      smul_mem' := fun r x hx => ⟨Submodule.smul_mem _ r hx.1, by
        rw [map_smul, thetaSum_smul, thetaSum_smul, hx.2, mul_left_comm]⟩ })
    (fun f φ hφ => ⟨pure_mem f hφ, (h.2.2.2.2.2 f φ hφ).2.2⟩) hΦ).2

theorem IsOp.bijOn (hψ : IsStd ψ) (h : IsOp ψ a e c ei ev) : Set.BijOn e (schA F κ : Set _) (schA F κ : Set _) := by
  classical
  refine ⟨h.maps, fun Φ hΦ Φ' hΦ' he => ?_, ?_⟩
  · have hd : Φ - Φ' ∈ schA F κ := sub_mem hΦ hΦ'
    refine sub_eq_zero.1 (GlobalTheory.T.eq_zero_of_schroedingerTranslates_thetaSum_zero F ψ hψ κ _ hd fun w => ?_)
    have h1 := h.theta _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ w _ hd)
    rw [h.Heisenberg₂ w _ hd, map_sub, he, sub_self, show schr ψ _ (0 : (κ → AF F) → ℂ) = 0 from (schrL ψ _).map_zero] at h1
    exact (mul_eq_zero.1 (h1.symm.trans (by simp [thetaSum]))).resolve_left h.1
  · refine schA_le (N := (schA F κ).map e) fun g φ' hφ' => ?_
    obtain ⟨f, rfl⟩ := h.2.1 g
    have key : ∀ v, ∃ p ∈ SB (κ → Fv F v), ev v p = φ' v ∧ (φ' v = ind κ v → ev v (ind κ v) = ind κ v → p = ind κ v) := by
      intro v
      by_cases hv : φ' v = ind κ v ∧ ev v (ind κ v) = ind κ v
      · exact ⟨ind κ v, hv.1 ▸ hφ'.1 v, hv.2.trans hv.1.symm, fun _ _ => rfl⟩
      · obtain ⟨p, hp, hp'⟩ := (h.2.2.1 v).surjOn (hφ'.1 v)
        exact ⟨p, hp, hp', fun h1 h2 => absurd ⟨h1, h2⟩ hv⟩
    choose φ h1 h2 h3 using key
    have hφ : IsFam φ := ⟨h1, by filter_upwards [hφ'.2, h.2.2.2.2.1] with v p q using h3 v p q⟩
    exact ⟨_, pure_mem f hφ, by rw [(h.2.2.2.2.2 f φ hφ).1]; simp only [h2]⟩

end Pure

section Vac

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

theorem schr_of_acts (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F} {γ : Matrix (Fin n) (Fin d) (AE F E)} (hγ : γ ∈ latAtV X W v)
    {φ : (Fin n × Fin d → Fv F v) → ℂ} (hφ : φ ∈ SB _) {χ : ℂ} (h : Acts (evFin F v) (M.co.rho ψ γ) φ (χ • φ)) :
    schr (GlobalTheory.LatVac.psiAt ψ v) (GlobalTheory.LatVac.locCo M.co v γ) φ = χ • φ := by
  obtain ⟨r, hr, x₀, hx₀⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v φ hφ
  funext ξ
  have := GlobalTheory.LatVac.heis_at_local_identity v M.co ψ γ φ χ ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ) h r hr x₀ hx₀ ξ
  rw [schr, invOf_eq_inv]
  exact this

theorem vac_line (B : Base F E) {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s')
    (M : Model σ X W) (v : Pl F) {φ φ' : (Fin n × Fin d → Fv F v) → ℂ} (h : M.IsVac B.ψ v φ) (h' : M.IsVac B.ψ v φ') :
    ∃ m : ℂ, φ' = m • φ := by
  classical
  obtain ⟨hφ, hφ0, θ, hθ, hA⟩ := h
  obtain ⟨hφ', -, θ', hθ', hA'⟩ := h'
  have hAt := (GlobalTheory.LatVac.latAtV_at_stable X W v).1
  let χ : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → ℂ := fun l =>
    if h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l then
      B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) h.choose h.choose) else 0
  have loc : ∀ f : (Fin n × Fin d → Fv F v) → ℂ, f ∈ SB _ →
      (∀ γ ∈ latAtV X W v, Acts (evFin F v) (M.co.rho B.ψ γ) f
        (B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) • f)) →
      ∀ l ∈ (latAtV X W v).map (GlobalTheory.LatVac.locCo M.co v), ∀ ξ,
        GlobalTheory.LatVac.psiAt B.ψ v (ξ ⬝ᵥ l.2 + (2 : Fv F v)⁻¹ * (l.1 ⬝ᵥ l.2)) * f (ξ + l.1) = χ l * f ξ := by
    intro f hf hA l hl ξ
    have h : ∃ γ ∈ latAtV X W v, GlobalTheory.LatVac.locCo M.co v γ = l := AddSubgroup.mem_map.mp hl
    have key := congrFun (schr_of_acts M B.ψ h.choose_spec.1 hf (hA _ h.choose_spec.1)) ξ
    simp only [χ, dif_pos h]
    rw [h.choose_spec.2, schr, invOf_eq_inv] at key
    exact key
  obtain ⟨c, hc0, hcb⟩ := GlobalTheory.LatBound.locCo_latAtV_bounded X W v M.co hX.lat.toIsLattice hW.lat.toIsLattice
  have hsd := GlobalTheory.LatVac.DualLoc.map_selfDual v M.co B.ψ _ hAt (GlobalTheory.T.heisenbergLattice_selfDual_every_finitePlace F E σ B n d X W r s r' s' hB hX hW v)
  have hfill := GlobalTheory.T.self_dual_lattice_invariant_vector F v _ (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
    (fun _ => GlobalTheory.StdCharFromIsStd.norm_psi hB.std _) (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v) _ c hc0 hsd
    (fun l hl i => by
      obtain ⟨γ, hγ, rfl⟩ := AddSubgroup.mem_map.mp hl
      exact hcb γ hγ i)
  refine GlobalTheory.heisenbergEigen_proportional (GlobalTheory.LatVac.psiAt B.ψ v) _ χ φ φ' (loc φ hφ hA) (loc φ' hφ' fun γ hγ => ?_) hφ0 hfill
  have heq := GlobalTheory.T.vacuum_eigenvalue_theta_independent F E σ B n d X W r s r' s' hB hX hW v θ θ' hθ hθ' γ hγ
  change B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) γ γ) =
    B.ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (θ' : E)) (incM F X.J) (incM F W.J) γ γ) at heq
  rw [heq]
  exact hA' γ hγ

theorem IsOp.isVac {ψ : AddChar (AF F) ℂ} {a e c ei ev} (h : IsOp (κ := Fin n × Fin d) ψ a e c ei ev) (M M₁ : Model σ X W)
    (hco : ∀ u, M₁.co.e u = act (a.map (algebraMap F (AF F))) (M.co.e u)) (v : Pl F) {φ : (Fin n × Fin d → Fv F v) → ℂ}
    (hφ : M.IsVac ψ v φ) : M₁.IsVac ψ v (ev v φ) := by
  obtain ⟨h1, h0, θ, hθ, hA⟩ := hφ
  refine ⟨(h.2.2.1 v).mapsTo h1, fun h2 => h0 ((h.2.2.1 v).injOn h1 (zero_mem _) (h2.trans (map_zero _).symm)), θ, hθ,
    fun γ hγ => ?_⟩
  have e1 : GlobalTheory.LatVac.locCo M₁.co v γ = act (a.map (algebraMap F (Fv F v))) (GlobalTheory.LatVac.locCo M.co v γ) := by
    have e2 : ∀ k, evFin F v ((a.map (algebraMap F (AF F)) *ᵥ Sum.elim (M.co.e γ).1 (M.co.e γ).2) k) =
        (a.map (algebraMap F (Fv F v)) *ᵥ Sum.elim (GlobalTheory.LatVac.locCo M.co v γ).1 (GlobalTheory.LatVac.locCo M.co v γ).2) k := fun k => by

      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
      refine Finset.sum_congr rfl fun j _ => ?_
      cases j <;> rfl
    refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
    · show evFin F v ((M₁.co.e γ).1 k) = _
      rw [hco]; exact e2 _
    · show evFin F v ((M₁.co.e γ).2 k) = _
      rw [hco]; exact e2 _
  have e3 := GlobalTheory.VacBridge.rho_acts_locCo M₁.co ψ v γ ((GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ) (ev v φ)
  rwa [e1, ← h.2.2.2.1 v _ φ h1, schr_of_acts M ψ hγ h1 (hA γ hγ), map_smul] at e3

end Vac

end GlobalTheory.RatWeilOp

end
