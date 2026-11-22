module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockHarmonicLatticeFgAndSpansValueSpace
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicPointLatticeIsLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupportTermSubset
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseLevelCharacterMemCoefficientRingStatement
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1600000open Formalism.L2.Host (embLL0)

noncomputable section

namespace GlobalTheory.BaseSpan

private theorem latAt_full : ∀ (D : D7) (ρ : Setup D.ntw), ρ.Good → ∀ (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool)
    (h : GA D (Vc D j)), Submodule.IsFullLattice D.host.E ((ρ.B i j b).latAt (finPt (Vc D j) h)) := by
  intro D ρ hρ i j b h
  open Matrix in
  have heq : (ρ.B i j b).latAt (finPt (Vc D j) h) = Bridge.hLat (Vc D j) (finPt (Vc D j) h) := by
    have hΛ := GlobalTheory.LatFull.baseFrame_one_eq _ _ _ (hρ.latS i j b)
    have e : Bridge.hLat (Vc D j) (finPt (Vc D j) h) = Submodule.span (𝓞 D.host.E) {x : Fin (Vc D j).rank → D.host.E |
        Matrix.mulVec ((finPt (Vc D j) h).1⁻¹).1 (fun i => (1 : Formalism.L2.Herm.Af D.host.F) ⊗ₜ[D.host.F] x i) ∈
          GlobalTheory.AdLat.hat D.host.F ((ρ.B i j b).F.ΛS : Set (Fin (Vc D j).rank → D.host.E))} := by
      unfold Bridge.hLat
      rw [hΛ]
      rfl
    rw [e, ← Submodule.span_eq ((ρ.B i j b).latAt (finPt (Vc D j) h))]
    congr 1
    ext x
    have e : ((Formalism.UG.bc (Lev.swapAE D) (finPt (Vc D j) h).1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) =
        fun i => Algebra.TensorProduct.comm D.host.F _ D.host.E ((((finPt (Vc D j) h).1⁻¹).1 *ᵥ (fun i => (1 : Formalism.L2.Herm.Af D.host.F) ⊗ₜ[D.host.F] x i)) i) := by
      rw [← map_inv]
      funext i
      change _ = Lev.swapAE D _
      rw [RingHom.map_mulVec (Lev.swapAE D)]
      rfl
    change ((Formalism.UG.bc (Lev.swapAE D) (finPt (Vc D j) h).1)⁻¹).1 *ᵥ (fun i => Formalism.UG.inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (x i)) ∈ Formalism.L2.Herm.hatL (F := D.host.F) (ρ.B i j b).F.ΛS ↔ _
    rw [e]
    constructor
    · intro hz
      have := GlobalTheory.PrincInLevel.swap_symm_mem_hat (ρ.B i j b).F.ΛS _ hz
      simpa only [Set.mem_setOf_eq, AlgEquiv.symm_apply_apply] using this
    · intro hz
      exact GlobalTheory.PrincInLevel.swap_mem_hatL (ρ.B i j b).F.ΛS _ hz
  rw [heq]
  obtain ⟨-, -, hfg, hsp, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D (Vc D j)
  obtain ⟨Λ, hΛ, h1, h2, -⟩ := GlobalTheory.AdLat.exists_lattice_latOf
    D.host.F D.host.E (Vc D j).rank (GlobalTheory.Member.latC (Vc D j))
      (finPt (Vc D j) h).1 hfg hsp
  rw [SetLike.coe_injective ((GlobalTheory.RepsCompare.coe_hLat (Vc D j)
    (finPt (Vc D j) h)).trans hΛ.symm)]
  exact { toIsLattice := Submodule.IsLattice.of_fg D.host.E h1
          span_eq_top := h2 }


variable {D : D7} {S T : HSp D}

theorem pq_le {B : Base S T} (hB : B.Good) (τ : D.what₂.Tau) : B.w.p τ + B.w.q τ ≤ T.rank := by
  obtain ⟨e, -⟩ := hB.sigOK (tauE D τ)
  rw [← hB.sig τ] at e
  have := Fintype.card_congr e
  simp only [Fintype.card_fin, Fintype.card_sum] at this
  omega

theorem coefLat_le_valSpace {B : Base S T} {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
    {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ} {y : Bridge.Gf S}
    (hspan : Submodule.span ℂ (B.coefLat σ emb O y : Set (PolF D T.rank S.rank)) = B.valSpace)
    {P : PolF D T.rank S.rank} (hP : P ∈ B.coefLat σ emb O y) : P ∈ B.valSpace :=
  hspan ▸ Submodule.subset_span hP

theorem tr_mem_mtLat {B : Base S T} (hB : B.Good) {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
    {emb : D.what₂.Tau → (D.host.E →+* K)} {O : Subring ℂ} (hc : IsCoefRing σ emb O) {ψ : Twist D Circle}
    (hlam : ∀ k, ((B.levLam ψ k : ℂˣ) : ℂ) ∈ O) {y : Bridge.Gf S}
    (hf : Finite (Bridge.stab (Bridge.ratF S) (B.levJ ψ) y))
    (hspan : Submodule.span ℂ (B.coefLat σ emb O y : Set (PolF D T.rank S.rank)) = B.valSpace)
    {P : PolF D T.rank S.rank} (hP : P ∈ B.coefLat σ emb O y) :
    GlobalTheory.LawTrace.tr (Bridge.ratF S) (B.act.comp (GQ S).subtype) (B.levJ ψ) (B.levLam ψ) y P ∈ B.mtLat σ emb O ψ := by
  refine (Base.mem_mtLat B σ emb O).2 ⟨Submodule.mem_inf.2 ⟨?_, GlobalTheory.LawTrace.mem_lawForms_tr hf P⟩, fun x => ?_⟩
  · refine Submodule.mem_pi.2 fun x _ => GlobalTheory.LawTrace.tr_mem hf P x B.valSpace fun γ h => ?_
    unfold GlobalTheory.LawTrace.term
    rw [dite_eq_left h]
    exact Submodule.smul_mem _ _ (Base.act_mem_valSpace _ (coefLat_le_valSpace hspan hP))
  · refine GlobalTheory.LawTrace.tr_mem hf P x (B.coefLat σ emb O x) fun γ h => ?_
    unfold GlobalTheory.LawTrace.term
    rw [dite_eq_left h]
    have hx : x = Bridge.ratF S γ * y * ((⟨_, h⟩ : B.levJ ψ) : Bridge.Gf S) := by
      change x = Bridge.ratF S γ * y * ((Bridge.ratF S γ * y)⁻¹ * x)
      group
    have h1 := Base.act_mem_coefLat hB.frame hc γ y _ (Base.mem_St_of_mem_levJ (B := B) h) hP
    rw [← hx] at h1
    have h2 := Submodule.smul_mem (B.coefLat σ emb O x) (⟨_, hlam ⟨_, h⟩⟩ : O) h1
    exact h2

end GlobalTheory.BaseSpan

namespace GlobalTheory.BaseSpan

theorem tw_one_good {D : D7} {ρ : Setup D.ntw} (i : D.ntw.Tw) (b : Bool) :
    (ρ.tw i b 0 ∅ 1).Good ∧ (ρ.tw i b 0 ∅ 1).Q = ∅ := by
  have hc : (ρ.tw i b 0 ∅ 1).chi = 1 := charOf_one _ _
  have hq : (ρ.tw i b 0 ∅ 1).Q = ∅ := half_empty _
  refine ⟨⟨?_, fun x => ?_, fun a => ?_, ?_, fun x _ _ _ _ => ?_, fun PP h => ?_⟩, hq⟩
  · rw [hc, MonoidHom.ker_one, Subgroup.coe_top]; exact isOpen_univ
  · rw [hc]; rfl
  · rw [hc]; rfl
  · rw [hq]; exact splitSet_empty
  · rw [hc]; rfl
  · rw [hq] at h; exact absurd h (Finset.notMem_empty _)

theorem formsC_le_span_mt : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool),
    ∀ F ∈ (Y.Z.ρ.B i j b).formsC (Y.Z.ρ.tw i b 0 ∅ 1),
      F ∈ Submodule.span ℂ (Y.Z.ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)) := by
  intro D X E Y i j b F hF
  have hρ : Y.Z.ρ.Good := Y.Z.good
  have hB : (Y.Z.ρ.B i j b).Good := hρ.base i j b
  obtain ⟨hψ, hψQ⟩ := tw_one_good (ρ := Y.Z.ρ) i b
  have hcls := hρ.classes i j b (Y.Z.ρ.tw i b 0 ∅ 1) hψ (by rw [hψQ]; exact Base.admissible_empty_of_good hB)
  have hlam : ∀ k, (((Y.Z.ρ.B i j b).levLam (Y.Z.ρ.tw i b 0 ∅ 1) k : ℂˣ) : ℂ) ∈ (Y.Z.ρ.eOk i b 0).range := fun k => GlobalTheory.T.baseLevelCharacter_mem_coefficientRing D X E Y i j b k
  have hL := (Submodule.mem_inf.1 hF).2
  rw [GlobalTheory.LawTrace.eq_sum_tr hcls.reps hcls.stab hL]
  refine Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ ?_
  have hspan : Submodule.span ℂ ((Y.Z.ρ.B i j b).coefLat (embLL0 D) (labLL0 D) (Y.Z.ρ.eOk i b 0).range
      (finPt (Vc D j) (Y.Z.ρ.rep i j b _ c)) : Set (PolF D (Wc D j).rank (Vc D j).rank)) = (Y.Z.ρ.B i j b).valSpace :=
    (GlobalTheory.ExportSeries.HarmLattice.harmLat_fg_span D (Wc D j).rank (Vc D j).rank (Y.Z.ρ.B i j b).w (Y.Z.ρ.B i j b).F.BS _
      (embLL0 D) (labLL0 D) _ _ hB.wt (pq_le hB) (hρ.isCoefRing_k i b 0)
      (latAt_full D Y.Z.ρ hρ i j b _)).2
  have hFy : F (finPt (Vc D j) (Y.Z.ρ.rep i j b _ c)) ∈ Submodule.span ℂ ((Y.Z.ρ.B i j b).coefLat (embLL0 D) (labLL0 D)
      (Y.Z.ρ.eOk i b 0).range (finPt (Vc D j) (Y.Z.ρ.rep i j b _ c)) : Set (PolF D (Wc D j).rank (Vc D j).rank)) := by
    rw [hspan]
    exact (Submodule.mem_pi.1 (Submodule.mem_inf.1 hF).1) _ trivial
  generalize F (finPt (Vc D j) (Y.Z.ρ.rep i j b _ c)) = v at hFy ⊢
  induction hFy using Submodule.span_induction with
  | mem P hP =>
    exact Submodule.subset_span (tr_mem_mtLat hB (hρ.isCoefRing_k i b 0) hlam (hcls.stab c) hspan hP)
  | zero =>
    rw [GlobalTheory.LawTrace.tr_zero]
    exact Submodule.zero_mem _
  | add P Q _ _ hP hQ =>
    rw [GlobalTheory.LawTrace.tr_add (hcls.stab c)]
    exact Submodule.add_mem _ hP hQ
  | smul a P _ hP =>
    rw [GlobalTheory.LawTrace.tr_smul]
    exact Submodule.smul_mem _ _ hP

end GlobalTheory.BaseSpan

end
