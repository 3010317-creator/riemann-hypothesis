module

public import Formalism.AdmissibleDesigns.Base
public import Formalism.AdmissibleDesigns.Cohomology
public import Formalism.AdicCompletionExports.AdicCompleteRingEquiv.IsAdicCompleteOfRingEquiv
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.LevelLetterCocycles.GoodCongruenceDataOf
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfWindows
public import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation
import Formalism.WachLatticeTwists.RealClassMaps.Statement
public import Formalism.WachLatticeTwists.RealDisplaySplitting.SurjectionRankOneIdempotent
import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.Statement
import Formalism.WachLatticeTwists.SplitClassesAll.Statement
public import Formalism.WachLatticeTwists.SplitLocalLifts.Cocycles1MapOfEquivariant
import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
import Mathlib.Algebra.Order.Star.Real
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

@[expose] public section

noncomputable section

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KLift

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Formalism.NG Module
open scoped Formalism.MainNotions.N.KRow

alias tr := KRow.tr
alias untr := KRow.untr
alias smul_eO := KRow.smul_eO
alias smul_Ow := KRow.smul_Ow
alias latT := KRow.latT
alias MO := KRow.MO
alias latMap := KRow.latMap
alias latEquiv := KRow.latEquiv
alias basMO := KRow.basMO
alias free_MO := KRow.free_MO
alias finite_MO := KRow.finite_MO
alias latOf := KRow.latOf
alias latHom := KRow.latHom
alias latHom_onto := KRow.latHom_onto

section Lift

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  {e : FractionRing O ≃+* LL} {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {P Q VP VQ : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
  [AddCommGroup VP] [Module (FractionRing O) VP] [Module O VP] [IsScalarTower O (FractionRing O) VP]
  [AddCommGroup VQ] [Module (FractionRing O) VQ] [Module O VQ] [IsScalarTower O (FractionRing O) VQ]
  [Module.Finite O P] [Module.Free O P] [Module.Finite O Q] [Module.Free O Q]
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {ρP : Representation O Γ P} {ρQ : Representation O Γ Q} {ρVP : Representation O Γ VP}
  {ρVQ : Representation O Γ VQ} {jP : P →ₗ[O] VP} {jQ : Q →ₗ[O] VQ}
  (hjP : Function.Injective jP) (hjQ : Function.Injective jQ)
  (hjeqP : ∀ γ m, jP (ρP γ m) = ρVP γ (jP m)) (hjeqQ : ∀ γ m, jQ (ρQ γ m) = ρVQ γ (jQ m))
  (hspP : ∀ v : VP, ∃ c : O, c ≠ 0 ∧ ∃ m, jP m = c • v) (hspQ : ∀ v : VQ, ∃ c : O, c ≠ 0 ∧ ∃ m, jQ m = c • v)
  {ev : P →ₗ[O] Q} {f0 : VP →ₗ[O] VQ}
  (hf0 : ∀ γ v, f0 (ρVP γ v) = ρVQ γ (f0 v)) (hcomm : ∀ m, f0 (jP m) = jQ (ev m))

theorem liftO_of_liftF (ℓ : ℕ) (hp : PD.p = ℓ) (hι : Function.Bijective ι) (hev : IsEquivMap ρP ρQ ev) (n : ℕ)
    (hL : (latHom ι heO hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm).LiftF PD n) :
    Formalism.RepresentationBoundsCohomology.JL.LiftO ℓ (finiteClassesModel e PD ι ρVP ρP jP) (finiteClassesModel e PD ι ρVQ ρQ jQ)
      (Formalism.RepresentationBoundsCohomology.JL.mapH1 ρP ρQ ev hev) n := by
  intro κ hκ
  obtain ⟨z, hz, rfl⟩ := hκ
  let σ : Γ ≃ G := (Equiv.ofBijective ι hι).symm
  have hισ : ∀ γ, ι (σ γ) = γ := fun γ => (Equiv.ofBijective ι hι).apply_symm_apply γ
  have hσι : ∀ g, σ (ι g) = g := fun g => (Equiv.ofBijective ι hι).symm_apply_apply g

  let c2 : G → TrV e VQ := fun g => tr e (jQ ((z : Γ → Q) (ι g)))
  have hz' : c2 ∈ finiteCocycles PD (repL e ρVQ ι) := hz
  have hc2 : c2 ∈ latticeFiniteCocycles PD (latOf e eO jQ ι heO ρVQ ρQ hjQ hjeqQ hspQ) :=
    ⟨⟨hz'.1, fun g _ => ⟨_, rfl⟩⟩, hz'⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hL c2 hc2)
  obtain ⟨c1, hc1, rfl⟩ := ha
  obtain ⟨y, ⟨q, rfl⟩, rfl⟩ := hb
  have hval : ∀ g, ∃ m, tr e (jP m) = c1 g := fun g => hc1.1.2 g (Set.mem_univ g)
  let z1 : Γ → P := fun γ => Classical.choose (hval (σ γ))
  have hz1 : ∀ γ, jP (z1 γ) = untr e (c1 (σ γ)) := fun γ => Classical.choose_spec (hval (σ γ))
  have hcoc : ∀ g h, c1 (g * h) = c1 g + repL e ρVP ι g (c1 h) := hc1.2.1.2
  have hσmul : ∀ γ δ, σ (γ * δ) = σ γ * σ δ := fun γ δ => hι.1 (by rw [hισ, ι.map_mul, hισ, hισ])
  have hz1c : z1 ∈ coZ1s ρP := by
    intro γ δ
    apply hjP
    rw [map_add (f := _), hz1, hz1, hjeqP, hz1, hσmul, hcoc]
    show untr e (c1 (σ γ)) + ρVP (ι (σ γ)) (untr e (c1 (σ δ))) = _
    rw [hισ]
  have hz1f : (fun g => tr e (jP (z1 (ι g)))) = c1 := by
    funext g
    show jP (z1 (ι g)) = untr e (c1 g)
    rw [hz1, hσι]
  refine ⟨Submodule.mkQ _ ⟨z1, hz1c⟩, ⟨⟨z1, hz1c⟩, ?_, rfl⟩, ?_⟩
  · show (fun g => tr e (jP (z1 (ι g)))) ∈ finiteCocycles PD (repL e ρVP ι)
    rw [hz1f]
    exact hc1.2

  have heq : ∀ g, (((PD.p : ℕ) : Ow) ^ n • c2) g =
      trL e f0 (c1 g) + (repL e ρVQ ι g (tr e (jQ q)) - tr e (jQ q)) := fun g => congrFun hab.symm g
  have heqV : ∀ γ, jQ (((ℓ : O) ^ n) • (z : Γ → Q) γ) =
      jQ (ev (z1 γ)) + (jQ (ρQ γ q) - jQ q) := by
    intro γ
    have h := heq (σ γ)
    rw [Pi.smul_apply, hp] at h
    have h1 : ((ℓ : Ow) ^ n) = eO ((ℓ : O) ^ n) := by rw [map_pow, map_natCast]
    rw [h1] at h
    have h2 := h
    simp only [c2, tr] at h2
    rw [smul_eO heO, hισ] at h2
    rw [repL_apply, hισ] at h2
    rw [map_smul, ← hcomm, hz1, hjeqQ]
    exact h2
  show Submodule.mapQ _ _ _ _ (Submodule.Quotient.mk _) = _
  rw [Submodule.mapQ_apply, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.eq]
  refine ⟨-q, funext fun γ => ?_⟩
  apply hjQ
  show jQ (ρQ γ (-q) - (-q)) = jQ (ev (z1 γ) - ((ℓ : O) ^ n) • (z : Γ → Q) γ)
  rw [map_sub, map_sub, heqV]
  simp only [map_neg]
  abel

end Lift

section FromAt

alias finDim_of_lat := KRow.finDim_of_lat

theorem subq_of_onto {LL : Type} [Field LL] {G : Type} [Group G] {V W : Type} [AddCommGroup V] [Module LL V]
    [AddCommGroup W] [Module LL W] {ρ : Representation LL G V} {ρ' : Representation LL G W}
    {ιx : Type} {k : ℕ} {Ms : ιx → G → Matrix (Fin k) (Fin k) LL} (f : V →ₗ[LL] W)
    (hf : Function.Surjective f) (heq : ∀ g v, f (ρ g v) = ρ' g (f v))
    (h : Formalism.MainNotions.N.IsSubquotOfSums ρ Ms) : Formalism.MainNotions.N.IsSubquotOfSums ρ' Ms := by
  obtain ⟨m, xs, U, q, hU, hq, hqe⟩ := h
  refine ⟨m, xs, U, f ∘ₗ q, hU, fun w => ?_, fun g u hu => ?_⟩
  · obtain ⟨v, rfl⟩ := hf w
    obtain ⟨u, hu, rfl⟩ := hq v
    exact ⟨u, hu, rfl⟩
  · rw [LinearMap.comp_apply, hqe g u hu, heq, LinearMap.comp_apply]

end FromAt

section Lift2

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL]
  {e : FractionRing O ≃+* LL} {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] {eO : O ≃+* Ow}
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {P Q VP VQ : Type} [AddCommGroup P] [Module O P] [AddCommGroup Q] [Module O Q]
  [AddCommGroup VP] [Module (FractionRing O) VP] [Module O VP] [IsScalarTower O (FractionRing O) VP]
  [AddCommGroup VQ] [Module (FractionRing O) VQ] [Module O VQ] [IsScalarTower O (FractionRing O) VQ]
  [Module.Finite O P] [Module.Free O P] [Module.Finite O Q] [Module.Free O Q]
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {ρP : Representation O Γ P} {ρQ : Representation O Γ Q} {ρVP : Representation O Γ VP}
  {ρVQ : Representation O Γ VQ} {jP : P →ₗ[O] VP} {jQ : Q →ₗ[O] VQ}
  (hjP : Function.Injective jP) (hjQ : Function.Injective jQ)
  (hjeqP : ∀ γ m, jP (ρP γ m) = ρVP γ (jP m)) (hjeqQ : ∀ γ m, jQ (ρQ γ m) = ρVQ γ (jQ m))
  (hspP : ∀ v : VP, ∃ c : O, c ≠ 0 ∧ ∃ m, jP m = c • v) (hspQ : ∀ v : VQ, ∃ c : O, c ≠ 0 ∧ ∃ m, jQ m = c • v)
  {ev : P →ₗ[O] Q} {f0 : VP →ₗ[O] VQ}
  (hf0 : ∀ γ v, f0 (ρVP γ v) = ρVQ γ (f0 v)) (hcomm : ∀ m, f0 (jP m) = jQ (ev m))

alias trL_onto := KRow.trL_onto

include heO hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm in
theorem liftO_of_liftAt (ℓ : ℕ) (hp : PD.p = ℓ) (hι : Function.Bijective ι) (hev : IsEquivMap ρP ρQ ev)
    (hevs : Function.Surjective ev) {ιx : Type} {k : ℕ} (Ms : ιx → G → Matrix (Fin k) (Fin k) LL) (n : ℕ)
    (hA : Formalism.MainNotions.N.LiftAt PD (O := Ow) Ms n)
    (hcP : ∀ x, Continuous fun g => repL e ρVP ι g x)
    (hsP : Formalism.MainNotions.N.IsSubquotOfSums (repL e ρVP ι) Ms) :
    Formalism.RepresentationBoundsCohomology.JL.LiftO ℓ (finiteClassesModel e PD ι ρVP ρP jP) (finiteClassesModel e PD ι ρVQ ρQ jQ)
      (Formalism.RepresentationBoundsCohomology.JL.mapH1 ρP ρQ ev hev) n := by
  let L1 := latOf e eO jP ι heO ρVP ρP hjP hjeqP hspP
  let L2 := latOf e eO jQ ι heO ρVQ ρQ hjQ hjeqQ hspQ
  haveI := finDim_of_lat (Ow := Ow) (Qp := Qp) L1
  haveI := finDim_of_lat (Ow := Ow) (Qp := Qp) L2
  have hons : Function.Surjective (trL e f0) := trL_onto (hspQ := hspQ) (hcomm := hcomm) hevs
  have heq : ∀ g v, trL e f0 (repL e ρVP ι g v) = repL e ρVQ ι g (trL e f0 v) := fun g v => hf0 (ι g) v
  have hcQ : ∀ y, Continuous fun g => repL e ρVQ ι g y := by
    intro y
    obtain ⟨x, rfl⟩ := hons y
    have h : (fun g => repL e ρVQ ι g (trL e f0 x)) = fun g => trL e f0 (repL e ρVP ι g x) :=
      funext fun g => (heq g x).symm
    rw [h]
    exact (trL_cont e f0).comp (hcP x)
  have hsQ := subq_of_onto (trL e f0) hons heq hsP
  exact liftO_of_liftF PD ι heO hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm ℓ hp hι hev n
    (hA (TrV e VP) (repL e ρVP ι) L1 hcP hsP (TrV e VQ) (repL e ρVQ ι) L2 hcQ hsQ
      (latHom ι heO hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm)
      (latHom_onto ι heO hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm hevs))

end Lift2

section Rec

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem finite_classes_local_eq {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {V M : Type} [AddCommGroup V]
    [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V] [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
    [AddCommGroup M] [Module (D.nd.O i) M]
    (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V) (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M)
    (φ : M →ₗ[D.nd.O i] V) :
    finiteClassesCocyclesMap i dc n ρ ρM φ = finiteClassesModel (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Br.iota D.nbr i _ hn) ρ ρM φ := by
  unfold finiteClassesCocyclesMap fPre finiteClassesModel finPre
  rw [fZ_pos i dc ρ hn]
  rfl

theorem heO_br {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (a : D.nd.O i) :
    algebraMap (Br.Ow (D.nbr i _ hn)) (Br.LLw (D.nbr i _ hn)) ((D.nbr i _ hn).eO a) =
      eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a) :=
  (Br.toLLK_alg (D.nbr i _ hn) a).symm

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem liftO_col (eR : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (hA : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc eR) (hG : K.SelfGood i)
    {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (hc : K.plOf i dc n ∈ dc.col)
    {P Q VP VQ : Type} [AddCommGroup P] [Module (D.nd.O i) P] [AddCommGroup Q] [Module (D.nd.O i) Q]
    [AddCommGroup VP] [Module (FractionRing (D.nd.O i)) VP] [Module (D.nd.O i) VP]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VP]
    [AddCommGroup VQ] [Module (FractionRing (D.nd.O i)) VQ] [Module (D.nd.O i) VQ]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VQ]
    [Module.Finite (D.nd.O i) P] [Module.Free (D.nd.O i) P] [Module.Finite (D.nd.O i) Q] [Module.Free (D.nd.O i) Q]
    {ρP : Representation (D.nd.O i) ↥(Γn i dc n) P} {ρQ : Representation (D.nd.O i) ↥(Γn i dc n) Q}
    {ρVP : Representation (D.nd.O i) ↥(Γn i dc n) VP} {ρVQ : Representation (D.nd.O i) ↥(Γn i dc n) VQ}
    {jP : P →ₗ[D.nd.O i] VP} {jQ : Q →ₗ[D.nd.O i] VQ}
    (hjP : Function.Injective jP) (hjQ : Function.Injective jQ)
    (hjeqP : ∀ γ m, jP (ρP γ m) = ρVP γ (jP m)) (hjeqQ : ∀ γ m, jQ (ρQ γ m) = ρVQ γ (jQ m))
    (hspP : ∀ v : VP, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m, jP m = c • v)
    (hspQ : ∀ v : VQ, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m, jQ m = c • v)
    {ev : P →ₗ[D.nd.O i] Q} {f0 : VP →ₗ[D.nd.O i] VQ}
    (hf0 : ∀ γ v, f0 (ρVP γ v) = ρVQ γ (f0 v)) (hcomm : ∀ m, f0 (jP m) = jQ (ev m))
    (hev : IsEquivMap ρP ρQ ev) (hevs : Function.Surjective ev)
    (hcP : ∀ x, Continuous fun g => repL (eK (D.nbr i _ hn)) ρVP (Br.iota D.nbr i _ hn) g x)
    (hsP : Formalism.MainNotions.N.IsSubquotOfSums (repL (eK (D.nbr i _ hn)) ρVP (Br.iota D.nbr i _ hn))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rTwO D.nd i r x)))) :
    Formalism.RepresentationBoundsCohomology.JL.LiftO (D.nd.l i) (finiteClassesCocyclesMap i dc n ρVP ρP jP) (finiteClassesCocyclesMap i dc n ρVQ ρQ jQ)
      (Formalism.RepresentationBoundsCohomology.JL.mapH1 ρP ρQ ev hev) (eR (K.plOf i dc n)) := by
  rw [finite_classes_local_eq i dc hn, finite_classes_local_eq i dc hn]
  have hbij : Function.Bijective (Br.iota D.nbr i _ hn) := (D.nbr i _ hn).e.symm.bijective
  exact liftO_of_liftAt (Br.PD D.loc D.nbr i _ hn) (Br.iota D.nbr i _ hn) (heO_br i dc hn)
    hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm (D.nd.l i) (Br.PD_p D.loc D.nbr i _ hn) hbij hev hevs _ _
    (hA _ hn hc (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (hG _ hn)) hcP hsP

end Rec

section Emb

theorem subq_of_inj {LL : Type} [Field LL] {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module LL V]
    {ρ : Representation LL G V} {ιx : Type} {k : ℕ} {Ms : ιx → G → Matrix (Fin k) (Fin k) LL}
    {m : ℕ} (xs : Fin m → ιx) (φ : V →ₗ[LL] (Fin m → Fin k → LL)) (hφ : Function.Injective φ)
    (heq : ∀ g v, φ (ρ g v) = fun a => (Ms (xs a) g).mulVec (φ v a)) : Formalism.MainNotions.N.IsSubquotOfSums ρ Ms := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective φ (LinearMap.ker_eq_bot.2 hφ)
  have hψv : ∀ v, ψ (φ v) = v := fun v => by rw [← LinearMap.comp_apply, hψ, LinearMap.id_apply]
  refine ⟨m, xs, LinearMap.range φ, ψ, ?_, fun v => ⟨φ v, ⟨v, rfl⟩, hψv v⟩, ?_⟩
  · rintro g _ ⟨v, rfl⟩
    exact ⟨ρ g v, heq g v⟩
  · rintro g _ ⟨v, rfl⟩
    rw [← heq, hψv, hψv]

theorem cont_of_inj {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] {G : Type} [Group G]
    [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    [ContinuousAdd V] [ContinuousSMul LL V]
    {ρ : Representation LL G V} {ιx : Type} {k : ℕ} {Ms : ιx → G → Matrix (Fin k) (Fin k) LL}
    {m : ℕ} (xs : Fin m → ιx) (φ : V →ₗ[LL] (Fin m → Fin k → LL)) (hφ : Function.Injective φ)
    (heq : ∀ g v, φ (ρ g v) = fun a => (Ms (xs a) g).mulVec (φ v a)) (hMs : ∀ x, Continuous (Ms x))
    (v : V) : Continuous fun g => ρ g v := by
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective φ (LinearMap.ker_eq_bot.2 hφ)
  have hψv : ∀ v, ψ (φ v) = v := fun v => by rw [← LinearMap.comp_apply, hψ, LinearMap.id_apply]
  have h : (fun g => ρ g v) = fun g => ψ (fun a => (Ms (xs a) g).mulVec (φ v a)) :=
    funext fun g => by rw [← heq, hψv]
  rw [h]
  have hψc : Continuous ψ := IsModuleTopology.continuous_of_linearMap ψ
  refine hψc.comp (continuous_pi fun a => continuous_pi fun i => ?_)
  simp only [Matrix.mulVec, dotProduct]
  exact continuous_finsetSum _ fun j _ => ((hMs (xs a)).matrix_elem i j).mul continuous_const

end Emb

alias mkK_inj := KRow.mkK_inj
alias mkK_span := KRow.mkK_span

section RecCol

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

abbrev MsAt {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    Br.G D.nbr i _ hn → Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LLw (D.nbr i _ hn)) :=
  ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rTwO D.nd i r x))

def EmbAt {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {VP : Type} [AddCommGroup VP]
    [Module (FractionRing (D.nd.O i)) VP] [Module (D.nd.O i) VP] [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VP]
    (ρVP : Representation (D.nd.O i) ↥(Γn i dc n) VP) : Prop :=
  ∃ (m : ℕ) (xs : Fin m → D.nd.X i)
    (φ : TrV (eK (D.nbr i _ hn)) VP →ₗ[Br.LLw (D.nbr i _ hn)] (Fin m → Fin D.R.nV → Br.LLw (D.nbr i _ hn))),
    Function.Injective φ ∧ ∀ g v, φ (repL (eK (D.nbr i _ hn)) ρVP (Br.iota D.nbr i _ hn) g v) =
      fun a => (MsAt i dc r hn (xs a) g).mulVec (φ v a)

def MsCont {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) : Prop :=
  ∀ x, Continuous (MsAt i dc r hn x)

theorem lift_integral_column (eR : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (hA : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc eR) (hG : K.SelfGood i)
    {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (hc : K.plOf i dc n ∈ dc.col)
    {P Q VP VQ : Type} [AddCommGroup P] [Module (D.nd.O i) P] [AddCommGroup Q] [Module (D.nd.O i) Q]
    [AddCommGroup VP] [Module (FractionRing (D.nd.O i)) VP] [Module (D.nd.O i) VP]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VP]
    [AddCommGroup VQ] [Module (FractionRing (D.nd.O i)) VQ] [Module (D.nd.O i) VQ]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VQ]
    [Module.Finite (D.nd.O i) P] [Module.Free (D.nd.O i) P] [Module.Finite (D.nd.O i) Q] [Module.Free (D.nd.O i) Q]
    {ρP : Representation (D.nd.O i) ↥(Γn i dc n) P} {ρQ : Representation (D.nd.O i) ↥(Γn i dc n) Q}
    {ρVP : Representation (D.nd.O i) ↥(Γn i dc n) VP} {ρVQ : Representation (D.nd.O i) ↥(Γn i dc n) VQ}
    {jP : P →ₗ[D.nd.O i] VP} {jQ : Q →ₗ[D.nd.O i] VQ}
    (hjP : Function.Injective jP) (hjQ : Function.Injective jQ)
    (hjeqP : ∀ γ m, jP (ρP γ m) = ρVP γ (jP m)) (hjeqQ : ∀ γ m, jQ (ρQ γ m) = ρVQ γ (jQ m))
    (hspP : ∀ v : VP, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m, jP m = c • v)
    (hspQ : ∀ v : VQ, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m, jQ m = c • v)
    {ev : P →ₗ[D.nd.O i] Q} {f0 : VP →ₗ[D.nd.O i] VQ}
    (hf0 : ∀ γ v, f0 (ρVP γ v) = ρVQ γ (f0 v)) (hcomm : ∀ m, f0 (jP m) = jQ (ev m))
    (hev : IsEquivMap ρP ρQ ev) (hevs : Function.Surjective ev)
    (hemb : EmbAt i dc r hn ρVP) (hMs : MsCont i dc r hn) :
    Formalism.RepresentationBoundsCohomology.JL.LiftO (D.nd.l i) (finiteClassesCocyclesMap i dc n ρVP ρP jP) (finiteClassesCocyclesMap i dc n ρVQ ρQ jQ)
      (Formalism.RepresentationBoundsCohomology.JL.mapH1 ρP ρQ ev hev) (eR (K.plOf i dc n)) := by
  obtain ⟨m, xs, φ, hφ, heq⟩ := hemb
  exact liftO_col i dc r eR hA hG hn hc hjP hjQ hjeqP hjeqQ hspP hspQ hf0 hcomm hev hevs
    (cont_of_inj xs φ hφ heq hMs) (subq_of_inj xs φ hφ heq)

end RecCol

section Cols

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem plOf_col (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) = l.1 :=
  K.plOf_idx i dc (Finset.mem_union_left _ (Finset.mem_union_right _ l.2))

theorem hcCol (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ dc.col := by
  rw [plOf_col]
  exact l.2

theorem hnCol (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ placesOver D.host.E (D.nd.l i) :=
  (dc.cover _).1 (Or.inr (hcCol i dc l))

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r' : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem liftCol_eve (eR : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (hA : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc eR) (hG : K.SelfGood i)
    {Pe L V : Type} [AddCommGroup Pe] [Module R' Pe] [Module (D.nd.O i) Pe] [SMulCommClass R' (D.nd.O i) Pe]
    [Module.Finite (D.nd.O i) Pe] [Module.Free (D.nd.O i) Pe]
    [AddCommGroup L] [Module R' L] [Module (D.nd.O i) L] [SMulCommClass R' (D.nd.O i) L]
    [Module.Finite (D.nd.O i) L] [Module.Free (D.nd.O i) L]
    [AddCommGroup V] [Module R' V] [Module (D.nd.O i) V] [Module (FractionRing (D.nd.O i)) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] [SMulCommClass R' (FractionRing (D.nd.O i)) V]
    (ince : Pe →ₗ[R'] R') (v₁ : L) (eve : Pe →ₗ[D.nd.O i] L) (heve : ∀ a, eve a = ince a • v₁)
    (hevs : Function.Surjective eve)
    (iL : L →ₗ[D.nd.O i] V) (hiL : Function.Injective iL) (hiLeq : ∀ (a : R') m, iL (a • m) = a • iL m)
    (hspL : ∀ v : V, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m, iL m = c • v)
    (hemb : ∀ l, EmbAt i dc r (hnCol i dc l)
      (locRep (resRep (uRep (D.nd.O i) (M := Pe) r' χ) (Γn i dc (K.colIdx i dc l)))))
    (hMs : ∀ l, MsCont i dc r (hnCol i dc l)) :
    LiftCol i dc (Hfe₁ i dc r' χ) (Ff i dc r' χ iL)
      (fun l => Formalism.RepresentationBoundsCohomology.JL.mapH1 _ _ eve (Formalism.RepresentationBoundsCohomology.JL.ev_equiv r' χ (Γn i dc (K.colIdx i dc l)) ince v₁ eve heve))
      (fun n => eR (K.plOf i dc n)) := by
  haveI := smulComm_O i (A := R') (V := V)
  intro l
  have hQ : ∀ (γ : ↥(Γn i dc (K.colIdx i dc l))) m,
      iL (resRep (uRep (D.nd.O i) (M := L) r' χ) (Γn i dc (K.colIdx i dc l)) γ m) =
        resRep (uRep (D.nd.O i) (M := V) r' χ) (Γn i dc (K.colIdx i dc l)) γ (iL m) :=
    fun γ m => hiLeq _ m
  have hev := Formalism.RepresentationBoundsCohomology.JL.ev_equiv r' χ (Γn i dc (K.colIdx i dc l)) ince v₁ eve heve
  exact lift_integral_column i dc r eR hA hG (hnCol i dc l) (hcCol i dc l)
    (ρVP := locRep (resRep (uRep (D.nd.O i) (M := Pe) r' χ) (Γn i dc (K.colIdx i dc l))))
    (ρVQ := resRep (uRep (D.nd.O i) (M := V) r' χ) (Γn i dc (K.colIdx i dc l)))
    (jP := mkK) (jQ := iL) mkK_inj hiL (fun γ m => (locRep_mkK _ γ m).symm) hQ mkK_span hspL
    (f0 := liftK (iL ∘ₗ eve))
    (liftK_equiv _ _ (iL ∘ₗ eve) (fun γ m => by rw [LinearMap.comp_apply, LinearMap.comp_apply, hev, hQ]))
    (fun m => liftK_mkK _ m) hev hevs (hemb l) (hMs l)

theorem liftCol_evE (eR : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (hA : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc eR) (hG : K.SelfGood i)
    (δO : D.nd.O i) [Module.Finite (D.nd.O i) ↥(Ideal.span {δO})] [Module.Free (D.nd.O i) ↥(Ideal.span {δO})]
    {PE : Type} [AddCommGroup PE] [Module R' PE] [Module (D.nd.O i) PE] [SMulCommClass R' (D.nd.O i) PE]
    [Module.Finite (D.nd.O i) PE] [Module.Free (D.nd.O i) PE]
    (evE : PE →ₗ[D.nd.O i] ↥(Ideal.span {δO})) (hevE : ∀ g a, evE (uElt r' χ g • a) = evE a)
    (hevs : Function.Surjective evE)
    (hemb : ∀ l, EmbAt i dc r (hnCol i dc l)
      (locRep (resRep (uRep (D.nd.O i) (M := PE) r' χ) (Γn i dc (K.colIdx i dc l)))))
    (hMs : ∀ l, MsCont i dc r (hnCol i dc l)) :
    LiftCol i dc (Hfe₁ i dc r' χ) (HfE₂ i dc δO)
      (fun l => Formalism.RepresentationBoundsCohomology.JL.mapH1 _ _ evE (Formalism.RepresentationBoundsCohomology.JL.ev_equiv_triv r' χ (Γn i dc (K.colIdx i dc l)) evE hevE))
      (fun n => eR (K.plOf i dc n)) := by
  intro l
  have hev := Formalism.RepresentationBoundsCohomology.JL.ev_equiv_triv r' χ (Γn i dc (K.colIdx i dc l)) evE hevE
  have hQ : ∀ (γ : ↥(Γn i dc (K.colIdx i dc l))) (m : ↥(Ideal.span {δO})),
      mkK (O := D.nd.O i) (Representation.trivial (D.nd.O i) ↥(Γn i dc (K.colIdx i dc l)) ↥(Ideal.span {δO}) γ m) =
        locRep (Representation.trivial (D.nd.O i) ↥(Γn i dc (K.colIdx i dc l)) ↥(Ideal.span {δO})) γ (mkK m) :=
    fun γ m => (locRep_mkK _ γ m).symm
  exact lift_integral_column i dc r eR hA hG (hnCol i dc l) (hcCol i dc l)
    (ρVP := locRep (resRep (uRep (D.nd.O i) (M := PE) r' χ) (Γn i dc (K.colIdx i dc l))))
    (ρVQ := locRep (Representation.trivial (D.nd.O i) ↥(Γn i dc (K.colIdx i dc l)) ↥(Ideal.span {δO})))
    (jP := mkK) (jQ := mkK) mkK_inj mkK_inj (fun γ m => (locRep_mkK _ γ m).symm) hQ mkK_span mkK_span
    (f0 := liftK (mkK ∘ₗ evE))
    (liftK_equiv _ _ (mkK ∘ₗ evE) (fun γ m => by rw [LinearMap.comp_apply, LinearMap.comp_apply, hev, hQ]))
    (fun m => liftK_mkK _ m) hev hevs (hemb l) (hMs l)

end Cols

section Cont

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem msCont_of (hr : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    MsCont i dc r hn := by
  intro x
  have hM := rTwO_cont D i r hr x
  refine continuous_matrix fun a b => ?_
  have h1 : Continuous fun g : Br.G D.nbr i _ hn =>
      rTwO D.nd i r x ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) a b :=
    (hM.matrix_elem a b).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i _ hn))
  have h2 : Continuous fun y : D.nd.O i => (((D.nbr i _ hn).eO y : ↥(OL (D.nbr i _ hn).LL)) :
      ↥(D.nbr i _ hn).LL.1) := continuous_subtype_val.comp (D.nbr i _ hn).eO_cont
  have h3 : Continuous fun y : ↥(D.nbr i _ hn).LL.1 => (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn).inc y :=
    Continuous.subtype_mk continuous_subtype_val _
  exact h3.comp (h2.comp h1)

end Cont

section Sel

theorem fin_sel {LL V : Type} [Field LL] [AddCommGroup V] [Module LL V] [FiniteDimensional LL V] {I : Type} {k : ℕ}
    (Ψ : I → V →ₗ[LL] (Fin k → LL)) (h : ∀ v, (∀ i, Ψ i v = 0) → v = 0) :
    ∃ (m : ℕ) (xs : Fin m → I), ∀ v, (∀ a, Ψ (xs a) v = 0) → v = 0 := by
  let f : I × Fin k → Module.Dual LL V := fun p => (LinearMap.proj p.2) ∘ₗ Ψ p.1
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent LL (Set.range f)
  have hfin : b.Finite := hli.setFinite
  have hpre : ∀ φ : b, ∃ p, f p = φ := fun φ => hbs φ.2
  haveI : Fintype b := hfin.fintype
  let eb := Fintype.equivFin b
  refine ⟨Fintype.card b, fun a => (Classical.choose (hpre (eb.symm a))).1, fun v hv => h v fun i => ?_⟩
  have hb : ∀ φ ∈ b, φ v = 0 := by
    intro φ hφ
    have hc := Classical.choose_spec (hpre (eb.symm (eb ⟨φ, hφ⟩)))
    have hψ : ((eb.symm (eb ⟨φ, hφ⟩) : b) : Module.Dual LL V) = φ := by rw [Equiv.symm_apply_apply]
    rw [← hψ, ← hc]
    show (Ψ _ v) _ = 0
    rw [hv (eb ⟨φ, hφ⟩)]
    rfl
  have hall : ∀ φ ∈ Submodule.span LL b, φ v = 0 := by
    intro φ hφ
    induction hφ using Submodule.span_induction with
    | mem x hx => exact hb x hx
    | zero => rfl
    | add x y _ _ hx hy => rw [LinearMap.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [LinearMap.smul_apply, hx, smul_zero]
  funext c
  exact hall (f (i, c)) (hspan ▸ Submodule.subset_span ⟨(i, c), rfl⟩)

end Sel

section EmbFam

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem embAt_of_fam {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {VP : Type} [AddCommGroup VP]
    [Module (FractionRing (D.nd.O i)) VP] [Module (D.nd.O i) VP] [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VP]
    (ρVP : Representation (D.nd.O i) ↥(Γn i dc n) VP)
    [FiniteDimensional (Br.LLw (D.nbr i _ hn)) (TrV (eK (D.nbr i _ hn)) VP)] {I : Type} (xx : I → D.nd.X i)
    (Ψ : I → TrV (eK (D.nbr i _ hn)) VP →ₗ[Br.LLw (D.nbr i _ hn)] (Fin D.R.nV → Br.LLw (D.nbr i _ hn)))
    (hinj : ∀ v, (∀ a, Ψ a v = 0) → v = 0)
    (heq : ∀ a g v, Ψ a (repL (eK (D.nbr i _ hn)) ρVP (Br.iota D.nbr i _ hn) g v) =
      (MsAt i dc r hn (xx a) g).mulVec (Ψ a v)) : EmbAt i dc r hn ρVP := by
  obtain ⟨m, xs, hxs⟩ := fin_sel Ψ hinj
  refine ⟨m, xx ∘ xs, LinearMap.pi fun a => Ψ (xs a), fun v w hvw => ?_, fun g v => funext fun a => heq _ g v⟩
  rw [← sub_eq_zero]
  refine hxs _ fun a => ?_
  rw [map_sub, sub_eq_zero]
  exact congrFun hvw a

end EmbFam

section Dd

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem chiInv_at (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    (g : GE D.nd) (x' : Dd.X') :
    ((((Dd.χ g)⁻¹ : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (((chiU D.nd i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
  have h1 : ((((Dd.χ g)⁻¹ : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' * (chiU D.nd i 1 g : D.nd.O i) = 1 := by
    have h0 : (((Dd.χ g)⁻¹ : (Dd.T')ˣ) : Dd.T') * (Dd.χ g : Dd.T') = 1 := Units.inv_mul _
    have := congrArg (fun f : Dd.T' => (f : Dd.X' → D.nd.O i) x') h0
    simp only [MulMemClass.coe_mul, OneMemClass.coe_one, Pi.mul_apply, Pi.one_apply] at this
    rwa [hχ g x'] at this
  exact Units.eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h1)

theorem uElt_at
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    (g : GE D.nd) (x' : Dd.X') :
    ((Formalism.NG.uElt Dd.r Dd.χ g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rTwO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) := by
  show (((((Dd.χ g)⁻¹ : (Dd.T')ˣ) : Dd.T') • Dd.r g : Dd.R') :
    Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' = _
  rw [hsm, hr', chiInv_at i Dd hχ]
  ext a b
  simp [rTwO, twistM, Matrix.map_apply, Matrix.smul_apply]

end Dd

section DdEmb

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem smul_mk {O M : Type} [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M] (m : M) (s : nonZeroDivisors O) :
    ((s : O) • LocalizedModule.mk m s : MK (O := O) M) = mkK m := by
  rw [LocalizedModule.smul'_mk]
  show _ = LocalizedModule.mk m 1
  rw [LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def]⟩

theorem smul_cancel {O A : Type} [CommRing O] [IsDomain O] [AddCommGroup A] [Module (FractionRing O) A] [Module O A]
    [IsScalarTower O (FractionRing O) A] (s : nonZeroDivisors O) {y z : A} (h : (s : O) • y = (s : O) • z) : y = z := by
  have hu := (Module.End.isUnit_iff _).1 (isUnit_end (V := A) s)
  apply hu.1
  simpa [Module.algebraMap_end_apply] using h

theorem msAt_apply {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i)
    (g : Br.G D.nbr i _ hn) (a b : Fin D.R.nV) :
    MsAt i dc r hn x g a b = eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      (rTwO D.nd i r x ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) a b)) := by
  rw [← heO_br i dc hn]
  rfl

theorem embAt_Dd {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    {Pe : Type} [AddCommGroup Pe] [Module Dd.R' Pe] [Module (D.nd.O i) Pe] [SMulCommClass Dd.R' (D.nd.O i) Pe]
    [Module.Finite (D.nd.O i) Pe] [Module.Free (D.nd.O i) Pe]
    (κ : Pe →ₗ[D.nd.O i] (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))))
    (hκ : Function.Injective κ)
    (hκa : ∀ (a : Dd.R') p, κ (a • p) = (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * κ p) :
    EmbAt i dc r hn (locRep (resRep (uRep (D.nd.O i) (M := Pe) Dd.r Dd.χ) (Γn i dc n))) := by
  set ρP := resRep (uRep (D.nd.O i) (M := Pe) Dd.r Dd.χ) (Γn i dc n) with hρP
  set e := eK (D.nbr i _ hn)
  let Λ := liftK (V := Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) κ
  have hΛs : ∀ m (s : nonZeroDivisors (D.nd.O i)), (s : D.nd.O i) • Λ (LocalizedModule.mk m s) = κ m := by
    intro m s
    rw [← map_smul, smul_mk, liftK_mkK]
  have hΛi : ∀ v, Λ v = 0 → v = 0 := by
    intro v hv
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h1 := hΛs m s
      rw [hv, smul_zero] at h1
      rw [hκ (h1.symm.trans (map_zero κ).symm), LocalizedModule.zero_mk]
  have hΛe : ∀ (γ : ↥(Γn i dc n)) v, Λ (locRep ρP γ v) =
      ((Formalism.NG.uElt Dd.r Dd.χ (γ : GE D.nd) : Dd.R') :
        Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * Λ v := by
    intro γ v
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h0 : locRep ρP γ (LocalizedModule.mk m s) = LocalizedModule.mk (ρP γ m) s := LocalizedModule.map_mk _ _ _ _
      rw [h0]
      apply smul_cancel s
      rw [hΛs, ← mul_smul_comm, hΛs]
      exact hκa _ m
  let Ψ : Dd.X' × Fin D.R.nV → TrV e (MK (O := D.nd.O i) Pe) →ₗ[Br.LLw (D.nbr i _ hn)]
      (Fin D.R.nV → Br.LLw (D.nbr i _ hn)) := fun q =>
    { toFun := fun v a => e ((Λ (untr e v)) q.1 a q.2)
      map_add' := fun v w => funext fun a => by
        show e ((Λ (untr e v + untr e w)) q.1 a q.2) = _
        rw [map_add (f := _)]
        simp [map_add (f := _)]
      map_smul' := fun c v => funext fun a => by
        show e ((Λ (e.symm c • untr e v)) q.1 a q.2) = c * e ((Λ (untr e v)) q.1 a q.2)
        rw [smulK]
        simp [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul] }
  haveI : FiniteDimensional (Br.LLw (D.nbr i _ hn)) (TrV e (MK (O := D.nd.O i) Pe)) :=
    finDim_of_lat (Ow := Br.Ow (D.nbr i _ hn)) (Qp := ℚ_[D.nd.l i])
      (latOf e (D.nbr i _ hn).eO mkK (Br.iota D.nbr i _ hn) (heO_br i dc hn) (locRep ρP) ρP mkK_inj
        (fun γ m => (locRep_mkK _ γ m).symm) mkK_span)
  refine embAt_of_fam i dc r hn _ (fun q => Dd.p q.1) Ψ (fun v hv => ?_) (fun q g v => ?_)
  · have h0 : Λ (untr e v) = 0 := by
      funext x'
      ext a b
      have := congrFun (hv (x', b)) a
      simpa [Ψ] using this
    exact hΛi _ h0
  · funext a
    have key : ∀ γ : ↥(Γn i dc n), (γ : GE D.nd) = ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) →
        e ((Λ (locRep ρP γ (untr e v))) q.1 a q.2) = (MsAt i dc r hn (Dd.p q.1) g).mulVec (Ψ q v) a := by
      intro γ hγ

      rw [hΛe, Pi.mul_apply, hγ, uElt_at i r Dd hr' hsm hχ, Matrix.mul_apply, map_sum]
      simp only [Matrix.mulVec, dotProduct, msAt_apply]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp [Ψ, Matrix.map_apply, map_mul]
      exact Or.inl rfl
    exact key (Br.iota D.nbr i _ hn g) rfl

end DdEmb

section Final

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem ringDef_lift {T : Subalgebra (D.nd.O i) (D.nd.X i → D.nd.O i)} {π : D.nd.X i} {ε : GE D.nd →* (D.nd.O i)ˣ}
    {g0 : GE D.nd} {eB e₁ s : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) T (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) ε g0 eB e₁ s Dd) :
    (∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) ∧
    (∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x') ∧
    (∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i)) :=
  ⟨hD.2.2.2.2.2.2.1, hD.2.2.2.2.2.2.2.2.1, hD.2.2.2.2.2.2.2.2.2.2.2.1⟩

theorem liftCol_eve_Dd (eR : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (hA : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc eR) (hG : K.SelfGood i)
    (hC : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
    {T : Subalgebra (D.nd.O i) (D.nd.X i → D.nd.O i)} {π : D.nd.X i} {ε : GE D.nd →* (D.nd.O i)ˣ}
    {g0 : GE D.nd} {eB e₁ s : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) T (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) ε g0 eB e₁ s Dd)
    {Pe L V : Type} [AddCommGroup Pe] [Module Dd.R' Pe] [Module (D.nd.O i) Pe] [SMulCommClass Dd.R' (D.nd.O i) Pe]
    [Module.Finite (D.nd.O i) Pe] [Module.Free (D.nd.O i) Pe]
    [AddCommGroup L] [Module Dd.R' L] [Module (D.nd.O i) L] [SMulCommClass Dd.R' (D.nd.O i) L]
    [Module.Finite (D.nd.O i) L] [Module.Free (D.nd.O i) L]
    [AddCommGroup V] [Module Dd.R' V] [Module (D.nd.O i) V] [Module (FractionRing (D.nd.O i)) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] [SMulCommClass Dd.R' (FractionRing (D.nd.O i)) V]
    (κ : Pe →ₗ[D.nd.O i] (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))))
    (hκ : Function.Injective κ)
    (hκa : ∀ (a : Dd.R') p, κ (a • p) = (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * κ p)
    (ince : Pe →ₗ[Dd.R'] Dd.R') (v₁ : L) (eve : Pe →ₗ[D.nd.O i] L) (heve : ∀ a, eve a = ince a • v₁)
    (hevs : Function.Surjective eve)
    (iL : L →ₗ[D.nd.O i] V) (hiL : Function.Injective iL) (hiLeq : ∀ (a : Dd.R') m, iL (a • m) = a • iL m)
    (hspL : ∀ v : V, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m, iL m = c • v) :
    LiftCol i dc (Hfe₁ i dc Dd.r Dd.χ) (Ff i dc Dd.r Dd.χ iL)
      (fun l => Formalism.RepresentationBoundsCohomology.JL.mapH1 _ _ eve (Formalism.RepresentationBoundsCohomology.JL.ev_equiv Dd.r Dd.χ (Γn i dc (K.colIdx i dc l)) ince v₁ eve heve))
      (fun n => eR (K.plOf i dc n)) := by
  obtain ⟨hr', hsm, hχ⟩ := ringDef_lift i r Dd hD
  exact liftCol_eve i dc r Dd.r Dd.χ eR hA hG ince v₁ eve heve hevs iL hiL hiLeq hspL
    (fun l => embAt_Dd i dc r Dd (hnCol i dc l) hr' hsm hχ κ hκ hκa) (fun l => msCont_of i dc r hC (hnCol i dc l))

theorem liftCol_evE_Dd (eR : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (hA : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc eR) (hG : K.SelfGood i)
    (hC : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
    {T : Subalgebra (D.nd.O i) (D.nd.X i → D.nd.O i)} {π : D.nd.X i} {ε : GE D.nd →* (D.nd.O i)ˣ}
    {g0 : GE D.nd} {eB e₁ s : D.nd.X i → Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)}
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) T (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) ε g0 eB e₁ s Dd)
    (δO : D.nd.O i) [Module.Finite (D.nd.O i) ↥(Ideal.span {δO})] [Module.Free (D.nd.O i) ↥(Ideal.span {δO})]
    {PE : Type} [AddCommGroup PE] [Module Dd.R' PE] [Module (D.nd.O i) PE] [SMulCommClass Dd.R' (D.nd.O i) PE]
    [Module.Finite (D.nd.O i) PE] [Module.Free (D.nd.O i) PE]
    (κ : PE →ₗ[D.nd.O i] (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))))
    (hκ : Function.Injective κ)
    (hκa : ∀ (a : Dd.R') p, κ (a • p) = (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * κ p)
    (evE : PE →ₗ[D.nd.O i] ↥(Ideal.span {δO})) (hevE : ∀ g a, evE (uElt Dd.r Dd.χ g • a) = evE a)
    (hevs : Function.Surjective evE) :
    LiftCol i dc (Hfe₁ i dc Dd.r Dd.χ) (HfE₂ i dc δO)
      (fun l => Formalism.RepresentationBoundsCohomology.JL.mapH1 _ _ evE (Formalism.RepresentationBoundsCohomology.JL.ev_equiv_triv Dd.r Dd.χ (Γn i dc (K.colIdx i dc l)) evE hevE))
      (fun n => eR (K.plOf i dc n)) := by
  obtain ⟨hr', hsm, hχ⟩ := ringDef_lift i r Dd hD
  exact liftCol_evE i dc r Dd.r Dd.χ eR hA hG δO evE hevE hevs
    (fun l => embAt_Dd i dc r Dd (hnCol i dc l) hr' hsm hχ κ hκ hκa) (fun l => msCont_of i dc r hC (hnCol i dc l))

end Final

section Inst

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

def kappaL (x : Dd.R') :
    K.LeftId (D.nd.O i) x →ₗ[D.nd.O i] (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) where
  toFun p := ((K.incl (D.nd.O i) x p : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i)))
  map_add' p q := by rw [map_add (f := _)]; rfl
  map_smul' c p := rfl

theorem kappaL_inj (x : Dd.R') : Function.Injective (kappaL i Dd x) := by
  intro p q h
  exact Subtype.ext (Subtype.ext h)

theorem kappaL_mul (x : Dd.R') (a : Dd.R') (p : K.LeftId (D.nd.O i) x) :
    kappaL i Dd x (a • p) = (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) * kappaL i Dd x p :=
  rfl

theorem ideal_finite (δO : D.nd.O i) : Module.Finite (D.nd.O i) ↥(Ideal.span {δO}) :=
  Module.Finite.iff_fg.2 (Submodule.fg_span (Set.finite_singleton δO))

theorem ideal_free [IsDiscreteValuationRing (D.nd.O i)] (δO : D.nd.O i) : Module.Free (D.nd.O i) ↥(Ideal.span {δO}) := by
  haveI := ideal_finite i δO
  exact Module.free_of_finite_type_torsion_free'

end Inst

section LeftFin

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem leftId_finite [Module.Finite (D.nd.O i) Dd.R'] (x : Dd.R') : Module.Finite (D.nd.O i) (K.LeftId (D.nd.O i) x) := by
  let S : Submodule (D.nd.O i) Dd.R' := (Submodule.span Dd.R' ({x} : Set Dd.R')).restrictScalars (D.nd.O i)
  haveI : Module.Finite (D.nd.O i) S := Module.IsNoetherian.finite (D.nd.O i) S
  let f : S ≃ₗ[D.nd.O i] K.LeftId (D.nd.O i) x :=
    { toFun := fun a => K.lmk (D.nd.O i) x a.1 a.2
      invFun := fun p => ⟨K.lv (D.nd.O i) x p, K.lv_mem (D.nd.O i) x p⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Module.Finite.equiv f

theorem leftId_free [Module.Finite (D.nd.O i) Dd.R'] (x : Dd.R') : Module.Free (D.nd.O i) (K.LeftId (D.nd.O i) x) := by
  haveI := leftId_finite i Dd x
  haveI : NoZeroSMulDivisors (D.nd.O i) (K.LeftId (D.nd.O i) x) :=
    ⟨fun {c p} h => by
      by_cases hc : c = 0
      · exact Or.inl hc
      right
      apply kappaL_inj i Dd x
      rw [map_zero]
      apply smul_cancel (⟨c, mem_nonZeroDivisors_of_ne_zero hc⟩ : nonZeroDivisors (D.nd.O i))
      show c • kappaL i Dd x p = c • 0
      rw [← map_smul, h, map_zero, smul_zero]⟩
  exact Module.free_of_finite_type_torsion_free'

end LeftFin

section LatMInst

theorem latM_finite (O : Type) [CommRing O] {R : Type} [Ring R] (n : Type) [Fintype n] [DecidableEq n]
    (ρ : R →+* Matrix n n O) : Module.Finite O (Formalism.RepresentationBoundsCohomology.SF.LatM O O n ρ) :=
  inferInstanceAs (Module.Finite O (n → O))

theorem latM_free (O : Type) [CommRing O] {R : Type} [Ring R] (n : Type) [Fintype n] [DecidableEq n]
    (ρ : R →+* Matrix n n O) : Module.Free O (Formalism.RepresentationBoundsCohomology.SF.LatM O O n ρ) :=
  inferInstanceAs (Module.Free O (n → O))

end LatMInst

end Formalism.MainNotions.N.KLift
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB

section Eps

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

def epsHom (e : ℕ) : G →* Matrix (Fin 1) (Fin 1) LL where
  toFun := Formalism.MainNotions.N.epsTw PD (LL := LL) e
  map_one' := by
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp [Formalism.MainNotions.N.epsTw]
  map_mul' g h := by
    ext a b
    have ha : a = 0 := Subsingleton.elim _ _
    have hb : b = 0 := Subsingleton.elim _ _
    subst ha hb
    simp [Formalism.MainNotions.N.epsTw, Matrix.mul_apply, mul_pow]
    ring

theorem matRep_eps (e : ℕ) (g : G) (v : Fin 1 → LL) :
    Formalism.MainNotions.N.matRep (epsHom PD (LL := LL) e) g v =
      fun _ => (algebraMap Qp LL (((PD.χ g)⁻¹ : Qpˣ) : Qp)) ^ e * v 0 := by
  funext j
  change Matrix.mulVec (Formalism.MainNotions.N.epsTw PD (LL := LL) e g) v j = _
  simp [Matrix.mulVec, dotProduct, Formalism.MainNotions.N.epsTw]

variable {PD}

@[reducible] def twLat (hinj : Function.Injective (algebraMap O LL)) (ε' : G → O)
    (hε : ∀ g, algebraMap O LL (ε' g) = algebraMap Qp LL (((PD.χ g)⁻¹ : Qpˣ) : Qp)) (e : ℕ)
    (hcont : Continuous fun g => (algebraMap O LL (ε' g)) ^ e) : TwLat PD LL O e where
  V := Fin 1 → LL
  ρ := Formalism.MainNotions.N.matRep (epsHom PD e)
  L :=
    { T := Formalism.MainNotions.N.stdG O LL 1
      stable := by
        intro g x hx
        obtain ⟨u, rfl⟩ := hx
        refine ⟨fun _ => (ε' g) ^ e * u 0, ?_⟩
        rw [matRep_eps]
        funext j
        simp only [LinearMap.compLeft_apply, Function.comp_apply, Algebra.linearMap_apply, map_mul, map_pow, hε]
      fg := (Formalism.MainNotions.N.stdLatG hinj (1 : G →* Matrix (Fin 1) (Fin 1) O)).fg
      free := (Formalism.MainNotions.N.stdLatG hinj (1 : G →* Matrix (Fin 1) (Fin 1) O)).free
      span := (Formalism.MainNotions.N.stdLatG hinj (1 : G →* Matrix (Fin 1) (Fin 1) O)).span }
  cont := by
    intro x
    have h : (fun g => Formalism.MainNotions.N.matRep (epsHom PD (LL := LL) e) g x) =
        fun g => fun _ : Fin 1 => (algebraMap O LL (ε' g)) ^ e * x 0 := by
      funext g
      rw [matRep_eps, hε]
    rw [h]
    exact continuous_pi fun _ => hcont.mul continuous_const
  mat := by
    refine ⟨LinearEquiv.refl LL _, fun g v => rfl, fun v => ⟨?_, ?_⟩⟩
    · rintro ⟨u, rfl⟩ j
      exact ⟨u j, rfl⟩
    · intro hv
      choose u hu using hv
      exact ⟨u, funext fun j => hu j⟩

theorem actD_twLat (hinj : Function.Injective (algebraMap O LL)) (ε' : G → O)
    (hε : ∀ g, algebraMap O LL (ε' g) = algebraMap Qp LL (((PD.χ g)⁻¹ : Qpˣ) : Qp)) (e : ℕ)
    (hcont : Continuous fun g => (algebraMap O LL (ε' g)) ^ e) (h : G)
    (x : (twLat hinj ε' hε e hcont).V ⧸ (twLat hinj ε' hε e hcont).L.T) :
    actD (twLat hinj ε' hε e hcont).L h x = (ε' h ^ e) • x := by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    unfold actD
    refine (congrArg Submodule.Quotient.mk
      (?_ : (twLat hinj ε' hε e hcont).ρ h v = (ε' h ^ e) • v)).trans
      (Submodule.Quotient.mk_smul _ _ _)
    funext j
    show Formalism.MainNotions.N.matRep (epsHom PD (LL := LL) e) h v j = (ε' h ^ e) • v j
    rw [matRep_eps, Algebra.smul_def, map_pow, hε, Subsingleton.elim j 0]

end Eps

section KO

variable {O' : Type} [CommRing O'] [IsDomain O'] {O LL : Type} [CommRing O] [Field LL] [Algebra O LL]
  (σ : O' ≃+* O) (eK : FractionRing O' ≃+* LL)
  (heK : ∀ c : O', eK (algebraMap O' (FractionRing O') c) = algebraMap O LL (σ c))

def kVec : FractionRing O' →ₛₗ[σ.toRingHom] (Fin 1 → LL) where
  toFun x := fun _ => eK x
  map_add' x y := by
    funext j
    simp
  map_smul' c x := by
    funext j
    simp only [Algebra.smul_def, map_mul, heK, Pi.smul_apply]
    rfl

def vecK : (Fin 1 → LL) →ₛₗ[σ.symm.toRingHom] FractionRing O' where
  toFun v := eK.symm (v 0)
  map_add' u v := by simp
  map_smul' c v := by
    apply eK.injective
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, RingEquiv.apply_symm_apply, heK]
    exact congrArg (fun y => algebraMap O LL y * v 0) (σ.apply_symm_apply c).symm

theorem kVec_le : (1 : Submodule O' (FractionRing O')) ≤ (Formalism.MainNotions.N.stdG O LL 1).comap (kVec σ eK heK) := by
  intro x hx
  obtain ⟨c, rfl⟩ := Submodule.mem_one.1 hx
  rw [Submodule.mem_comap]
  refine ⟨fun _ => σ c, ?_⟩
  funext j
  show algebraMap O LL (σ c) = eK (algebraMap O' (FractionRing O') c)
  exact (heK c).symm

def koTo : KO O' →ₛₗ[σ.toRingHom] ((Fin 1 → LL) ⧸ Formalism.MainNotions.N.stdG O LL 1) :=
  Submodule.mapQ _ _ (kVec σ eK heK) (kVec_le σ eK heK)

def koEquiv : KO O' ≃+ ((Fin 1 → LL) ⧸ Formalism.MainNotions.N.stdG O LL 1) where
  toFun := koTo σ eK heK
  invFun := Submodule.mapQ _ _ (vecK σ eK heK) (by
    rintro _ ⟨u, rfl⟩
    refine Submodule.mem_one.2 ⟨σ.symm (u 0), ?_⟩
    apply eK.injective
    show eK (algebraMap O' (FractionRing O') (σ.symm (u 0))) = eK (eK.symm (algebraMap O LL (u 0)))
    rw [heK, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply])
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      show Submodule.Quotient.mk (eK.symm (eK x)) = _
      rw [RingEquiv.symm_apply_apply]
  right_inv v := by
    induction v using Submodule.Quotient.induction_on with
    | H v =>
      show Submodule.Quotient.mk (fun _ => eK (eK.symm (v 0))) = _
      congr 1
      funext j
      rw [RingEquiv.apply_symm_apply, Subsingleton.elim j 0]
  map_add' x y := map_add _ x y

theorem koEquiv_smul (a : O') (x : KO O') : koEquiv σ eK heK (a • x) = σ a • koEquiv σ eK heK x := by
  show koTo σ eK heK (a • x) = σ a • koTo σ eK heK x
  exact (koTo σ eK heK).map_smulₛₗ a x

end KO

end Formalism.MainNotions.N.K.TBb

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.ShaT
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

def CycW : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (g : Dw i dc (idx i dc w)),
    (((Br.PD D.loc D.nbr i w hw).χ (eW i dc hw g) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) =
      (((cycE i (g : GE D.nd) : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) : ℚ_[D.nd.l i])

def sE (e : ℕ) (g : GE D.nd) : D.nd.O i :=
  ((((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp (cycE i ^ (-(e : ℤ)))) g : (D.nd.O i)ˣ) : D.nd.O i)

def epsL {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (h : Br.G D.nbr i w hw) : Br.Ow (D.nbr i w hw) :=
  (D.nbr i w hw).eO (algebraMap ℤ_[D.nd.l i] (D.nd.O i) (((cycE i ((eW i dc hw).symm h : GE D.nd))⁻¹ : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]))

end Rec

section Dict

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem algZ_LL {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (z : ℤ_[D.nd.l i]) :
    algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) ((D.nbr i w hw).eO (algebraMap ℤ_[D.nd.l i] (D.nd.O i) z)) =
      algebraMap ℚ_[D.nd.l i] (Br.LLw (D.nbr i w hw)) (z : ℚ_[D.nd.l i]) := by
  rw [(D.nbr i w hw).eO_alg z, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply ℤ_[D.nd.l i] ℚ_[D.nd.l i] (Br.LLw (D.nbr i w hw))]
  rfl

theorem epsL_eq (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (h : Br.G D.nbr i w hw) :
    algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h) =
      algebraMap ℚ_[D.nd.l i] (Br.LLw (D.nbr i w hw))
        ((((Br.PD D.loc D.nbr i w hw).χ h)⁻¹ : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) := by
  have hc := hcyc w hw ((eW i dc hw).symm h)
  rw [MulEquiv.apply_symm_apply] at hc
  rw [epsL, algZ_LL, Units.val_inv_eq_inv_val, hc]
  congr 1
  exact eq_inv_of_mul_eq_one_left (by rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one])

variable [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def uRec {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : Fin (D.R.t + 1))
    (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i)) :
    Mc i Dd c ≃+ ((Fin 1 → Br.LLw (D.nbr i w hw)) ⧸ Formalism.MainNotions.N.stdG (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) 1) :=
  φ.toAddEquiv.trans (koEquiv (D.nbr i w hw).eO (Formalism.MainNotions.N.KHf.eK (D.nbr i w hw)) (fun c => Br.toLLK_alg (D.nbr i w hw) c))

theorem uRec_apply {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : Fin (D.R.t + 1))
    (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i)) (m : Mc i Dd c) :
    uRec i Dd hw c φ m =
      koEquiv (D.nbr i w hw).eO (Formalism.MainNotions.N.KHf.eK (D.nbr i w hw)) (fun c => Br.toLLK_alg (D.nbr i w hw) c) (φ m) :=
  rfl

end Dict

section Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem yLoc_of
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (c : Fin (D.R.t + 1)) (n : ℕ) :
    YLoc (O := D.nd.O i) (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc n) := by
  intro ψ _
  let _ := Formalism.MainNotions.N.K.Topo.fracTopology (D.nd.O i)
  let _ := Formalism.MainNotions.N.K.Topo.rTopology (D.nd.O i) Dd.R'
  have := Formalism.MainNotions.N.K.Topo.fracTop_addGroup_O i
  have := Formalism.MainNotions.N.K.Topo.fracTop_smul_O i
  have := Formalism.MainNotions.N.K.Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  have := Formalism.MainNotions.N.K.Topo.rTop_constSMul_RD i Dd
  have := Formalism.MainNotions.N.K.Topo.rTop_mul_RD i r π g0 eB e₁ s Dd hD
  have htors (m : Mc i Dd c) : ∃ a : D.nd.O i, a ≠ 0 ∧ a • m = 0 := by
    have h1 : ∀ y : KO (D.nd.O i), ∃ a : D.nd.O i, a ≠ 0 ∧ a • y = 0 := by
      intro y
      induction y using Submodule.Quotient.induction_on with
      | H x =>
        obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (D.nd.O i)) x
        refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
        exact ⟨a, by rw [Algebra.smul_def, mul_comm]; exact hab.symm⟩
    choose a ha0 ha using fun j => h1 (m j)
    refine ⟨∏ j, a j, Finset.prod_ne_zero_iff.2 fun j _ => ha0 j, ?_⟩
    funext j
    change (∏ j, a j) • m j = 0
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_smul, ha j, smul_zero]
  have hA := Formalism.MainNotions.N.K.Topo.fgTop_RD i r π g0 eB e₁ s Dd hD
  have hfg : ReciprocityTheory.ChartRestriction.T2.IsFGTop (D.nd.O i) (Ymod Dd.r Dd.χ Dd.E) := by
    have := hA.fg
    have := hA.t2
    have := hA.csmul
    refine ⟨?_, inferInstance, ?_⟩
    · exact Module.Finite.of_injective ((Ymod Dd.r Dd.χ Dd.E).subtype.restrictScalars (D.nd.O i)) Subtype.val_injective
    · exact ⟨Continuous.subtype_mk (f := fun q : (D.nd.O i) × (Ymod Dd.r Dd.χ Dd.E) => q.1 • (q.2 : Dd.R'))
        (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  obtain ⟨a, ha, hka⟩ : ∃ a : D.nd.O i, a ≠ 0 ∧ ∀ y : Ymod Dd.r Dd.χ Dd.E, a • ψ y = 0 := by
    obtain ⟨t, ht⟩ := hfg.fg.fg_top
    choose f hf0 hf using fun y : Ymod Dd.r Dd.χ Dd.E => htors (ψ y)
    refine ⟨∏ y ∈ t, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), fun y => ?_⟩
    have hy : y ∈ Submodule.span (D.nd.O i) (t : Set (Ymod Dd.r Dd.χ Dd.E)) := ht ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨b, hb⟩ := Finset.dvd_prod_of_mem f hx
      rw [hb, mul_comm, mul_smul, hf, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]
    | smul b x _ hx => rw [map_smul, smul_comm, hx, smul_zero]
  have continuous_of_isLocalHom {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
      [TopologicalSpace A] [TopologicalSpace B] [IsTopologicalRing A] [IsTopologicalRing B]
      (hA : IsAdic (IsLocalRing.maximalIdeal A)) (hB : IsAdic (IsLocalRing.maximalIdeal B)) (φ : A →+* B)
      [IsLocalHom φ] : Continuous φ := by
    refine continuous_of_continuousAt_zero φ ?_
    rw [ContinuousAt, map_zero]
    intro s hs
    obtain ⟨n, hn⟩ := (isAdic_iff.1 hB).2 s hs
    have hopen := (isAdic_iff.1 hA).1 n
    rw [Filter.mem_map]
    filter_upwards [hopen.mem_nhds (Ideal.zero_mem _)] with x hx
    apply hn
    have hle : (IsLocalRing.maximalIdeal A).map φ ≤ IsLocalRing.maximalIdeal B :=
      Ideal.map_le_iff_le_comap.2 fun a ha => map_nonunit φ a ha
    have h1 : φ x ∈ ((IsLocalRing.maximalIdeal A) ^ n).map φ := Ideal.mem_map_of_mem φ hx
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono hle n h1
  
  have l_mem_max : ((D.nd.l i : ℕ) : D.nd.O i) ∈ IsLocalRing.maximalIdeal (D.nd.O i) := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    have h2 := Formalism.MainNotions.SumRepresentations.norm_iotaOQ_unit D.nd D.naut i u
    have h3 := Formalism.MainNotions.SumRepresentations.norm_iotaOQ_l D.nd D.naut i
    rw [hu] at h2
    rw [h2] at h3
    exact lt_irrefl _ h3
  have l_ne_zero : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 :=
    Formalism.MainNotions.SumRepresentations.natCast_ne_zero_O D.nd i (D.nd.l i) (D.nd.lPrime i).out.ne_zero
  have isLocalHom_alg : IsLocalHom (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
    refine ⟨fun z hz => ?_⟩
    by_contra hn
    have h1 : z ∈ IsLocalRing.maximalIdeal ℤ_[D.nd.l i] := hn
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
    obtain ⟨y, rfl⟩ := h1
    rw [map_mul, map_natCast] at hz
    exact (IsLocalRing.mem_maximalIdeal _).1 (l_mem_max) (isUnit_of_mul_isUnit_left hz)
  have continuous_alg : Continuous (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
    haveI := isLocalHom_alg
    exact continuous_of_isLocalHom (ReciprocityTheory.ChartRestriction.T2.padicCoeff_padicInt (p := D.nd.l i)).adic (D.nd.O_adic i) _
  have compact_O : CompactSpace (D.nd.O i) := by
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ_[D.nd.l i] (D.nd.O i)
    have hc : Continuous f := by
      have : (f : (Fin n → ℤ_[D.nd.l i]) → D.nd.O i) = fun v =>
          ∑ k, algebraMap ℤ_[D.nd.l i] (D.nd.O i) (v k) * f (fun j => if k = j then 1 else 0) := by
        funext v
        rw [LinearMap.pi_apply_eq_sum_univ f v]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Algebra.smul_def]
      rw [this]
      fun_prop (disch := exact continuous_alg)
    exact hf.compactSpace hc
  have t2Space_nd_O : T2Space (D.nd.O i) := by
    have hopen : ∀ n : ℕ, IsOpen ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) : Set (D.nd.O i)) :=
      (isAdic_iff.1 (D.nd.O_adic i)).1
    have hclosed : ∀ n : ℕ, IsClosed ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) : Set (D.nd.O i)) :=
      fun n => AddSubgroup.isClosed_of_isOpen (Submodule.toAddSubgroup (IsLocalRing.maximalIdeal (D.nd.O i) ^ n)) (hopen n)
    have h0 : ({0} : Set (D.nd.O i)) =
        ⋂ n : ℕ, ((IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) : Set (D.nd.O i)) := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_iInter, SetLike.mem_coe]
      constructor
      · rintro rfl n
        exact Ideal.zero_mem _
      · intro h
        have h1 : x ∈ (⨅ n : ℕ, IsLocalRing.maximalIdeal (D.nd.O i) ^ n : Ideal (D.nd.O i)) := by
          rw [Ideal.mem_iInf]; exact h
        rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (IsLocalRing.maximalIdeal.isMaximal _).ne_top] at h1
        exact h1
    have : IsClosed ({0} : Set (D.nd.O i)) := by
      rw [h0]; exact isClosed_iInter hclosed
    haveI : T1Space (D.nd.O i) := IsTopologicalAddGroup.t1Space _ this
    infer_instance
  have padicCoeff_O : ReciprocityTheory.ChartRestriction.T2.PadicCoeff (D.nd.l i) (D.nd.O i) :=
    ⟨D.nd.trO i, compact_O, t2Space_nd_O, D.nd.O_adic i, l_mem_max, l_ne_zero⟩
  have hopen := hfg.isOpen_mulSub padicCoeff_O ha
  have hy : Continuous fun g => yY Dd.r Dd.χ Dd.E g :=
    Continuous.subtype_mk (f := fun g => (uElt Dd.r Dd.χ g - 1) * Dd.E)
      (((Formalism.MainNotions.N.K.Topo.uElt_cont i r π g0 eB e₁ s Dd hD hc).sub continuous_const).mul continuous_const) _
  set_option synthInstance.maxHeartbeats 200000 in
  have h : IsLocallyConstant fun g => ψ (yY Dd.r Dd.χ Dd.E g) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro g₀
    refine ⟨(fun g => yY Dd.r Dd.χ Dd.E g - yY Dd.r Dd.χ Dd.E g₀) ⁻¹' _, hopen.preimage (hy.sub continuous_const), ?_, ?_⟩
    · show yY Dd.r Dd.χ Dd.E g₀ - yY Dd.r Dd.χ Dd.E g₀ ∈ Formalism.RepresentationBoundsCohomology.LOC.mulSub a (Ymod Dd.r Dd.χ Dd.E)
      rw [sub_self]
      exact zero_mem _
    · rintro g ⟨z, hz⟩
      have hz' : a • z = yY Dd.r Dd.χ Dd.E g - yY Dd.r Dd.χ Dd.E g₀ := hz
      have h1 : ψ (yY Dd.r Dd.χ Dd.E g - yY Dd.r Dd.χ Dd.E g₀) = 0 := by
        rw [← hz', map_smul, hka]
      rw [map_sub, sub_eq_zero] at h1
      exact h1
  exact h.comp_continuous continuous_subtype_val

end Loc

end Formalism.MainNotions.N.K.TBb

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.ShaT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Eval
variable {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {π : D.nd.X i} {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
  {Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)}

structure EvS (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
    (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)) : Prop where
  r_eval : ∀ (g : GE D.nd) (x' : Dd.X'),
    ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))
  chi_eval : ∀ (g : GE D.nd) (x' : Dd.X'),
    (((Dd.χ g : Dd.T'ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = ((D.nd.chi i 1 g : (D.nd.O i)ˣ) : D.nd.O i)
  smul_eval : ∀ (f : Dd.T') (a : Dd.R') (x' : Dd.X'),
    ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x'
  blk_smul : ∀ (f : Dd.T') k (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k), f • m = ((f : Dd.X' → D.nd.O i) Dd.π') • m
  ρπ_eval : ∀ a : Dd.R', (Dd.ρπ a).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) =
    (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) Dd.π'
  ρk_eval : ∀ (a : Dd.R') k, (Dd.ρπ a).toSquareBlock (RepresentationBoundsCohomology.blk D.R) k = Dd.ρk k a
  pπ : Dd.p Dd.π' = π

theorem evS_of (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    EvS r π Dd := by
  obtain ⟨-, -, -, -, h4, -, h6, -, h8, -, h10, h11, -, -, -, -, h16, h17, -⟩ := hD
  exact ⟨fun g x' => h6 g x', fun g x' => h11 g x', h8, h10, h16, h17, h4⟩

end Eval

section GlobalTheory
variable {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} {π : D.nd.X i}
  {Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)}

theorem blkS_eq {c' : Fin D.R.t} (a : Fin D.R.nV) (h : RepresentationBoundsCohomology.blk D.R a = c'.succ) :
    a = (Fin.natAdd D.R.r c' : Fin (D.R.r + D.R.t)) := by
  have h' := h
  simp only [Formalism.MainNotions.N.RepresentationBoundsCohomology.blk, Formalism.MainNotions.N.RepresentationBoundsCohomology.blkG] at h'
  split_ifs at h' with h1
  · exact absurd h'.symm (Fin.succ_ne_zero c')
  · apply Fin.ext
    have h2 := congrArg Fin.val h'
    simp only [Fin.val_succ] at h2
    simp only [Fin.coe_natAdd]
    omega

theorem blkS_act (c' : Fin D.R.t) (a : Dd.R') (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ) (hE : EvS r π Dd) :
    a • m = (Dd.ρπ a (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c')) • m := by
  have hb : RepresentationBoundsCohomology.blk D.R (Fin.natAdd D.R.r c') = c'.succ := by
    simp only [Formalism.MainNotions.N.RepresentationBoundsCohomology.blk, Formalism.MainNotions.N.RepresentationBoundsCohomology.blkG]
    rw [dite_eq_right (by simp)]
    ext
    simp
  have hu : ∀ y : {x : Fin D.R.nV // RepresentationBoundsCohomology.blk D.R x = c'.succ}, y = ⟨Fin.natAdd D.R.r c', hb⟩ :=
    fun y => Subtype.ext (blkS_eq y.1 y.2)
  funext j
  show ∑ k, (Dd.ρk c'.succ a) j k • m k =
    (Dd.ρπ a (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c')) • m j
  rw [Fintype.sum_eq_single j (fun k hk => absurd ((hu k).trans (hu j).symm) hk),
    ← hE.ρk_eval a c'.succ, hu j]
  rfl

end GlobalTheory

section LocQ
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

variable {i r ρ π Dd} in
theorem rblkS (hE : EvS r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c' : Fin D.R.t) (g : GE D.nd) :
    Dd.ρπ (Dd.r g) (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c') =
      ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  have h3 : (Dd.ρπ (Dd.r g)).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) =
      (rO D.nd i r π g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) := by
    rw [hE.ρπ_eval, hE.r_eval, hE.pπ]
  have h4 := congrFun (congrFun h3 (Fin.natAdd D.R.r c')) (Fin.natAdd D.R.r c')
  have h5 : Dd.ρπ (Dd.r g) (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c') =
      rO D.nd i r π g (Fin.natAdd D.R.r c') (Fin.natAdd D.R.r c') :=
    IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)) h4
  rw [h5]
  exact hN.2.1 g c'

variable {i r ρ π Dd} in
theorem rS_act (hE : EvS r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c' : Fin D.R.t) (g : GE D.nd)
    (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ) :
    Dd.r g • m = ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) • m := by
  rw [blkS_act c' (Dd.r g) m hE, rblkS hE hN c' g]

end LocQ

end Formalism.MainNotions.N.K.ShaT

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.ShaT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.MainNotions.N.K.QS Formalism.RepresentationBoundsCohomology.FIN
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Map

variable {R G M M' : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  (ρ : Representation R G M) (ρ' : Representation R G M') (φ : M →ₗ[R] M')
  (hφ : ∀ g m, φ (ρ g m) = ρ' g (φ m))

def continuousCocycleMap : coZ1s ρ →ₗ[R] coZ1s ρ' where
  toFun c := ⟨fun g => φ ((c : G → M) g), fun g h => by
    show φ ((c : G → M) (g * h)) = φ ((c : G → M) g) + ρ' g (φ ((c : G → M) h))
    rw [c.2 g h, map_add (f := _), hφ]⟩
  map_add' a b := Subtype.ext <| funext fun g => map_add φ ((a : G → M) g) ((b : G → M) g)
  map_smul' r a := Subtype.ext <| funext fun g => map_smul φ r ((a : G → M) g)

def h1Map : H1z ρ →ₗ[R] H1z ρ' :=
  Submodule.mapQ _ _ (continuousCocycleMap ρ ρ' φ hφ) (by
    rintro x ⟨v, hv⟩
    refine ⟨φ v, funext fun g => ?_⟩
    have h : ρ g v - v = (x : G → M) g := congrFun hv g
    show ρ' g (φ v) - φ v = φ ((x : G → M) g)
    rw [← h]
    show ρ' g (φ v) - φ v = φ (ρ g v - v)
    rw [map_sub, hφ])

theorem h1Map_mk (c : coZ1s ρ) :
    h1Map ρ ρ' φ hφ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (continuousCocycleMap ρ ρ' φ hφ c) := rfl

theorem res_h1Map (Dg : Subgroup G) (x : H1z ρ) :
    resH1 ρ' Dg (h1Map ρ ρ' φ hφ x) =
      h1Map (resRep ρ Dg) (resRep ρ' Dg) φ (fun g m => hφ g m) (resH1 ρ Dg x) := by
  induction x using Submodule.Quotient.induction_on with
  | H c => rfl

theorem h1Map_mem_unrH1 {Dg : Subgroup G} {x : H1z ρ} (hx : x ∈ unrH1 ρ Dg) : h1Map ρ ρ' φ hφ x ∈ unrH1 ρ' Dg := by
  unfold unrH1 at hx ⊢
  rw [LinearMap.mem_ker] at hx ⊢
  rw [res_h1Map ρ ρ' φ hφ Dg x, hx, map_zero]

theorem h1Map_mem_lcH1 [TopologicalSpace G] {x : H1z ρ} (hx : x ∈ lcH1 ρ) : h1Map ρ ρ' φ hφ x ∈ lcH1 ρ' := by
  unfold lcH1 at hx ⊢
  obtain ⟨c, hc, rfl⟩ := hx
  refine ⟨continuousCocycleMap ρ ρ' φ hφ c, ?_, ?_⟩
  · show IsLocallyConstant (φ ∘ (c : G → M))
    exact hc.comp φ
  · first
      | exact (h1Map_mk ρ ρ' φ hφ c).symm

theorem resH1_h1Map_mem_Fsha (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs : Finset ℕ) (w : ℕ) {x : H1z ρ}
    (hx : resH1 ρ (D w) x ∈ Fsha ρ D Iq qs w) : resH1 ρ' (D w) (h1Map ρ ρ' φ hφ x) ∈ Fsha ρ' D Iq qs w := by
  unfold Fsha at hx ⊢
  rw [res_h1Map ρ ρ' φ hφ (D w) x]
  split_ifs at hx ⊢ with hw
  · exact h1Map_mem_unrH1 (resRep ρ (D w)) (resRep ρ' (D w)) φ (fun g m => hφ g m) hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem h1Map_mem_selRep2 [TopologicalSpace G] {V VS : Type} (J : V → Subgroup G) (JS : VS → Subgroup G)
    (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs P : Finset ℕ) {x : H1z ρ}
    (hx : x ∈ selRep2 ρ J JS D (Fsha ρ D Iq qs) P) :
    h1Map ρ ρ' φ hφ x ∈ selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P := by
  unfold selRep2 at hx ⊢
  simp only [Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hx ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx
  exact ⟨⟨⟨h1Map_mem_lcH1 ρ ρ' φ hφ h1, fun v => h1Map_mem_unrH1 ρ ρ' φ hφ (h2 v)⟩,
    fun v => h1Map_mem_unrH1 ρ ρ' φ hφ (h3 v)⟩, fun w hw => resH1_h1Map_mem_Fsha ρ ρ' φ hφ D Iq qs w (h4 w hw)⟩

end Map

section Iso

variable {R G M M' : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']

theorem len_selRep2_le_of_iso (ρ : Representation R G M) (ρ' : Representation R G M') (h : RepIso ρ ρ')
    {V VS : Type} (J : V → Subgroup G) (JS : VS → Subgroup G)
    (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs P : Finset ℕ) :
    Module.length R ↥(selRep2 ρ J JS D (Fsha ρ D Iq qs) P) ≤
      Module.length R ↥(selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P) := by
  obtain ⟨e, he⟩ := h
  have he' : ∀ g m, (e.symm : M' →ₗ[R] M) (ρ' g m) = ρ g ((e.symm : M' →ₗ[R] M) m) := by
    intro g m
    apply e.injective
    show e (e.symm (ρ' g m)) = e (ρ g (e.symm m))
    rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]
  have hinv : ∀ x, h1Map ρ' ρ (e.symm : M' →ₗ[R] M) he' (h1Map ρ ρ' (e : M →ₗ[R] M') he x) = x := by
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H c =>
      rw [h1Map_mk, h1Map_mk]
      congr 1
      exact Subtype.ext (funext fun g => e.symm_apply_apply _)
  let F := (h1Map ρ ρ' (e : M →ₗ[R] M') he).restrict
    (p := selRep2 ρ J JS D (Fsha ρ D Iq qs) P) (q := selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P)
    (fun x hx => h1Map_mem_selRep2 ρ ρ' _ he J JS D Iq qs P hx)
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    have h1 := congrArg Subtype.val hab
    rw [LinearMap.restrict_coe_apply, LinearMap.restrict_coe_apply] at h1
    have h2 := congrArg (h1Map ρ' ρ (e.symm : M' →ₗ[R] M) he') h1
    rwa [hinv, hinv] at h2
  exact Module.length_le_of_injective F hF

end Iso

section GlobalTheory

variable {D : D7} {i : D.nd.Loc} {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
  {Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)}
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def k0 (c' : Fin D.R.t) : {a : Fin D.R.nV // RepresentationBoundsCohomology.blk D.R a = c'.succ} :=
  ⟨Fin.natAdd D.R.r c', RepresentationBoundsCohomology.blkG_natAdd D.R.r D.R.t c'⟩

variable (Dd) in
def blkEquiv (c' : Fin D.R.t) : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ ≃ₗ[D.nd.O i] KO (D.nd.O i) where
  toFun m := m (k0 c')
  invFun x := fun _ => x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv m := funext fun k => congrArg m (Subtype.ext (blkS_eq k.1 k.2)).symm
  right_inv _ := rfl

omit [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
theorem chi_ratio (c' : Fin D.R.t) (g : GE D.nd) :
    (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) =
      ((((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp
        (cycE i ^ (-((((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1 : ℕ) : ℤ)))) g : (D.nd.O i)ˣ) : D.nd.O i) := by
  have hc := D.nd.chi_def i ((c' : ℕ) + 1) (by omega) (by have := c'.isLt; omega)
  have hn : (-(((((c' : ℕ) + 1 : ℕ)) : ℤ) - 1)) =
      -((((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1 : ℕ) : ℤ) := by
    simp [Fin.val_succ]
  rw [hc, hn]
  simp only [MonoidHom.mul_apply, Units.val_mul, Units.inv_mul_cancel_left]
  simp [cycE]

theorem uRep_blk (hE : EvS r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c' : Fin D.R.t) (g : GE D.nd)
    (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ) :
    uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c'.succ) Dd.r Dd.χ g m =
      ((((Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom).comp
        (cycE i ^ (-((((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1 : ℕ) : ℤ)))) g : (D.nd.O i)ˣ) : D.nd.O i) • m := by
  show uElt Dd.r Dd.χ g • m = _
  rw [uElt, smul_assoc, rS_act hE hN c' g m, hE.blk_smul, smul_smul, ← chi_ratio c' g]
  congr 2
  rw [← map_inv, hE.chi_eval, map_inv]

theorem blkTw_of (hE : EvS r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) :
    BlockTwistedCyclotomic i Dd c := by
  induction c using Fin.cases with
  | zero => simp at hc
  | succ k =>
    refine ⟨blkEquiv Dd k, fun g m => ?_⟩
    have h := uRep_blk hE hN k g m
    show blkEquiv Dd k (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k.succ) Dd.r Dd.χ g m) = _
    rw [h, map_smul]
    first
      | rfl

theorem blkTw_of_def {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) : BlockTwistedCyclotomic i Dd c :=
  blkTw_of (evS_of hD) hN c hc

end GlobalTheory

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem Fall_eq_Fsha (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1))
    (hc : 2 ≤ (c : ℕ)) :
    Fall i dc Dd F0 c = Fsha (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (decs D.host.E (Aw i dc)) (I i dc)
      (qsN i dc) := by
  unfold Fall
  induction c using Fin.cases with
  | zero => simp at hc
  | succ k =>
    funext w
    simp only [Fin.cases_succ]
    have h1 : ((k.succ : Fin (D.R.t + 1)) : ℕ) ≠ 1 := by omega
    unfold Fpos Fsha
    simp only [h1, ↓reduceIte]
    split_ifs <;> rfl

theorem selChi_eq (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1))
    (hc : 2 ≤ (c : ℕ)) :
    selChi (Mc i Dd c) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) (qsN i dc)
        (Fall i dc Dd F0 c) (Io i) (IS i) =
      selRep2 (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (Io i) (IS i) (decs D.host.E (Aw i dc))
        (Fsha (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (decs D.host.E (Aw i dc)) (I i dc) (qsN i dc))
        (Pall i dc) := by
  rw [Fall_eq_Fsha i dc Dd F0 c hc]
  rfl

theorem tieSel2_of (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1))
    (hc : 2 ≤ (c : ℕ)) (hB : BlockTwistedCyclotomic i Dd c) (hC : CoefChange (D.nd.l i) (D.nd.O i))
    (hZ : ZlSha i dc ((c : ℕ) - 1)) :
    Module.length (D.nd.O i) ↥(selChi (Mc i Dd c) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc)
        (qsN i dc) (Fall i dc Dd F0 c) (Io i) (IS i)) ≤ ShaN i ((c : ℕ) - 1) := by
  rw [selChi_eq i dc Dd F0 c hc]
  refine le_trans (len_selRep2_le_of_iso _ _ hB (Io i) (IS i) (decs D.host.E (Aw i dc)) (I i dc)
    (qsN i dc) (Pall i dc)) ?_
  have h2 := hC (GE D.nd) (cycE i ^ (-(((c : ℕ) - 1 : ℕ) : ℤ))) (Io i) (IS i) (decs D.host.E (Aw i dc))
    (I i dc) (qsN i dc) (Pall i dc)
  refine le_trans h2 ?_
  unfold ShaN eON
  exact mul_le_mul' le_rfl hZ

theorem tieSel2 (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1))
    (hc : 2 ≤ (c : ℕ)) (hB : BlockTwistedCyclotomic i Dd c) (hC : CoefChange (D.nd.l i) (D.nd.O i))
    (hZ : ZlSha i dc ((c : ℕ) - 1)) :
    TieSel2 i (Mc i Dd c) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) (qsN i dc)
      (Fall i dc Dd F0 c) (Io i) (IS i) (c : ℕ) :=
  tieSel2_of i dc Dd F0 c hc hB hC hZ

theorem tieSel2_rec [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))}
    {π : D.nd.X i} {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hC : CoefChange (D.nd.l i) (D.nd.O i))
    (hZ : ∀ e ∈ Finset.Ioo 0 D.R.t, ZlSha i dc e)
    (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1)) (hc : 2 ≤ (c : ℕ)) :
    TieSel2 i (Mc i Dd c) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) (qsN i dc)
      (Fall i dc Dd F0 c) (Io i) (IS i) (c : ℕ) :=
  tieSel2 i dc Dd F0 c hc (blkTw_of_def hD hN c (by omega)) hC
    (hZ _ (Finset.mem_Ioo.2 ⟨by omega, by have := c.isLt; omega⟩))

end Rec

end Formalism.MainNotions.N.K.ShaT

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Module Formalism.MainNotions.N.KHf Formalism.NG

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace O]
  {LL : Type} [Field LL] [TopologicalSpace LL] (e : FractionRing O ≃+* LL)

abbrev modO (V : Type) [AddCommGroup V] [Module (FractionRing O) V] : Module O (TrV e V) :=
  Module.compHom (TrV e V) (e.toRingHom.comp (algebraMap O (FractionRing O)))

theorem contSMulO (hO : Continuous fun c : O => e (algebraMap O (FractionRing O) c)) (V : Type)
    [AddCommGroup V] [Module (FractionRing O) V] :
    letI := modO e V
    ContinuousSMul O (TrV e V) := by
  letI := modO e V
  exact ⟨(ModuleTopology.continuousSMul LL (TrV e V)).continuous_smul.comp
    ((hO.comp continuous_fst).prodMk continuous_snd)⟩

variable {A : Type} [Ring A] [Algebra O A]
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [Module A V]

def smulL (hP : ∀ (c : O) (v : V), (algebraMap O A c) • v = c • v) (v : V) :
    letI := modO e V
    A →ₗ[O] TrV e V :=
  letI := modO e V
  { toFun := fun a => (a • v : V)
    map_add' := fun a b => add_smul a b v
    map_smul' := fun c a => by
      show (c • a) • v = e.symm (e (algebraMap O (FractionRing O) c)) • (a • v : V)
      rw [RingEquiv.symm_apply_apply, algebraMap_smul, Algebra.smul_def, mul_smul, hP] }

theorem smul_cont [TopologicalSpace A] [IsModuleTopology O A]
    (hO : Continuous fun c : O => e (algebraMap O (FractionRing O) c))
    (hP : ∀ (c : O) (v : V), (algebraMap O A c) • v = c • v) (v : V) :
    Continuous fun a : A => (show TrV e V from (a • v : V)) := by
  letI := modO e V
  haveI := contSMulO e hO V
  haveI : ContinuousAdd (TrV e V) := ModuleTopology.continuousAdd LL (TrV e V)
  exact (IsModuleTopology.continuous_of_linearMap (R := O) (smulL e hP v) :)

theorem orbit_cont {G Γ : Type} [Group G] [TopologicalSpace G] [Group Γ] [TopologicalSpace Γ]
    (ι : G →* Γ) (hι : Continuous ι) [TopologicalSpace A] [IsModuleTopology O A]
    (u : Γ → A) (hu : Continuous u) (ρ : Representation O Γ V) (hρ : ∀ g v, ρ g v = u g • v)
    (hO : Continuous fun c : O => e (algebraMap O (FractionRing O) c))
    (hP : ∀ (c : O) (v : V), (algebraMap O A c) • v = c • v) (v : TrV e V) :
    Continuous fun g => repL e ρ ι g v := by
  refine ((smul_cont e hO hP v).comp (hu.comp hι)).congr fun g => ?_
  show u (ι g) • (show V from v) = ρ (ι g) v
  exact (hρ _ _).symm

end Gen

section Rec

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem eK_alg_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Continuous fun c : D.nd.O i => eK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c) := by
  have h : (fun c : D.nd.O i => eK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c)) =
      fun c => algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) ((D.nbr i w hw).eO c) :=
    funext fun c => by rw [eK_apply, Br.toLLK_alg]
  rw [h]
  exact continuous_subtype_val.comp (D.nbr i w hw).eO_cont

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem uElt_cont_n
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (n : ℕ) :
    letI := K.Topo.rTopology (D.nd.O i) Dd.R'
    Continuous fun g : ↥(Γn i dc n) => uElt Dd.r Dd.χ (g : GE D.nd) := by
  letI := K.Topo.rTopology (D.nd.O i) Dd.R'
  exact (K.Topo.uElt_cont (hD := hD) (hc := hc)).comp continuous_subtype_val

theorem orbC_uRep
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
    {V : Type} [AddCommGroup V] [Module Dd.R' V] [Module (D.nd.O i) V] [Module (FractionRing (D.nd.O i)) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] [SMulCommClass Dd.R' (D.nd.O i) V]
    (hP : ∀ (c : D.nd.O i) (v : V), (algebraMap (D.nd.O i) Dd.R' c) • v = c • v) (n : ℕ) :
    OrbC i dc (resRep (uRep (D.nd.O i) (M := V) Dd.r Dd.χ) (Γn i dc n)) := by
  intro hn v
  letI := K.Topo.rTopology (D.nd.O i) Dd.R'
  haveI : IsModuleTopology (D.nd.O i) Dd.R' := K.Topo.rTop_isModuleTopology (D.nd.O i) Dd.R'
  have hι : Continuous (Br.iota D.nbr i _ hn) := (D.nbr i _ hn).e_symm_cont.congr fun g => rfl
  exact orbit_cont (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) hι
    (fun g : ↥(Γn i dc n) => uElt Dd.r Dd.χ (g : GE D.nd)) (uElt_cont_n i dc r π g0 eB e₁ s Dd hD hc n)
    _ (fun g v => rfl) (eK_alg_cont i _) hP v

theorem orbC_repE
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (x' : Dd.X') (n : ℕ) :
    letI := evalModO i (R' := Dd.R') x'
    haveI := evalTower i (R' := Dd.R') x'
    OrbC i dc (repE i dc Dd.r Dd.χ x' n) := by
  letI := evalModO i (R' := Dd.R') x'
  haveI := evalTower i (R' := Dd.R') x'
  haveI := evalComm i (R' := Dd.R') x'
  haveI := smulComm_O i (A := Dd.R') (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
  exact orbC_uRep i dc r π g0 eB e₁ s Dd hD hc (fun c v => evalScalar i x' c v) n

theorem latM_alg {n : Type} [Fintype n] [DecidableEq n] (ρ : Dd.R' →ₐ[D.nd.O i] Matrix n n (D.nd.O i))
    (c : D.nd.O i) (v : Formalism.RepresentationBoundsCohomology.SF.LatM (D.nd.O i) (FractionRing (D.nd.O i)) n ρ.toRingHom) :
    (algebraMap (D.nd.O i) Dd.R' c) • v = c • v := by
  funext j
  show ∑ k, (ρ (algebraMap (D.nd.O i) Dd.R' c)) j k • v k = c • v j
  rw [AlgHom.commutes]
  simp [Matrix.algebraMap_matrix_apply, Finset.sum_ite_eq, ite_smul]

end Rec

section Homeo

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem eK_cont :
    letI := K.Topo.fracTopology (D.nd.O i)
    Continuous (eK (D.nbr i w hw)) := by
  letI := K.Topo.fracTopology (D.nd.O i)
  haveI := K.Topo.fracTop_addGroup_O (D := D) i
  have hemb := (K.Topo.fracTop_O (D := D) i).1
  refine continuous_of_continuousAt_zero (eK (D.nbr i w hw)).toAddMonoidHom ?_
  show ContinuousAt (eK (D.nbr i w hw)) 0
  rw [← map_zero (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))), ← hemb.continuousAt_iff]
  exact (eK_alg_cont i hw).continuousAt

theorem eK_symm_val (z : Br.Ow (D.nbr i w hw)) :
    (eK (D.nbr i w hw)).symm (z : Br.LLw (D.nbr i w hw)) =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((D.nbr i w hw).eO.symm z) := by
  rw [RingEquiv.symm_apply_eq, eK_apply, Br.toLLK_alg, RingEquiv.apply_symm_apply]
  rfl

theorem eK_symm_cont :
    letI := K.Topo.fracTopology (D.nd.O i)
    Continuous (eK (D.nbr i w hw)).symm := by
  letI := K.Topo.fracTopology (D.nd.O i)
  haveI := K.Topo.fracTop_addGroup_O (D := D) i
  have hemb := (K.Topo.fracTop_O (D := D) i).1
  have hOemb : Topology.IsOpenEmbedding
      (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))) :=
    ⟨Topology.IsEmbedding.subtypeVal, ReciprocityTheory.ChartRestriction.T2.GlobAlg.isOpen_range_OL (D.nbr i w hw).LL⟩
  refine continuous_of_continuousAt_zero (eK (D.nbr i w hw)).symm.toAddMonoidHom ?_
  show ContinuousAt (eK (D.nbr i w hw)).symm 0
  rw [← map_zero (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))), ← hOemb.continuousAt_iff]
  have hfun : ((eK (D.nbr i w hw)).symm ∘ algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))) =
      fun z => algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((D.nbr i w hw).eO.symm z) :=
    funext fun z => eK_symm_val i hw z
  rw [hfun]
  exact (hemb.continuous.comp (D.nbr i w hw).eO_symm_cont).continuousAt

theorem homeoK :
    letI := K.Topo.fracTopology (D.nd.O i)
    KBKa.HomeoK (eK (D.nbr i w hw)) := by
  exact ⟨eK_cont i hw, eK_symm_cont i hw⟩

theorem topMatch_pi (n : Type) [Finite n] :
    letI := K.Topo.fracTopology (D.nd.O i)
    KBKa.TopMatch (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i)) := by
  letI := K.Topo.fracTopology (D.nd.O i)
  haveI := K.Topo.fracTop_addGroup_O (D := D) i
  letI τ : TopologicalSpace (TrV (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i))) :=
    (Pi.topologicalSpace : TopologicalSpace (n → FractionRing (D.nd.O i)))
  let φ : (n → Br.LLw (D.nbr i w hw)) ≃L[Br.LLw (D.nbr i w hw)]
      TrV (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i)) :=
    { toFun := fun v j => (eK (D.nbr i w hw)).symm (v j)
      invFun := fun x j => eK (D.nbr i w hw) (x j)
      left_inv := fun v => funext fun j => (eK (D.nbr i w hw)).apply_symm_apply (v j)
      right_inv := fun x => funext fun j => (eK (D.nbr i w hw)).symm_apply_apply (x j)
      map_add' := fun v v' => funext fun j => map_add (eK (D.nbr i w hw)).symm (v j) (v' j)
      map_smul' := fun c v => funext fun j => map_mul (eK (D.nbr i w hw)).symm c (v j)
      continuous_toFun := continuous_pi fun j => (eK_symm_cont i hw).comp (continuous_apply j)
      continuous_invFun := continuous_pi fun j => (eK_cont i hw).comp (continuous_apply j) }
  have hM : IsModuleTopology (Br.LLw (D.nbr i w hw)) (TrV (eK (D.nbr i w hw)) (n → FractionRing (D.nd.O i))) :=
    IsModuleTopology.iso φ
  exact hM.1.symm

end Homeo

section Cyc

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))

end Cyc

section Row

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

end Row

section RowTop

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

end RowTop

section Ms

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem rTwO_cont (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (x : D.nd.X i) : Continuous (rTwO D.nd i r x) := by
  have hχ : Continuous fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i) := by
    have e : (fun g : GE D.nd => ((((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ)) : D.nd.O i)) =
        fun g => ((chiU D.nd i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      rw [MonoidHom.inv_apply, map_inv]
    rw [e]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  exact hχ.smul (hc x)

theorem locC_cont (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (x : D.nd.X i) :
    Continuous ⇑(TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r x)) := by
  have hinc : Continuous (TruncatedSeriesCountingIdentities.CoefExt.inc C) :=
    continuous_induced_rng.2 (by exact continuous_subtype_val)
  have h1 : Continuous fun g : Br.G D.nbr i w hw =>
      rTwO D.nd i r x ((Br.iota D.nbr i w hw g : _) : GE D.nd) :=
    (rTwO_cont i r hc x).comp (continuous_subtype_val.comp (Br.iota_cont D.nbr i w hw))
  exact ((h1.matrix_map (D.nbr i w hw).eO_cont).matrix_map continuous_subtype_val).matrix_map hinc

end Ms

end Formalism.MainNotions.N.KOrb

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Len

variable {R S : Type} [CommRing R] [CommRing S] (σ : R ≃+* S)

theorem length_le_semi {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →+ N) (hf : Function.Injective f) (hs : ∀ (a : R) (m : M), f (a • m) = σ a • f m) :
    Module.length R M ≤ Module.length S N := by
  classical
  rw [Module.length_eq_height, Module.length_eq_height]
  let F : Submodule R M → Submodule S N := fun p =>
    { carrier := f '' p
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, p.add_mem hx hy, map_add f x y⟩
      zero_mem' := ⟨0, p.zero_mem, map_zero f⟩
      smul_mem' := by
        rintro s _ ⟨x, hx, rfl⟩
        refine ⟨σ.symm s • x, p.smul_mem _ hx, ?_⟩
        rw [hs, RingEquiv.apply_symm_apply] }
  have hF : StrictMono F := by
    intro p q hpq
    rw [SetLike.lt_iff_le_and_exists] at hpq ⊢
    obtain ⟨hle, x, hxq, hxp⟩ := hpq
    refine ⟨?_, f x, ⟨x, hxq, rfl⟩, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hle hy, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      exact hxp (hf hyx ▸ hy)
  exact (Order.height_le_height_apply_of_strictMono F hF ⊤).trans (Order.height_mono le_top)

theorem length_quot_eq (a : R) :
    Module.length R (R ⧸ Ideal.span {a}) = Module.length S (S ⧸ Ideal.span {σ a}) := by
  classical
  have hJ : Ideal.span {σ a} = (Ideal.span {a}).map (σ : R →+* S) := by
    simp [Ideal.map_span]
  let e := Ideal.quotientEquiv (Ideal.span {a}) (Ideal.span {σ a}) σ hJ
  have he : ∀ (r : R) (x : R ⧸ Ideal.span {a}), e (r • x) = σ r • e x := by
    intro r x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [e, Ideal.quotientEquiv_apply, Algebra.smul_def, Ideal.quotientMap_mk, Ideal.Quotient.algebraMap_eq]
  refine le_antisymm (length_le_semi σ e.toAddEquiv.toAddMonoidHom e.injective he) ?_
  refine length_le_semi σ.symm e.symm.toAddEquiv.toAddMonoidHom e.symm.injective ?_
  intro s y
  apply e.injective
  show e (e.symm (s • y)) = e (σ.symm s • e.symm y)
  rw [he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

end Len

section QRec

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL] {e : ℕ}

abbrev QrecS (Ce : TwLat PD LL O e) (cB : ℕ) : Submodule O (G → Ce.V ⧸ Ce.L.T) :=
  divisibleCocycles Ce.L ⊓ (HfD PD Ce.L).comap (((PD.p : O) ^ cB) • LinearMap.id)

abbrev Qrec (Ce : TwLat PD LL O e) (cB : ℕ) : Type :=
  ↥(QrecS PD Ce cB) ⧸ (divisibleCocycles Ce.L ⊓ HfD PD Ce.L).comap (QrecS PD Ce cB).subtype

def LenMap {O' : Type} [CommRing O'] (σ : O' ≃+* O) (X : Type) [AddCommGroup X] [Module O' X]
    (Ce : TwLat PD LL O e) (cB : ℕ) : Prop :=
  ∃ f : X →+ Qrec PD Ce cB, Function.Injective f ∧ ∀ (a : O') (x : X), f (a • x) = σ a • f x

theorem len_gen {t cB : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (het : e < t) (Ce : TwLat PD LL O e)
    {O' : Type} [CommRing O'] (σ : O' ≃+* O) {X : Type} [AddCommGroup X] [Module O' X]
    (h : LenMap PD σ X Ce cB) :
    Module.length O' X ≤ ((finrank Qp K : ℕ∞) + 1) * (cB : ℕ∞) * lenOl PD (O := O) := by
  obtain ⟨f, hf, hs⟩ := h
  refine (length_le_semi σ f hf hs).trans ?_
  cases Ce
  exact (hTB.2 e het _ _ _ (by assumption) (by assumption)).2.2

end QRec

section RecLen

open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def TBDict2 (cB : ℕ) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
      ∃ (Y : YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL))
        (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1)),
        YtCrys (PD := Br.PD D.loc D.nbr i w hw) Y (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) ∧
        PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) Y Cd ∧
        YLoc (O := D.nd.O i) (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) ∧
        LenMap (Br.PD D.loc D.nbr i w hw) (selfO i hw) (Qcore i dc Dd c (idx i dc w) cB) Cd.Ce cB

private theorem lenMap_Qcore (cB : ℕ) (hd : TBDict2 i dc r π Dd cB) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hwrow : w ∈ dc.row)
    (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) :
    ∃ Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1),
      LenMap (Br.PD D.loc D.nbr i w hw) (selfO i hw) (Qcore i dc Dd c (idx i dc w) cB) Cd.Ce cB :=
  (hd w hw hwrow c hc).elim fun _ h => h.elim fun Cd h' => ⟨Cd, h'.2.2.2⟩

theorem tbDict_of (cB : ℕ) (h : TBDict2 i dc r π Dd cB) : TBDict i dc r π Dd := by
  unfold TBDict2 at h
  unfold TBDict
  intro w hw hrow c hc
  obtain ⟨Y, Cd, h1, h2, h3, -⟩ := h w hw hrow c hc
  exact ⟨Y, Cd, h1, h2, h3⟩

theorem tbLen_w (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hd : TBDict2 i dc r π Dd cB) {w : HeightOneSpectrum (𝓞 D.host.E)} (hwrow : w ∈ dc.row)
    (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) : TBLenAt i dc Dd cB (idx i dc w) c := by
  have hw : w ∈ placesOver D.host.E (D.nd.l i) := (dc.cover w).1 (Or.inl hwrow)
  have hpl : w ∈ plSet i dc := by simp [plSet, hwrow]
  unfold TrivialBoundAtRows at hTB
  unfold TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility at hTie
  obtain ⟨Cd, hL⟩ := lenMap_Qcore (hd := hd) (hw := hw) (hwrow := hwrow) (c := c) (hc := hc)
  have het : (c : ℕ) - 1 < D.R.t := by have := c.isLt; omega
  have hdeg := (hTie w hw).2.2
  unfold Br.DegW at hdeg

  have aux : ∀ {R' S' : Type} [CommRing R'] [CommRing S'] (σ' : R' ≃+* S') (n : ℕ),
      Module.length R' (R' ⧸ Ideal.span {(n : R')}) = Module.length S' (S' ⧸ Ideal.span {(n : S')}) := by
    intro R' S' _ _ σ' n
    rw [length_quot_eq σ', map_natCast]
  unfold TBLenAt
  refine le_trans (len_gen (Br.PD D.loc D.nbr i w hw) (hTB w hw hwrow) het Cd.Ce (selfO i hw) hL) (le_of_eq ?_)
  rw [plOf_idx (h := hpl), ← hdeg]
  unfold lenOl
  rw [Br.PD_p, ← aux (selfO i hw) (D.nd.l i)]
  ring

theorem tbLen_of (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hd : TBDict2 i dc r π Dd cB) : TBLen i dc Dd cB := by
  unfold TBLen
  intro n hn c hc
  unfold rowsN at hn
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.1 hn
  exact tbLen_w (hTB := hTB) (hTie := hTie) (hd := hd) (hwrow := hw) (c := c) (hc := hc)

theorem trivial_bound_target_of_dict (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i)
    (hd : TBDict2 i dc r π Dd cB) : TBTarget i dc Dd cB :=
  tbTarget_of (hTB := hTB) (hd := tbDict_of (h := hd)) (hlen := tbLen_of (hTB := hTB) (hTie := hTie) (hd := hd))

end RecLen

end Formalism.MainNotions.N.K.TB

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBa

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.TB Formalism.MainNotions.N.KHf

section Record

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))

theorem nzsd_R' : NoZeroSMulDivisors (D.nd.O i) Dd.R' := by
  first
  | exact ⟨fun {c x} h => by
      by_cases hc : c = 0
      · exact Or.inl hc
      · refine Or.inr (Subtype.ext (funext fun x' => Matrix.ext fun a b => ?_))
        have h1 := congrFun (congrFun (congrFun (congrArg Subtype.val h) x') a) b
        have h2 : algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c ≠ 0 := fun h0 =>
          hc (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)) (h0.trans (map_zero _).symm))
        simp only [SetLike.val_smul, Pi.smul_apply, Matrix.smul_apply,
          ZeroMemClass.coe_zero, Pi.zero_apply, Matrix.zero_apply] at h1
        rw [Algebra.smul_def] at h1
        exact (mul_eq_zero.mp h1).resolve_left h2⟩

theorem heS {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (a : D.nd.O i) :
    algebraMap ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (selfO i hw a) =
      eS i hw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a) := by
  first
  | (have e1 : ∀ y, eS i hw y = Formalism.MainNotions.N.Br.toLLK (D.nbr i w hw) y := fun _ => rfl
     rw [e1, Formalism.MainNotions.N.Br.toLLK, IsFractionRing.lift_algebraMap]
     rfl)

variable {i dc r Dd}

theorem fd_yt {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (hemb : YtEmbW i dc r Dd hw) :
    FiniteDimensional ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (TrV (eS i hw) (MK (O := D.nd.O i) (YtM i Dd))) := by
  obtain ⟨m, xs, φ, hφ, -⟩ := hemb
  first
  | exact FiniteDimensional.of_injective φ hφ

private theorem continuous_of_injective_linearMap_comp {K V W G : Type*} [Field K] [TopologicalSpace K]
    {_a : AddCommMonoid V} {_m : Module K V} [TopologicalSpace V] [ContinuousAdd V] [IsModuleTopology K V]
    {_aw : AddCommMonoid W} {_mw : Module K W} [TopologicalSpace W] [IsModuleTopology K W]
    [TopologicalSpace G] (φ : V →ₗ[K] W) (hφ : Function.Injective φ) (f : G → V)
    (hf : Continuous fun g => φ (f g)) : Continuous f := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  letI : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  haveI : ContinuousSMul K V := by
    first
    | exact inferInstance
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective φ (LinearMap.ker_eq_bot.mpr hφ)
  have hψc : Continuous ψ := IsModuleTopology.continuous_of_linearMap ψ
  have e1 : f = fun g => ψ (φ (f g)) := funext fun g => (LinearMap.congr_fun hψ (f g)).symm
  rw [e1]
  exact hψc.comp hf

theorem cont_yt {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}
    (hemb : YtEmbW i dc r Dd hw) (hc : MsContW i r hw) (v) : Continuous fun g => ytV i dc Dd hw g v := by
  obtain ⟨m, xs, φ, hφ, heq⟩ := hemb
  have hc' : ∀ x, Continuous (MsW i r hw x) := hc
  refine continuous_of_injective_linearMap_comp φ hφ (fun g => ytV i dc Dd hw g v) ?_
  refine Continuous.congr (f := fun g => fun a => (MsW i r hw (xs a) g).mulVec (φ v a)) ?_
    (fun g => (heq g v).symm)
  refine continuous_pi fun a => ?_
  first
  | exact (hc' (xs a)).matrix_mulVec continuous_const

def ytY (hfin : Module.Finite (D.nd.O i) Dd.R') {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (hemb : YtEmbW i dc r Dd hw) (hc : MsContW i r hw) :
    YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
      ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) :=
  haveI := hfin
  haveI := nzsd_R' i Dd
  ytG ℚ_[D.nd.l i] (heS i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) (fd_yt hemb) (cont_yt hemb hc)

theorem msW_eq {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    MsW i r hw x = twistM (TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C (TruncatedSeriesCountingIdentities.CoefExt.self i w hw))⁻¹ := by
  ext g a b
  first
  | (simp only [MsW, TruncatedSeriesCountingIdentities.locC, TruncatedSeriesCountingIdentities.chi1C, rTwO, twistM, mapM, Formalism.MainNotions.N.Br.loc, Formalism.MainNotions.N.Br.locChi,
      Formalism.MainNotions.N.Br.locM, Formalism.MainNotions.N.Br.locO, Formalism.MainNotions.N.Br.chiG, MonoidHom.coe_comp, Function.comp_apply,
      MonoidHom.coe_mk, OneHom.coe_mk, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe,
      RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, MonoidHom.inv_apply,
      Units.coe_map_inv, map_mul]
     rfl)

variable (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

theorem ytPsi_rec (hfin : Module.Finite (D.nd.O i) Dd.R') {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (hemb : YtEmbW i dc r Dd hw) (hc : MsContW i r hw)
    [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] (c : Fin (D.R.t + 1))
    (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1)) :
    PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) (ytY hfin hemb hc) Cd := by
  haveI := hfin
  haveI := nzsd_R' i Dd
  first
  | apply ytG_psi

theorem jump_pi (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hc : MsContW i r hw) (x : D.nd.X i) (τ) (a : ℤ)
    (hx : IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x)) τ a) :
    IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw π)) τ a := by
  have hFs := hF w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)
  have hMs : ∀ y, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw y)) := fun y => by
    rw [msW_eq]
    exact (hG2 w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).2 y
  have hfd : FiniteDimensional ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
      ↥(DdR (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x))) :=
    fd_of_crys (Br.PD D.loc D.nbr i w hw) hFs (matG (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)) (MsW i r hw) hc x) (hMs x)
  have hp := mult_pos (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x)) τ a hx
  have heqm := (hG2 w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).1.2.1 τ x π a
  rw [← msW_eq, ← msW_eq] at heqm
  exact jump_of_mult _ _ τ a (by rw [← heqm]; exact hp.ne')

theorem ytTarget_of (hfin : Module.Finite (D.nd.O i) Dd.R') (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hemb : YtEmbW i dc r Dd hw) (hc : MsContW i r hw)
    [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] (c : Fin (D.R.t + 1)) :
    YtTarget i dc r π Dd hw c := by
  intro Cd
  haveI := hfin
  haveI := nzsd_R' i Dd
  have hMs : ∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x)) := fun x => by
    rw [msW_eq hw x]
    exact (hG2 w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).2 x
  obtain ⟨m, xs, φ, hφ, heq⟩ := id hemb
  have hcrys : IsCrys (Br.PD D.loc D.nbr i w hw) (ytY hfin hemb hc).ρ ∧
      ∀ τ a, IsJumpV (Br.PD D.loc D.nbr i w hw) (ytY hfin hemb hc).ρ τ a →
        ∃ x, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (MsW i r hw x)) τ a :=
    ytG_crys (hF := hF w hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) (Ms := MsW i r hw) (hMc := hc) (hMs := hMs)
      (xs := xs) (φ := φ) (hφ := hφ) (heq := heq) ..
  refine ⟨ytY hfin hemb hc, ?_, ytPsi_rec hfin hemb hc c Cd⟩
  unfold YtCrys
  refine ⟨hcrys.1, fun τ => ?_⟩
  intro a ha
  obtain ⟨x, hx⟩ := hcrys.2 τ a ha
  exact jump_pi (hF := hF) (hG2 := hG2) (hw := hw) (hc := hc) (x := x) (hx := hx)

end Record

end Formalism.MainNotions.N.K.TBa

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Module

section Len

theorem len_comap_surj {O A B : Type} [CommRing O] [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B]
    (f : A →ₗ[O] B) (hf : Function.Surjective f) (Q P : Submodule O B) :
    Module.length O (↥(Q.comap f) ⧸ (P.comap f).comap (Q.comap f).subtype) =
      Module.length O (↥Q ⧸ P.comap Q.subtype) := by
  let q : ↥(Q.comap f) →ₗ[O] ↥Q ⧸ P.comap Q.subtype :=
    (P.comap Q.subtype).mkQ ∘ₗ LinearMap.codRestrict Q (f ∘ₗ (Q.comap f).subtype) (fun x => x.2)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.mkQ_surjective _ y
    obtain ⟨a, rfl⟩ := hf b
    exact ⟨⟨a, hb⟩, rfl⟩
  have hk : LinearMap.ker q = (P.comap f).comap (Q.comap f).subtype := by
    ext x
    rw [LinearMap.mem_ker]
    exact Submodule.Quotient.mk_eq_zero _
  exact ((Submodule.quotEquivOfEq _ _ hk.symm).trans (q.quotKerEquivOfSurjective hq)).length_eq

variable {R S M N : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
  (e : R ≃+* S) [RingHomInvPair (e : R →+* S) (e.symm : S →+* R)] [RingHomInvPair (e.symm : S →+* R) (e : R →+* S)]
  (Ψ : M →ₛₗ[(e : R →+* S)] N) (hinj : Function.Injective Ψ)
  (Q P : Submodule R M) (Q' P' : Submodule S N)
  (hQ : ∀ y, y ∈ Q' ↔ ∃ x : M, x ∈ Q ∧ Ψ x = y) (hP : ∀ x ∈ Q, x ∈ P ↔ Ψ x ∈ P')

def resQ : ↥Q →ₛₗ[(e : R →+* S)] ↥Q' where
  toFun x := ⟨Ψ (x : M), (hQ _).2 ⟨x, x.2, rfl⟩⟩
  map_add' a b := Subtype.ext (map_add Ψ (a : M) (b : M))
  map_smul' c a := Subtype.ext (Ψ.map_smulₛₗ c (a : M))

include hinj in
theorem resQ_bij : Function.Bijective (resQ e Ψ Q Q' hQ) := by
  constructor
  · intro a b h
    have h' : Ψ (a : M) = Ψ (b : M) := congrArg Subtype.val h
    exact Subtype.ext (hinj h')
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := (hQ y).1 hy
    exact ⟨⟨x, hx⟩, rfl⟩

include hinj hQ in
def resQE : ↥Q ≃ₛₗ[(e : R →+* S)] ↥Q' :=
  LinearEquiv.ofBijective (resQ e Ψ Q Q' hQ) (resQ_bij e Ψ hinj Q Q' hQ)

include hinj hQ in
theorem resQE_apply (x : ↥Q) : ((resQE e Ψ hinj Q Q' hQ x : ↥Q') : N) = Ψ (x : M) := rfl

include hinj hQ hP in
theorem len_semi :
    Module.length R (↥Q ⧸ P.comap Q.subtype) = Module.length S (↥Q' ⧸ P'.comap Q'.subtype) := by
  obtain ⟨E, hE⟩ : ∃ E : ↥Q ≃ₛₗ[(e : R →+* S)] ↥Q', ∀ x, ((E x : ↥Q') : N) = Ψ (x : M) :=
    ⟨resQE e Ψ hinj Q Q' hQ, resQE_apply e Ψ hinj Q Q' hQ⟩
  have hmap : (P.comap Q.subtype).map (E : ↥Q →ₛₗ[(e : R →+* S)] ↥Q') = P'.comap Q'.subtype := by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hE]
      exact (hP x x.2).1 hx
    · intro hy
      obtain ⟨x, rfl⟩ := E.surjective y
      rw [hE] at hy
      exact ⟨x, (hP x x.2).2 hy, rfl⟩
  let F := Submodule.Quotient.equiv (P.comap Q.subtype) (P'.comap Q'.subtype) E hmap
  have h1 := Order.height_orderIso (Submodule.orderIsoMapComap F) ⊤
  rw [OrderIso.map_top] at h1
  rw [Module.length_eq_height, Module.length_eq_height]
  exact h1.symm

end Len

section Props

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  {T₁ T₂ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁] [IsTopologicalAddGroup T₁]
  [ContinuousConstSMul (D.nd.O i) T₁] [AddCommGroup T₂] [Module (D.nd.O i) T₂]
  (ρ₁ : Representation (D.nd.O i) (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) T₁) (π : T₁ →ₗ[D.nd.O i] T₂)
  (vD : ∀ w, T₂ ≃ₗ[D.nd.O i] (Dat w).T') (hpD : ∀ w, Continuous fun t => vD w (π t))
  (heD : ∀ w g t, vD w (π (resRep ρ₁ (Γn i dc w) g t)) = (Dat w).ρTl' g (vD w (π t)))

def imRow (w : ℕ) : Submodule (D.nd.O i) (ReciprocityTheory.Gal.H1 (Dat w).ρTl') :=
  (Hf₁ i dc ρ₁ w).map (gRow (Dat w) (resRep ρ₁ (Γn i dc w)) π (vD w) (hpD w) (heD w))

variable [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

def rowLenD (w : ℕ) : ℕ∞ :=
  Module.length (D.nd.O i) (↥(Fs i dc VT VT' Dat w) ⧸
    (imRow i dc VT VT' Dat ρ₁ π vD hpD heD w).comap (Fs i dc VT VT' Dat w).subtype)

theorem heO_br {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) (a : D.nd.O i) :
    algebraMap (Br.Ow (D.nbr i _ hn)) (Br.LLw (D.nbr i _ hn)) ((D.nbr i _ hn).eO a) =
      eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a) := by
  change _ = Br.toLLK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a)
  rw [Br.toLLK, IsFractionRing.lift_algebraMap]
  rfl

def RowSub (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    IsSubOfSums (repL (eK (D.nbr i _ hn)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r x)))

def RowOrb : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    ∀ x, Continuous fun g => repL (eK (D.nbr i _ hn)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn) g x

def RowMat (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (πx : D.nd.X i) : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    IsMatLat (ρ := repL (eK (D.nbr i _ hn)) (Dat n).ρT' (Br.iota D.nbr i _ hn))
      (latT (eK (D.nbr i _ hn)) (D.nbr i _ hn).eO (Dat n).T'.subtype (heO_br i dc hn))
      (⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (T2O D.nd i ρ πx)))

def RowTop : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    (∀ c : ↥(Γn i dc n) → VT' n,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (c (Br.iota D.nbr i _ hn g))) → Continuous c) ∧
    (∀ c : ↥(Γn i dc n) → T₁,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hn g)))) →
        Continuous c)

def RowFin : Prop :=
  Module.Finite (D.nd.O i) T₁ ∧ Module.Free (D.nd.O i) T₁ ∧
  ∀ n ∈ K.rowsN i dc, Module.Finite (D.nd.O i) (Dat n).T' ∧ Module.Free (D.nd.O i) (Dat n).T' ∧
    ∀ v : VT' n, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ t : (Dat n).T', (t : VT' n) = c • v

end Props

end Formalism.MainNotions.N.KRow

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Classical

namespace Formalism.MainNotions.N.KBKa

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.MainNotions.N.KHf

section Cyc

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
  [IsAlgClosure E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (P : LocPrime l)

theorem cycZ_eq_χQ (g : ↥(GK Bw.Kw)) :
    ((ReciprocityTheory.Gal.cycZ (F := E) (Ω := Ω) l ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) : ℤ_[l]) : ℚ_[l]) =
      ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) := by
  set x : ℚ_[l] := ((ReciprocityTheory.Gal.cycZ (F := E) (Ω := Ω) l ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) : ℤ_[l]) : ℚ_[l])
    with hx
  set x' : ℚ_[l] := ((P.χQ (g : GQ l) : ℚ_[l]ˣ) : ℚ_[l]) with hx'
  have key : ∀ m : ℕ, ‖x - x'‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
    intro m
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
    haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
    haveI : NeZero ((l ^ m : ℕ) : Ω) := ⟨by exact_mod_cast pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    obtain ⟨ζ', hζ'⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hζ : IsPrimitiveRoot (Bw.j ζ') (l ^ m) := hζ'.map_of_injective Bw.j.injective
    obtain ⟨a, ha, hxa⟩ := Formalism.AdicCompletionExports.isCycG_cycZ l E Ω ℤ_[l] (RingHom.id _)
      ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) m ζ' hζ'.pow_eq_one
    obtain ⟨a', hxa', ha'⟩ := P.χQ_cyc (g : GQ l) m (Bw.j ζ') hζ.pow_eq_one
    have hg : (g : GQ l) (Bw.j ζ') = Bw.j ζ' ^ a := by
      have h0 := Bw.e_comm (Br.ι Bw g) ζ'
      have he : Bw.e (Br.ι Bw g) = g := Bw.e.apply_symm_apply g
      rw [he] at h0
      rw [h0, ha, map_pow]
    have h1 : a ≡ a' [MOD l ^ m] := by
      have h0 := hg.symm.trans ha'
      have hf : IsOfFinOrder (Bw.j ζ') :=
        isOfFinOrder_iff_pow_eq_one.2 ⟨l ^ m, pow_pos (Fact.out : l.Prime).pos m, hζ.pow_eq_one⟩
      rwa [hf.pow_eq_pow_iff_modEq, ← hζ.eq_orderOf] at h0
    have hxa2 : ‖x - (a : ℚ_[l])‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      change ((ReciprocityTheory.Gal.cycZ (F := E) (Ω := Ω) l ((Br.ι Bw g : Gw) : Ω ≃ₐ[E] Ω) : ℤ_[l]) - (a : ℤ_[l]))
        ∈ Ideal.span {(l : ℤ_[l]) ^ m} at hxa
      have h0 := (PadicInt.norm_le_pow_iff_mem_span_pow _ m).2 hxa
      rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.coe_natCast] at h0
      exact h0
    have h2 : ‖((a : ℚ_[l]) - (a' : ℚ_[l]))‖ ≤ (l : ℝ) ^ (-(m : ℤ)) := by
      have h3 : ((l ^ m : ℕ) : ℤ) ∣ (a : ℤ) - (a' : ℤ) := Nat.modEq_iff_dvd.1 h1.symm
      have h4 := (Padic.norm_int_le_pow_iff_dvd ((a : ℤ) - a') m).2 (by exact_mod_cast h3)
      simpa using h4
    have h4 : x - x' = (x - a) + ((a - a') + -(x' - a')) := by ring
    rw [h4]
    exact (Padic.nonarchimedean _ _).trans (max_le hxa2 ((Padic.nonarchimedean _ _).trans
      (max_le h2 (by rwa [norm_neg]))))
  have hlim : Filter.Tendsto (fun m : ℕ => (l : ℝ) ^ (-(m : ℤ))) Filter.atTop (nhds 0) := by
    have h5 : ∀ m : ℕ, (l : ℝ) ^ (-(m : ℤ)) = ((l : ℝ)⁻¹) ^ m := fun m => by
      rw [zpow_neg, zpow_natCast, inv_pow]
    simp only [h5]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity)
      (inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt))
  exact sub_eq_zero.1 (norm_le_zero_iff.1 (ge_of_tendsto' hlim key))

end Cyc

section TopPi

variable {O : Type} [CommRing O] [IsDomain O] [TopologicalSpace (FractionRing O)]
  {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] (e : FractionRing O ≃+* LL)
  (n : Type) [Fintype n]

end TopPi

section RecC

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  {VT VT' : Type}
  [AddCommGroup VT] [Module (D.nd.O i) VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
  [ContinuousSMul (D.nd.O i) VT] [Module (FractionRing (D.nd.O i)) VT]
  [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VT]
  [AddCommGroup VT'] [Module (D.nd.O i) VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
  [ContinuousSMul (D.nd.O i) VT'] [Module (FractionRing (D.nd.O i)) VT']
  [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) VT']

theorem cycMatch_rec {w : ℕ} (hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i))
    (Dw : Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) VT VT')
    (hε : ∀ g : ↥(Γn i dc w), Dw.ε g = epsU D.nd i (g : GE D.nd)) :
    CycMatch Dw (eK (D.nbr i _ hn)) (Br.iota D.nbr i _ hn) (Br.PD D.loc D.nbr i _ hn) := by
  intro g
  rw [hε]
  have hP := cycZ_eq_χQ (D.nbr i _ hn) (D.loc (D.nd.l i)) g
  have hχ := (D.loc (D.nd.l i)).PD_χ (D.nbr i _ hn).Kw g
  simp only [eK, RingEquiv.ofBijective_apply, Br.toLLK, IsFractionRing.lift_algebraMap, LocBridge.toLL,
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, epsU, Glob.epsO, MonoidHom.comp_apply,
    Units.coe_map, MonoidHom.coe_coe, cycLL, Br.PD, RingHom.toMonoidHom_eq_coe, LocBridge.eO_alg]
  rw [← IsScalarTower.algebraMap_apply, hχ, ← hP]
  first
  | exact IsScalarTower.algebraMap_apply ℤ_[D.nd.l i] ℚ_[D.nd.l i] _ _

end RecC

section RecD

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))

theorem rowIn_of {w : ℕ} (hε : ∀ g : ↥(Γn i dc w), (Dat w).ε g = epsU D.nd i (g : GE D.nd))
    (ht : ∀ hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
      HomeoK (eK (D.nbr i _ hn)) ∧ TopMatch (eK (D.nbr i _ hn)) (VT w) ∧ TopMatch (eK (D.nbr i _ hn)) (VT' w))
    (hdr : ∀ hn : K.plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
      IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn)) (Dat w).ρT (Br.iota D.nbr i _ hn))) :
    RowIn i dc VT VT' Dat w := by
  intro hn
  obtain ⟨h1, h2, h3⟩ := ht hn
  exact ⟨h1, h2, h3, cycMatch_rec i dc hn (Dat w) hε, hdr hn⟩

end RecD

end Formalism.MainNotions.N.KBKa
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KUnr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N

section Gen

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {p : ℕ} [Fact p.Prime]

theorem exists_unr_dec (A : ValuationSubring Ω) (hp : A.valuation (p : Ω) < 1) :
    ∃ χ : ↥(A.decompositionSubgroup F) → ℤ_[p], Continuous χ ∧ (∀ g h, χ (g * h) = χ g + χ h) ∧
      (∀ g : ↥(A.decompositionSubgroup F), (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A → χ g = 0) ∧ ∃ g, χ g = 1 := by
  exact hT2Core.out.unr A hp

end Gen

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

private lemma plOf_colIdx (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) = l.1 := by
  have hmem : l.1 ∈ K.plSet i dc := by
    simp only [K.plSet, Finset.mem_union]
    exact Or.inl (Or.inr l.2)
  have hlt : ((K.plSet i dc).equivFin ⟨l.1, hmem⟩ : ℕ) < (K.plSet i dc).card := Fin.is_lt _
  unfold K.colIdx K.idx K.plOf
  rw [dite_eq_left hmem, dite_eq_left hlt]
  simp

theorem col_over (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ placesOver D.host.E (D.nd.l i) := by
  rw [plOf_colIdx]
  first
  | exact (dc.cover l.1).mp (Or.inr l.2)

theorem col_hp (l : K.Col i dc) :
    (K.Aw i dc (K.colIdx i dc l)).valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 := by
  have hov := col_over i dc l
  rw [plOf_colIdx] at hov
  unfold K.Aw
  rw [plOf_colIdx]
  have h2 := (D.nd.plOm.2 l.1 ((D.nd.l i : ℕ) : 𝓞 D.host.E)).mpr hov
  simpa using h2

theorem unrHom (l : K.Col i dc) : KFin.UnrHom i dc l := by
  obtain ⟨χ, hc, hm, hI, g1, h1⟩ :=
    exists_unr_dec (F := D.host.E) (K.Aw i dc (K.colIdx i dc l)) (col_hp i dc l)
  refine ⟨fun g => algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g), ⟨fun g h => ?_, fun g hg => ?_, fun hn => ?_⟩, g1, ?_⟩
  · show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ (g * h)) = _ + _
    rw [hm, map_add (f := _)]
  · have hg' : ((g : D.nd.Om ≃ₐ[D.host.E] D.nd.Om)) ∈ Ine (F := D.host.E) (K.Aw i dc (K.colIdx i dc l)) :=
      Subgroup.mem_subgroupOf.1 hg
    show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g) = 0
    rw [hI g hg', map_zero]
  · have hf : Continuous fun g : ↥(KFin.Γc i dc l) => algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g) :=
      (K.Topo.continuous_alg i).comp hc
    have e1 : ∀ c : D.nd.O i, KHf.eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c) =
        ((D.nbr i _ hn).eO c : Br.LLw (D.nbr i _ hn)) := fun c => by
      rw [KHf.eK_apply, Br.toLLK_alg]
      rfl
    simp only [e1]
    exact continuous_subtype_val.comp ((D.nbr i _ hn).eO_cont.comp (hf.comp (Br.iota_cont D.nbr i _ hn)))
  · show algebraMap ℤ_[D.nd.l i] (D.nd.O i) (χ g1) = 1
    rw [h1, map_one]

end Rec

end Formalism.MainNotions.N.KUnr
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i)

theorem wpO_cont (hρ : Continuous fun g => rhoO D.nd i ρ π g) : Continuous (WpO D.nd i ρ π) := by
  have hχ : Continuous fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) := by
    have he : (fun g : GE D.nd => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
      funext g
      simp [chiU, map_inv]
    rw [he]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  show Continuous fun g => (((chiU D.nd i 1)⁻¹ g : (D.nd.O i)ˣ) : D.nd.O i) • rhoO D.nd i ρ π g
  exact hχ.smul hρ

theorem loc_cont {k : ℕ} {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous M) :
    Continuous ⇑(Br.loc D.nbr i w hw M) := by
  unfold Br.loc Br.locM Br.locO mapM
  simp only [MonoidHom.coe_comp]
  refine Continuous.comp ?_ (Continuous.comp (Continuous.comp ?_ (Continuous.comp hM ?_)) ?_)
  · first
      | exact continuous_id.matrix_map continuous_subtype_val
  · exact continuous_id.matrix_map (D.nbr i w hw).eO_cont
  · exact continuous_subtype_val
  · first
      | exact (D.nbr i w hw).e_symm_cont

theorem contW_of (hρ : Continuous fun g => rhoO D.nd i ρ π g) (l : K.Col i dc) :
    KDim.ContW (i := i) (dc := dc) (ρ := ρ) (π := π) l := by
  intro v
  have hL := loc_cont i (KDim.col_over i dc l) (WpO D.nd i ρ π) (wpO_cont i ρ π hρ)
  have h2 : Continuous fun g => Matrix.mulVec (Br.loc D.nbr i _ (KDim.col_over i dc l) (WpO D.nd i ρ π) g) v :=
    hL.matrix_mulVec continuous_const
  refine h2.congr fun g => ?_
  first
    | rfl

end Formalism.MainNotions.N.KOrb

end
end
