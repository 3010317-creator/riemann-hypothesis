module

public import Formalism.AdmissibleDesigns.Base
public import Formalism.AdmissibleDesigns.Cohomology
public import Formalism.AdmissibleDesigns.InvariantsEqBotIff
public import Formalism.AdmissibleDesigns.KernelLengthHigherColumns
public import Formalism.AdmissibleDesigns.LocalCohom
public import Formalism.SharpRestriction.LevelLetterCocycles.GoodCongruenceDataOf
public import Formalism.SharpRestriction.LevelLetterCocycles.IsobaricMultiplicityOne
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.GaloisConditionFiveExtraOf
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.FirstSummandActionMem
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.FirstSummandRepresentation
public import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation
import Formalism.WachLatticeTwists.SplitClassesAll.Statement
import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Galois
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.LinearAlgebra.Dimension.Torsion.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs

@[expose] public section

noncomputable section

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.NG

namespace Formalism.MainNotions.N.KTate

open Formalism.MainNotions.N.KHf

section Gen

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) (OL : Type) [CommRing OL] [Algebra OL LL] {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G]
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [FiniteDimensional (FractionRing O) V]

abbrev modOL : Module OL (TrV e V) := Module.compHom _ (algebraMap OL LL)

theorem towOL : @IsScalarTower OL LL (TrV e V) _ _ (modOL e OL).toSMul := by
  letI := modOL (V := V) e OL
  exact ⟨fun a b v => by
    show (a • b) • v = (algebraMap OL LL a) • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩

def grepV (ρ : Representation O Γ V) (ι : G →* Γ) (hc : ∀ v : TrV e V, Continuous fun g => repL e ρ ι g v) :
    GRep G Qp LL OL :=
  { V := TrV e V
    modO := modOL (V := V) e OL
    towO := towOL (V := V) e OL
    fd := KDim.finDim_TrV (V := V) e
    ρ := repL e ρ ι
    cont := hc }

variable {OL} (σ : O ≃+* OL) (hσ : ∀ c : O, algebraMap OL LL (σ c) = e (algebraMap O (FractionRing O) c))

include hσ in
theorem smul_OL (c : O) (v : V) :
    @HSMul.hSMul OL (TrV e V) (TrV e V) (@instHSMul _ _ (modOL (V := V) e OL).toSMul) (σ c) (show TrV e V from v) =
      (c • v : V) := by
  show e.symm (algebraMap OL LL (σ c)) • v = c • v
  rw [hσ, RingEquiv.symm_apply_apply, algebraMap_smul]

variable {n : Type} [Fintype n] (bV : Basis n (FractionRing O) V)

def latT : @Submodule OL (TrV e V) _ _ (modOL (V := V) e OL) :=
  letI := modOL (V := V) e OL
  Submodule.span OL (Set.range fun j => (show TrV e V from bV j))

end Gen

abbrev tr {O : Type} [CommRing O] {LL : Type} [Field LL] (e : FractionRing O ≃+* LL) {V : Type} (v : V) : TrV e V := v

section Lat

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {OL : Type} [CommRing OL] [Algebra OL LL] {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G]
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [FiniteDimensional (FractionRing O) V]
  (σ : O ≃+* OL) (hσ : ∀ c : O, algebraMap OL LL (σ c) = e (algebraMap O (FractionRing O) c))
  {n : Type} [Fintype n] (bV : Basis n (FractionRing O) V)
  {L : Type} [AddCommGroup L] [Module O L] (bL : Basis n O L) (iL : L →ₗ[O] V) (hb : ∀ j, iL (bL j) = bV j)

include hσ hb in
theorem iL_mem_latT (m : L) : letI := modOL (V := V) e OL
    tr e (iL m) ∈ latT e (OL := OL) bV := by
  letI := modOL (V := V) e OL
  have hm : tr e (iL m) = ∑ j, σ (bL.repr m j) • tr e (bV j) := by
    show iL m = ∑ j, e.symm (algebraMap OL LL (σ (bL.repr m j))) • bV j
    conv_lhs => rw [← bL.sum_repr m]

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hb, hσ, RingEquiv.symm_apply_apply, algebraMap_smul]
  rw [hm]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

include hσ hb in
theorem exists_of_mem_latT (x : TrV e V) (hx : letI := modOL (V := V) e OL; x ∈ latT e (OL := OL) bV) :
    ∃ m : L, tr e (iL m) = x := by
  letI := modOL (V := V) e OL
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    exact ⟨bL j, hb j⟩
  | zero => exact ⟨0, map_zero iL⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, map_add iL a b⟩
  | smul o x _ hx =>
    obtain ⟨a, rfl⟩ := hx
    refine ⟨σ.symm o • a, ?_⟩
    show iL (σ.symm o • a) = e.symm (algebraMap OL LL o) • iL a
    rw [map_smul]
    conv_rhs => rw [← RingEquiv.apply_symm_apply σ o]
    rw [hσ, RingEquiv.symm_apply_apply, algebraMap_smul]

include hσ in
theorem linInd_latT : letI := modOL (V := V) e OL
    LinearIndependent OL (fun j => tr e (bV j)) := by
  letI := modOL (V := V) e OL
  rw [Fintype.linearIndependent_iff]
  intro o ho j
  have h2 : ∑ k, (e.symm (algebraMap OL LL (o k))) • bV k = 0 := ho
  have h3 := (Fintype.linearIndependent_iff.mp bV.linearIndependent) _ h2 j
  obtain ⟨c, hc⟩ := σ.surjective (o j)
  rw [← hc, hσ, RingEquiv.symm_apply_apply] at h3
  have : c = 0 := IsFractionRing.injective O (FractionRing O) (h3.trans (map_zero _).symm)
  rw [← hc, this, map_zero]

theorem span_latT : letI := modOL (V := V) e OL
    Submodule.span LL ((latT e (OL := OL) bV : Set (TrV e V))) = ⊤ := by
  letI := modOL (V := V) e OL
  rw [eq_top_iff]
  intro v _
  have hv := bV.sum_repr (show V from v)
  have h : v = ∑ j, e (bV.repr v j) • tr e (bV j) := by
    show (v : V) = ∑ j, e.symm (e (bV.repr v j)) • bV j
    simp only [RingEquiv.symm_apply_apply]
    exact hv.symm
  rw [h]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Submodule.subset_span ⟨j, rfl⟩))

include hσ in
theorem free_latT : letI := modOL (V := V) e OL
    Module.Free OL ↥(latT e (OL := OL) bV) := by
  letI := modOL (V := V) e OL
  exact Module.Free.of_basis (Basis.span (linInd_latT e σ hσ bV))

def latV (ρ : Representation O Γ V) (ι : G →* Γ) (hc : ∀ v : TrV e V, Continuous fun g => repL e ρ ι g v)
    (ρL : Representation O Γ L) (hiL : ∀ γ m, iL (ρL γ m) = ρ γ (iL m)) :
    Lattice (O := OL) (grepV e OL (Qp := Qp) ρ ι hc).ρ where
  T := latT e (OL := OL) (V := V) bV
  stable g x hx := by
    obtain ⟨m, hm⟩ := exists_of_mem_latT e σ hσ bV bL iL hb (show TrV e V from x) hx
    have h : (grepV e OL (Qp := Qp) ρ ι hc).ρ g x = tr e (iL (ρL (ι g) m)) := by
      rw [← hm, hiL]
      rfl
    rw [h]
    exact iL_mem_latT e σ hσ bV bL iL hb _
  fg := Submodule.fg_span (Set.finite_range _)
  free := free_latT e (V := V) σ hσ bV
  span := span_latT e (V := V) bV

end Lat

theorem finite_compHom {R S M : Type} [CommRing R] [CommRing S] [AddCommGroup M] [Module S M] (σ : R ≃+* S)
    [hM : Module.Finite S M] : @Module.Finite R M _ _ (Module.compHom M σ.toRingHom) := by
  letI : Module R M := Module.compHom M σ.toRingHom
  obtain ⟨s, hs⟩ := hM.fg_top
  refine ⟨⟨s, eq_top_iff.2 fun x hx0 => ?_⟩⟩
  clear hx0
  have hx : x ∈ Submodule.span S (s : Set M) := by rw [hs]; trivial
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact Submodule.zero_mem _
  | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    have h : c • y = σ.symm c • y := by
      show c • y = σ (σ.symm c) • y
      rw [RingEquiv.apply_symm_apply]
    rw [h]
    exact Submodule.smul_mem _ _ hy

section FinFf

variable {O : Type} [CommRing O] [IsDomain O] [IsNoetherianRing O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {OL : Type} [CommRing OL] [Algebra OL LL] {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G]
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [FiniteDimensional (FractionRing O) V]
  (σ : O ≃+* OL) (hσ : ∀ c : O, algebraMap OL LL (σ c) = e (algebraMap O (FractionRing O) c))
  {n : Type} [Fintype n] (bV : Basis n (FractionRing O) V)
  {L : Type} [AddCommGroup L] [Module O L] (bL : Basis n O L) (iL : L →ₗ[O] V) (hb : ∀ j, iL (bL j) = bV j)
  (ρ : Representation O Γ V) (ι : G →* Γ) (hc : ∀ v : TrV e V, Continuous fun g => repL e ρ ι g v)
  (ρL : Representation O Γ L) (hiL : ∀ γ m, iL (ρL γ m) = ρ γ (iL m))

theorem transp_mem (p : ↥((KFin.finPreG iL (finZ e PD ρ ι)).comap (coZ1s ρL).subtype)) :
    (fun g => tr e (iL (((p : coZ1s ρL) : Γ → L) (ι g)))) ∈
      latticeCocycles (latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL) := by
  have hp : (fun g => tr e (iL (((p : coZ1s ρL) : Γ → L) (ι g)))) ∈ finiteCocycles PD (repL e ρ ι) := p.2
  exact ⟨hp.1, fun g _ => iL_mem_latT e σ hσ bV bL iL hb _⟩

def transportToH1Lattice :
    letI := Module.compHom (LatticeCohomology (latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL)) σ.toRingHom
    ↥((KFin.finPreG iL (finZ e PD ρ ι)).comap (coZ1s ρL).subtype) →ₗ[O]
      LatticeCohomology (latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL) :=
  letI := Module.compHom (LatticeCohomology (latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL)) σ.toRingHom
  { toFun := fun p => Submodule.Quotient.mk ⟨_, transp_mem e PD σ hσ bV bL iL hb ρ ι hc ρL hiL p⟩
    map_add' := fun p q => by
      rw [← Submodule.Quotient.mk_add]
      congr 1
      exact Subtype.ext (funext fun g => map_add iL _ _)
    map_smul' := fun c p => by
      show _ = (σ c : OL) • (Submodule.Quotient.mk _ : LatticeCohomology (latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL))
      rw [← Submodule.Quotient.mk_smul]
      congr 1
      refine Subtype.ext (funext fun g => ?_)
      show iL (c • ((p : coZ1s ρL) : Γ → L) (ι g)) = e.symm (algebraMap OL LL (σ c)) • iL (((p : coZ1s ρL) : Γ → L) (ι g))
      rw [hσ, RingEquiv.symm_apply_apply, algebraMap_smul, map_smul] }

include hσ hb hiL in
theorem finite_FfG (hι : Function.Surjective ι) (hinj : Function.Injective iL)
    (hfin : Module.Finite OL (LatticeCohomology (latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL))) :
    Module.Finite O ↥(KFin.FfG ρL iL (finZ e PD ρ ι)) := by
  set LA := latV e σ hσ bV bL iL hb (Qp := Qp) ρ ι hc ρL hiL with hLA
  letI : Module O (LatticeCohomology LA) := Module.compHom (LatticeCohomology LA) σ.toRingHom
  haveI : Module.Finite O (LatticeCohomology LA) := finite_compHom σ
  haveI : IsNoetherian O (LatticeCohomology LA) := isNoetherian_of_isNoetherianRing_of_finite O _
  set P := (KFin.finPreG iL (finZ e PD ρ ι)).comap (coZ1s ρL).subtype with hP
  set Φ := transportToH1Lattice e PD σ hσ bV bL iL hb ρ ι hc ρL hiL (Qp := Qp) with hΦ
  have hker : LinearMap.ker Φ ≤ LinearMap.ker ((Submodule.mkQ ((coB1 ρL).comap (coZ1s ρL).subtype)).comp P.subtype) := by
    intro p hp
    rw [LinearMap.mem_ker] at hp ⊢
    have hp' := (Submodule.Quotient.mk_eq_zero _).mp hp
    obtain ⟨x, hxT, hx⟩ := hp'
    obtain ⟨m, rfl⟩ := exists_of_mem_latT e σ hσ bV bL iL hb x hxT
    show Submodule.Quotient.mk (p : coZ1s ρL) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨m, funext fun γ => ?_⟩
    obtain ⟨g, rfl⟩ := hι γ
    have h := congrFun hx g
    apply hinj
    show iL (ρL (ι g) m - m) = iL (((p : coZ1s ρL) : Γ → L) (ι g))
    rw [map_sub, hiL]
    exact h
  haveI : Module.Finite O (↥P ⧸ LinearMap.ker Φ) := Module.Finite.equiv (Φ.quotKerEquivRange).symm
  have hF : KFin.FfG ρL iL (finZ e PD ρ ι) =
      LinearMap.range ((LinearMap.ker Φ).liftQ ((Submodule.mkQ ((coB1 ρL).comap (coZ1s ρL).subtype)).comp P.subtype) hker) := by
    rw [Submodule.range_liftQ, LinearMap.range_comp, Submodule.range_subtype]
    rfl
  rw [hF]
  infer_instance

end FinFf

section Cpt

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL OL : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing OL] [IsDomain OL] [Algebra OL LL] [TopologicalSpace LL] (A : GRep G Qp LL OL)

def DivT (T : Submodule OL A.V) : Prop := ∀ v : A.V, ∃ a : OL, a ≠ 0 ∧ a • v ∈ T

theorem cont_smulOL (a : OL) : Continuous fun w : A.V => a • w := by
  have h : (fun w : A.V => a • w) = fun w => (algebraMap OL LL a) • w := funext fun w => (algebraMap_smul LL a w).symm
  rw [h]
  exact continuous_const_smul _

theorem bound_compact (T : Submodule OL A.V) (hopen : IsOpen (T : Set A.V)) (hdiv : DivT A T) (S : Set A.V)
    (hS : IsCompact S) : ∃ a : OL, a ≠ 0 ∧ ∀ v ∈ S, a • v ∈ T := by
  choose f hf0 hfT using hdiv
  have hU : ∀ v, IsOpen {w : A.V | f v • w ∈ T} := fun v => hopen.preimage (cont_smulOL A (f v))
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun v => {w : A.V | f v • w ∈ T}) hU
    (fun w _ => Set.mem_iUnion.2 ⟨w, hfT w⟩)
  refine ⟨∏ v ∈ t, f v, Finset.prod_ne_zero_iff.2 fun v _ => hf0 v, fun w hw => ?_⟩
  obtain ⟨v, hv, hwv⟩ := Set.mem_iUnion₂.1 (ht hw)
  rw [← Finset.mul_prod_erase t f hv, mul_comm, mul_smul]
  exact T.smul_mem _ hwv

variable [CompactSpace G]

theorem bound_cont (T : Submodule OL A.V) (hopen : IsOpen (T : Set A.V)) (hdiv : DivT A T) (c : G → A.V)
    (hc : Continuous c) : ∃ a : OL, a ≠ 0 ∧ ∀ g, a • c g ∈ T := by
  obtain ⟨a, ha, h⟩ := bound_compact A T hopen hdiv _ (isCompact_range hc)
  exact ⟨a, ha, fun g => h _ ⟨g, rfl⟩⟩

def incT (LA : Lattice (O := OL) A.ρ) : ↥(latticeCocycles LA) →ₗ[OL] ↥(continuousCocycles A.ρ) where
  toFun c := ⟨c.1, c.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def h1TV (LA : Lattice (O := OL) A.ρ) :
    letI := Module.compHom (H1V A.ρ) (algebraMap OL LL)
    LatticeCohomology LA →ₗ[OL] H1V A.ρ :=
  letI := Module.compHom (H1V A.ρ) (algebraMap OL LL)
  Submodule.liftQ _
    { toFun := fun c => Submodule.Quotient.mk (incT A LA c)
      map_add' := fun _ _ => rfl
      map_smul' := fun a c => by
        show (Submodule.Quotient.mk (incT A LA (a • c)) : H1V A.ρ) =
          (algebraMap OL LL a) • (Submodule.Quotient.mk (incT A LA c) : H1V A.ρ)
        rw [← Submodule.Quotient.mk_smul]
        congr 1
        exact Subtype.ext (funext fun g => (algebraMap_smul LL a _).symm) }
    (by
      rintro c hc
      obtain ⟨x, _, hx⟩ := hc
      rw [LinearMap.mem_ker]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, hx⟩)

theorem h1_lattice_to_vector_mk (LA : Lattice (O := OL) A.ρ) (c : ↥(latticeCocycles LA)) :
    h1TV A LA (Submodule.Quotient.mk c) = Submodule.Quotient.mk (incT A LA c) := rfl

theorem finite_H1V (LA : Lattice (O := OL) A.ρ) (hopen : IsOpen (LA.T : Set A.V)) (hdiv : DivT A LA.T)
    (hinj : Function.Injective (algebraMap OL LL)) [hfin : Module.Finite OL (LatticeCohomology LA)] :
    Module.Finite LL (H1V A.ρ) := by
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨⟨s.image (h1TV A LA), eq_top_iff.2 fun x _ => ?_⟩⟩
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨a, ha, hac⟩ := bound_cont A LA.T hopen hdiv c.1 c.2.1
  have hT : a • c.1 ∈ latticeCocycles LA := ⟨(continuousCocycles A.ρ).restrictScalars OL |>.smul_mem a c.2, fun g _ => hac g⟩
  letI := Module.compHom (H1V A.ρ) (algebraMap OL LL)
  have hrange : h1TV A LA (Submodule.Quotient.mk ⟨_, hT⟩) ∈
      Submodule.span OL ((s.image (h1TV A LA) : Finset (H1V A.ρ)) : Set (H1V A.ρ)) := by
    have h1 : (Submodule.Quotient.mk ⟨_, hT⟩ : LatticeCohomology LA) ∈ Submodule.span OL (s : Set (LatticeCohomology LA)) := by
      rw [hs]; trivial
    have h2 := Submodule.mem_map_of_mem (f := h1TV A LA) h1
    rw [Submodule.map_span] at h2
    simpa [Finset.coe_image] using h2
  have hle : ∀ y ∈ (letI := Module.compHom (H1V A.ρ) (algebraMap OL LL)
      Submodule.span OL ((s.image (h1TV A LA) : Finset (H1V A.ρ)) : Set (H1V A.ρ))),
      y ∈ Submodule.span LL ((s.image (h1TV A LA) : Finset (H1V A.ρ)) : Set (H1V A.ρ)) := by
    letI := Module.compHom (H1V A.ρ) (algebraMap OL LL)
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul a y _ hy => exact Submodule.smul_mem _ (algebraMap OL LL a) hy
  have hmem := hle _ hrange
  have heq : h1TV A LA (Submodule.Quotient.mk ⟨_, hT⟩) = (algebraMap OL LL a) • Submodule.Quotient.mk c := by
    rw [h1_lattice_to_vector_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (funext fun g => (algebraMap_smul LL a (c.1 g)).symm)
  rw [heq] at hmem
  have ha' : algebraMap OL LL a ≠ 0 := fun h0 => ha (hinj (h0.trans (map_zero _).symm))
  have := Submodule.smul_mem _ (algebraMap OL LL a)⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ ha', one_smul] at this

omit [CompactSpace G] in
theorem finDim_H1fV {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) [Module.Finite LL (H1V A.ρ)] :
    FiniteDimensional LL (FiniteCohomology PD A.ρ) := by
  let f : FiniteCohomology PD A.ρ →ₗ[LL] H1V A.ρ :=
    Submodule.mapQ _ _ (Submodule.inclusion (fun c hc => hc.1 : finiteCocycles PD A.ρ ≤ continuousCocycles A.ρ)) (fun c hc => hc)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    have h := (Submodule.Quotient.mk_eq_zero _).mp hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero]
    exact h
  exact Module.Finite.of_injective f hf

end Cpt

section Stab

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL OL : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [CommRing OL] [IsDomain OL] [Algebra OL LL] [TopologicalSpace LL] (A : GRep G Qp LL OL)
  {n : Type} [Fintype n] (b : Basis n LL A.V)

def T0 : Submodule OL A.V where
  carrier := {x | ∀ j, b.equivFun x j ∈ Set.range (algebraMap OL LL)}
  zero_mem' j := ⟨0, by simp⟩
  add_mem' {x y} hx hy j := by
    obtain ⟨a, ha⟩ := hx j
    obtain ⟨c, hc⟩ := hy j
    exact ⟨a + c, by simp [ha, hc]⟩
  smul_mem' o x hx j := by
    obtain ⟨a, ha⟩ := hx j
    refine ⟨o * a, ?_⟩
    show _ = b.equivFun (o • x) j
    rw [← algebraMap_smul LL o x, map_smul, Pi.smul_apply, ← ha, smul_eq_mul, map_mul]

theorem mem_integral_span (x : A.V) : x ∈ T0 A b ↔ ∀ j, b.equivFun x j ∈ Set.range (algebraMap OL LL) := Iff.rfl

theorem integral_span_open [IsTopologicalRing LL] (hO : IsOpen (Set.range (algebraMap OL LL))) :
    IsOpen ((T0 A b : Submodule OL A.V) : Set A.V) := by
  have hc : Continuous b.equivFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have h : ((T0 A b : Submodule OL A.V) : Set A.V) =
      b.equivFun ⁻¹' (Set.univ.pi fun _ => Set.range (algebraMap OL LL)) := by
    ext x
    simp [mem_integral_span]
  rw [h]
  exact (isOpen_set_pi Set.finite_univ fun _ _ => hO).preimage hc

theorem integral_span_divisible [IsFractionRing OL LL] : DivT A (T0 A b) := by
  intro v
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors OL) Finset.univ
    (fun j => b.equivFun v j)
  refine ⟨a, nonZeroDivisors.ne_zero a.2, fun j => ?_⟩
  obtain ⟨c, hc⟩ := ha j (Finset.mem_univ j)
  refine ⟨c, ?_⟩
  rw [hc, ← algebraMap_smul LL (a : OL) v, map_smul, Pi.smul_apply, smul_eq_mul, Algebra.smul_def]

theorem basis_mem_integral_span (j : n) : b j ∈ T0 A b := by
  intro k
  rw [Basis.equivFun_self]
  by_cases h : j = k
  · exact ⟨1, by simp [h]⟩
  · exact ⟨0, by rw [map_zero, ite_eq_right h]⟩

theorem integral_span_coordinates (x : A.V) (hx : x ∈ T0 A b) : ∃ o : n → OL, x = ∑ j, o j • b j := by
  choose o ho using hx
  refine ⟨o, ?_⟩
  conv_lhs => rw [← b.sum_equivFun x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← ho j, algebraMap_smul]

def Tst : Submodule OL A.V := Submodule.span OL (⋃ g : G, A.ρ g '' (T0 A b : Set A.V))

theorem integral_span_le_stable : T0 A b ≤ Tst A b := fun x hx =>
  Submodule.subset_span (Set.mem_iUnion.2 ⟨1, x, hx, by simp⟩)

theorem Tst_stable (g : G) (x : A.V) (hx : x ∈ Tst A b) : A.ρ g x ∈ Tst A b := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
    refine Submodule.subset_span (Set.mem_iUnion.2 ⟨g * h, y, hy, ?_⟩)
    rw [map_mul]
    rfl
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hx

theorem Tst_bound [CompactSpace G] (hopen : IsOpen ((T0 A b : Submodule OL A.V) : Set A.V))
    (hdiv : DivT A (T0 A b)) : ∃ a : OL, a ≠ 0 ∧ ∀ x ∈ Tst A b, a • x ∈ T0 A b := by
  have hS : IsCompact (⋃ j, Set.range fun g => A.ρ g (b j)) :=
    isCompact_iUnion fun j => isCompact_range (A.cont (b j))
  obtain ⟨a, ha, hb⟩ := bound_compact A (T0 A b) hopen hdiv _ hS
  refine ⟨a, ha, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, y, hy, rfl⟩ := Set.mem_iUnion.1 hx
    obtain ⟨o, rfl⟩ := integral_span_coordinates A b y hy

    rw [map_sum, Finset.smul_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [LinearMap.map_smul_of_tower, smul_comm]
    exact Submodule.smul_mem _ _ (hb _ (Set.mem_iUnion.2 ⟨j, g, rfl⟩))
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem noZero (hinj : Function.Injective (algebraMap OL LL)) : NoZeroSMulDivisors OL A.V :=
  ⟨fun {c x} h => by
    rw [← algebraMap_smul LL c x] at h
    rcases smul_eq_zero.1 h with h | h
    · exact Or.inl (hinj (h.trans (map_zero _).symm))
    · exact Or.inr h⟩

def latSt [CompactSpace G] [IsNoetherianRing OL] [IsPrincipalIdealRing OL] [IsTopologicalRing LL]
    (hO : IsOpen (Set.range (algebraMap OL LL))) [IsFractionRing OL LL] : Lattice (O := OL) A.ρ where
  T := Tst A b
  stable := Tst_stable A b
  fg := by
    have hinj : Function.Injective (algebraMap OL LL) := IsFractionRing.injective OL LL
    obtain ⟨a, ha, hab⟩ := Tst_bound A b (integral_span_open A b hO) (integral_span_divisible A b)
    haveI : Module.Finite OL ↥(Submodule.span OL (Set.range b)) :=
      Module.Finite.span_of_finite OL (Set.finite_range b)
    haveI := noZero A hinj
    let f : ↥(Tst A b) →ₗ[OL] ↥(Submodule.span OL (Set.range b)) :=
      { toFun := fun x => ⟨a • x.1, by
          obtain ⟨o, ho⟩ := integral_span_coordinates A b _ (hab x.1 x.2)
          rw [ho]
          exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)⟩
        map_add' := fun x y => Subtype.ext (smul_add a x.1 y.1)
        map_smul' := fun o x => Subtype.ext (smul_comm a o x.1) }
    have hf : Function.Injective f := fun x y h => by
      have h' : a • (x.1 - y.1) = 0 := by
        rw [smul_sub]
        exact sub_eq_zero.2 (congrArg Subtype.val h)
      rcases smul_eq_zero.1 h' with h0 | h0
      · exact absurd h0 ha
      · exact Subtype.ext (sub_eq_zero.1 h0)
    haveI : Module.Finite OL ↥(Tst A b) := Module.Finite.of_injective f hf
    exact Module.Finite.iff_fg.1 inferInstance
  free := by
    haveI := noZero A (IsFractionRing.injective OL LL)
    haveI : Module.Finite OL ↥(Tst A b) := by
      have hinj : Function.Injective (algebraMap OL LL) := IsFractionRing.injective OL LL
      obtain ⟨a, ha, hab⟩ := Tst_bound A b (integral_span_open A b hO) (integral_span_divisible A b)
      haveI : Module.Finite OL ↥(Submodule.span OL (Set.range b)) :=
        Module.Finite.span_of_finite OL (Set.finite_range b)
      let f : ↥(Tst A b) →ₗ[OL] ↥(Submodule.span OL (Set.range b)) :=
        { toFun := fun x => ⟨a • x.1, by
            obtain ⟨o, ho⟩ := integral_span_coordinates A b _ (hab x.1 x.2)
            rw [ho]
            exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)⟩
          map_add' := fun x y => Subtype.ext (smul_add a x.1 y.1)
          map_smul' := fun o x => Subtype.ext (smul_comm a o x.1) }
      have hf : Function.Injective f := fun x y h => by
        have h' : a • (x.1 - y.1) = 0 := by
          rw [smul_sub]
          exact sub_eq_zero.2 (congrArg Subtype.val h)
        rcases smul_eq_zero.1 h' with h0 | h0
        · exact absurd h0 ha
        · exact Subtype.ext (sub_eq_zero.1 h0)
      exact Module.Finite.of_injective f hf
    exact Module.free_of_finite_type_torsion_free'
  span := by
    rw [eq_top_iff, ← b.span_eq]
    exact Submodule.span_le.2 fun x ⟨j, hj⟩ => hj ▸ Submodule.subset_span (integral_span_le_stable A b (basis_mem_integral_span A b j))

theorem latSt_open [CompactSpace G] [IsNoetherianRing OL] [IsPrincipalIdealRing OL] [IsTopologicalRing LL]
    (hO : IsOpen (Set.range (algebraMap OL LL))) [IsFractionRing OL LL] :
    IsOpen (((latSt A b hO).T : Submodule OL A.V) : Set A.V) := by
  haveI : ContinuousNeg A.V := ⟨by
    have h : (fun v : A.V => -v) = fun v => (-1 : LL) • v := funext fun v => (neg_one_smul LL v).symm
    rw [h]
    exact continuous_const_smul _⟩
  haveI : IsTopologicalAddGroup A.V := {}
  exact Submodule.isOpen_mono (integral_span_le_stable A b) (integral_span_open A b hO)

theorem latSt_div [CompactSpace G] [IsNoetherianRing OL] [IsPrincipalIdealRing OL] [IsTopologicalRing LL]
    (hO : IsOpen (Set.range (algebraMap OL LL))) [IsFractionRing OL LL] : DivT A (latSt A b hO).T := fun v => by
  obtain ⟨a, ha, h⟩ := integral_span_divisible A b v
  exact ⟨a, ha, integral_span_le_stable A b h⟩

theorem finDim_of_tate [CompactSpace G] [IsNoetherianRing OL] [IsPrincipalIdealRing OL] [IsTopologicalRing LL]
    (hO : IsOpen (Set.range (algebraMap OL LL))) [IsFractionRing OL LL]
    (hT : ∀ LA : Lattice (O := OL) A.ρ, Module.Finite OL (LatticeCohomology LA))
    {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) : FiniteDimensional LL (FiniteCohomology PD A.ρ) := by
  let b₀ := Module.finBasis LL A.V
  haveI := hT (latSt A b₀ hO)
  haveI := finite_H1V A (latSt A b₀ hO) (latSt_open A b₀ hO) (latSt_div A b₀ hO) (IsFractionRing.injective OL LL)
  exact finDim_H1fV A PD

end Stab

section Rank

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {OL : Type} [CommRing OL] [IsDomain OL] [Algebra OL LL] {Qp : Type} [Field Qp]
  [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G]
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [FiniteDimensional (FractionRing O) V]
  (σ : O ≃+* OL) (hσ : ∀ c : O, algebraMap OL LL (σ c) = e (algebraMap O (FractionRing O) c))
  {n : Type} [Fintype n] (bV : Basis n (FractionRing O) V)
  {L : Type} [AddCommGroup L] [Module O L] (bL : Basis n O L) (iL : L →ₗ[O] V) (hb : ∀ j, iL (bL j) = bV j)
  (ρ : Representation O Γ V) (ι : G →* Γ) (hc : ∀ v : TrV e V, Continuous fun g => repL e ρ ι g v)
  (ρL : Representation O Γ L) (hiL : ∀ γ m, iL (ρL γ m) = ρ γ (iL m))

abbrev QF := ↥(finZ e PD ρ ι) ⧸ (LinearMap.range (KDim.cobK ρ)).comap (finZ e PD ρ ι).subtype

abbrev PF := (KFin.finPreG iL (finZ e PD ρ ι)).comap (coZ1s ρL).subtype

def thet0 : ↥(PF e PD iL ρ ι ρL) →ₗ[O] QF e PD ρ ι where
  toFun p := Submodule.Quotient.mk ⟨fun γ => iL (((p : coZ1s ρL) : Γ → L) γ), p.2⟩
  map_add' p q := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    exact Subtype.ext (funext fun γ => map_add iL _ _)
  map_smul' c p := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (funext fun γ => map_smul iL c _)

abbrev hF : ↥(PF e PD iL ρ ι ρL) →ₗ[O] H1z ρL :=
  (Submodule.mkQ ((coB1 ρL).comap (coZ1s ρL).subtype)).comp (PF e PD iL ρ ι ρL).subtype

include hiL in
theorem ker_le : LinearMap.ker (hF e PD iL ρ ι ρL) ≤ LinearMap.ker (thet0 e PD iL ρ ι ρL) := by
  intro p hp
  rw [LinearMap.mem_ker] at hp ⊢
  have h := (Submodule.Quotient.mk_eq_zero _).mp hp
  obtain ⟨m, hm⟩ := h
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨iL m, funext fun γ => ?_⟩
  have h2 : ((p : coZ1s ρL) : Γ → L) γ = ρL γ m - m := (congrFun hm γ).symm
  show ρ γ (iL m) - iL m = iL (((p : coZ1s ρL) : Γ → L) γ)
  rw [h2, map_sub, hiL]

theorem F_eq : KFin.FfG ρL iL (finZ e PD ρ ι) = LinearMap.range (hF e PD iL ρ ι ρL) := by
  rw [LinearMap.range_comp, Submodule.range_subtype]
  rfl

def thet : ↥(KFin.FfG ρL iL (finZ e PD ρ ι)) →ₗ[O] QF e PD ρ ι :=
  ((LinearMap.ker (hF e PD iL ρ ι ρL)).liftQ (thet0 e PD iL ρ ι ρL) (ker_le e PD iL ρ ι ρL hiL)).comp
    (((hF e PD iL ρ ι ρL).quotKerEquivRange).symm.toLinearMap.comp
      (LinearEquiv.ofEq _ _ (F_eq e PD iL ρ ι ρL)).toLinearMap)

theorem thet_mk (p : ↥(PF e PD iL ρ ι ρL)) :
    thet e PD iL ρ ι ρL hiL ⟨hF e PD iL ρ ι ρL p, (F_eq e PD iL ρ ι ρL).symm ▸ LinearMap.mem_range_self _ p⟩ =
      thet0 e PD iL ρ ι ρL p := by
  have h1 : LinearEquiv.ofEq _ _ (F_eq e PD iL ρ ι ρL)
      ⟨hF e PD iL ρ ι ρL p, (F_eq e PD iL ρ ι ρL).symm ▸ LinearMap.mem_range_self _ p⟩ =
      ⟨hF e PD iL ρ ι ρL p, LinearMap.mem_range_self _ p⟩ := Subtype.ext rfl
  show ((LinearMap.ker (hF e PD iL ρ ι ρL)).liftQ (thet0 e PD iL ρ ι ρL) (ker_le e PD iL ρ ι ρL hiL))
      ((hF e PD iL ρ ι ρL).quotKerEquivRange.symm (LinearEquiv.ofEq _ _ (F_eq e PD iL ρ ι ρL)
        ⟨hF e PD iL ρ ι ρL p, (F_eq e PD iL ρ ι ρL).symm ▸ LinearMap.mem_range_self _ p⟩)) = _
  rw [h1, LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

end Rank

section RankLoc

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {OL : Type} [CommRing OL] [IsDomain OL] [Algebra OL LL] {Qp : Type} [Field Qp]
  [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G]
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [FiniteDimensional (FractionRing O) V]
  (σ : O ≃+* OL) (hσ : ∀ c : O, algebraMap OL LL (σ c) = e (algebraMap O (FractionRing O) c))
  {n : Type} [Fintype n] (bV : Basis n (FractionRing O) V)
  {L : Type} [AddCommGroup L] [Module O L] (bL : Basis n O L) (iL : L →ₗ[O] V) (hb : ∀ j, iL (bL j) = bV j)
  (ρ : Representation O Γ V) (ι : G →* Γ) (hc : ∀ v : TrV e V, Continuous fun g => repL e ρ ι g v)
  (ρL : Representation O Γ L) (hiL : ∀ γ m, iL (ρL γ m) = ρ γ (iL m))

def bA : Basis n LL (grepV e OL (Qp := Qp) ρ ι hc).V :=
  Basis.ofEquivFun
    { toFun := fun v j => e (bV.equivFun (show V from v) j)
      invFun := fun f => (bV.equivFun.symm fun j => e.symm (f j) : V)
      map_add' := fun u v => funext fun j => by
        have h : bV.equivFun ((show V from u) + (show V from v)) j =
            bV.equivFun (show V from u) j + bV.equivFun (show V from v) j := by
          rw [map_add (f := _)]
          rfl
        exact (congrArg e h).trans (map_add e _ _)
      map_smul' := fun c v => funext fun j => by
        have h : bV.equivFun (e.symm c • (show V from v)) j = e.symm c * bV.equivFun (show V from v) j := by
          rw [map_smul]
          rfl
        show e (bV.equivFun (e.symm c • (show V from v)) j) = c * e (bV.equivFun (show V from v) j)
        rw [h, map_mul, RingEquiv.apply_symm_apply]
      left_inv := fun v => by
        show bV.equivFun.symm (fun j => e.symm (e (bV.equivFun (show V from v) j))) = (show V from v)
        simp only [RingEquiv.symm_apply_apply]
        exact bV.equivFun.symm_apply_apply _
      right_inv := fun f => funext fun j => by
        show e (bV.equivFun (bV.equivFun.symm fun j => e.symm (f j)) j) = f j
        rw [LinearEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] }

theorem bA_coord (x : (grepV e OL (Qp := Qp) ρ ι hc).V) (j : n) :
    (bA e (OL := OL) (Qp := Qp) bV ρ ι hc).equivFun x j = e (bV.equivFun (show V from x) j) := by
  unfold bA
  rw [Basis.equivFun_ofEquivFun]
  rfl

include hσ hb in
theorem coord_iL (m : L) (j : n) : bV.equivFun (iL m) j = algebraMap O (FractionRing O) (bL.equivFun m j) := by
  have h : iL m = bV.equivFun.symm (fun j => algebraMap O (FractionRing O) (bL.equivFun m j)) := by
    rw [Basis.equivFun_symm_apply]
    conv_lhs => rw [← bL.sum_equivFun m]

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hb, algebraMap_smul]
  rw [h, LinearEquiv.apply_symm_apply]

include hσ hb in
theorem mem_integral_span_iff_image (x : TrV e V) :
    x ∈ T0 (grepV e OL (Qp := Qp) ρ ι hc) (bA e (OL := OL) (Qp := Qp) bV ρ ι hc) ↔ ∃ m : L, tr e (iL m) = x := by
  constructor
  · intro hx
    choose o ho using hx
    refine ⟨∑ j, σ.symm (o j) • bL j, ?_⟩
    show iL (∑ j, σ.symm (o j) • bL j) = (x : V)
    conv_rhs => rw [← bV.sum_equivFun (x : V)]

    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hb, ← algebraMap_smul (FractionRing O) (σ.symm (o j)) (bV j)]
    congr 1
    apply e.injective
    have h1 : algebraMap OL LL (o j) = e (bV.equivFun (show V from x) j) :=
      (ho j).trans (bA_coord e (OL := OL) (Qp := Qp) bV ρ ι hc x j)
    rw [← hσ, RingEquiv.apply_symm_apply, h1]
  · rintro ⟨m, rfl⟩ j
    refine ⟨σ (bL.equivFun m j), ?_⟩
    rw [hσ, ← coord_iL e σ hσ bV bL iL hb]
    exact (bA_coord e (OL := OL) (Qp := Qp) bV ρ ι hc _ j).symm

variable [IsTopologicalRing LL] [IsFractionRing OL LL]

include hb in
theorem div_L (v : V) : ∃ s : O, s ≠ 0 ∧ ∃ m : L, iL m = s • v := by
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ
    (fun j => bV.equivFun v j)
  choose c hc using fun j => hs j (Finset.mem_univ j)
  refine ⟨s, nonZeroDivisors.ne_zero s.2, ∑ j, c j • bL j, ?_⟩

  rw [map_sum]
  conv_rhs => rw [← bV.sum_equivFun v, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hb, ← algebraMap_smul (FractionRing O) (c j), hc j, smul_assoc]

variable [CompactSpace G]

include hσ hb hc hiL in
theorem bound_fin (hι : Function.Surjective ι) (hO : IsOpen (Set.range (algebraMap OL LL))) (c : ↥(finZ e PD ρ ι)) :
    ∃ s : O, s ≠ 0 ∧ ∃ p : Γ → L, ∀ γ, iL (p γ) = s • (c : Γ → V) γ := by
  have hcont : Continuous fun g => tr e ((c : Γ → V) (ι g)) := c.2.1.1
  obtain ⟨a, ha, h⟩ := bound_cont (grepV e OL (Qp := Qp) ρ ι hc) _ (integral_span_open _ (bA e (OL := OL) (Qp := Qp) bV ρ ι hc) hO)
    (integral_span_divisible _ (bA e (OL := OL) (Qp := Qp) bV ρ ι hc)) _ hcont
  have hs : σ.symm a ≠ 0 := fun h0 => ha (by rw [← σ.apply_symm_apply a, h0, map_zero])
  have hγ : ∀ γ, ∃ m : L, iL m = σ.symm a • (c : Γ → V) γ := by
    intro γ
    obtain ⟨g, rfl⟩ := hι γ
    obtain ⟨m, hm⟩ := (mem_integral_span_iff_image e σ hσ bV bL iL hb ρ ι hc (Qp := Qp) _).1 (h g)
    refine ⟨m, ?_⟩
    have h2 := smul_OL e σ hσ (σ.symm a) ((c : Γ → V) (ι g))
    rw [RingEquiv.apply_symm_apply] at h2
    rw [← h2]
    exact hm
  choose p hp using hγ
  exact ⟨σ.symm a, hs, p, hp⟩

end RankLoc

section RankThm

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {OL : Type} [CommRing OL] [IsDomain OL] [Algebra OL LL] {Qp : Type} [Field Qp]
  [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G]
  {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  [FiniteDimensional (FractionRing O) V]
  (σ : O ≃+* OL) (hσ : ∀ c : O, algebraMap OL LL (σ c) = e (algebraMap O (FractionRing O) c))
  {n : Type} [Fintype n] (bV : Basis n (FractionRing O) V)
  {L : Type} [AddCommGroup L] [Module O L] (bL : Basis n O L) (iL : L →ₗ[O] V) (hb : ∀ j, iL (bL j) = bV j)
  (ρ : Representation O Γ V) (ι : G →* Γ) (hc : ∀ v : TrV e V, Continuous fun g => repL e ρ ι g v)
  (ρL : Representation O Γ L) (hiL : ∀ γ m, iL (ρL γ m) = ρ γ (iL m))
  [IsTopologicalRing LL] [IsFractionRing OL LL] [CompactSpace G]

include hσ hb hc in
theorem thet_loc (hι : Function.Bijective ι) (hO : IsOpen (Set.range (algebraMap OL LL)))
    (hinj : Function.Injective iL) :
    IsLocalizedModule (nonZeroDivisors O) (thet e PD iL ρ ι ρL hiL) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s
    rw [Module.End.isUnit_iff]
    have hs : algebraMap O (FractionRing O) (s : O) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    constructor
    · intro q1 q2 h
      rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
        ← algebraMap_smul (FractionRing O) (s : O) q1, ← algebraMap_smul (FractionRing O) (s : O) q2] at h
      exact smul_right_injective _ hs h
    · intro q
      refine ⟨(algebraMap O (FractionRing O) (s : O))⁻¹ • q, ?_⟩
      rw [Module.algebraMap_end_apply, ← algebraMap_smul (FractionRing O) (s : O), smul_smul,
        mul_inv_cancel₀ hs, one_smul]
  · intro q
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨s, hs, p, hp⟩ := bound_fin e PD σ hσ bV bL iL hb ρ ι hc ρL hiL (Qp := Qp) hι.2 hO c
    have hcoc : ∀ γ δ, (c : Γ → V) (γ * δ) = (c : Γ → V) γ + ρ γ ((c : Γ → V) δ) := by
      intro γ δ
      obtain ⟨g, rfl⟩ := hι.2 γ
      obtain ⟨h, rfl⟩ := hι.2 δ
      have h1 := c.2.1.2 g h
      rw [← map_mul]
      exact h1
    have hpz : p ∈ coZ1s ρL := fun γ δ => hinj (by rw [map_add (f := _), hiL, hp, hp, hp, hcoc, smul_add, map_smul])
    have hpf : p ∈ KFin.finPreG iL (finZ e PD ρ ι) := by
      show (fun γ => iL (p γ)) ∈ finZ e PD ρ ι
      have h1 : (fun γ => iL (p γ)) = s • (c : Γ → V) := funext hp
      rw [h1]
      exact ((finZ e PD ρ ι).restrictScalars O).smul_mem s c.2
    let z : ↥(PF e PD iL ρ ι ρL) := ⟨⟨p, hpz⟩, hpf⟩
    refine ⟨(⟨hF e PD iL ρ ι ρL z, (F_eq e PD iL ρ ι ρL).symm ▸ LinearMap.mem_range_self _ z⟩,
      ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩), ?_⟩
    show (s : O) • (Submodule.Quotient.mk c : QF e PD ρ ι) = _
    rw [thet_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (funext fun γ => (hp γ).symm)
  · intro z1 z2 h
    have hz : ((z1 - z2 : ↥(KFin.FfG ρL iL (finZ e PD ρ ι))) : H1z ρL) ∈ LinearMap.range (hF e PD iL ρ ι ρL) := by
      rw [← F_eq e PD iL ρ ι ρL]
      exact (z1 - z2).2
    obtain ⟨p, hp⟩ := hz
    have h1 : thet e PD iL ρ ι ρL hiL (z1 - z2) = thet0 e PD iL ρ ι ρL p := by
      have h2 : z1 - z2 = ⟨hF e PD iL ρ ι ρL p, (F_eq e PD iL ρ ι ρL).symm ▸ LinearMap.mem_range_self _ p⟩ :=
        Subtype.ext hp.symm
      rw [h2, thet_mk]
    have h0 : thet0 e PD iL ρ ι ρL p = 0 := by rw [← h1, map_sub, h, sub_self]
    obtain ⟨v, hv⟩ := (Submodule.Quotient.mk_eq_zero _).mp h0
    obtain ⟨s, hs, m, hm⟩ := div_L bV bL iL hb v
    refine ⟨⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩, ?_⟩
    rw [← sub_eq_zero, ← smul_sub]
    show (s : O) • (z1 - z2) = 0
    apply Subtype.ext
    show (s : O) • ((z1 - z2 : ↥(KFin.FfG ρL iL (finZ e PD ρ ι))) : H1z ρL) = 0
    rw [← hp]
    show (s : O) • (Submodule.Quotient.mk (p : coZ1s ρL) : H1z ρL) = 0
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨m, funext fun γ => hinj ?_⟩
    show iL (ρL γ m - m) = iL ((s : O) • ((p : coZ1s ρL) : Γ → L) γ)
    rw [map_sub, hiL, hm, map_smul, map_smul, ← smul_sub]
    congr 1
    exact congrFun hv γ

include hσ hb hc hiL in
theorem finrank_Ff (hι : Function.Bijective ι) (hO : IsOpen (Set.range (algebraMap OL LL)))
    (hinj : Function.Injective iL) :
    Module.finrank O (↥(KFin.FfG ρL iL (finZ e PD ρ ι)) ⧸ Submodule.torsion O ↥(KFin.FfG ρL iL (finZ e PD ρ ι))) =
      Module.finrank LL (FiniteCohomology PD (repL e ρ ι)) := by
  haveI := thet_loc e PD σ hσ bV bL iL hb ρ ι hc ρL hiL (Qp := Qp) hι hO hinj
  have h1 : Module.finrank O (↥(KFin.FfG ρL iL (finZ e PD ρ ι)) ⧸ Submodule.torsion O ↥(KFin.FfG ρL iL (finZ e PD ρ ι))) =
      Module.finrank O ↥(KFin.FfG ρL iL (finZ e PD ρ ι)) := by
    unfold Module.finrank
    rw [rank_quotient_eq_of_le_torsion le_rfl]
  have h2 := IsLocalizedModule.finrank_eq (p := nonZeroDivisors O) (f := thet e PD iL ρ ι ρL hiL) le_rfl
  have h3 := IsLocalization.finrank_eq (S := FractionRing O) (p := nonZeroDivisors O) (N := QF e PD ρ ι) le_rfl
  have h4 : Module.finrank (FractionRing O) (QF e PD ρ ι) = Module.finrank LL (FiniteCohomology PD (repL e ρ ι)) := by
    unfold Module.finrank
    rw [KDim.rank_finQuot (e := e) (PD := PD) (ρ := ρ) (hι := hι)]
  rw [h1, ← h2, ← h3, h4]

include hσ hb hc hiL in
theorem finrank_Ff' (hι : Function.Bijective ι) (hO : IsOpen (Set.range (algebraMap OL LL)))
    (hinj : Function.Injective iL) (Zf : Submodule (FractionRing O) (Γ → V)) (hZ : Zf = finZ e PD ρ ι) :
    Module.finrank O (↥(KFin.FfG ρL iL Zf) ⧸ Submodule.torsion O ↥(KFin.FfG ρL iL Zf)) =
      Module.finrank LL (FiniteCohomology PD (repL e ρ ι)) := by
  subst hZ
  exact finrank_Ff e PD σ hσ bV bL iL hb ρ ι hc ρL hiL (Qp := Qp) hι hO hinj

end RankThm

section Rec

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev bVr : Basis {a // RepresentationBoundsCohomology.blk D.R a = 0} (FractionRing (D.nd.O i)) (KFin.Vr i Dd) :=
  Pi.basisFun (FractionRing (D.nd.O i)) {a // RepresentationBoundsCohomology.blk D.R a = 0}

abbrev bLr : Basis {a // RepresentationBoundsCohomology.blk D.R a = 0} (D.nd.O i) (KFin.Lr i Dd) :=
  Pi.basisFun (D.nd.O i) {a // RepresentationBoundsCohomology.blk D.R a = 0}

theorem iLr_basis (j : {a // RepresentationBoundsCohomology.blk D.R a = 0}) : KFin.iLr i Dd (bLr i Dd j) = bVr i Dd j := by
  funext k
  have h1 : (bLr i Dd j : {a // RepresentationBoundsCohomology.blk D.R a = 0} → D.nd.O i) k = (Pi.single j (1 : D.nd.O i) : _ → D.nd.O i) k :=
    congrFun (Pi.basisFun_apply (D.nd.O i) {a // RepresentationBoundsCohomology.blk D.R a = 0} j) k
  have h2 : (bVr i Dd j : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) k =
      (Pi.single j (1 : FractionRing (D.nd.O i)) : _ → FractionRing (D.nd.O i)) k :=
    congrFun (Pi.basisFun_apply (FractionRing (D.nd.O i)) {a // RepresentationBoundsCohomology.blk D.R a = 0} j) k
  show algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((bLr i Dd j : {a // RepresentationBoundsCohomology.blk D.R a = 0} → D.nd.O i) k) =
    (bVr i Dd j : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) k
  rw [h1, h2]
  rcases eq_or_ne k j with rfl | h
  · simp
  · simp [h]

theorem iLr_inj : Function.Injective (KFin.iLr i Dd) := fun _ _ h =>
  funext fun k => IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i)) (congrFun h k)

instance finDimVr : FiniteDimensional (FractionRing (D.nd.O i)) (KFin.Vr i Dd) :=
  inferInstanceAs (FiniteDimensional (FractionRing (D.nd.O i)) ({a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)))

theorem finFf_of (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) (l : K.Col i dc) (hO : KHf.OrbC i dc (KFin.ρV i dc Dd l)) :
    KFin.FinFf i dc Dd l := by
  have hn := KDim.col_over i dc l
  show Module.Finite (D.nd.O i) ↥(KFin.FfG (KFin.ρL i dc Dd l) (KFin.iLr i Dd)
    (KHf.fZ i dc (K.colIdx i dc l) (KFin.ρV i dc Dd l)))
  rw [KHf.fZ_pos i dc _ hn]
  exact finite_FfG (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (D.nbr i _ hn).eO
    (fun c => (Br.toLLK_alg (D.nbr i _ hn) c).symm) (bVr i Dd) (bLr i Dd) (KFin.iLr i Dd) (iLr_basis i Dd)
    (KFin.ρV i dc Dd l) (Br.iota D.nbr i _ hn) (hO hn) (KFin.ρL i dc Dd l) (KFin.iL_equiv i dc Dd l)
    (Br.ι_bijective (D.nbr i _ hn)).2 (iLr_inj i Dd)
    (hFin _ hn (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) _ _)

end Rec

section RecRank

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem compact_G {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    CompactSpace (Br.G D.nbr i w hw) :=
  isCompact_iff_compactSpace.1 (InfiniteGalois.fixingSubgroup_isClosed _).isCompact

set_option synthInstance.maxHeartbeats 100000 in
theorem jr_eq (l : K.Col i dc) :
    KFin.jr i dc ρ π (K.colIdx i dc l) =
      Module.finrank (Br.LL D.nbr i _ (KDim.col_over i dc l))
        (FiniteCohomology (Br.PD D.loc D.nbr i _ (KDim.col_over i dc l))
          (KDim.repW i dc ρ π (K.colIdx i dc l) (KDim.col_over i dc l))) := by
  show KHf.jK i dc ρ π (K.colIdx i dc l) = _
  unfold KHf.jK
  rw [dite_eq_left (KDim.col_over i dc l)]
  rfl

set_option synthInstance.maxHeartbeats 100000 in
def DimV (l : K.Col i dc) : Prop :=
  Module.finrank (Br.LL D.nbr i _ (KDim.col_over i dc l))
      (FiniteCohomology (Br.PD D.loc D.nbr i _ (KDim.col_over i dc l))
        (repL (eK (D.nbr i _ (KDim.col_over i dc l))) (KFin.ρV i dc Dd l) (Br.iota D.nbr i _ (KDim.col_over i dc l)))) =
    Module.finrank (Br.LL D.nbr i _ (KDim.col_over i dc l))
      (FiniteCohomology (Br.PD D.loc D.nbr i _ (KDim.col_over i dc l))
        (KDim.repW i dc ρ π (K.colIdx i dc l) (KDim.col_over i dc l)))

set_option maxHeartbeats 1000000 in
theorem rankFf_of (hO : Formalism.MainNotions.N.LitGoodO) (l : K.Col i dc) (hOrb : KHf.OrbC i dc (KFin.ρV i dc Dd l))
    (hdim : DimV i dc Dd ρ π l) : KFin.RankFf i dc Dd ρ π l := by
  have hn := KDim.col_over i dc l
  obtain ⟨⟨_, hdvr, hfr⟩, -, -, htop, hopen⟩ := hO (D.nd.l i) (D.nbr i _ hn).LL
  haveI := hfr
  haveI := htop
  haveI := compact_G i hn
  have hZ : KFin.Zf i dc Dd l = finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (KFin.ρV i dc Dd l)
      (Br.iota D.nbr i _ hn) := KHf.fZ_pos i dc _ hn
  have h1 := finrank_Ff' (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (D.nbr i _ hn).eO
    (fun c => (Br.toLLK_alg (D.nbr i _ hn) c).symm) (bVr i Dd) (bLr i Dd) (KFin.iLr i Dd) (iLr_basis i Dd)
    (KFin.ρV i dc Dd l) (Br.iota D.nbr i _ hn) (hOrb hn) (KFin.ρL i dc Dd l) (KFin.iL_equiv i dc Dd l)
    (Br.ι_bijective (D.nbr i _ hn)) hopen (iLr_inj i Dd) _ hZ
  exact h1.trans (hdim.trans (jr_eq i dc ρ π l).symm)

end RecRank

section RecX

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem finX_of (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) (hO : Formalism.MainNotions.N.LitGoodO) (x' : X') (l : K.Col i dc)
    (hc : KDim.ContX i dc r χ x' l) : KDim.FinX i dc r χ x' l := by
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  have hn := KDim.col_over i dc l
  obtain ⟨⟨_, hdvr, hfr⟩, -, -, htop, hopen⟩ := hO (D.nd.l i) (D.nbr i _ hn).LL
  haveI := hdvr
  haveI := hfr
  haveI := htop
  haveI := compact_G i hn
  exact finDim_of_tate (KDim.grepX i dc r χ x' l hc) hopen
    (fun LA => hFin _ hn (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) _ LA) (Br.PD D.loc D.nbr i _ hn)

end RecX

section Final

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem rankFf (l : K.Col i dc) (hOrb : KHf.OrbC i dc (KFin.ρV i dc Dd l)) (hdim : DimV i dc Dd ρ π l) :
    KFin.RankFf i dc Dd ρ π l :=
  rankFf_of i dc Dd ρ π Formalism.MainNotions.N.T2.litGoodO l hOrb hdim

end Final

section FinalX

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem finX (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) (x' : X') (l : K.Col i dc) (hc : KDim.ContX i dc r χ x' l) :
    KDim.FinX i dc r χ x' l :=
  finX_of i dc r χ hFin Formalism.MainNotions.N.T2.litGoodO x' l hc

end FinalX

section RecOrb

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))

theorem orbC_V
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (l : K.Col i dc) : KHf.OrbC i dc (KFin.ρV i dc Dd l) :=
  KOrb.orbC_uRep i dc r π g0 eB e₁ s Dd hD hc (V := KFin.Vr i Dd)
    (fun c v => KOrb.latM_alg (i := i) (Dd := Dd) (Dd.ρk 0) c v) (K.colIdx i dc l)

theorem finFf_rec (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (l : K.Col i dc) : KFin.FinFf i dc Dd l :=
  finFf_of i dc Dd hFin l (orbC_V i dc r π g0 eB e₁ s Dd hD hc l)

theorem rankFf_rec
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (l : K.Col i dc) (hdim : DimV i dc Dd ρ π l) : KFin.RankFf i dc Dd ρ π l :=
  rankFf i dc Dd ρ π l (orbC_V i dc r π g0 eB e₁ s Dd hD hc l) hdim

end RecOrb

section IsoH1f

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ Kk : Type} [Field Qp] [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) {LL : Type} [Field LL] [Algebra Qp LL]
    {V W : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup W] [Module LL W] [Module Qp W] [IsScalarTower Qp LL W]
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]
    [TopologicalSpace W] [ContinuousAdd W] [ContinuousConstSMul LL W]
    (ρ : Representation LL G V) (ρ' : Representation LL G W)

theorem finrank_H1fV_congr (f : V ≃ₗ[LL] W) (hf : Continuous f) (hf' : Continuous f.symm)
    (heq : ∀ g v, f (ρ g v) = ρ' g (f v)) :
    Module.finrank LL (FiniteCohomology PD ρ) = Module.finrank LL (FiniteCohomology PD ρ') := by
  have heq' : ∀ g w, f.symm (ρ' g w) = ρ g (f.symm w) := fun g w => f.injective (by
    rw [heq, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply])
  let φ : ↥(finiteCocycles PD ρ) →ₗ[LL] ↥(finiteCocycles PD ρ') :=
    { toFun := fun c => ⟨f ∘ c.1, (cocyclesFunctorial_holds G Qp K₀ Kk B BdR PD LL V W ρ ρ' f.toLinearMap hf heq c.1).2 c.2⟩
      map_add' := fun a b => Subtype.ext (funext fun g => map_add f _ _)
      map_smul' := fun a b => Subtype.ext (funext fun g => map_smul f _ _) }
  let ψ : ↥(finiteCocycles PD ρ') →ₗ[LL] ↥(finiteCocycles PD ρ) :=
    { toFun := fun c => ⟨f.symm ∘ c.1,
        (cocyclesFunctorial_holds G Qp K₀ Kk B BdR PD LL W V ρ' ρ f.symm.toLinearMap hf' heq' c.1).2 c.2⟩
      map_add' := fun a b => Subtype.ext (funext fun g => map_add f.symm _ _)
      map_smul' := fun a b => Subtype.ext (funext fun g => map_smul f.symm _ _) }
  let E : ↥(finiteCocycles PD ρ) ≃ₗ[LL] ↥(finiteCocycles PD ρ') := LinearEquiv.ofLinear φ ψ
    (LinearMap.ext fun c => Subtype.ext (funext fun g => f.apply_symm_apply _))
    (LinearMap.ext fun c => Subtype.ext (funext fun g => f.symm_apply_apply _))
  have hpq : ((B1 ρ).comap (finiteCocycles PD ρ).subtype).map E.toLinearMap = (B1 ρ').comap (finiteCocycles PD ρ').subtype := by
    ext c
    constructor
    · rintro ⟨c₀, ⟨x, hx⟩, rfl⟩
      refine ⟨f x, funext fun g => ?_⟩
      have h : (c₀ : G → V) g = ρ g x - x := (congrFun hx g).symm
      show ρ' g (f x) - f x = f ((c₀ : G → V) g)
      rw [h, map_sub, heq]
    · rintro ⟨y, hy⟩
      refine ⟨E.symm c, ⟨f.symm y, funext fun g => ?_⟩, E.apply_symm_apply c⟩
      have h : (c : G → W) g = ρ' g y - y := (congrFun hy g).symm
      show ρ g (f.symm y) - f.symm y = f.symm ((c : G → W) g)
      rw [h, map_sub, heq']
  exact (Submodule.Quotient.equiv _ _ E hpq).finrank_eq

end IsoH1f

section RecIso

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def IsoV (l : K.Col i dc) : Prop :=
  ∃ f : TrV (eK (D.nbr i _ (KDim.col_over i dc l))) (KFin.Vr i Dd) ≃ₗ[Br.LL D.nbr i _ (KDim.col_over i dc l)]
      (Fin D.R.r → Br.LL D.nbr i _ (KDim.col_over i dc l)),
    ∀ g v, f (repL (eK (D.nbr i _ (KDim.col_over i dc l))) (KFin.ρV i dc Dd l)
        (Br.iota D.nbr i _ (KDim.col_over i dc l)) g v) =
      KDim.repW i dc ρ π (K.colIdx i dc l) (KDim.col_over i dc l) g (f v)

theorem dimV_of_iso (l : K.Col i dc) (h : IsoV i dc Dd ρ π l) : DimV i dc Dd ρ π l := by
  obtain ⟨f, hf⟩ := h
  have hn := KDim.col_over i dc l
  obtain ⟨-, -, -, htop, -⟩ := Formalism.MainNotions.N.T2.litGoodO (D.nd.l i) (D.nbr i _ hn).LL
  haveI := htop
  exact finrank_H1fV_congr (Br.PD D.loc D.nbr i _ hn) _ _ f
    (IsModuleTopology.continuous_of_linearMap f.toLinearMap)
    (IsModuleTopology.continuous_of_linearMap f.symm.toLinearMap) hf

theorem rankFf_iso (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (g0 : GE D.nd)
    (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (l : K.Col i dc) (hiso : IsoV i dc Dd ρ π l) : KFin.RankFf i dc Dd ρ π l :=
  rankFf_rec i dc r π g0 eB e₁ s Dd ρ hD hc l (dimV_of_iso i dc Dd ρ π l hiso)

end RecIso

end Formalism.MainNotions.N.KTate
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Formalism.NG Module Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.FIN

section SpanK

variable {O : Type} [CommRing O] [IsDomain O] {H : Type} [AddCommGroup H] [Module O H]
  [Module (FractionRing O) H] [IsScalarTower O (FractionRing O) H]

theorem mem_spanK (S : Submodule O H) {x : H} (hx : x ∈ Submodule.span (FractionRing O) (S : Set H)) :
    ∃ t : O, t ≠ 0 ∧ t • x ∈ S := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by rw [one_smul]; exact hy⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact S.zero_mem⟩
  | add y z _ _ hy hz =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨s, hs, hsz⟩ := hz
    refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
    rw [smul_add, mul_smul, mul_comm s t, mul_smul]
    exact S.add_mem (S.smul_mem s hty) (S.smul_mem t hsz)
  | smul a y _ hy =>
    obtain ⟨t, ht, hty⟩ := hy
    obtain ⟨⟨n, d⟩, hnd⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) a
    dsimp only at hnd
    have key : (d : O) • a = algebraMap O (FractionRing O) n := by
      rw [← hnd, Algebra.smul_def, mul_comm]
      exact IsLocalization.mk'_spec (FractionRing O) n d
    refine ⟨(d : O) * t, mul_ne_zero (nonZeroDivisors.coe_ne_zero d) ht, ?_⟩
    have e : ((d : O) * t) • (a • y) = n • (t • y) := by
      rw [mul_comm, ← smul_smul, ← smul_assoc (d : O) a y, key, algebraMap_smul, smul_comm]
    rw [e]
    exact S.smul_mem n hty

end SpanK

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {LL : Type} [Field LL] [TopologicalSpace LL] (e : FractionRing O ≃+* LL) {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Ow : Type} [CommRing Ow] [Algebra Ow LL] (eO : O ≃+* Ow)
  (heO : ∀ a : O, algebraMap Ow LL (eO a) = e (algebraMap O (FractionRing O) a))
  {Γ G : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {VT VT' : Type}
  [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
  [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
  [Module (FractionRing O) VT'] [IsScalarTower O (FractionRing O) VT']
  (Dt : LatData O Γ VT VT')

def psiR : (Γ → Dt.T') →ₛₗ[(eO : O →+* Ow)] (G → TrV e VT') where
  toFun c g := tr e ((c (ι g) : VT'))
  map_add' a b := by
    funext g
    rfl
  map_smul' a c := by
    funext g
    show tr e (a • ((c (ι g) : VT'))) = eO a • tr e ((c (ι g) : VT'))
    rw [smul_eO heO]

theorem psiR_inj (hι : Function.Bijective ι) : Function.Injective (psiR e eO heO ι Dt) := by
  intro a b h
  funext γ
  obtain ⟨g, rfl⟩ := hι.2 γ
  exact Subtype.ext (congrFun h g)

variable [Module (FractionRing O) (ReciprocityTheory.Gal.H1 Dt.ρT')] [IsScalarTower O (FractionRing O) (ReciprocityTheory.Gal.H1 Dt.ρT')]

def FsG : Submodule O (ReciprocityTheory.Gal.H1 Dt.ρTl') :=
  ((Submodule.span (FractionRing O) (finiteClassesContinuous e PD ι Dt.ρT' Dt.ρT' LinearMap.id :
    Set (ReciprocityTheory.Gal.H1 Dt.ρT'))).restrictScalars O).comap Dt.j'

theorem mem_FsG (hcob : ∀ v : VT', (fun γ => Dt.ρT' γ v - v) ∈ finZ e PD Dt.ρT' ι)
    (x : ReciprocityTheory.Gal.Z1 Dt.ρTl') :
    Submodule.mkQ _ x ∈ FsG e PD ι Dt ↔ (fun γ => ((x : Γ → Dt.T') γ : VT')) ∈ finZ e PD Dt.ρT' ι := by
  have hx' : (fun γ => ((x : Γ → Dt.T') γ : VT')) ∈ ReciprocityTheory.Gal.Z1 Dt.ρT' :=
    ⟨continuous_subtype_val.comp x.2.1, fun g h => by
      show (((x : Γ → Dt.T') (g * h) : Dt.T') : VT') = _
      rw [x.2.2 g h]
      rfl⟩
  have hj : Dt.j' (Submodule.mkQ _ x) = Submodule.mkQ _ ⟨_, hx'⟩ := rfl
  constructor
  · intro hF
    have hF' : Dt.j' (Submodule.mkQ _ x) ∈ Submodule.span (FractionRing O) (finiteClassesContinuous e PD ι Dt.ρT' Dt.ρT' LinearMap.id :
        Set (ReciprocityTheory.Gal.H1 Dt.ρT')) := hF
    obtain ⟨t, ht, hS⟩ := mem_spanK _ hF'
    rw [hj, ← map_smul] at hS
    obtain ⟨f, hf, hfe⟩ := hS
    have hfz : ((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') ∈ finZ e PD Dt.ρT' ι := hf
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hfe
    obtain ⟨v, hv⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 hfe
    have htK : algebraMap O (FractionRing O) t ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht)
    have heq : (fun γ => ((x : Γ → Dt.T') γ : VT')) =
        (algebraMap O (FractionRing O) t)⁻¹ • (((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') -
          fun γ => Dt.ρT' γ v - v) := by
      funext γ
      have e1 : ((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') γ - t • ((x : Γ → Dt.T') γ : VT') = Dt.ρT' γ v - v :=
        hv γ
      show ((x : Γ → Dt.T') γ : VT') = (algebraMap O (FractionRing O) t)⁻¹ •
        (((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') γ - (Dt.ρT' γ v - v))
      have e2 : ((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') γ - (Dt.ρT' γ v - v) =
          algebraMap O (FractionRing O) t • ((x : Γ → Dt.T') γ : VT') := by
        rw [algebraMap_smul]
        have e3 : ((f : ReciprocityTheory.Gal.Z1 Dt.ρT') : Γ → VT') γ = Dt.ρT' γ v - v + t • ((x : Γ → Dt.T') γ : VT') := by
          rw [← e1]
          abel
        rw [e3]
        abel
      rw [e2, smul_smul, inv_mul_cancel₀ htK, one_smul]
    rw [heq]
    exact (finZ e PD Dt.ρT' ι).smul_mem _ ((finZ e PD Dt.ρT' ι).sub_mem hfz (hcob v))
  · intro h
    show Dt.j' (Submodule.mkQ _ x) ∈ Submodule.span (FractionRing O) _
    rw [hj]
    exact Submodule.subset_span ⟨⟨_, hx'⟩, h, rfl⟩

variable {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [TopologicalSpace T₁] [IsTopologicalAddGroup T₁]
  [ContinuousConstSMul O T₁] [AddCommGroup T₂] [Module O T₂] [Module.Finite O T₁] [Module.Free O T₁]
  [Module.Finite O Dt.T'] [Module.Free O Dt.T']
  (ρ₁ : Representation O Γ T₁) (π : T₁ →ₗ[O] T₂) (v : T₂ ≃ₗ[O] Dt.T')
  (hc : Continuous fun t => v (π t)) (he : ∀ g t, v (π (ρ₁ g t)) = Dt.ρTl' g (v (π t)))
  (hsp : ∀ x : VT', ∃ c : O, c ≠ 0 ∧ ∃ m : Dt.T', Dt.T'.subtype m = c • x)

def imG : Submodule O (ReciprocityTheory.Gal.H1 Dt.ρTl') :=
  (finiteClassesContinuousLattice e PD ι ρ₁).map (gRow Dt ρ₁ π v hc he)

abbrev L1 : Lattice (O := Ow) (repL e (locRep ρ₁) ι) :=
  latOf e eO (mkK (O := O) (M := T₁)) ι heO (locRep ρ₁) ρ₁ mkK_inj (fun γ m => (locRep_mkK ρ₁ γ m).symm) mkK_span

abbrev L2 : Lattice (O := Ow) (repL e Dt.ρT' ι) :=
  latOf e eO Dt.T'.subtype ι heO Dt.ρT' Dt.ρTl' Subtype.val_injective (fun _ _ => rfl) hsp

abbrev f0 : MK (O := O) T₁ →ₗ[O] VT' := liftK (Dt.T'.subtype ∘ₗ v.toLinearMap ∘ₗ π)

theorem lift_map_mk (m : T₁) : f0 Dt π v (mkK m) = Dt.T'.subtype ((v.toLinearMap ∘ₗ π) m) := liftK_mkK _ m

include he in
theorem lift_map_equivariant (γ : Γ) (x : MK (O := O) T₁) : f0 Dt π v (locRep ρ₁ γ x) = Dt.ρT' γ (f0 Dt π v x) :=
  liftK_equiv Dt.ρT' ρ₁ _ (fun g m => congrArg Subtype.val (he g m)) γ x

abbrev FR : LatHom (L1 e eO heO ι ρ₁) (L2 e eO heO ι Dt hsp) :=
  latHom ι heO mkK_inj Subtype.val_injective (fun γ m => (locRep_mkK ρ₁ γ m).symm) (fun _ _ => rfl) mkK_span hsp
    (lift_map_equivariant Dt ρ₁ π v he) (fun m => lift_map_mk Dt π v m)

theorem psi_mem_Z1fT (hcob : ∀ x : VT', (fun γ => Dt.ρT' γ x - x) ∈ finZ e PD Dt.ρT' ι)
    (x : ReciprocityTheory.Gal.Z1 Dt.ρTl') (hx : Submodule.mkQ _ x ∈ FsG e PD ι Dt) :
    psiR e eO heO ι Dt (x : Γ → Dt.T') ∈ latticeFiniteCocycles PD (L2 e eO heO ι Dt hsp) := by
  have h : psiR e eO heO ι Dt (x : Γ → Dt.T') ∈ finiteCocycles PD (repL e Dt.ρT' ι) := (mem_FsG e PD ι Dt hcob x).1 hx
  exact ⟨⟨h.1, fun g _ => ⟨(x : Γ → Dt.T') (ι g), rfl⟩⟩, h⟩

theorem exists_pre (hι : Function.Bijective ι)
    (hcob : ∀ x : VT', (fun γ => Dt.ρT' γ x - x) ∈ finZ e PD Dt.ρT' ι)
    (htopV : ∀ c : Γ → VT', Continuous (fun g => tr e (c (ι g))) → Continuous c)
    (y : G → TrV e VT') (hy : y ∈ latticeFiniteCocycles PD (L2 e eO heO ι Dt hsp)) :
    ∃ x : ReciprocityTheory.Gal.Z1 Dt.ρTl', Submodule.mkQ _ x ∈ FsG e PD ι Dt ∧ psiR e eO heO ι Dt (x : Γ → Dt.T') = y := by
  let σ : Γ ≃ G := (Equiv.ofBijective ι hι).symm
  have hισ : ∀ γ, ι (σ γ) = γ := fun γ => (Equiv.ofBijective ι hι).apply_symm_apply γ
  have hσι : ∀ g, σ (ι g) = g := fun g => (Equiv.ofBijective ι hι).symm_apply_apply g
  have hσmul : ∀ γ δ, σ (γ * δ) = σ γ * σ δ := fun γ δ => hι.1 (by rw [hισ, ι.map_mul, hισ, hισ])
  have hval : ∀ g, ∃ m : Dt.T', tr e (Dt.T'.subtype m) = y g := fun g => hy.1.2 g (Set.mem_univ g)
  let x0 : Γ → Dt.T' := fun γ => Classical.choose (hval (σ γ))
  have hx0 : ∀ γ, ((x0 γ : Dt.T') : VT') = untr e (y (σ γ)) := fun γ => Classical.choose_spec (hval (σ γ))
  have hpsi : psiR e eO heO ι Dt x0 = y := by
    funext g
    show ((x0 (ι g) : Dt.T') : VT') = untr e (y g)
    rw [hx0, hσι]
  have hcv : Continuous fun γ => ((x0 γ : Dt.T') : VT') := by
    apply htopV
    have : (fun g => tr e (((x0 (ι g) : Dt.T') : VT'))) = y := hpsi
    rw [this]
    exact hy.1.1.1
  have hcont : Continuous x0 := continuous_induced_rng.2 hcv
  have hcoc : ∀ γ δ, x0 (γ * δ) = x0 γ + Dt.ρTl' γ (x0 δ) := by
    intro γ δ
    apply Subtype.ext
    show ((x0 (γ * δ) : Dt.T') : VT') = ((x0 γ : Dt.T') : VT') + Dt.ρT' γ ((x0 δ : Dt.T') : VT')
    rw [hx0, hx0, hx0, hσmul]
    have h2 := hy.1.1.2 (σ γ) (σ δ)
    show untr e (y (σ γ * σ δ)) = untr e (y (σ γ)) + Dt.ρT' γ (untr e (y (σ δ)))
    rw [h2]
    show untr e (y (σ γ)) + Dt.ρT' (ι (σ γ)) (untr e (y (σ δ))) = _
    rw [hισ]
  let x : ReciprocityTheory.Gal.Z1 Dt.ρTl' := ⟨x0, hcont, hcoc⟩
  refine ⟨x, (mem_FsG e PD ι Dt hcob x).2 ?_, hpsi⟩
  show psiR e eO heO ι Dt x0 ∈ finiteCocycles PD (repL e Dt.ρT' ι)
  rw [hpsi]
  exact hy.2

theorem im_iff (hι : Function.Bijective ι)
    (htop1 : ∀ c : Γ → T₁, Continuous (fun g => tr e (mkK (O := O) (c (ι g)))) → Continuous c)
    (x : ReciprocityTheory.Gal.Z1 Dt.ρTl') :
    Submodule.mkQ _ x ∈ imG e PD ι Dt ρ₁ π v hc he ↔
      psiR e eO heO ι Dt (x : Γ → Dt.T') ∈ (FR e eO heO ι Dt ρ₁ π v he hsp).ImF PD := by
  let σ : Γ ≃ G := (Equiv.ofBijective ι hι).symm
  have hισ : ∀ γ, ι (σ γ) = γ := fun γ => (Equiv.ofBijective ι hι).apply_symm_apply γ
  have hσι : ∀ g, σ (ι g) = g := fun g => (Equiv.ofBijective ι hι).symm_apply_apply g
  have hσmul : ∀ γ δ, σ (γ * δ) = σ γ * σ δ := fun γ δ => hι.1 (by rw [hισ, ι.map_mul, hισ, hισ])
  constructor
  · rintro ⟨z, ⟨c₁, hc₁, rfl⟩, hzx⟩
    have hfin : (fun γ => mkK (O := O) ((c₁ : Γ → T₁) γ)) ∈ finZ e PD (locRep ρ₁) ι := hc₁
    have hzx' : Submodule.mkQ _ (ReciprocityTheory.Gal.cocycles1MapOfEquivariant ρ₁ Dt.ρTl' (v.toLinearMap ∘ₗ π) hc he c₁) =
        Submodule.mkQ _ x := hzx
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hzx'
    obtain ⟨t, ht⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 hzx'
    let d₁ : G → TrV e (MK (O := O) T₁) := fun g => tr e (mkK (O := O) ((c₁ : Γ → T₁) (ι g)))
    have hd₁ : d₁ ∈ latticeFiniteCocycles PD (L1 e eO heO ι ρ₁) := ⟨⟨hfin.1, fun g _ => ⟨_, rfl⟩⟩, hfin⟩
    refine Submodule.mem_sup.2 ⟨_, ⟨d₁, hd₁, rfl⟩, _, ⟨tr e (((-t : Dt.T')) : VT'), ⟨-t, rfl⟩, rfl⟩, ?_⟩
    funext g
    have h1 : ((v (π ((c₁ : Γ → T₁) (ι g))) : Dt.T') : VT') - (((x : Γ → Dt.T') (ι g) : Dt.T') : VT') =
        Dt.ρT' (ι g) (t : VT') - (t : VT') := congrArg Subtype.val (ht (ι g))
    show f0 Dt π v (mkK ((c₁ : Γ → T₁) (ι g))) + (Dt.ρT' (ι g) (((-t : Dt.T')) : VT') - (((-t : Dt.T')) : VT')) =
      (((x : Γ → Dt.T') (ι g) : Dt.T') : VT')
    rw [lift_map_mk]
    have h2 : (((x : Γ → Dt.T') (ι g) : Dt.T') : VT') =
        ((v (π ((c₁ : Γ → T₁) (ι g))) : Dt.T') : VT') - (Dt.ρT' (ι g) (t : VT') - (t : VT')) := by
      rw [← h1]
      abel
    rw [h2]
    simp only [Submodule.coe_neg, map_neg]
    show ((v (π ((c₁ : Γ → T₁) (ι g))) : Dt.T') : VT') + (-(Dt.ρT' (ι g) (t : VT')) - -(t : VT')) = _
    abel
  · intro h
    obtain ⟨a, ⟨d₁, hd₁, rfl⟩, b, ⟨yv, ⟨t, rfl⟩, rfl⟩, hab⟩ := Submodule.mem_sup.1 h
    have hval : ∀ g, ∃ m : T₁, tr e (mkK (O := O) m) = d₁ g := fun g => hd₁.1.2 g (Set.mem_univ g)
    let c0 : Γ → T₁ := fun γ => Classical.choose (hval (σ γ))
    have hc0 : ∀ γ, mkK (O := O) (c0 γ) = untr e (d₁ (σ γ)) := fun γ => Classical.choose_spec (hval (σ γ))
    have hd : (fun g => tr e (mkK (O := O) (c0 (ι g)))) = d₁ := by
      funext g
      show mkK (O := O) (c0 (ι g)) = untr e (d₁ g)
      rw [hc0, hσι]
    have hcont : Continuous c0 := htop1 c0 (by rw [hd]; exact hd₁.1.1.1)
    have hcoc : ∀ γ δ, c0 (γ * δ) = c0 γ + ρ₁ γ (c0 δ) := by
      intro γ δ
      apply mkK_inj (O := O)
      rw [map_add (f := _), ← locRep_mkK, hc0, hc0, hc0, hσmul]
      have h2 := hd₁.1.1.2 (σ γ) (σ δ)
      show untr e (d₁ (σ γ * σ δ)) = untr e (d₁ (σ γ)) + locRep ρ₁ γ (untr e (d₁ (σ δ)))
      rw [h2]
      show untr e (d₁ (σ γ)) + locRep ρ₁ (ι (σ γ)) (untr e (d₁ (σ δ))) = _
      rw [hισ]
    let c₁ : ReciprocityTheory.Gal.Z1 ρ₁ := ⟨c0, hcont, hcoc⟩
    have hfin : (fun γ => mkK (O := O) (c0 γ)) ∈ finZ e PD (locRep ρ₁) ι := by
      show (fun g => tr e (mkK (O := O) (c0 (ι g)))) ∈ finiteCocycles PD (repL e (locRep ρ₁) ι)
      rw [hd]
      exact hd₁.2
    refine ⟨Submodule.mkQ _ c₁, ⟨c₁, hfin, rfl⟩, ?_⟩
    show Submodule.mkQ _ (ReciprocityTheory.Gal.cocycles1MapOfEquivariant ρ₁ Dt.ρTl' (v.toLinearMap ∘ₗ π) hc he c₁) = Submodule.mkQ _ x
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    refine (ReciprocityTheory.Gal.mem_coboundaries1 _ _).2 ⟨-t, fun γ => ?_⟩
    apply Subtype.ext
    have h3 := congrFun hab (σ γ)
    have h5 : f0 Dt π v (untr e (d₁ (σ γ))) + (Dt.ρT' (ι (σ γ)) (t : VT') - (t : VT')) =
        (((x : Γ → Dt.T') (ι (σ γ)) : Dt.T') : VT') := h3
    rw [← hc0, lift_map_mk, hισ] at h5
    have h4 : ((v (π (c0 γ)) : Dt.T') : VT') + (Dt.ρT' γ (t : VT') - (t : VT')) =
        (((x : Γ → Dt.T') γ : Dt.T') : VT') := h5
    show ((v (π (c0 γ)) : Dt.T') : VT') - (((x : Γ → Dt.T') γ : Dt.T') : VT') =
      Dt.ρT' γ ((-t : Dt.T') : VT') - ((-t : Dt.T') : VT')
    rw [← h4]
    simp only [Submodule.coe_neg, map_neg]
    abel

theorem len_eq_col (hι : Function.Bijective ι)
    (hcob : ∀ x : VT', (fun γ => Dt.ρT' γ x - x) ∈ finZ e PD Dt.ρT' ι)
    (htopV : ∀ c : Γ → VT', Continuous (fun g => tr e (c (ι g))) → Continuous c)
    (htop1 : ∀ c : Γ → T₁, Continuous (fun g => tr e (mkK (O := O) (c (ι g)))) → Continuous c) :
    Module.length O (↥(FsG e PD ι Dt) ⧸ (imG e PD ι Dt ρ₁ π v hc he).comap (FsG e PD ι Dt).subtype) =
      (FR e eO heO ι Dt ρ₁ π v he hsp).col PD := by
  haveI h1 := RingHomInvPair.of_ringEquiv eO
  haveI h2 := RingHomInvPair.symm (eO : O →+* Ow) (eO.symm : Ow →+* O)
  rw [← len_comap_surj (Submodule.mkQ _) (Submodule.mkQ_surjective _)]
  unfold LatHom.col
  refine len_semi eO ((psiR e eO heO ι Dt).comp (ReciprocityTheory.Gal.Z1 Dt.ρTl').subtype)
    ((psiR_inj e eO heO ι Dt hι).comp Subtype.val_injective) _ _ _ _ ?_ ?_
  · intro y
    constructor
    · intro hy
      obtain ⟨x, hx, hxy⟩ := exists_pre e eO heO PD ι Dt hsp hι hcob htopV y hy
      exact ⟨x, hx, hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact psi_mem_Z1fT e eO heO PD ι Dt hsp hcob x hx
  · intro x _
    exact im_iff e eO heO PD ι Dt ρ₁ π v hc he hsp hι htop1 x

end Gen

end Formalism.MainNotions.N.KRow

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KRowA

open Formalism.MainNotions.N.KHf Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Gen

theorem sub_of_fam {LL : Type} [Field LL] {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module LL V]
    [FiniteDimensional LL V] {ρ : Representation LL G V} {ιx : Type} {k : ℕ}
    {Ms : ιx → G → Matrix (Fin k) (Fin k) LL} {I : Type} (xx : I → ιx)
    (Ψ : I → V →ₗ[LL] (Fin k → LL)) (hinj : ∀ v, (∀ a, Ψ a v = 0) → v = 0)
    (heq : ∀ a g v, Ψ a (ρ g v) = (Ms (xx a) g).mulVec (Ψ a v)) : IsSubOfSums ρ Ms := by
  obtain ⟨m, xs, hxs⟩ := KLift.fin_sel Ψ hinj
  refine ⟨m, xx ∘ xs, LinearMap.pi fun a => Ψ (xs a), fun v w hvw => ?_, fun g v => funext fun a => heq _ g v⟩
  rw [← sub_eq_zero]
  refine hxs _ fun a => ?_
  rw [map_sub, sub_eq_zero]
  exact congrFun hvw a

theorem orb_of_sub {LL : Type} [Field LL] [TopologicalSpace LL] [IsTopologicalRing LL] {G : Type} [Group G]
    [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module LL V] [TopologicalSpace V] [IsModuleTopology LL V]
    [ContinuousAdd V] [ContinuousSMul LL V]
    {ρ : Representation LL G V} {ιx : Type} {k : ℕ} {Ms : ιx → G → Matrix (Fin k) (Fin k) LL}
    (h : IsSubOfSums ρ Ms) (hMs : ∀ x, Continuous (Ms x)) (v : V) : Continuous fun g => ρ g v := by
  obtain ⟨m, xs, φ, hφ, heq⟩ := h
  exact KLift.cont_of_inj xs φ hφ heq hMs v

end Gen

section Fin

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}

end Fin

section Rec

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

def kap1 : FirstSummandSubmodule (D.nd.O i) Dd.e₁ →ₗ[D.nd.O i]
    (Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) where
  toFun p := (((p : Dd.R')) : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem lattice_inclusion_injective : Function.Injective (kap1 i Dd) := by
  intro a b h
  exact Subtype.ext (Subtype.ext h)

theorem idempotent_part_representation_at
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    (g : GE D.nd) (p : FirstSummandSubmodule (D.nd.O i) Dd.e₁) (x' : Dd.X') :
    kap1 i Dd (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i) g p) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          ((chiU D.nd i 1 g : D.nd.O i) * ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i)) •
        (kap1 i Dd p x' * (rO D.nd i r (Dd.p x') g⁻¹).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) := by
  show (((((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) • (((Dd.χ g : (Dd.T')ˣ) : Dd.T') •
    ((p : Dd.R') * Dd.r g⁻¹)) : Dd.R')) : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' = _
  rw [Subalgebra.coe_smul, Pi.smul_apply, hsm, hχ, Subalgebra.coe_mul, Pi.mul_apply, hr', map_mul, mul_smul,
    ← algebraMap_smul (FractionRing (D.nd.O i)) ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i), smul_comm]
  rfl

theorem locC_apply {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i _ hn) (a b : Fin k) :
    TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) M g a b = eK (D.nbr i _ hn) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
      (M ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) a b)) := by
  rw [← KLift.heO_br i dc hn]
  rfl

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem rowSub_at
    (hr' : ∀ g x', ((Dd.r g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' =
      (rO D.nd i r (Dd.p x') g).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))))
    (hsm : ∀ (f : Dd.T') (a : Dd.R') x', ((f • a : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV)
      (FractionRing (D.nd.O i))) x' = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) ((f : Dd.X' → D.nd.O i) x') •
        (a : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x')
    (hχ : ∀ g x', (((Dd.χ g : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' = (chiU D.nd i 1 g : D.nd.O i))
    [Module.Finite (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)] [Module.Free (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)]
    {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    IsSubOfSums (repL (eK (D.nbr i _ hn))
        (locRep (resRep (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i)) (Γn i dc n))) (Br.iota D.nbr i _ hn))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r x))) := by
  set ρP := resRep (firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i)) (Γn i dc n) with hρP
  set e := eK (D.nbr i _ hn)
  let Λ := liftK (V := Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) (kap1 i Dd)
  have hΛs : ∀ m (s : nonZeroDivisors (D.nd.O i)), (s : D.nd.O i) • Λ (LocalizedModule.mk m s) = kap1 i Dd m := by
    intro m s
    rw [← map_smul, KLift.smul_mk, liftK_mkK]
  have hΛi : ∀ v, Λ v = 0 → v = 0 := by
    intro v hv
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h1 := hΛs m s
      rw [hv, smul_zero] at h1
      rw [lattice_inclusion_injective i Dd (h1.symm.trans (map_zero (kap1 i Dd)).symm), LocalizedModule.zero_mk]
  have hΛe : ∀ (γ : ↥(Γn i dc n)) v x', Λ (locRep ρP γ v) x' =
      algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          ((chiU D.nd i 1 (γ : GE D.nd) : D.nd.O i) * ((epsU D.nd i (γ : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i)) •
        (Λ v x' * (rO D.nd i r (Dd.p x') (γ : GE D.nd)⁻¹).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) := by
    intro γ v x'
    induction v using LocalizedModule.induction_on with
    | h m s =>
      have h0 : locRep ρP γ (LocalizedModule.mk m s) = LocalizedModule.mk (ρP γ m) s := LocalizedModule.map_mk _ _ _ _
      rw [h0]
      apply KLift.smul_cancel s
      have h1 := congrFun (hΛs (ρP γ m) s) x'
      have h2 := congrFun (hΛs m s) x'
      rw [Pi.smul_apply] at h1 h2
      rw [h1, smul_comm, ← Matrix.smul_mul, h2]
      exact idempotent_part_representation_at i r Dd hr' hsm hχ (γ : GE D.nd) m x'
  let Ψ : Dd.X' × Fin D.R.nV → TrV e (MK (O := D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁)) →ₗ[Br.LLw (D.nbr i _ hn)]
      (Fin D.R.nV → Br.LLw (D.nbr i _ hn)) := fun q =>
    { toFun := fun v j => e ((Λ (KLift.untr e v)) q.1 q.2 j)
      map_add' := fun v w => funext fun j => by
        show e ((Λ (KLift.untr e v + KLift.untr e w)) q.1 q.2 j) = _
        rw [map_add (f := _)]
        simp [map_add (f := _)]
      map_smul' := fun c v => funext fun j => by
        show e ((Λ (e.symm c • KLift.untr e v)) q.1 q.2 j) = c * e ((Λ (KLift.untr e v)) q.1 q.2 j)
        rw [smulK]
        simp [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul, map_mul] }
  haveI : FiniteDimensional (Br.LLw (D.nbr i _ hn)) (TrV e (MK (O := D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁))) :=
    KLift.finDim_of_lat (Ow := Br.Ow (D.nbr i _ hn)) (Qp := ℚ_[D.nd.l i])
      (KLift.latOf e (D.nbr i _ hn).eO mkK (Br.iota D.nbr i _ hn) (KLift.heO_br i dc hn) (locRep ρP) ρP KLift.mkK_inj
        (fun γ m => (locRep_mkK _ γ m).symm) KLift.mkK_span)
  refine sub_of_fam (fun q => Dd.p q.1) Ψ (fun v hv => ?_) (fun q g v => ?_)
  · have h0 : Λ (KLift.untr e v) = 0 := by
      funext x'
      ext a b
      have := congrFun (hv (x', a)) b
      simpa [Ψ] using this
    exact hΛi _ h0
  · funext j
    have key : ∀ γ : ↥(Γn i dc n), (γ : GE D.nd) = ((Br.iota D.nbr i _ hn g : Gw D.nd (K.plOf i dc n)) : GE D.nd) →
        e ((Λ (locRep ρP γ (KLift.untr e v))) q.1 q.2 j) =
          (TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) (rDuO D.nd i r (Dd.p q.1)) g).mulVec (Ψ q v) j := by
      intro γ hγ
      rw [hΛe, hγ]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Matrix.mulVec, dotProduct, locC_apply i dc hn, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul,
        Finset.mul_sum, map_sum, map_mul, Matrix.map_apply, rDuO, twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk,
        Matrix.transpose_apply, Ψ, LinearMap.coe_mk, AddHom.coe_mk]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp only [MonoidHom.mul_apply, Units.val_mul, map_mul]
      rw [show eK (D.nbr i _ hn) = e from rfl]
      have hc : ∀ x y z w : Br.LLw (D.nbr i _ hn), x * y * (z * w) = x * y * w * z := fun x y z w => by ring
      exact hc _ _ _ _
    exact key (Br.iota D.nbr i _ hn g) rfl

end Rec

end Formalism.MainNotions.N.KRowA

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN Formalism.NG

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT' w)] [∀ w, TopologicalSpace (VT' w)] [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)]
  {T₁ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁]

def RowTop1 : Prop :=
  ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
    ∀ c : ↥(Γn i dc n) → T₁,
      Continuous (fun g => tr (eK (D.nbr i _ hn)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hn g)))) →
        Continuous c

theorem rowTop_of
    (hT : ∀ n ∈ K.rowsN i dc, ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i),
      KBKa.TopMatch (eK (D.nbr i _ hn)) (VT' n))
    (h1 : RowTop1 i dc (T₁ := T₁)) : RowTop i dc VT' (T₁ := T₁) := by
  intro n hn hpl
  refine ⟨fun c hc => ?_, h1 n hn hpl⟩
  have h := hT n hn hpl
  have h2 := (KBKa.cont_iff _ h _).1 hc
  have h3 : Continuous fun g => c (Br.iota D.nbr i _ hpl g) := h2
  obtain ⟨hm, hhm⟩ := KBKa.iotaHomeo_rec (i := i) (dc := dc) hpl
  have hc' : c = (fun g => c (Br.iota D.nbr i _ hpl g)) ∘ hm.symm := by
    funext x
    simp only [Function.comp, ← hhm]
    exact congrArg c (hm.apply_symm_apply x).symm
  rw [hc']
  exact h3.comp hm.symm.continuous

end Rec

end Formalism.MainNotions.N.KRow

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))

theorem msContW (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) : K.TBa.MsContW (i := i) (r := r) hw :=
  fun x => locC_cont i r hc hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) x

end Formalism.MainNotions.N.KOrb

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Font

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct Formalism.MainNotions.N.K.TBa

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem multV_zero_of_subsingleton {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V]
    [IsScalarTower Qp LL V] [Subsingleton V] (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    multV PD ρ τ a = 0 := by
  have hs : ∀ b, Subsingleton ↥(FildR PD ρ τ b) := fun b =>
    ⟨fun x y => Subtype.ext ((tens_subsingleton (x : V ⊗[Qp] BdR)).trans (tens_subsingleton (y : V ⊗[Qp] BdR)).symm)⟩
  unfold multV
  haveI := hs a
  haveI := hs (a + 1)
  rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
  rfl

variable {ι : Type} {k : ℕ} (Ms : ι → G →* Matrix (Fin k) (Fin k) LL)
  (hF : TruncatedSeriesCountingIdentities.FontaineAt PD LL O) (hMc : ∀ x, Continuous (Ms x))
include hF hMc

theorem mult_sum_neg : ∀ (m : ℕ) (xs : Fin m → ι), IsCrys PD (sumRep Ms xs) →
    (∀ (j : Fin m) (τ : K →ₐ[Qp] LL) (b : ℤ), IsJumpV PD (matRep (Ms (xs j))) τ b → 0 ≤ b) →
    ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), a < 0 → multV PD (sumRep Ms xs) τ a = 0 := by
  intro m
  induction m with
  | zero =>
    intro xs _ _ τ a _
    haveI : Subsingleton (Fin 0 → Fin k → LL) := inferInstance
    exact multV_zero_of_subsingleton PD _ τ a
  | succ m ih =>
    intro xs hc hJ τ a ha
    let A₀ : GRep G Qp LL O := sumG Ms hMc (fun a => xs a.succ)
    let A₁ : GRep G Qp LL O := sumG Ms hMc xs
    let A₂ : GRep G Qp LL O := matG Ms hMc (xs 0)
    let ι₀ : A₀.V →ₗ[LL] A₁.V := consZ (W := Fin k → LL) m
    let π₀ : A₁.V →ₗ[LL] A₂.V := LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0
    let σ₀ : A₂.V →ₗ[LL] A₁.V := consV (W := Fin k → LL) m
    have e1 : ∀ g x, ι₀ (A₀.ρ g x) = A₁.ρ g (ι₀ x) := fun g x => funext fun a => by
      cases a using Fin.cases
      · show (0 : Fin k → LL) = (Ms (xs 0) g).mulVec 0
        rw [Matrix.mulVec_zero]
      · rfl
    have e2 : ∀ g x, π₀ (A₁.ρ g x) = A₂.ρ g (π₀ x) := fun g x => rfl
    have hinj : Function.Injective ι₀ := consZ_inj (W := Fin k → LL) m
    have hsurj : Function.Surjective π₀ := fun v => ⟨σ₀ v, proj_consV (W := Fin k → LL) m v⟩
    have hex : LinearMap.range ι₀ = LinearMap.ker π₀ := range_consZ (W := Fin k → LL) m
    have hF1 := hF.1 A₀ A₁ A₂ ι₀ π₀ e1 e2 hinj hsurj hex
    obtain ⟨hc0, hc2, hadd⟩ := hF1.1 hc
    have h0 : multV PD A₀.ρ τ a = 0 :=
      ih (fun a => xs a.succ) hc0 (fun j => hJ j.succ) τ a ha
    have h2 : multV PD A₂.ρ τ a = 0 := by
      by_contra hne
      have := hJ 0 τ a (jump_of_mult PD _ τ a hne)
      omega
    show multV PD A₁.ρ τ a = 0
    rw [hadd τ a, h0, h2, add_zero]

theorem decomp_neg (A₁ A₀ : GRep G Qp LL O) {m : ℕ} (xs : Fin m → ι)
    (e : A₁.V ≃ₗ[LL] A₀.V × (Fin m → Fin k → LL))
    (he : ∀ g v, e (A₁.ρ g v) = (A₀.ρ g (e v).1, sumRep Ms xs g (e v).2))
    (hc : IsCrys PD A₁.ρ)
    (hJ : ∀ (j : Fin m) (τ : K →ₐ[Qp] LL) (b : ℤ), IsJumpV PD (matRep (Ms (xs j))) τ b → 0 ≤ b) :
    IsCrys PD A₀.ρ ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), a < 0 → multV PD A₁.ρ τ a = multV PD A₀.ρ τ a := by
  let A₂ : GRep G Qp LL O := sumG Ms hMc xs
  let ι₀ : A₀.V →ₗ[LL] A₁.V := e.symm.toLinearMap ∘ₗ LinearMap.inl LL A₀.V (Fin m → Fin k → LL)
  let π₀ : A₁.V →ₗ[LL] A₂.V := LinearMap.snd LL A₀.V (Fin m → Fin k → LL) ∘ₗ e.toLinearMap
  have e1 : ∀ g x, ι₀ (A₀.ρ g x) = A₁.ρ g (ι₀ x) := by
    intro g x
    apply e.injective
    show e (e.symm (A₀.ρ g x, 0)) = e (A₁.ρ g (e.symm (x, 0)))
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, map_zero]
  have e2 : ∀ g x, π₀ (A₁.ρ g x) = A₂.ρ g (π₀ x) := by
    intro g x
    show (e (A₁.ρ g x)).2 = sumRep Ms xs g (e x).2
    rw [he]
  have hinj : Function.Injective ι₀ := by
    intro x y h
    have h' : e.symm (x, 0) = e.symm (y, 0) := h
    have := congrArg Prod.fst (e.symm.injective h')
    exact this
  have hsurj : Function.Surjective π₀ := by
    intro y
    refine ⟨e.symm (0, y), ?_⟩
    show (e (e.symm (0, y))).2 = y
    rw [LinearEquiv.apply_symm_apply]
  have hex : LinearMap.range ι₀ = LinearMap.ker π₀ := by
    ext v
    constructor
    · rintro ⟨x, rfl⟩
      show (e (e.symm (x, 0))).2 = 0
      rw [LinearEquiv.apply_symm_apply]
    · intro hv
      have hv' : (e v).2 = 0 := hv
      refine ⟨(e v).1, ?_⟩
      show e.symm ((e v).1, 0) = v
      rw [← hv']
      exact e.symm_apply_apply v
  have hF1 := hF.1 A₀ A₁ A₂ ι₀ π₀ e1 e2 hinj hsurj hex
  obtain ⟨hc0, hc2, hadd⟩ := hF1.1 hc
  refine ⟨hc0, fun τ a ha => ?_⟩
  have h2 : multV PD A₂.ρ τ a = 0 := mult_sum_neg PD Ms hF hMc m xs hc2 hJ τ a ha
  rw [hadd τ a, h2, add_zero]

end Gen

section GenNT

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

section DR

variable {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {ρ : Representation LL G V} {ρ' : Representation LL G V'} (e : V ≃ₗ[LL] V')
    (he : ∀ g x, e (ρ g x) = ρ' g (e x))
include he

theorem isDR_congr (h : IsDR PD ρ) : IsDR PD ρ' := by
  let E : V ⊗[Qp] BdR ≃ₗ[LL] V' ⊗[Qp] BdR := AlgebraTensorModule.congr e (LinearEquiv.refl Qp BdR)
  have hE : ∀ g x, E (actVdR PD ρ g x) = actVdR PD ρ' g (E x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [E, actVdR, he]
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb, map_add (f := _), map_add (f := _)]
  have hD : DdR PD ρ = (DdR PD ρ').comap (E : V ⊗[Qp] BdR →ₗ[LL] V' ⊗[Qp] BdR) := by
    ext x
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, Submodule.mem_comap, sub_eq_zero]
    constructor
    · intro hx g
      rw [LinearEquiv.coe_coe, ← hE, hx g]
    · intro hx g
      apply E.injective
      rw [hE]
      exact hx g
  unfold IsDR at h ⊢
  rw [← e.finrank_eq, ← h, hD]
  exact (E.ofSubmodule' (DdR PD ρ')).finrank_eq.symm

end DR

section MatT

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V] {k : ℕ}
  (M : G →* Matrix (Fin k) (Fin k) LL) (ρ' : Representation LL G V) (e : V ≃ₗ[LL] (Fin k → LL))
  (he : ∀ g x, e (ρ' g x) = matRep M g (e x))
include he

theorem crys_of_mat (h : IsCrys PD (matRep M)) : IsCrys PD ρ' := by
  refine Norm.isCrys_congr PD e.symm (fun g y => ?_) h
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

theorem multV_mat (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD ρ' τ a = multV PD (matRep M) τ a :=
  Norm.multV_congr PD e he τ a

theorem dR_of_mat (h : IsDR PD (matRep M)) : IsDR PD ρ' := by
  refine isDR_congr PD e.symm (fun g y => ?_) h
  apply e.injective
  rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply]

end MatT

end GenNT

end Formalism.MainNotions.N.K.Font

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Font

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KHf Formalism.MainNotions.N.KDim NumberField IsDedekindDomain Formalism.NG Formalism.BasicNotions

section Loc

variable {D : D7} (i : D.nd.Loc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem loc_apply {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) (a b : Fin k) :
    Br.loc D.nbr i w hw M g a b =
      eK (D.nbr i w hw) (toK D.nd i (M ((Br.iota D.nbr i w hw g : _) : GE D.nd) a b)) := by
  exact (Br.toLLK_alg (Bw := D.nbr i w hw) (c := M ((Br.iota D.nbr i w hw g : _) : GE D.nd) a b)).symm

theorem locChi_apply (χ : GE D.nd →* (D.nd.O i)ˣ) (g : Br.G D.nbr i w hw) :
    ((Br.locChi D.nbr i w hw χ g : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) =
      eK (D.nbr i w hw) (toK D.nd i ((χ ((Br.iota D.nbr i w hw g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i)) := by
  exact (IsFractionRing.lift_algebraMap (Br.toLL_inj (D.nbr i w hw))
    ((χ ((Br.iota D.nbr i w hw g : _) : GE D.nd) : (D.nd.O i)ˣ) : D.nd.O i)).symm

end Loc

section Ident

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

abbrev MrTw {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    Br.G D.nbr i w hw →* Matrix (Fin D.R.nV) (Fin D.R.nV) (Br.LL D.nbr i w hw) :=
  twistM (TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C (TruncatedSeriesCountingIdentities.CoefExt.self i w hw))⁻¹

theorem repX_mulVec (x' : Dd.X') (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    (g : Br.G D.nbr i _ hn) (v : TrV (eK (D.nbr i _ hn)) (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')) :
    ((KDim.repX i dc Dd.r Dd.χ x' n hn g v : EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') : Fin D.R.nV → FractionRing (D.nd.O i)) =
      (((Formalism.NG.uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd) : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x').mulVec
        (v : Fin D.R.nV → FractionRing (D.nd.O i)) := by
  rfl

abbrev phiL (x' : Dd.X') {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    TrV (eK (D.nbr i w hw)) (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') ≃ₗ[Br.LL D.nbr i w hw] (Fin D.R.nV → Br.LL D.nbr i w hw) :=
  phiX i Dd x' (eK (D.nbr i w hw))

theorem phiX_equiv (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd)
    (x' : Dd.X') (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    (g : Br.G D.nbr i _ hn) (v : TrV (eK (D.nbr i _ hn)) (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')) :
    phiL i Dd x' hn (KDim.repX i dc Dd.r Dd.χ x' n hn g v) =
      matRep (MrTw i r hn (Dd.p x')) g (phiL i Dd x' hn v) := by
  obtain ⟨-, -, -, -, -, -, hr, -, hsm, -, -, hχ, -⟩ := hD
  funext j
  have hv := congrArg (eK (D.nbr i _ hn)) (congrFun (repX_mulVec i dc Dd x' n hn g v) j)
  refine hv.trans ?_
  change _ = ((MrTw i r hn (Dd.p x')) g).mulVec
    (fun k => eK (D.nbr i _ hn) ((v : Fin D.R.nV → FractionRing (D.nd.O i)) k)) j
  have hu : ∀ h : GE D.nd, ((((Dd.χ h)⁻¹ : (Dd.T')ˣ) : Dd.T') : Dd.X' → D.nd.O i) x' =
      (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
    intro h
    rw [← map_inv, hχ, map_inv]
  have hrep : ∀ (h : GE D.nd) (y : D.nd.X i), RepresentationBoundsCohomology.repX D.nd r h y = rO D.nd i r y h := fun _ _ => rfl

  simp [Formalism.NG.uElt, hsm, hr, hu, hrep, MrTw, twistM, TruncatedSeriesCountingIdentities.locC, TruncatedSeriesCountingIdentities.chi1C, mapM, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.map_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine congrArg₂ (· * ·) (congrArg₂ (· * ·) ?_ ?_) ?_
  · exact ((Units.val_inv_eq_inv_val
      (TruncatedSeriesCountingIdentities.chi1C (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn) g : (Br.LL D.nbr i _ hn)ˣ)).trans
      (congrArg Inv.inv (locChi_apply i hn (chiU D.nd i 1) g))).symm
  · exact (loc_apply i hn (rO D.nd i r (Dd.p x')) g j k).symm
  · rfl

theorem crysX_of (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (x' : Dd.X') (l : K.Col i dc) :
    KDim.CrysX i dc Dd.r Dd.χ x' l := by
  have hn := col_over i dc l
  have hc := (hG2 _ hn (TruncatedSeriesCountingIdentities.CoefExt.self i _ hn)).2 (Dd.p x')
  unfold KDim.CrysX
  exact crys_of_mat _ _ _ (phiL i Dd x' hn) (phiX_equiv i dc r π g0 eB e₁ s Dd hD x' _ hn) hc

end Ident

section BC

theorem smulMV {Kf : Type} [CommRing Kf] {n m : ℕ} (c : Kf) (M : Matrix (Fin n) (Fin m) Kf) (u : Fin m → Kf) :
    (c • M).mulVec u = c • M.mulVec u := by
  ext a
  simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum, mul_assoc]

variable {Kf LL : Type} [Field Kf] [Field LL] (f : Kf ≃+* LL) {n r t : ℕ}
  (e : (Fin n → Kf) ≃ₗ[Kf] (Fin r → Kf) × (Fin t → Kf))

def eL : (Fin n → LL) ≃ₗ[LL] (Fin r → LL) × (Fin t → Fin 1 → LL) where
  toFun v := (fun a => f ((e (fun b => f.symm (v b))).1 a), fun j _ => f ((e (fun b => f.symm (v b))).2 j))
  invFun z := fun b => f (e.symm (fun a => f.symm (z.1 a), fun j => f.symm (z.2 j 0)) b)
  map_add' u v := by
    have h : (fun b => f.symm ((u + v) b)) = (fun b => f.symm (u b)) + (fun b => f.symm (v b)) :=
      funext fun b => by simp
    refine Prod.ext (funext fun a => ?_) (funext fun j => funext fun x => ?_)
    · show f ((e (fun b => f.symm ((u + v) b))).1 a) =
        f ((e (fun b => f.symm (u b))).1 a) + f ((e (fun b => f.symm (v b))).1 a)
      rw [h, map_add (f := _), Prod.fst_add, Pi.add_apply, map_add (f := _)]
    · show f ((e (fun b => f.symm ((u + v) b))).2 j) =
        f ((e (fun b => f.symm (u b))).2 j) + f ((e (fun b => f.symm (v b))).2 j)
      rw [h, map_add (f := _), Prod.snd_add, Pi.add_apply, map_add (f := _)]
  map_smul' c v := by
    have h : (fun b => f.symm ((c • v) b)) = f.symm c • (fun b => f.symm (v b)) :=
      funext fun b => by simp
    refine Prod.ext (funext fun a => ?_) (funext fun j => funext fun x => ?_)
    · show f ((e (fun b => f.symm ((c • v) b))).1 a) = c * f ((e (fun b => f.symm (v b))).1 a)
      rw [h, map_smul, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply]
    · show f ((e (fun b => f.symm ((c • v) b))).2 j) = c * f ((e (fun b => f.symm (v b))).2 j)
      rw [h, map_smul, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul, RingEquiv.apply_symm_apply]
  left_inv v := by
    funext b
    simp
  right_inv z := by
    refine Prod.ext (funext fun a => ?_) (funext fun j => funext fun x => ?_)
    · simp
    · rw [Fin.fin_one_eq_zero x]
      simp

theorem eL_apply (v : Fin n → LL) :
    eL f e v = (fun a => f ((e (fun b => f.symm (v b))).1 a), fun j _ => f ((e (fun b => f.symm (v b))).2 j)) := rfl

theorem eL_mul (R : Matrix (Fin n) (Fin n) Kf) (P : Matrix (Fin r) (Fin r) Kf) (c : Fin t → Kf)
    (he : ∀ u, e (R.mulVec u) = (P.mulVec (e u).1, fun j => c j * (e u).2 j))
    (R' : Matrix (Fin n) (Fin n) LL) (P' : Matrix (Fin r) (Fin r) LL) (c' : Fin t → LL)
    (hR : ∀ a b, R' a b = f (R a b)) (hP : ∀ a b, P' a b = f (P a b)) (hc : ∀ j, c' j = f (c j))
    (v : Fin n → LL) :
    eL f e (R'.mulVec v) = (P'.mulVec (eL f e v).1, fun j _ => c' j * (eL f e v).2 j 0) := by

  have key : (fun b => f.symm ((R'.mulVec v) b)) = R.mulVec (fun b => f.symm (v b)) := by
    funext b

    simp only [Matrix.mulVec, dotProduct, hR, map_sum, map_mul, RingEquiv.symm_apply_apply]
  have h2 : e (fun b => f.symm ((R'.mulVec v) b)) =
      (P.mulVec (e (fun b => f.symm (v b))).1, fun j => c j * (e (fun b => f.symm (v b))).2 j) :=
    (congrArg e key).trans (he _)
  rw [eL_apply, eL_apply, h2]
  refine Prod.ext (funext fun a => ?_) (funext fun j => funext fun x => ?_)

  · simp only [Matrix.mulVec, dotProduct, hP, map_sum, map_mul]
  · simp only [hc, map_mul]

end BC

section Dec

variable {D : D7} (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem chiRat_cont (c : ℕ) : Continuous (chiRatO D.nd i c) := by
  have e : (fun g : GE D.nd => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (D.nd.O i)ˣ) : D.nd.O i)) =
      fun g => ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i) * ((chiU D.nd i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
    funext g
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, map_inv, Units.val_mul]
  have hχ : Continuous fun g : GE D.nd => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (D.nd.O i)ˣ) : D.nd.O i) := by
    rw [e]
    exact (D.nd.chi_cont i c).mul ((D.nd.chi_cont i 1).comp continuous_inv)
  show Continuous fun g => (((chiU D.nd i c * (chiU D.nd i 1)⁻¹) g : (D.nd.O i)ˣ) : D.nd.O i) •
    ((1 : GE D.nd →* Matrix (Fin 1) (Fin 1) (D.nd.O i)) g)
  exact hχ.smul (continuous_const : Continuous fun _ : GE D.nd => (1 : Matrix (Fin 1) (Fin 1) (D.nd.O i)))

theorem locC_cont' {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (hM : Continuous M)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    Continuous ⇑(TruncatedSeriesCountingIdentities.locC C M) := by
  have hinc : Continuous (TruncatedSeriesCountingIdentities.CoefExt.inc C) :=
    continuous_induced_rng.2 (by exact continuous_subtype_val)
  exact (KOrb.loc_cont i hw M hM).matrix_map hinc

abbrev MsC {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (j : Fin D.R.t) :
    Br.G D.nbr i w hw →* Matrix (Fin 1) (Fin 1) (Br.LL D.nbr i w hw) :=
  TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (chiRatO D.nd i ((j : ℕ) + 1))

theorem mrTw_eq {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (x : D.nd.X i) :
    twistM (TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i w hw) (rO D.nd i r x)) (TruncatedSeriesCountingIdentities.chi1C (TruncatedSeriesCountingIdentities.CoefExt.self i w hw))⁻¹ =
      TBa.MsW i r hw x := by
  ext g a b
  simp [TBa.MsW, TruncatedSeriesCountingIdentities.locC, TruncatedSeriesCountingIdentities.chi1C, rTwO, mapM, twistM, loc_apply, locChi_apply]

end Dec

section DecRec

variable {D : D7} (i : D.nd.Loc)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem decomp_at (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    ∃ e' : (Fin D.R.nV → Br.LL D.nbr i w hw) ≃ₗ[Br.LL D.nbr i w hw]
        (Fin D.R.r → Br.LL D.nbr i w hw) × (Fin D.R.t → Fin 1 → Br.LL D.nbr i w hw),
      ∀ g v, e' (matRep (Kf := Br.LL D.nbr i w hw) (TBa.MsW i r hw π) g v) =
        (matRep (Br.loc D.nbr i w hw (WpO D.nd i ρ π)) g (e' v).1, TBa.sumRep (MsC i hw) id g (e' v).2) := by
  obtain ⟨e, he⟩ := hDec
  refine ⟨eL (eK (D.nbr i w hw)) e, fun g v => ?_⟩
  obtain ⟨h, hh⟩ : ∃ h : GE D.nd, h = ((Br.iota D.nbr i w hw g : _) : GE D.nd) := ⟨_, rfl⟩

  have hE : ∀ u, e ((toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) (rO D.nd i r π) h).mulVec u) =
      ((toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) (rhoO D.nd i ρ π) h).mulVec (e u).1,
        fun j : Fin D.R.t => toK D.nd i ((chiU D.nd i ((j : ℕ) + 1) h : (D.nd.O i)ˣ) : D.nd.O i) * toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * (e u).2 j) := by
    intro u
    rw [smulMV, smulMV, map_smul, he h u]
    refine Prod.ext rfl (funext fun j => ?_)
    simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
    ring
  have hR : ∀ a b, TBa.MsW i r hw π g a b =
      eK (D.nbr i w hw) ((toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) (rO D.nd i r π) h) a b) := by
    intro a b
    subst hh
    simp [TBa.MsW, TruncatedSeriesCountingIdentities.locC, rTwO, twistM, mapM, loc_apply] <;> rfl
  have hP : ∀ a b, Br.loc D.nbr i w hw (WpO D.nd i ρ π) g a b =
      eK (D.nbr i w hw) ((toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) (rhoO D.nd i ρ π) h) a b) := by
    intro a b
    subst hh
    simp [WpO, twistM, mapM, loc_apply]
  have hc : ∀ j : Fin D.R.t, MsC i hw j g 0 0 = eK (D.nbr i w hw) (toK D.nd i ((chiU D.nd i ((j : ℕ) + 1) h : (D.nd.O i)ˣ) : D.nd.O i) * toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) := by
    intro j
    subst hh
    refine (loc_apply i hw (chiRatO D.nd i ((j : ℕ) + 1)) g 0 0).trans ?_
    congr 1
    simp [chiRatO, twistM]
  have key := eL_mul (eK (D.nbr i w hw)) e
    (toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) (rO D.nd i r π) h)
    (toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) • mapM (toK D.nd i) (rhoO D.nd i ρ π) h)
    (fun j : Fin D.R.t => toK D.nd i ((chiU D.nd i ((j : ℕ) + 1) h : (D.nd.O i)ˣ) : D.nd.O i) * toK D.nd i (((chiU D.nd i 1 h)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i))
    hE (TBa.MsW i r hw π g) (Br.loc D.nbr i w hw (WpO D.nd i ρ π) g) (fun j => MsC i hw j g 0 0)
    hR hP hc v
  refine key.trans ?_
  refine Prod.ext rfl (funext fun j => funext fun x => ?_)
  rw [Fin.fin_one_eq_zero x]
  simp [TBa.sumRep, Matrix.mulVec, dotProduct]

theorem wp_font (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hρ : Continuous fun g => rhoO D.nd i ρ π g)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (WpO D.nd i ρ π))) ∧
      ∀ (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (a : ℤ), a < 0 →
        multV (Br.PD D.loc D.nbr i w hw) (matRep (Kf := Br.LL D.nbr i w hw) (TBa.MsW i r hw π)) τ a =
          multV (Br.PD D.loc D.nbr i w hw) (matRep (Br.loc D.nbr i w hw (WpO D.nd i ρ π))) τ a := by
  obtain ⟨e', he'⟩ := decomp_at i r ρ π hDec hw
  have hMsc : ∀ j, Continuous (MsC i hw j) := fun j => locC_cont' i _ (chiRat_cont i _) hw _
  have hWc : Continuous ⇑(Br.loc D.nbr i w hw (WpO D.nd i ρ π)) :=
    KOrb.loc_cont i hw _ (KOrb.wpO_cont i ρ π hρ)
  have hc0 := (hG2 _ hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).2 π
  rw [mrTw_eq] at hc0
  have hc : IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (Kf := Br.LL D.nbr i w hw) (TBa.MsW i r hw π)) := hc0
  have hJ : ∀ (j : Fin D.R.t) (τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] Br.LL D.nbr i w hw) (b : ℤ),
      IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (MsC i hw (id j))) τ b → 0 ≤ b := by
    intro j τ b hb
    have hj := j.2
    have h := ((hG2 _ hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).1.2.2.2.1 ((j : ℕ) + 1) (by omega) (by omega) τ b).1 hb
    rw [h]
    push_cast
    omega
  exact decomp_neg (O := Br.OLL D.nbr i w hw) (Br.PD D.loc D.nbr i w hw) (MsC i hw) (by exact hF _ hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) hMsc
    (TBa.matG (TBa.MsW i r hw) (KOrb.msContW i r hCont hw) π)
    (TBa.matG (fun _ : Unit => Br.loc D.nbr i w hw (WpO D.nd i ρ π)) (fun _ => hWc) ()) id e' he' hc hJ

theorem dR_of_wp (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hρ : Continuous fun g => rhoO D.nd i ρ π g)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    {V : Type} [AddCommGroup V] [Module (Br.LL D.nbr i w hw) V] [Module ℚ_[D.nd.l i] V]
    [IsScalarTower ℚ_[D.nd.l i] (Br.LL D.nbr i w hw) V]
    (ρ' : Representation (Br.LL D.nbr i w hw) (Br.G D.nbr i w hw) V)
    (e : V ≃ₗ[Br.LL D.nbr i w hw] (Fin D.R.r → Br.LL D.nbr i w hw))
    (he : ∀ g x, e (ρ' g x) = matRep (Br.loc D.nbr i w hw (WpO D.nd i ρ π)) g (e x)) :
    IsDR (Br.PD D.loc D.nbr i w hw) ρ' := by
  have hWc : Continuous ⇑(Br.loc D.nbr i w hw (WpO D.nd i ρ π)) :=
    KOrb.loc_cont i hw _ (KOrb.wpO_cont i ρ π hρ)
  have hcr := (wp_font i r ρ π hF hG2 hDec hCont hρ hw).1
  have hdr := (hF _ hw (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)).2.2.2
    (TBa.matG (fun _ : Unit => Br.loc D.nbr i w hw (WpO D.nd i ρ π)) (fun _ => hWc) ()) hcr
  exact dR_of_mat _ _ _ e he hdr

end DecRec

section Targets

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem crysW_of (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hρ : Continuous fun g => rhoO D.nd i ρ π g) (l : K.Col i dc) :
    KDim.CrysW i dc ρ π l := (wp_font i r ρ π hF hG2 hDec hCont hρ (col_over i dc l)).1

theorem negX_of (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hρ : Continuous fun g => rhoO D.nd i ρ π g)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (x' : Dd.X') (l : K.Col i dc) :
    KDim.NegX i dc Dd.r Dd.χ ρ π x' l := by
  intro τ a ha
  have h1 := multV_mat (Br.PD D.loc D.nbr i _ (col_over i dc l)) (MrTw i r (col_over i dc l) (Dd.p x')) _
    (phiL i Dd x' (col_over i dc l)) (phiX_equiv i dc r π g0 eB e₁ s Dd hD x' _ (col_over i dc l)) τ a
  have h2 := (hG2 _ (col_over i dc l) (TruncatedSeriesCountingIdentities.CoefExt.self i _ (col_over i dc l))).1.2.1 τ (Dd.p x') π a
  have h3 := (wp_font i r ρ π hF hG2 hDec hCont hρ (col_over i dc l)).2 τ a ha
  rw [← mrTw_eq] at h3
  exact h1.trans (h2.trans h3)

end Targets

section RowDR

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

def WpIso (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {V : Type} [AddCommGroup V]
    [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V] [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
    (ρT : Representation (D.nd.O i) ↥(Γn i dc n) V) : Prop :=
  ∃ e : TrV (eK (D.nbr i _ hn)) V ≃ₗ[Br.LL D.nbr i _ hn] (Fin D.R.r → Br.LL D.nbr i _ hn),
    ∀ g x, e (repL (eK (D.nbr i _ hn)) ρT (Br.iota D.nbr i _ hn) g x) =
      matRep (Br.loc D.nbr i _ hn (WpO D.nd i ρ π)) g (e x)

theorem isDR_of_wpIso (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hρ : Continuous fun g => rhoO D.nd i ρ π g)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) {V : Type} [AddCommGroup V]
    [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V] [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
    (ρT : Representation (D.nd.O i) ↥(Γn i dc n) V) (h : WpIso i dc ρ π n hn ρT) :
    IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn)) ρT (Br.iota D.nbr i _ hn)) := by
  obtain ⟨e, he⟩ := h
  exact dR_of_wp i r ρ π hF hG2 hDec hCont hρ hn _ e he

end RowDR

end Formalism.MainNotions.N.K.Font

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.St

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {X' d : Type} [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}
  {Tc : Type} [CommRing Tc] [Algebra Tc R']
  {Ek Ω : Type} [Field Ek] [Field Ω] [Algebra Ek Ω]
  (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) {t : ℕ} (bl : d → Fin (t + 1))
  (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
  (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ)

theorem rhoTwo_eq (g : Ω ≃ₐ[Ek] Ω) (y : {a // bl a = 0} → O) :
    rhoTwo (ρk 0) r χ ε g y = KLat.rho2 r χ bl ρk ε g y := by
  simp [rhoTwo, KLat.rho2, KLat.repL', KLat.M0]
  rfl

theorem pi_equiv2 (e₁ : R') (w : {a // bl a = 0} → O) (g : Ω ≃ₐ[Ek] Ω) (b : FirstSummandSubmodule O e₁) :
    piM (ρk 0) e₁ w (firstSummandRep O r χ e₁ ε g b) = KLat.rho2 r χ bl ρk ε g (piM (ρk 0) e₁ w b) := by
  rw [← rhoTwo_eq]
  apply pi_equiv

end Gen

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

variable {D : D7} (i : D.nd.Loc)

instance fracAdd : IsTopologicalAddGroup (FractionRing (D.nd.O i)) := Topo.fracTop_addGroup_O i
instance fracSmul : ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i)) := Topo.fracTop_smul_O i

instance rSmul {D : D7} (i : D.nd.Loc)
    (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)) :
    ContinuousConstSMul (D.nd.O i) Dd.R' := Topo.rTop_constSMul_RD i Dd

section Rec

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev Lr : Type := LatM (D.nd.O i) (D.nd.O i) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

abbrev Vr : Type := LatM (D.nd.O i) (FractionRing (D.nd.O i)) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

abbrev rho1 := firstSummandRep (D.nd.O i) Dd.r Dd.χ Dd.e₁ (epsU D.nd i)

abbrev rho2 := KLat.rho2 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i)

theorem hKm : ContinuousMul (FractionRing (D.nd.O i)) := by
  infer_instance

theorem hEps : Continuous fun g : GE D.nd => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) :=
  have hO : PadicCoeff (D.nd.l i) (D.nd.O i) :=
    ⟨D.nd.trO i, Topo.compact_O i, Topo.t2Space_nd_O i, D.nd.O_adic i, Topo.l_mem_max i, Topo.l_ne_zero i⟩
  KLat.eps_cont_nf (D.nd.l i) hO (epsU D.nd i) (Topo.isCyc_eps i)

theorem hM0 (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) :
    ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  have hO : PadicCoeff (D.nd.l i) (D.nd.O i) :=
    ⟨D.nd.trO i, Topo.compact_O i, Topo.t2Space_nd_O i, D.nd.O_adic i, Topo.l_mem_max i, Topo.l_ne_zero i⟩
  KLat.block_zero_continuous Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk hO (Topo.fgTop_RD i r π g0 eB e₁ s Dd hD)
    (Topo.uElt_cont i r π g0 eB e₁ s Dd hD hc)

variable (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

abbrev DatS (w : ℕ) := KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

abbrev uDS (w : ℕ) := KLat.uD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

abbrev vDS (w : ℕ) := KLat.vD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

abbrev modS (w : ℕ) := KLat.modT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

abbrev modS' (w : ℕ) := KLat.modT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
  (hM0 i r π g0 eB e₁ s Dd hD hc) w

theorem huDS (w : ℕ) (g : decs D.host.E (Aw i dc) w) (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) :
    uDS i r π dc g0 eB e₁ s Dd hD hc w
        (resRep (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ) ((decs D.host.E (Aw i dc)) w) g m) =
      (DatS i r π dc g0 eB e₁ s Dd hD hc w).ρA g (uDS i r π dc g0 eB e₁ s Dd hD hc w m) :=
  KLat.huD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) w g m

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

abbrev piS := piDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk

theorem hpDS (w : ℕ) :
    haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
    Continuous fun t => vDS i r π dc g0 eB e₁ s Dd hD hc w (piS i Dd hT hrk t) :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  have hO : PadicCoeff (D.nd.l i) (D.nd.O i) :=
    ⟨D.nd.trO i, Topo.compact_O i, Topo.t2Space_nd_O i, D.nd.O_adic i, Topo.l_mem_max i, Topo.l_ne_zero i⟩
  KLat.hpD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) (piS i Dd hT hrk)
    (piM_cont hO (Topo.fgTop_RD i r π g0 eB e₁ s Dd hD) (Dd.ρk 0) Dd.e₁
      (wDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk)) (Topo.fracTop_O i) w

theorem heDS (w : ℕ) (g : decs D.host.E (Aw i dc) w) (t : FirstSummandSubmodule (D.nd.O i) Dd.e₁) :
    vDS i r π dc g0 eB e₁ s Dd hD hc w (piS i Dd hT hrk (resRep (rho1 i Dd) ((decs D.host.E (Aw i dc)) w) g t)) =
      (DatS i r π dc g0 eB e₁ s Dd hD hc w).ρTl' g (vDS i r π dc g0 eB e₁ s Dd hD hc w (piS i Dd hT hrk t)) :=
  KLat.heD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) (rho1 i Dd) (piS i Dd hT hrk)
    (fun g x => pi_equiv2 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) Dd.e₁ _ g x) w g t

abbrev v1S := v1Dd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk
abbrev eveS := eveDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk
abbrev evES := evEDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT
abbrev lamS := lamDd Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk

theorem hevES (g : GE D.nd) (a : LeftId (D.nd.O i) Dd.E) :
    evES i Dd hT (uElt Dd.r Dd.χ g • a) = evES i Dd hT a :=
  evEM_inv Dd.r Dd.χ _ _ _ _ (top_facts Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT).2.2.2.2 g a

end Rec

end Formalism.MainNotions.N.K.St

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.KRowA

open Formalism.MainNotions.N.KHf Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.RepresentationBoundsCohomology.BR
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section FinT

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}

theorem rFree [Module.Finite O R'] : Module.Free O R' := by
  haveI hK : Module.IsTorsionFree O (FractionRing O) := inferInstance
  haveI : Module.IsTorsionFree O (X' → Matrix d d (FractionRing O)) :=
    Module.IsTorsionFree.mk fun r hr x y hxy => by
      funext a i j
      have h := congrFun (congrFun (congrFun hxy a) i) j
      exact hK.isSMulRegular hr h
  haveI : Module.IsTorsionFree O R' := inferInstance
  exact Module.free_of_finite_type_torsion_free'

theorem idempotent_submodule_finite [Module.Finite O R'] (e₁ : R') : Module.Finite O (FirstSummandSubmodule O e₁) := by
  haveI : IsNoetherian O R' := isNoetherian_of_isNoetherianRing_of_finite O R'
  exact Module.Finite.of_injective (FirstSummandSubmodule O e₁).subtype Subtype.val_injective

theorem idempotent_submodule_free [Module.Finite O R'] (e₁ : R') : Module.Free O (FirstSummandSubmodule O e₁) := by
  haveI := idempotent_submodule_finite (R' := R') e₁
  haveI hK : Module.IsTorsionFree O (FractionRing O) := inferInstance
  haveI : Module.IsTorsionFree O (X' → Matrix d d (FractionRing O)) :=
    Module.IsTorsionFree.mk fun r hr x y hxy => by
      funext a i j
      have h := congrFun (congrFun (congrFun hxy a) i) j
      exact hK.isSMulRegular hr h
  haveI : Module.IsTorsionFree O R' := inferInstance
  haveI : Module.IsTorsionFree O (FirstSummandSubmodule O e₁) := inferInstance
  exact Module.free_of_finite_type_torsion_free'

end FinT

section RecTop

attribute [local instance 2000] K.Topo.fracTopology K.Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (π : D.nd.X i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem idempotent_part_finite_and_free (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    Module.Finite (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁) ∧ Module.Free (D.nd.O i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁) := by
  haveI := Formalism.MainNotions.N.K.Topo.finite_R' hD
  exact ⟨idempotent_submodule_finite Dd.e₁, idempotent_submodule_free Dd.e₁⟩

def eL {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    TrV (eK (D.nbr i _ hn)) (FractionRing (D.nd.O i)) →ₗ[Br.LLw (D.nbr i _ hn)] Br.LLw (D.nbr i _ hn) where
  toFun k := eK (D.nbr i _ hn) k
  map_add' a b := map_add (eK (D.nbr i _ hn)) a b
  map_smul' c k := by
    show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm c * (show FractionRing (D.nd.O i) from k)) =
      c * eK (D.nbr i _ hn) (show FractionRing (D.nd.O i) from k)
    rw [map_mul, RingEquiv.apply_symm_apply]

theorem rowTop1_S (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    KRow.RowTop1 i dc (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁) := by
  set_option synthInstance.maxHeartbeats 200000 in
  haveI := K.Topo.finite_RD i r π g0 eB e₁ s Dd hD
  haveI : Module.Free (D.nd.O i) Dd.R' := rFree
  haveI := K.Topo.rTop_isModuleTopology (D.nd.O i) Dd.R'
  haveI := K.Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  haveI := K.Topo.rTop_smul (D.nd.O i) Dd.R'
  intro n _ hw c hc
  let b := Module.Free.chooseBasis (D.nd.O i) Dd.R'
  have hco : ∀ j, Continuous fun γ => b.equivFun ((c γ : Dd.R')) j := by
    intro j
    let f : FirstSummandSubmodule (D.nd.O i) Dd.e₁ →ₗ[D.nd.O i] FractionRing (D.nd.O i) :=
      (Algebra.linearMap (D.nd.O i) (FractionRing (D.nd.O i))) ∘ₗ (b.coord j) ∘ₗ (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype
    let ℓ := (eL i dc hw).comp (trL (eK (D.nbr i _ hw)) (liftK f))
    have hℓ : Continuous ℓ := IsModuleTopology.continuous_of_linearMap ℓ
    have h1 : Continuous fun g => eK (D.nbr i _ hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
        (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')))) := by
      have e1 : (fun g => eK (D.nbr i _ hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R'))))) =
          fun g => ℓ (KRow.tr (eK (D.nbr i _ hw)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hw g)))) := by
        funext g
        show _ = eK (D.nbr i _ hw) (liftK f (mkK (c (Br.iota D.nbr i _ hw g))))
        rw [liftK_mkK]
        rfl
      rw [e1]
      exact hℓ.comp hc
    have h2 : Continuous fun g => (D.nbr i _ hw).eO (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R'))) := by
      refine continuous_induced_rng.2 ?_
      have e2 : ((↑) ∘ fun g => (D.nbr i _ hw).eO (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')))) =
          fun g => eK (D.nbr i _ hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
            (b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')))) :=
        funext fun g => (Br.toLLK_alg (D.nbr i _ hw) _).symm
      rw [e2]
      exact h1
    have h3 : Continuous fun g => b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R')) := by
      have := (D.nbr i _ hw).eO_symm_cont.comp h2
      simpa [Function.comp_def] using this
    have heq : (fun γ => b.equivFun ((c γ : Dd.R')) j) =
        (fun g => b.coord j ((c (Br.iota D.nbr i _ hw g) : Dd.R'))) ∘ (Br.ιHomeo (D.nbr i _ hw)).symm := by
      funext γ
      simp only [Basis.equivFun_apply, Basis.coord_apply]
      exact congrArg (fun γ' => b.repr ((c γ' : Dd.R')) j) (((D.nbr i _ hw).e.symm_apply_apply γ).symm)
    rw [heq]
    exact h3.comp (Br.ιHomeo (D.nbr i _ hw)).symm.continuous
  have hv : Continuous fun γ => ((c γ : Dd.R')) := by
    have e3 : (fun γ => ((c γ : Dd.R'))) = fun γ => b.equivFun.symm (fun j => b.equivFun ((c γ : Dd.R')) j) :=
      funext fun γ => (b.equivFun.symm_apply_apply _).symm
    rw [e3]
    exact (IsModuleTopology.continuous_of_linearMap b.equivFun.symm.toLinearMap).comp (continuous_pi hco)
  exact continuous_induced_rng.2 hv

end RecTop

end Formalism.MainNotions.N.KRowA

end
end
