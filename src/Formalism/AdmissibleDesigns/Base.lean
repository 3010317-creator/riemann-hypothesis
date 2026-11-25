module

public import Formalism.AdmissibleDesigns.InvariantsEqBotIff
public import Development.AutomorphicArithmetic.CyclotomicBounds.FactorizationConductorLeLocalLevel
public import Formalism.AdicCompletionExports.AdicCompleteRingEquiv.IsAdicCompleteOfRingEquiv
public import Formalism.CharacterColumnKernels.CharacterColumnKernelEqualityForm
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.GlobalConcreteOf
import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthEqKerAddRange
public import Formalism.CharacterColumnKernels.IdempotentNormalForms.LengthKerOfDetEqZero
public import Formalism.CharacterColumnKernels.StatementPsi
public import Formalism.CharacterColumnKernels.StatementRho
import Formalism.PeriodIntegrals.FinExtTop
public import Formalism.SharpRestriction.LevelLetterCocycles.DecompositionData
public import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
public import Formalism.SharpRestriction.LevelLetterCocycles.GoodCongruenceDataOf
public import Formalism.SharpRestriction.LevelLetterCocycles.RingDataOfIdempotents
public import Formalism.WachLatticeTwists.CharacterSplitJumps.Statement
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.FirstSummandActionMem
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.SmulYGenEqZero
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.StatBridgeChiOne
public import Formalism.WachLatticeTwists.CoprimeLiftBounds.Statement
public import Formalism.WachLatticeTwists.CupProductVanishing.H2MapInjective
public import Formalism.WachLatticeTwists.LatticeDualFibres.Statement
public import Formalism.WachLatticeTwists.RamifiedBlockRings.DistinctEigenvalueCornerPerturbation
public import Formalism.WachLatticeTwists.RamifiedBlockRings.LocalToDisplayFree
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapProofs.ClsRowVOfMem
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapSecondPlace
public import Formalism.WachLatticeTwists.RealClassMaps.RealClassMapTheorem
public import Formalism.WachLatticeTwists.RealClassMaps.StatClassMapReal
public import Formalism.WachLatticeTwists.RealClassMaps.Statement
public import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.IdempotentRankOneAtPoint
public import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.SurjectionOfRankOneIdempotent
public import Formalism.WachLatticeTwists.RealDisplaySplitting.SurjectionRankOneIdempotent
public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.ShapeRowProofs.BkInRow
public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.StatClause5Row
public import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.Statement
public import Formalism.WachLatticeTwists.SplitClassesAll.Statement
public import Formalism.WachLatticeTwists.SplitLocalLifts.Cocycles1MapOfEquivariant
public import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
public import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Galois
public import Mathlib.Data.Nat.PadicValNat
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
public import Mathlib.Topology.Algebra.Nonarchimedean.Bases
public import ReciprocityTheory.GaloisValuations.Global
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

namespace Formalism.MainNotions.N.KLat

open Matrix
open Formalism.NG Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.FIN Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology ReciprocityTheory.Gal
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop)

theorem fgTop_continuous_linearMap {ℓ : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] {M N : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [ContinuousAdd M]
    [AddCommGroup N] [Module O N] [TopologicalSpace N] [ContinuousAdd N] [ContinuousSMul O N]
    (hR : IsFGTop O M) (hO : PadicCoeff ℓ O) (f : M →ₗ[O] N) : Continuous f := by
  haveI := hO.compact
  haveI := hR.t2
  haveI := hR.csmul
  haveI := hR.fg
  obtain ⟨k, π, hπ⟩ := Module.Finite.exists_fin' O M
  have hπc : Continuous π := LinearMap.continuous_on_pi π
  have hq : Topology.IsQuotientMap π := hπc.isClosedMap.isQuotientMap hπc hπ
  rw [hq.continuous_iff]
  exact LinearMap.continuous_on_pi (f.comp π)

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {n : Type} [Fintype n] [DecidableEq n]

def matK (A : Matrix n n O) : Matrix n n (FractionRing O) := A.map (algebraMap O (FractionRing O))

theorem matK_mul (A B : Matrix n n O) : matK (A * B) = matK A * matK B := by
  exact Matrix.map_mul

theorem matK_one : matK (1 : Matrix n n O) = 1 := by
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem matK_transpose (A : Matrix n n O) : matK Aᵀ = (matK A)ᵀ := rfl

theorem matK_mulVec (A : Matrix n n O) (v : n → FractionRing O) (a : n) :
    (matK A *ᵥ v) a = ∑ j, A a j • v j := by
  simp only [matK, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def]

theorem matK_mulVec_alg (A : Matrix n n O) (y : n → O) :
    matK A *ᵥ (fun a => algebraMap O (FractionRing O) (y a)) =
      fun a => algebraMap O (FractionRing O) ((A *ᵥ y) a) := by
  funext a

  simp only [matK, Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]

variable {Γ : Type} [Group Γ]

def repV (M : Γ →* Matrix n n O) : Representation O Γ (n → FractionRing O) where
  toFun g := (Matrix.mulVecLin (matK (M g))).restrictScalars O
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [matK_one]
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    simp [matK_mul, Matrix.mulVec_mulVec]

theorem repV_apply (M : Γ →* Matrix n n O) (g : Γ) (v : n → FractionRing O) :
    repV M g v = matK (M g) *ᵥ v := rfl

def repV' (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O) : Representation O Γ (n → FractionRing O) where
  toFun g := ((ε g : Oˣ) : O) • (Matrix.mulVecLin (matK (M g⁻¹)ᵀ)).restrictScalars O
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp [matK_one]
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    simp only [map_mul, Units.val_mul, LinearMap.smul_apply,
      LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Module.End.mul_apply, Matrix.mulVec_smul, smul_smul]
    rw [_root_.mul_inv_rev, map_mul, Matrix.transpose_mul, matK_mul, ← Matrix.mulVec_mulVec]

theorem repV'_apply (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O) (g : Γ) (v : n → FractionRing O) :
    repV' ε M g v = ((ε g : Oˣ) : O) • (matK (M g⁻¹)ᵀ *ᵥ v) := rfl

def repL' (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O) : Representation O Γ (n → O) where
  toFun g := ((ε g : Oˣ) : O) • Matrix.mulVecLin (M g⁻¹)ᵀ
  map_one' := by
    refine LinearMap.ext fun v => ?_
    simp
  map_mul' g h := by
    refine LinearMap.ext fun v => ?_
    simp only [map_mul, Units.val_mul, LinearMap.smul_apply,
      Matrix.mulVecLin_apply, Module.End.mul_apply, Matrix.mulVec_smul, smul_smul]
    rw [_root_.mul_inv_rev, map_mul, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]

def pairStd : (n → FractionRing O) →ₗ[O] (n → FractionRing O) →ₗ[O] FractionRing O :=
  LinearMap.mk₂ O (fun x y => x ⬝ᵥ y) (fun x x' y => add_dotProduct x x' y)
    (fun c x y => smul_dotProduct c x y) (fun x y y' => dotProduct_add x y y')
    (fun c x y => dotProduct_smul c x y)

theorem pairStd_apply (x y : n → FractionRing O) : pairStd x y = x ⬝ᵥ y := rfl

def latT : Submodule O (n → FractionRing O) :=
  Submodule.pi Set.univ (fun _ => (1 : Submodule O (FractionRing O)))

theorem mem_latT (x : n → FractionRing O) :
    x ∈ (latT : Submodule O (n → FractionRing O)) ↔ ∃ y : n → O, x = fun a => algebraMap O _ (y a) := by
  simp only [latT, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  constructor
  · intro h
    choose y hy using h
    exact ⟨y, funext fun a => (hy a).symm⟩
  · rintro ⟨y, rfl⟩ a
    exact ⟨y a, rfl⟩

theorem latT_stable (M : Γ →* Matrix n n O) : StableUnder (repV M) (latT : Submodule O (n → FractionRing O)) := by
  intro g x hx
  obtain ⟨y, rfl⟩ := (mem_latT x).1 hx
  refine (mem_latT _).2 ⟨M g *ᵥ y, ?_⟩
  rw [repV_apply, matK_mulVec_alg]

theorem matK_inv_mul (M : Γ →* Matrix n n O) (g : Γ) : matK (M g⁻¹) * matK (M g) = 1 := by
  rw [← matK_mul, ← map_mul, inv_mul_cancel, map_one, matK_one]

theorem eq_pairStd (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O) : EquivPair ε (repV M) (repV' ε M) pairStd := by
  intro g x f
  rw [pairStd_apply, pairStd_apply, repV_apply, repV'_apply, dotProduct_smul, matK_transpose,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, matK_inv_mul, Matrix.one_mulVec]

section Top
variable [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] [TopologicalSpace Γ]

theorem contAction_repV' (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O)
    (hε : Continuous fun g => ((ε g : Oˣ) : O)) (hM : ∀ a b, Continuous fun g => M g⁻¹ b a) :
    ContAction (repV' ε M) := by
  show Continuous fun p : Γ × (n → FractionRing O) => repV' ε M p.1 p.2
  refine continuous_pi fun a => ?_
  simp only [repV'_apply, Pi.smul_apply, matK_mulVec]
  refine (hε.comp continuous_fst).smul ?_
  exact continuous_finsetSum _ fun j _ =>
    ((hM a j).comp continuous_fst).smul ((continuous_apply j).comp continuous_snd)

theorem contAction_repV (M : Γ →* Matrix n n O) (hM : ∀ a b, Continuous fun g => M g a b) :
    ContAction (repV M) := by
  show Continuous fun p : Γ × (n → FractionRing O) => repV M p.1 p.2
  refine continuous_pi fun a => ?_
  simp only [repV_apply, matK_mulVec]
  exact continuous_finsetSum _ fun j _ =>
    ((hM a j).comp continuous_fst).smul ((continuous_apply j).comp continuous_snd)

theorem cont_pairStd [ContinuousMul (FractionRing O)] :
    Continuous fun p : (n → FractionRing O) × (n → FractionRing O) => pairStd p.1 p.2 := by
  simp only [pairStd_apply, dotProduct]
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)

def datStd (hK : ContinuousMul (FractionRing O)) (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O)
    (hε : Continuous fun g => ((ε g : Oˣ) : O)) (hM : ∀ a b, Continuous fun g => M g⁻¹ b a) :
    LatData O Γ (n → FractionRing O) (n → FractionRing O) where
  ε := ε
  ρT := repV M
  ρT' := repV' ε M
  bT := pairStd
  T := latT
  stT := latT_stable M
  eqT := eq_pairStd ε M
  contT' := contAction_repV' ε M hε hM
  contbT := haveI := hK; cont_pairStd
  inv := 0
  invF := 0

end Top

end Gen

section Iso

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {n : Type} [Fintype n] [DecidableEq n]

def vMap : (n → O) →ₗ[O] dualLat (pairStd (O := O) (n := n)) latT where
  toFun y := ⟨fun a => algebraMap O (FractionRing O) (y a), by
    intro x hx
    obtain ⟨z, rfl⟩ := (mem_latT x).1 hx
    refine Submodule.mem_one.2 ⟨∑ a, z a * y a, ?_⟩

    simp [pairStd_apply, dotProduct, map_sum, map_mul]⟩
  map_add' y y' := Subtype.ext (funext fun a => by simp)
  map_smul' c y := Subtype.ext (funext fun a => by simp [Algebra.smul_def])

theorem unit_mem_latT (a : n) :
    (fun j => if a = j then (1 : FractionRing O) else 0) ∈ (latT : Submodule O (n → FractionRing O)) := by
  refine (mem_latT _).2 ⟨fun j => if a = j then 1 else 0, funext fun j => ?_⟩
  by_cases h : a = j <;> simp [h]

theorem vMap_bij : Function.Bijective (vMap (O := O) (n := n)) := by
  constructor
  · intro y y' h
    funext a
    have h' := congrFun (congrArg Subtype.val h) a
    exact IsFractionRing.injective O (FractionRing O) h'
  · rintro ⟨f, hf⟩
    have h : ∀ a, ∃ y : O, algebraMap O (FractionRing O) y = f a := by
      intro a
      have h1 := hf _ (unit_mem_latT a)
      rw [pairStd_apply] at h1
      simpa [dotProduct, Submodule.mem_one] using h1
    choose y hy using h
    exact ⟨y, Subtype.ext (funext fun a => hy a)⟩

def vStd : (n → O) ≃ₗ[O] dualLat (pairStd (O := O) (n := n)) latT :=
  LinearEquiv.ofBijective vMap vMap_bij

theorem vStd_apply (y : n → O) (a : n) :
    ((vStd y : dualLat (pairStd (O := O) (n := n)) latT) : n → FractionRing O) a = algebraMap O _ (y a) := rfl

def uStd : (n → KO O) ≃ₗ[O] (n → FractionRing O) ⧸ (latT : Submodule O (n → FractionRing O)) :=
  (Submodule.quotientPi (fun _ : n => (1 : Submodule O (FractionRing O)))).symm

theorem uStd_mk (x : n → FractionRing O) :
    uStd (fun a => toKO O (x a)) = Submodule.Quotient.mk x := by
  apply (uStd (O := O) (n := n)).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  funext a
  first
    | rfl

def gamStd : (n → O) →ₗ[O] (n → KO O) →ₗ[O] KO O :=
  LinearMap.mk₂ O (fun t m => ∑ a, t a • m a)
    (fun t t' m => by simp [add_smul, Finset.sum_add_distrib])
    (fun c t m => by simp [Finset.smul_sum, mul_smul])
    (fun t m m' => by simp [smul_add, Finset.sum_add_distrib])
    (fun c t m => by simp [Finset.smul_sum, smul_comm c])

theorem gamStd_apply (t : n → O) (m : n → KO O) : gamStd t m = ∑ a, t a • m a := rfl

theorem gamStd_eq (t : n → O) (m : n → KO O) :
    gamStd t m = pairKO (pairStd (O := O) (n := n)) (latT (O := O) (n := n)) (uStd m) (vStd t) := by
  obtain ⟨x, rfl⟩ : ∃ x : n → FractionRing O, (fun a => toKO O (x a)) = m :=
    ⟨fun a => (Submodule.Quotient.mk_surjective _ (m a)).choose,
      funext fun a => (Submodule.Quotient.mk_surjective _ (m a)).choose_spec⟩
  rw [uStd_mk, gamStd_apply]
  simp only [pairKO, Submodule.liftQ_apply, LinearMap.compr₂_apply, LinearMap.compl₂_apply,
    Submodule.subtype_apply, pairStd_apply, dotProduct, vStd_apply]

  rw [map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← map_smul, Algebra.smul_def, mul_comm]

end Iso

section RL

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {n : Type} [Fintype n] [DecidableEq n] {Γ : Type} [Group Γ] [TopologicalSpace Γ]

theorem t2Space_fractionRing_of_padicCoeff (ℓ : ℕ) (hO : PadicCoeff ℓ O) (hF : FracTop O) : T2Space (FractionRing O) := by
  haveI := hO.t2
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun z hz => ?_
  by_cases h : z ∈ Set.range (algebraMap O (FractionRing O))
  · obtain ⟨w, rfl⟩ := h
    have hw : w ≠ 0 := by
      rintro rfl
      exact hz (map_zero _)
    obtain ⟨U1, U2, hU1, _, h0, hw', hd⟩ := t2_separation hw.symm
    refine ⟨algebraMap O _ '' U1, (hF.emb.isOpenMap U1 hU1).mem_nhds ⟨0, h0, map_zero _⟩, ?_⟩
    rintro ⟨v, hv, hvw⟩
    have hvw' : v = w := IsFractionRing.injective O (FractionRing O) hvw
    subst hvw'
    exact Set.disjoint_left.1 hd hv hw'
  · exact ⟨_, hF.emb.isOpen_range.mem_nhds ⟨0, map_zero _⟩, h⟩

theorem latT_fg : (latT : Submodule O (n → FractionRing O)).FG := by
  have h : (latT : Submodule O (n → FractionRing O)) = Submodule.map
      (LinearMap.pi fun a => (Algebra.linearMap O (FractionRing O)).comp (LinearMap.proj a)) ⊤ := by
    ext x
    rw [mem_latT, Submodule.map_top, LinearMap.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, rfl⟩
  rw [h]
  exact Module.Finite.fg_top.map _

theorem latT_span :
    Submodule.span (FractionRing O) ((latT : Submodule O (n → FractionRing O)) : Set (n → FractionRing O)) = ⊤ := by
  rw [eq_top_iff]
  rintro v -
  have hv : v = ∑ a, v a • (fun j => if a = j then (1 : FractionRing O) else 0) := by
    funext j
    simp [Finset.sum_apply]
  rw [hv]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span (unit_mem_latT a))

theorem perf_pairStd : PerfectRight (pairStd (O := O) (n := n)) := by
  intro ψ
  refine ⟨fun a => ψ (fun j => if a = j then 1 else 0), fun x => ?_, fun f hf => ?_⟩
  · rw [pairStd_apply, LinearMap.pi_apply_eq_sum_univ ψ x]
    simp [dotProduct, smul_eq_mul]
  · funext a
    have h := hf (fun j => if a = j then 1 else 0)
    rw [pairStd_apply] at h
    simpa [dotProduct] using h

theorem latT_open (hF : FracTop O) :
    IsOpen ((latT : Submodule O (n → FractionRing O)) : Set (n → FractionRing O)) := by
  have h : ((latT : Submodule O (n → FractionRing O)) : Set (n → FractionRing O)) =
      Set.univ.pi fun _ => Set.range (algebraMap O (FractionRing O)) := by
    ext x
    simp only [SetLike.mem_coe, mem_latT, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_range]
    constructor
    · rintro ⟨y, rfl⟩ a
      exact ⟨y a, rfl⟩
    · intro h
      choose y hy using h
      exact ⟨y, funext fun a => (hy a).symm⟩
  rw [h]
  exact isOpen_set_pi Set.finite_univ fun a _ => hF.emb.isOpen_range

theorem realLat_datStd (ℓ : ℕ) (hO : PadicCoeff ℓ O) (hF : FracTop O) (hK : ContinuousMul (FractionRing O))
    (ε : Γ →* Oˣ) (M : Γ →* Matrix n n O) (hε : Continuous fun g => ((ε g : Oˣ) : O))
    (hM : ∀ a b, Continuous fun g => M g⁻¹ b a) (hM' : ∀ a b, Continuous fun g => M g a b) :
    RealLat (datStd hK ε M hε hM) := by
  have := t2Space_fractionRing_of_padicCoeff ℓ hO hF
  have := hK
  exact
    { lat := ⟨latT_fg, latT_span⟩
      perf := perf_pairStd
      contT := contAction_repV M hM'
      openT := latT_open hF
      t2 := inferInstance
      t2' := inferInstance
      cs := inferInstance
      cs' := inferInstance }

end RL

section Cont

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]

theorem eps_cont (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hO : PadicCoeff ℓ O) {Ek Ω : Type} [Field Ek] [Field Ω] [Algebra Ek Ω]
    [CharZero Ω] [IsAlgClosed Ω] (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (hc : IsCycG ℓ ε) :
    Continuous fun g => ((ε g : Oˣ) : O) := by
  haveI := hO.ring
  have hB : ∀ U ∈ nhds (0 : O), ∃ n : ℕ, ((Ideal.span {(ℓ : O) ^ n} : Ideal O) : Set O) ⊆ U := by
    intro U hU
    obtain ⟨k, hk⟩ := (isAdic_iff.1 hO.adic).2 U hU
    exact ⟨k, fun x hx => hk ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.pow_mem_pow hO.p_mem k) hx)⟩
  have hA : ∀ n : ℕ, ∃ W : Set (Ω ≃ₐ[Ek] Ω), IsOpen W ∧ (1 : Ω ≃ₐ[Ek] Ω) ∈ W ∧
      ∀ h ∈ W, ((ε h : Oˣ) : O) - 1 ∈ Ideal.span {(ℓ : O) ^ n} := by
    intro n
    have hN : 0 < ℓ ^ n := pow_pos hℓ.out.pos n
    haveI : NeZero ((ℓ ^ n : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hN.ne'⟩
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic (ℓ ^ n) Ω)
      (Polynomial.degree_cyclotomic_pos _ Ω hN).ne'
    have hprim : IsPrimitiveRoot ζ (ℓ ^ n) := Polynomial.isRoot_cyclotomic_iff.1 hζ
    have hint : IsIntegral Ek ζ := IsIntegral.of_pow hN (by rw [hprim.pow_eq_one]; exact isIntegral_one)
    haveI : FiniteDimensional Ek (IntermediateField.adjoin Ek {ζ}) :=
      IntermediateField.adjoin.finiteDimensional hint
    refine ⟨((IntermediateField.adjoin Ek {ζ}).fixingSubgroup : Set (Ω ≃ₐ[Ek] Ω)),
      IntermediateField.fixingSubgroup_isOpen _, (IntermediateField.adjoin Ek {ζ}).fixingSubgroup.one_mem,
      fun h hh => ?_⟩
    have hfix : h ζ = ζ := by
      first
        | exact ((IntermediateField.mem_fixingSubgroup_iff _ _).1 hh) ζ (IntermediateField.mem_adjoin_simple_self Ek ζ)
    obtain ⟨a, ha1, ha2⟩ := hc h n ζ hprim.pow_eq_one
    rw [hfix] at ha1
    have hz : ζ ≠ 0 := hprim.ne_zero hN.ne'
    have hdvd : ((ℓ ^ n : ℕ) : ℤ) ∣ (a : ℤ) - 1 := by
      rw [← hprim.zpow_eq_one_iff_dvd, zpow_sub₀ hz, zpow_natCast, zpow_one, ← ha1, div_self hz]
    obtain ⟨m, hm⟩ := hdvd
    have hm' := congrArg (Int.cast : ℤ → O) hm
    push_cast at hm'
    have he : ((ε h : Oˣ) : O) - 1 = (((ε h : Oˣ) : O) - a) + (ℓ : O) ^ n * (m : O) := by
      linear_combination hm'
    rw [he]
    exact Ideal.add_mem _ ha2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  rw [continuous_iff_continuousAt]
  intro g₀
  refine Filter.tendsto_def.2 fun V hV => ?_
  have hV' : (fun x => ((ε g₀ : Oˣ) : O) + x) ⁻¹' V ∈ nhds (0 : O) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hV)
  obtain ⟨n, hn⟩ := hB _ hV'
  obtain ⟨W, hWo, hW1, hW⟩ := hA n
  have hWn : (fun g => g₀⁻¹ * g) ⁻¹' W ∈ nhds g₀ :=
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hWo.mem_nhds hW1)
  refine Filter.mem_of_superset hWn fun g hg => ?_
  have h1 := hW _ hg
  have hg' : g = g₀ * (g₀⁻¹ * g) := by group
  have he : ((ε g : Oˣ) : O) = ((ε g₀ : Oˣ) : O) + ((ε g₀ : Oˣ) : O) * (((ε (g₀⁻¹ * g) : Oˣ) : O) - 1) := by
    conv_lhs => rw [hg']
    rw [map_mul, Units.val_mul]
    ring
  rw [Set.mem_preimage, he]
  exact hn (Ideal.mul_mem_left _ _ h1)

end Cont

section H1K

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] {V : Type} [AddCommGroup V] [Module O V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [TopologicalSpace O] [ContinuousSMul O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
  (ρ : Representation O Γ V) (hcs : ContinuousConstSMul (FractionRing O) V)
  (hρ : ∀ g (c : FractionRing O) v, ρ g (c • v) = c • ρ g v)

def cocyclesFractionSubspace : Submodule (FractionRing O) (Γ → V) where
  carrier := {f | f ∈ Z1 ρ}
  zero_mem' := (Z1 ρ).zero_mem
  add_mem' ha hb := (Z1 ρ).add_mem ha hb
  smul_mem' c f hf := by
    have := hcs
    refine ⟨hf.1.const_smul c, fun g h => ?_⟩
    simp only [Pi.smul_apply, hf.2 g h, smul_add, hρ]

def zsm (c : FractionRing O) : Z1 ρ →ₗ[O] Z1 ρ where
  toFun z := ⟨c • (z : Γ → V), (cocyclesFractionSubspace ρ hcs hρ).smul_mem c z.2⟩
  map_add' z z' := Subtype.ext (smul_add c _ _)
  map_smul' o z := Subtype.ext (by
    funext g
    show c • (o • (z : Γ → V) g) = o • (c • (z : Γ → V) g)
    rw [← algebraMap_smul (FractionRing O) o ((z : Γ → V) g),
      ← algebraMap_smul (FractionRing O) o (c • (z : Γ → V) g), smul_smul, smul_smul, mul_comm])

theorem zsm_B (c : FractionRing O) :
    (B1 ρ).comap (Z1 ρ).subtype ≤ ((B1 ρ).comap (Z1 ρ).subtype).comap (zsm ρ hcs hρ c) := by
  intro z hz
  simp only [Submodule.mem_comap, Submodule.coe_subtype] at hz ⊢
  obtain ⟨v, hv⟩ := hz
  refine ⟨c • v, ?_⟩
  rw [show ((zsm ρ hcs hρ c z : Z1 ρ) : Γ → V) = c • (z : Γ → V) from rfl, ← hv]
  funext g
  simp [d0, hρ, smul_sub]

def smulH1FractionField : SMul (FractionRing O) (H1 ρ) :=
  ⟨fun c => Submodule.mapQ _ _ (zsm ρ hcs hρ c) (zsm_B ρ hcs hρ c)⟩

def cocyclesToH1 : cocyclesFractionSubspace ρ hcs hρ →+ H1 ρ where
  toFun z := Submodule.Quotient.mk ⟨z.1, z.2⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def moduleH1FractionField : Module (FractionRing O) (H1 ρ) :=
  letI := smulH1FractionField ρ hcs hρ
  Function.Surjective.module (FractionRing O) (cocyclesToH1 ρ hcs hρ)
    (by
      intro x
      induction x using Submodule.Quotient.induction_on with
      | H z => exact ⟨⟨z.1, z.2⟩, rfl⟩)
    (fun _ _ => rfl)

theorem isScalarTower_H1 :
    @IsScalarTower O (FractionRing O) (H1 ρ) _ (moduleH1FractionField ρ hcs hρ).toSMul _ := by
  letI := moduleH1FractionField ρ hcs hρ
  refine ⟨fun o c x => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H z =>
    change Submodule.mapQ _ _ (zsm ρ hcs hρ (o • c)) (zsm_B ρ hcs hρ (o • c)) (Submodule.Quotient.mk z) =
      o • Submodule.mapQ _ _ (zsm ρ hcs hρ c) (zsm_B ρ hcs hρ c) (Submodule.Quotient.mk z)
    rw [Submodule.mapQ_apply, Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    funext g
    exact smul_assoc o c ((z : Γ → V) g)

end H1K

section Spec

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {X' d : Type} [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}
  {Tc : Type} [CommRing Tc] [Algebra Tc R']
  {Ek Ω : Type} [Field Ek] [Field Ω] [Algebra Ek Ω]
  (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) {t : ℕ} (bl : d → Fin (t + 1))
  (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
  (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (Aw : ℕ → ValuationSubring Ω)

def uHom : (Ω ≃ₐ[Ek] Ω) →* R' where
  toFun := uElt r χ
  map_one' := uElt_one r χ
  map_mul' := uElt_mul r χ

def M0 : (Ω ≃ₐ[Ek] Ω) →* Matrix {a // bl a = 0} {a // bl a = 0} O :=
  (ρk 0).toRingHom.toMonoidHom.comp (uHom r χ)

def Mw (w : ℕ) : decs Ek Aw w →* Matrix {a // bl a = 0} {a // bl a = 0} O :=
  (M0 r χ bl ρk).comp (decs Ek Aw w).subtype

def epsW (w : ℕ) : decs Ek Aw w →* Oˣ := ε.comp (decs Ek Aw w).subtype

def rho2 : Representation O (Ω ≃ₐ[Ek] Ω) ({a // bl a = 0} → O) := repL' ε (M0 r χ bl ρk)

theorem rho2_apply (g : Ω ≃ₐ[Ek] Ω) (y : {a // bl a = 0} → O) :
    rho2 r χ bl ρk ε g y = ((ε g : Oˣ) : O) • ((ρk 0 (uElt r χ g⁻¹))ᵀ *ᵥ y) := rfl

abbrev VT (_w : ℕ) : Type := {a // bl a = 0} → FractionRing O

def Dat (hK : ContinuousMul (FractionRing O)) (hε : Continuous fun g => ((ε g : Oˣ) : O))
    (hM : ∀ a b, Continuous fun g => M0 r χ bl ρk g a b) (w : ℕ) :
    LatData O (decs Ek Aw w) (VT (O := O) bl w) (VT (O := O) bl w) :=
  datStd (Γ := decs Ek Aw w) hK (epsW ε Aw w) (Mw r χ bl ρk Aw w)
    (hε.comp continuous_subtype_val)
    (fun a b => (hM b a).comp (continuous_subtype_val.comp continuous_inv))

def blkEquiv : blockRestrictedRepresentationType bl ρk 0 ≃ₗ[O] ({a // bl a = 0} → KO O) where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable (hK : ContinuousMul (FractionRing O)) (hε : Continuous fun g => ((ε g : Oˣ) : O))
    (hM : ∀ a b, Continuous fun g => M0 r χ bl ρk g a b)

def uD (w : ℕ) : blockRestrictedRepresentationType bl ρk 0 ≃ₗ[O] (VT (O := O) bl w ⧸ (Dat r χ bl ρk ε Aw hK hε hM w).T) :=
  (blkEquiv bl ρk).trans uStd

def vD (w : ℕ) : ({a // bl a = 0} → O) ≃ₗ[O] (Dat r χ bl ρk ε Aw hK hε hM w).T' := vStd

def gam : ({a // bl a = 0} → O) →ₗ[O] blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O :=
  gamStd.compl₂ (blkEquiv bl ρk).toLinearMap

theorem vD_equiv (w : ℕ) (g : decs Ek Aw w) (y : {a // bl a = 0} → O) :
    vD r χ bl ρk ε Aw hK hε hM w (rho2 r χ bl ρk ε g y) =
      (Dat r χ bl ρk ε Aw hK hε hM w).ρTl' g (vD r χ bl ρk ε Aw hK hε hM w y) := by
  apply Subtype.ext
  funext a
  change algebraMap O (FractionRing O) (rho2 r χ bl ρk ε (g : Ω ≃ₐ[Ek] Ω) y a) =
    (repV' (epsW ε Aw w) (Mw r χ bl ρk Aw w) g (fun b => algebraMap O (FractionRing O) (y b))) a
  rw [repV'_apply, matK_mulVec_alg, rho2_apply]
  simp only [Pi.smul_apply, smul_eq_mul, Algebra.smul_def, map_mul]
  try rfl

theorem gam_eq (w : ℕ) (y : {a // bl a = 0} → O) (m : blockRestrictedRepresentationType bl ρk 0) :
    gam bl ρk y m = pairKO (Dat r χ bl ρk ε Aw hK hε hM w).bT (Dat r χ bl ρk ε Aw hK hε hM w).T
      (uD r χ bl ρk ε Aw hK hε hM w m) (vD r χ bl ρk ε Aw hK hε hM w y) := by
  exact gamStd_eq y (blkEquiv bl ρk m)

private theorem smul_apply_eq_toKO_matK_mulVec {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {X' d : Type} [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}
    {t : ℕ} (bl : d → Fin (t + 1)) (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    (u : R') (m : blockRestrictedRepresentationType bl ρk 0) (a : {a // bl a = 0}) (x : {a // bl a = 0} → FractionRing O)
    (hx : (fun a => toKO O (x a)) = m) :
    (u • m) a = toKO O ((matK (ρk 0 u) *ᵥ x) a) := by
  subst hx
  simp [matK_mulVec]
  rfl

theorem huD [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] (w : ℕ) (g : decs Ek Aw w) (m : blockRestrictedRepresentationType bl ρk 0) :
    uD r χ bl ρk ε Aw hK hε hM w (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ) (decs Ek Aw w) g m) =
      (Dat r χ bl ρk ε Aw hK hε hM w).ρA g (uD r χ bl ρk ε Aw hK hε hM w m) := by
  choose x hx using fun a => Submodule.Quotient.mk_surjective _ (m a)
  have hxm : (fun a => toKO O (x a)) = m := funext hx
  have hL : (fun a => toKO O ((matK (ρk 0 (uElt r χ (g : Ω ≃ₐ[Ek] Ω))) *ᵥ x) a)) =
      resRep (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ) (decs Ek Aw w) g m := by
    funext a
    exact (smul_apply_eq_toKO_matK_mulVec bl ρk _ m a x hxm).symm
  have e1 : uD r χ bl ρk ε Aw hK hε hM w (fun a => toKO O (x a)) = Submodule.Quotient.mk x := uStd_mk x
  rw [← hL, ← hxm, e1]
  exact uStd_mk (matK (ρk 0 (uElt r χ (g : Ω ≃ₐ[Ek] Ω))) *ᵥ x)

end Spec

section Cont2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
variable [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {X' d : Type} [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}
  [TopologicalSpace R'] [IsTopologicalAddGroup R']
  {Tc : Type} [CommRing Tc] [Algebra Tc R']
  {Ek Ω : Type} [Field Ek] [Field Ω] [Algebra Ek Ω]
  (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) {t : ℕ} (bl : d → Fin (t + 1))
  (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)

theorem block_zero_continuous {ℓ : ℕ} (hO : PadicCoeff ℓ O) (hR : IsFGTop O R') (hu : Continuous fun g => uElt r χ g)
    (a b : {a // bl a = 0}) : Continuous fun g => M0 r χ bl ρk g a b := by
  haveI := hO.ring
  let f : R' →ₗ[O] O :=
    { toFun := fun x => ρk 0 x a b
      map_add' := fun x y => by simp
      map_smul' := fun c x => by simp }
  have hf : Continuous f := by
    set_option synthInstance.maxHeartbeats 100000 in
      exact fgTop_continuous_linearMap hR hO f
  exact hf.comp hu

end Cont2

section Clauses

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
  [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
  {X' d : Type} [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))}
  {Tc : Type} [CommRing Tc] [Algebra Tc R']
  {Ek Ω : Type} [Field Ek] [Field Ω] [Algebra Ek Ω]
  (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) {t : ℕ} (bl : d → Fin (t + 1))
  (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
  (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (Aw : ℕ → ValuationSubring Ω)
  (hK : ContinuousMul (FractionRing O)) (hε : Continuous fun g => ((ε g : Oˣ) : O))
  (hM : ∀ a b, Continuous fun g => M0 r χ bl ρk g a b)

theorem realLat_Dat (ℓ : ℕ) (hO : PadicCoeff ℓ O) (hF : FracTop O) (w : ℕ) :
    RealLat (Dat r χ bl ρk ε Aw hK hε hM w) := by
  exact realLat_datStd ℓ hO hF hK (epsW ε Aw w) (Mw r χ bl ρk Aw w) _ _
    (fun a b => (hM a b).comp continuous_subtype_val)

theorem rowLat (ℓ : ℕ) (hO : PadicCoeff ℓ O) (hF : FracTop O) (w : ℕ) :
    (∀ g : decs Ek Aw w, (Dat r χ bl ρk ε Aw hK hε hM w).ε g = ε g) ∧
    RealLat (Dat r χ bl ρk ε Aw hK hε hM w) ∧
    (∀ (g : decs Ek Aw w) (y : {a // bl a = 0} → O),
      vD r χ bl ρk ε Aw hK hε hM w (rho2 r χ bl ρk ε g y) =
        (Dat r χ bl ρk ε Aw hK hε hM w).ρTl' g (vD r χ bl ρk ε Aw hK hε hM w y)) ∧
    (∀ (y : {a // bl a = 0} → O) (m : blockRestrictedRepresentationType bl ρk 0),
      gam bl ρk y m = pairKO (Dat r χ bl ρk ε Aw hK hε hM w).bT (Dat r χ bl ρk ε Aw hK hε hM w).T
        (uD r χ bl ρk ε Aw hK hε hM w m) (vD r χ bl ρk ε Aw hK hε hM w y)) := by
  exact ⟨fun g => rfl, realLat_Dat r χ bl ρk ε Aw hK hε hM ℓ hO hF w,
    fun g y => vD_equiv r χ bl ρk ε Aw hK hε hM w g y, fun y m => gam_eq r χ bl ρk ε Aw hK hε hM w y m⟩

theorem hpD {T₁ : Type} [AddCommGroup T₁] [Module O T₁] [TopologicalSpace T₁]
    (π : T₁ →ₗ[O] ({a // bl a = 0} → O)) (hπ : Continuous π) (hF : FracTop O) (w : ℕ) :
    Continuous fun x => vD r χ bl ρk ε Aw hK hε hM w (π x) := by
  refine continuous_induced_rng.2 ?_
  exact continuous_pi fun a => hF.emb.continuous.comp ((continuous_apply a).comp hπ)

theorem heD {T₁ : Type} [AddCommGroup T₁] [Module O T₁] (ρ₁ : Representation O (Ω ≃ₐ[Ek] Ω) T₁)
    (π : T₁ →ₗ[O] ({a // bl a = 0} → O)) (hπe : ∀ g x, π (ρ₁ g x) = rho2 r χ bl ρk ε g (π x))
    (w : ℕ) (g : decs Ek Aw w) (x : T₁) :
    vD r χ bl ρk ε Aw hK hε hM w (π (resRep ρ₁ (decs Ek Aw w) g x)) =
      (Dat r χ bl ρk ε Aw hK hε hM w).ρTl' g (vD r χ bl ρk ε Aw hK hε hM w (π x)) := by
  have h : π (resRep ρ₁ (decs Ek Aw w) g x) = rho2 r χ bl ρk ε g (π x) := hπe g x
  rw [h]
  exact vD_equiv r χ bl ρk ε Aw hK hε hM w g (π x)

theorem csK (h : ContinuousMul (FractionRing O)) :
    ContinuousConstSMul (FractionRing O) ({a // bl a = 0} → FractionRing O) := by
  haveI := h
  infer_instance

def modT (w : ℕ) : Module (FractionRing O) (H1 (Dat r χ bl ρk ε Aw hK hε hM w).ρT) :=
  moduleH1FractionField _ (csK bl hK) (fun g c v => Matrix.mulVec_smul _ c v)

theorem towerT (w : ℕ) :
    @IsScalarTower O (FractionRing O) (H1 (Dat r χ bl ρk ε Aw hK hε hM w).ρT) _
      (modT r χ bl ρk ε Aw hK hε hM w).toSMul _ := by
  exact isScalarTower_H1 _ _ _

theorem repV'_smul {Γ : Type} [Group Γ] {n : Type} [Fintype n] [DecidableEq n] (ε' : Γ →* Oˣ)
    (M : Γ →* Matrix n n O) (g : Γ) (c : FractionRing O) (v : n → FractionRing O) :
    repV' ε' M g (c • v) = c • repV' ε' M g v := by
  rw [repV'_apply, repV'_apply, Matrix.mulVec_smul, smul_comm]

def modT' (w : ℕ) : Module (FractionRing O) (H1 (Dat r χ bl ρk ε Aw hK hε hM w).ρT') :=
  moduleH1FractionField _ (csK bl hK) (repV'_smul _ _)

theorem towerT' (w : ℕ) :
    @IsScalarTower O (FractionRing O) (H1 (Dat r χ bl ρk ε Aw hK hε hM w).ρT') _
      (modT' r χ bl ρk ε Aw hK hε hM w).toSMul _ := by
  exact isScalarTower_H1 _ _ _

end Clauses

section Inputs

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  {Ek Ω : Type} [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]

theorem eps_cont_nf (ℓ : ℕ) [Fact ℓ.Prime] (hO : PadicCoeff ℓ O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (hc : IsCycG ℓ ε) :
    Continuous fun g => ((ε g : Oˣ) : O) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed Ek
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap Ek Ω).injective
  exact eps_cont ℓ hO ε hc

end Inputs

end Formalism.MainNotions.N.KLat
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.MainNotions.N.K

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.SF

section Ko
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem ko_faithful (c : O) (h : ∀ z : KO O, c • z = 0) : c = 0 := by
  by_contra hc
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : ϖ ≠ 0 := hϖ.ne_zero
  let ι := algebraMap O (FractionRing O)
  have hc' : ι c ≠ 0 := fun h0 => hc (IsFractionRing.injective O (FractionRing O) (h0.trans (map_zero ι).symm))
  have hϖ' : ι ϖ ≠ 0 := fun h0 => hϖ0 (IsFractionRing.injective O (FractionRing O) (h0.trans (map_zero ι).symm))
  have h1 := h (Submodule.Quotient.mk ((ι c * ι ϖ)⁻¹))
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Algebra.smul_def, mul_inv,
    ← mul_assoc, mul_inv_cancel₀ hc', one_mul] at h1
  obtain ⟨o, ho⟩ := Submodule.mem_one.1 h1
  apply hϖ.not_isUnit
  refine isUnit_iff_exists_inv.2 ⟨o, IsFractionRing.injective O (FractionRing O) ?_⟩
  rw [map_mul, map_one]
  change ι ϖ * ι o = 1
  rw [ho, mul_inv_cancel₀ hϖ']

end Ko

section Blocks
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type} [Ring A] [Algebra O A]
  {n : Type} [Fintype n] [DecidableEq n]

theorem latQ_act (ρ : A →ₐ[O] Matrix n n O) (x : A) (m : LatQ O n ρ.toRingHom) (i : n) :
    (x • m) i = ∑ j, ρ x i j • (m j : KO O) := rfl

theorem mat_eq_of_act (ρ : A →ₐ[O] Matrix n n O) (x : A) (y : O)
    (h : ∀ m : LatQ O n ρ.toRingHom, x • m = y • m) : ρ x = y • (1 : Matrix n n O) := by
  ext i j
  apply sub_eq_zero.1
  apply ko_faithful O
  intro z
  have h1 := congrFun (h (Pi.single j z : n → KO O)) i
  change ∑ j', ρ x i j' • (Pi.single j z : n → KO O) j' = y • (Pi.single j z : n → KO O) i at h1
  rw [Finset.sum_eq_single j (fun b _ hb => by simp [hb]) (by simp)] at h1
  have h2 : ρ x i j • z = y • (Pi.single j z : n → KO O) i := by
    have h3 := h1
    rwa [Pi.single_eq_same] at h3
  rw [sub_smul, h2, Matrix.smul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

theorem act_trace (ρ : A →ₐ[O] Matrix n n O) (h1 : Fintype.card n = 1) (x : A) (m : LatQ O n ρ.toRingHom) :
    x • m = (ρ x).trace • m := by
  obtain ⟨i0, hi0⟩ := Fintype.card_eq_one_iff.1 h1
  funext i
  rw [latQ_act]
  change _ = (ρ x).trace • (m i : KO O)
  have hu : ∀ j : n, j = i := fun j => (hi0 j).trans (hi0 i).symm
  rw [Finset.sum_eq_single i (fun b _ hb => absurd (hu b) hb) (by simp), Matrix.trace,
    Finset.sum_eq_single i (fun b _ hb => absurd (hu b) hb) (by simp)]
  rfl

end Blocks

section ZlStr
variable {ℓ : ℕ} [Fact ℓ.Prime]

end ZlStr

section Lat
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type} [Ring A] [Algebra O A]
  {n : Type} [Fintype n] [DecidableEq n]

def vOne (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (h : SurjectionRankOneIdempotent O A n ρ.toRingHom e₁) : LatM O O n ρ.toRingHom := h.choose

theorem vOne_spec (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (h : SurjectionRankOneIdempotent O A n ρ.toRingHom e₁) :
    (∀ (a : A) v x, tensM O n ρ.toRingHom (a • v) x = a • tensM O n ρ.toRingHom v x) ∧
    (∀ m : LatQ O n ρ.toRingHom, e₁ • m = m → ∃ x, m = tensM O n ρ.toRingHom (vOne ρ e₁ h) x) ∧
    (∀ (a : A) v, iLM O n ρ.toRingHom (a • v) = a • iLM O n ρ.toRingHom v) ∧
    (∀ (a : A) v, qVM O n ρ.toRingHom (a • v) = a • qVM O n ρ.toRingHom v) ∧
    (∀ v (x : FractionRing O), tensM O n ρ.toRingHom v (Submodule.Quotient.mk x) =
      qVM O n ρ.toRingHom (x • iLM O n ρ.toRingHom v)) ∧
    Function.Injective (iLM O n ρ.toRingHom) ∧ Function.Surjective (qVM O n ρ.toRingHom) ∧
    LinearMap.ker (qVM O n ρ.toRingHom) = LinearMap.range (iLM O n ρ.toRingHom) ∧
    (∀ v : LatM O (FractionRing O) n ρ.toRingHom, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range (iLM O n ρ.toRingHom)) ∧
    e₁ • vOne ρ e₁ h = vOne ρ e₁ h ∧ (∀ v : LatM O O n ρ.toRingHom, ∃ c : A, (c * e₁) • vOne ρ e₁ h = v) :=
  h.choose_spec

end Lat

def LeftId (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] (x : A) : Type :=
  ↥(Submodule.span A ({x} : Set A))

section LeftId
variable (O : Type) [CommRing O] {A : Type} [Ring A] [Algebra O A] (x : A)

instance : AddCommGroup (LeftId O x) := inferInstanceAs (AddCommGroup ↥(Submodule.span A ({x} : Set A)))
instance : Module A (LeftId O x) := inferInstanceAs (Module A ↥(Submodule.span A ({x} : Set A)))
instance : Module O (LeftId O x) := inferInstanceAs (Module O ↥(Submodule.span A ({x} : Set A)))

def lv (p : LeftId O x) : A := @Subtype.val A (· ∈ Submodule.span A ({x} : Set A)) p

def lmk (a : A) (h : a ∈ Submodule.span A ({x} : Set A)) : LeftId O x := ⟨a, h⟩

theorem lv_lmk (a : A) (h : a ∈ Submodule.span A ({x} : Set A)) : lv O x (lmk O x a h) = a := rfl
theorem lv_smul (c : O) (p : LeftId O x) : lv O x (c • p) = c • lv O x p := rfl
theorem lv_mem (p : LeftId O x) : lv O x p ∈ Submodule.span A ({x} : Set A) := p.2

instance : SMulCommClass A O (LeftId O x) :=
  ⟨fun a c p => Subtype.ext (by
    show a * (c • lv O x p) = c • (a * lv O x p)
    exact mul_smul_comm c a _)⟩

def incl : LeftId O x →ₗ[A] A := (Submodule.span A ({x} : Set A)).subtype

theorem incl_apply (p : LeftId O x) : incl O x p = lv O x p := rfl

theorem incl_mul (p : LeftId O x) : ∃ c : A, incl O x p = c * x := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (lv_mem O x p)
  exact ⟨c, by rw [incl_apply, ← hc, smul_eq_mul]⟩

theorem incl_smul (a : A) (p : LeftId O x) : incl O x (a • p) = a * incl O x p := rfl

end LeftId

section Pe
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type} [Ring A] [Algebra O A]
  {n : Type} [Fintype n] [DecidableEq n]

def eveM (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (v₁ : LatM O O n ρ.toRingHom) :
    LeftId O e₁ →ₗ[O] LatM O O n ρ.toRingHom where
  toFun p := incl O e₁ p • v₁
  map_add' p q := by rw [map_add (f := _), add_smul]
  map_smul' c p := by
    rw [RingHom.id_apply, incl_apply, incl_apply, lv_smul]
    funext i
    show ∑ j, ρ (c • lv O e₁ p) i j * (v₁ j : O) = c * ∑ j, ρ (lv O e₁ p) i j * (v₁ j : O)
    rw [map_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]

theorem eveM_apply (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (v₁ : LatM O O n ρ.toRingHom) (p : LeftId O e₁) :
    eveM ρ e₁ v₁ p = incl O e₁ p • v₁ := rfl

theorem eveM_onto (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (h : SurjectionRankOneIdempotent O A n ρ.toRingHom e₁) :
    Function.Surjective (eveM ρ e₁ (vOne ρ e₁ h)) := by
  intro v
  obtain ⟨c, hc⟩ := (vOne_spec ρ e₁ h).2.2.2.2.2.2.2.2.2.2 v
  refine ⟨lmk O e₁ (c * e₁) (Submodule.mem_span_singleton.2 ⟨c, rfl⟩), ?_⟩
  rw [eveM_apply, incl_apply, lv_lmk]
  exact hc

end Pe

section PE
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type} [Ring A] [Algebra O A]
  {m : Type} [Fintype m] [DecidableEq m]

theorem trace_mem (ρ₁ : A →ₐ[O] Matrix m m O) (E : A) (δO : O) (hE : ρ₁ E = δO • (1 : Matrix m m O))
    (p : LeftId O E) : (ρ₁ (incl O E p)).trace ∈ Ideal.span ({δO} : Set O) := by
  obtain ⟨c, hc⟩ := incl_mul O E p
  rw [hc, map_mul, hE, Matrix.mul_smul, mul_one, Matrix.trace_smul, smul_eq_mul]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self δO)

def evEM (ρ₁ : A →ₐ[O] Matrix m m O) (E : A) (δO : O) (hE : ρ₁ E = δO • (1 : Matrix m m O)) :
    LeftId O E →ₗ[O] ↥(Ideal.span ({δO} : Set O)) where
  toFun p := ⟨(ρ₁ (incl O E p)).trace, trace_mem ρ₁ E δO hE p⟩
  map_add' p q := Subtype.ext (by
    show (ρ₁ (incl O E (p + q))).trace = (ρ₁ (incl O E p)).trace + (ρ₁ (incl O E q)).trace
    rw [map_add (f := _), map_add (f := _), Matrix.trace_add])
  map_smul' c p := Subtype.ext (by
    show (ρ₁ (lv O E (c • p))).trace = c * (ρ₁ (lv O E p)).trace
    rw [lv_smul, map_smul, Matrix.trace_smul, smul_eq_mul])

theorem evEM_val (ρ₁ : A →ₐ[O] Matrix m m O) (E : A) (δO : O) (hE : ρ₁ E = δO • (1 : Matrix m m O))
    (p : LeftId O E) : ((evEM ρ₁ E δO hE p : ↥(Ideal.span ({δO} : Set O))) : O) = (ρ₁ (incl O E p)).trace := rfl

theorem evEM_act (ρ₁ : A →ₐ[O] Matrix m m O) (h1 : Fintype.card m = 1) (E : A) (δO : O)
    (hE : ρ₁ E = δO • (1 : Matrix m m O)) (p : LeftId O E) (v : LatQ O m ρ₁.toRingHom) :
    incl O E p • v = ((evEM ρ₁ E δO hE p : ↥(Ideal.span ({δO} : Set O))) : O) • v := by
  rw [evEM_val]; exact act_trace ρ₁ h1 _ v

theorem evEM_onto (ρ₁ : A →ₐ[O] Matrix m m O) (h1 : Fintype.card m = 1) (E : A) (δO : O)
    (hE : ρ₁ E = δO • (1 : Matrix m m O)) : Function.Surjective (evEM ρ₁ E δO hE) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  refine ⟨lmk O E (y • E) (Submodule.smul_of_tower_mem _ y (Submodule.mem_span_singleton_self E)), Subtype.ext ?_⟩
  rw [evEM_val, incl_apply, lv_lmk]
  show (ρ₁ (y • E)).trace = y * δO
  rw [map_smul, hE, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one, h1, smul_eq_mul, smul_eq_mul]
  simp

theorem evEM_inv {T' G : Type} [CommRing T'] [Algebra T' A] [Group G] (r : G →* A) (χ : G →* T'ˣ)
    (ρ₁ : A →ₐ[O] Matrix m m O) (E : A) (δO : O) (hE : ρ₁ E = δO • (1 : Matrix m m O))
    (hu : ∀ g (v : LatQ O m ρ₁.toRingHom), uElt r χ g • v = v) (g : G) (p : LeftId O E) :
    evEM ρ₁ E δO hE (uElt r χ g • p) = evEM ρ₁ E δO hE p := by
  apply Subtype.ext
  rw [evEM_val, evEM_val, incl_smul, map_mul,
    mat_eq_of_act ρ₁ (uElt r χ g) 1 (fun v => by rw [one_smul]; exact hu g v), one_smul, one_mul]

end PE

section T12
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {A : Type} [Ring A] [Algebra O A]
  {n : Type} [Fintype n] [DecidableEq n] {T' G : Type} [CommRing T'] [Algebra T' A] [Group G]

def rhoTwo (ρ : A →ₐ[O] Matrix n n O) (r : G →* A) (χ : G →* T'ˣ) (ε : G →* Oˣ) : Representation O G (n → O) where
  toFun g := Matrix.mulVecLin (((ε g : Oˣ) : O) • (ρ (uElt r χ g⁻¹)).transpose)
  map_one' := by
    rw [inv_one, uElt_one, map_one ρ, Matrix.transpose_one, map_one ε, Units.val_one, one_smul]
    exact Matrix.mulVecLin_one
  map_mul' g h := by
    rw [Module.End.mul_eq_comp, ← Matrix.mulVecLin_mul, mul_inv_rev, uElt_mul, map_mul ρ, Matrix.transpose_mul,
      map_mul ε, Units.val_mul, smul_mul_smul_comm]

theorem rhoTwo_apply (ρ : A →ₐ[O] Matrix n n O) (r : G →* A) (χ : G →* T'ˣ) (ε : G →* Oˣ) (g : G) (t : n → O) :
    rhoTwo ρ r χ ε g t = (((ε g : Oˣ) : O) • (ρ (uElt r χ g⁻¹)).transpose).mulVec t := rfl

def gamM (ρ : A →ₐ[O] Matrix n n O) : (n → O) →ₗ[O] LatQ O n ρ.toRingHom →ₗ[O] KO O :=
  LinearMap.mk₂ O (fun (t : n → O) (m : LatQ O n ρ.toRingHom) => ∑ a, t a • (m a : KO O))
    (fun t t' m => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib])
    (fun c t m => by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum])
    (fun t m m' => by
      show ∑ a, t a • ((m a : KO O) + m' a) = _
      simp only [smul_add, Finset.sum_add_distrib])
    (fun c t m => by
      show ∑ a, t a • (c • (m a : KO O)) = c • ∑ a, t a • (m a : KO O)
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun a _ => smul_comm _ _ _)

def lamM (ρ : A →ₐ[O] Matrix n n O) (w : n → O) : LatQ O n ρ.toRingHom →ₗ[O] KO O := gamM ρ w

def piM (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (w : n → O) : FirstSummandSubmodule O e₁ →ₗ[O] (n → O) where
  toFun b := Matrix.vecMul w (ρ (b : A))
  map_add' b b' := by rw [Submodule.coe_add, map_add (f := _), Matrix.vecMul_add]
  map_smul' c b := by rw [Submodule.coe_smul, map_smul, Matrix.vecMul_smul, RingHom.id_apply]

theorem piM_apply (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (w : n → O) (b : FirstSummandSubmodule O e₁) :
    piM ρ e₁ w b = Matrix.vecMul w (ρ (b : A)) := rfl

theorem gam_pi (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (w : n → O) (b : FirstSummandSubmodule O e₁) (m : LatQ O n ρ.toRingHom) :
    gamM ρ (piM ρ e₁ w b) m = lamM ρ w ((FirstSummandSubmodule O e₁).subtype b • m) := by
  show ∑ a, (Matrix.vecMul w (ρ (b : A))) a • (m a : KO O) = ∑ i, w i • (((b : A) • m) i : KO O)
  simp only [latQ_act, Matrix.vecMul, dotProduct, Finset.sum_smul, Finset.smul_sum, mul_smul]
  exact Finset.sum_comm

theorem pi_equiv (ρ : A →ₐ[O] Matrix n n O) (r : G →* A) (χ : G →* T'ˣ) (e₁ : A) (ε : G →* Oˣ) (w : n → O) :
    IsEquivMap (firstSummandRep O r χ e₁ ε) (rhoTwo ρ r χ ε) (piM ρ e₁ w) := by
  intro g b
  have hu : ((χ g : T'ˣ) : T') • ((b : A) * r g⁻¹) = (b : A) * uElt r χ g⁻¹ := by
    rw [uElt, map_inv χ, inv_inv, mul_smul_comm]
  rw [rhoTwo_apply, piM_apply, piM_apply]
  show Matrix.vecMul w (ρ (((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((b : A) * r g⁻¹)))) = _
  rw [hu, map_smul, map_mul, Matrix.vecMul_smul]
  funext a
  simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, Matrix.smul_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem pi_onto (ρ : A →ₐ[O] Matrix n n O) (hs : Function.Surjective ρ) (e₁ : A) (v w : n → O)
    (hvw : ∀ i j, ρ e₁ i j = v i * w j) (hwv : ∑ j, w j * v j = 1) : Function.Surjective (piM ρ e₁ w) := by
  intro t
  obtain ⟨b', hb'⟩ := hs (Matrix.vecMulVec v t)
  refine ⟨⟨e₁ * b', b', rfl⟩, ?_⟩
  rw [piM_apply]
  show Matrix.vecMul w (ρ (e₁ * b')) = t
  rw [map_mul, ← Matrix.vecMul_vecMul, hb']
  have h1 : Matrix.vecMul w (ρ e₁) = w := by
    funext j
    simp only [Matrix.vecMul, dotProduct, hvw, ← mul_assoc]
    rw [← Finset.sum_mul, hwv, one_mul]
  rw [h1]
  funext j
  simp only [Matrix.vecMul, dotProduct, Matrix.vecMulVec_apply, ← mul_assoc]
  rw [← Finset.sum_mul, hwv, one_mul]

theorem inc_equiv (r : G →* A) (χ : G →* T'ˣ) (e₁ : A) (ε : G →* Oˣ) (g : G) (b : FirstSummandSubmodule O e₁) :
    (FirstSummandSubmodule O e₁).subtype (firstSummandRep O r χ e₁ ε g b) =
      ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • ((FirstSummandSubmodule O e₁).subtype b * r g⁻¹)) := rfl

end T12

omit hT2Core in
instance submoduleContinuousConstSMul {O M : Type} [Semiring O] [AddCommMonoid M] [Module O M] [TopologicalSpace M]
    [ContinuousConstSMul O M] (S : Submodule O M) : ContinuousConstSMul O ↥S :=
  ⟨fun c => (continuous_subtype_val.const_smul c).subtype_mk _⟩

section Top
variable {O : Type} [CommRing O] {A : Type} [Ring A] [Algebra O A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [ContinuousConstSMul O A] (e₁ : A)

theorem inc_cont : Continuous (FirstSummandSubmodule O e₁).subtype := continuous_subtype_val

end Top

section Dd
open Formalism.RepresentationBoundsCohomology.ringDataObjects

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type}
  [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)}

def cOne (ht : 1 ≤ t) : Fin (t + 1) := ⟨1, by omega⟩

theorem cOne_ne (ht : 1 ≤ t) : cOne ht ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  simp [cOne] at this

variable (Dd : RingData O X d G t bl) (T : Subalgebra O (X → O)) (ht : 1 ≤ t)
  [∀ k, SMulCommClass Dd.R' O (blockRestrictedRepresentationType bl Dd.ρk k)]

theorem top_facts (hT : Dd.Top T ht) :
    Dd.e₁ * Dd.e₁ = Dd.e₁ ∧ (∀ k, Function.Surjective (Dd.ρk k)) ∧ Fintype.card {a // bl a = cOne ht} = 1 ∧
    Dd.ρk (cOne ht) Dd.E = Dd.δO • (1 : Matrix {a // bl a = cOne ht} {a // bl a = cOne ht} O) ∧
    (∀ g (m : blockRestrictedRepresentationType bl Dd.ρk (cOne ht)), uElt Dd.r Dd.χ g • m = m) := by
  obtain ⟨-, -, -, -, hee, -, -, -, hsurj, -, hcard1, -, -, -, -, -, -, hOne⟩ := hT
  obtain ⟨p1, -, p3, -⟩ := hOne
  exact ⟨hee, hsurj, hcard1 _ (cOne_ne ht), mat_eq_of_act _ _ _ p3, p1⟩

theorem rank_reduction_idempotent_one {T : Subalgebra O (X → O)} {r₀ : G →* (X → Matrix d d O)} {π : X} {χ₁ ε : G →* Oˣ} {g₀ : G}
    {eB e₁ s : X → Matrix d d O} (hI : IdemHyp O T r₀ π bl eB e₁) (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s Dd) :
    ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1 :=
  idempotent_rank_one_at_point hI hD

theorem rho_hypotheses_of_ring_data (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    SurjectionRankOneIdempotent O Dd.R' {a // bl a = 0} (Dd.ρk 0).toRingHom Dd.e₁ :=
  surjection_of_rank_one_idempotent O Dd.R' _ (Dd.ρk 0).toRingHom Dd.e₁ ((top_facts Dd T ht hT).2.1 0) (top_facts Dd T ht hT).1 hrk

theorem rankOne_Dd (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    ∃ v w : {a // bl a = 0} → O, (∀ i j, Dd.ρk 0 Dd.e₁ i j = v i * w j) ∧ ∑ j, w j * v j = 1 :=
  rank_one_factor O _ (Dd.ρk 0 Dd.e₁) (by rw [← map_mul, (top_facts Dd T ht hT).1]) hrk

def v1Dd (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    LatM O O {a // bl a = 0} (Dd.ρk 0).toRingHom :=
  vOne (Dd.ρk 0) Dd.e₁ (rho_hypotheses_of_ring_data Dd T ht hT hrk)

def wDd (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    {a // bl a = 0} → O :=
  (rankOne_Dd Dd T ht hT hrk).choose_spec.choose

def eveDd (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    LeftId O Dd.e₁ →ₗ[O] LatM O O {a // bl a = 0} (Dd.ρk 0).toRingHom :=
  eveM (Dd.ρk 0) Dd.e₁ (v1Dd Dd T ht hT hrk)

def evEDd (hT : Dd.Top T ht) : LeftId O Dd.E →ₗ[O] ↥(Ideal.span ({Dd.δO} : Set O)) :=
  evEM (Dd.ρk (cOne ht)) Dd.E Dd.δO (top_facts Dd T ht hT).2.2.2.1

def piDd (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    FirstSummandSubmodule O Dd.e₁ →ₗ[O] ({a // bl a = 0} → O) :=
  piM (Dd.ρk 0) Dd.e₁ (wDd Dd T ht hT hrk)

def lamDd (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1) :
    blockRestrictedRepresentationType bl Dd.ρk 0 →ₗ[O] KO O :=
  lamM (Dd.ρk 0) (wDd Dd T ht hT hrk)

theorem tensor_lattice_facts (hT : Dd.Top T ht) (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap O (FractionRing O))).rank = 1)
    (ε : G →* Oˣ) :
    let ρ0 := (Dd.ρk 0).toRingHom
    let v₁ := v1Dd Dd T ht hT hrk
    let c1 : Fin (t + 1) := ⟨1, by omega⟩

    ((∀ (a : Dd.R') v x, tensM O _ ρ0 (a • v) x = a • tensM O _ ρ0 v x) ∧
      (∀ m : blockRestrictedRepresentationType bl Dd.ρk 0, Dd.e₁ • m = m → ∃ x, m = tensM O _ ρ0 v₁ x) ∧
      (∀ (a : Dd.R') v, iLM O _ ρ0 (a • v) = a • iLM O _ ρ0 v) ∧
      (∀ (a : Dd.R') v, qVM O _ ρ0 (a • v) = a • qVM O _ ρ0 v) ∧
      (∀ v (x : FractionRing O), tensM O _ ρ0 v (Submodule.Quotient.mk x) = qVM O _ ρ0 (x • iLM O _ ρ0 v)) ∧
      Function.Injective (iLM O _ ρ0) ∧ Function.Surjective (qVM O _ ρ0) ∧
      LinearMap.ker (qVM O _ ρ0) = LinearMap.range (iLM O _ ρ0) ∧
      (∀ v : LatM O (FractionRing O) {a // bl a = 0} ρ0, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range (iLM O _ ρ0)) ∧
      Dd.e₁ • v₁ = v₁) ∧

    (∀ a, eveDd Dd T ht hT hrk a = incl O Dd.e₁ a • v₁) ∧ Function.Surjective (eveDd Dd T ht hT hrk) ∧

    (∀ g a, evEDd Dd T ht hT (uElt Dd.r Dd.χ g • a) = evEDd Dd T ht hT a) ∧
    Function.Surjective (evEDd Dd T ht hT) ∧ (∀ a, ∃ c : Dd.R', incl O Dd.E a = c * Dd.E) ∧
    (∀ a (m : blockRestrictedRepresentationType bl Dd.ρk c1),
      incl O Dd.E a • m = ((evEDd Dd T ht hT a : ↥(Ideal.span ({Dd.δO} : Set O))) : O) • m) ∧

    (∀ g b, (FirstSummandSubmodule O Dd.e₁).subtype (firstSummandRep O Dd.r Dd.χ Dd.e₁ ε g b) =
      ((ε g : Oˣ) : O) • (((Dd.χ g : Dd.T'ˣ) : Dd.T') • ((FirstSummandSubmodule O Dd.e₁).subtype b * Dd.r g⁻¹))) ∧
    IsEquivMap (firstSummandRep O Dd.r Dd.χ Dd.e₁ ε) (rhoTwo (Dd.ρk 0) Dd.r Dd.χ ε) (piDd Dd T ht hT hrk) ∧
    (∀ b m, gamM (Dd.ρk 0) (piDd Dd T ht hT hrk b) m = lamDd Dd T ht hT hrk ((FirstSummandSubmodule O Dd.e₁).subtype b • m)) ∧
    Function.Surjective (piDd Dd T ht hT hrk) := by
  intro ρ0 v₁ c1
  have hs := vOne_spec (Dd.ρk 0) Dd.e₁ (rho_hypotheses_of_ring_data Dd T ht hT hrk)
  have hf := top_facts Dd T ht hT
  have hvw := (rankOne_Dd Dd T ht hT hrk).choose_spec.choose_spec
  refine ⟨⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1, hs.2.2.2.2.2.2.1,
      hs.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.2.1⟩,
    fun a => rfl, eveM_onto _ _ _,
    evEM_inv Dd.r Dd.χ _ _ _ _ hf.2.2.2.2, evEM_onto _ hf.2.2.1 _ _ _, incl_mul O Dd.E,
    evEM_act _ hf.2.2.1 _ _ _,
    inc_equiv Dd.r Dd.χ Dd.e₁ ε, pi_equiv _ _ _ _ _ _, gam_pi _ _ _,
    pi_onto _ (hf.2.1 0) _ _ _ hvw.1 hvw.2⟩

end Dd

section Checks
variable {ℓ : ℕ} [Fact ℓ.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[ℓ] O]
  {A : Type} [Ring A] [Algebra O A] [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A]
  {n : Type} [Fintype n] [DecidableEq n] (ρ : A →ₐ[O] Matrix n n O) (x e₁ : A)

end Checks

section Cont
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff IsFGTop)

variable {ℓ : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  {A : Type} [Ring A] [Algebra O A] [TopologicalSpace A] [IsTopologicalAddGroup A]

theorem lin_cont (hO : PadicCoeff ℓ O) (hA : IsFGTop O A) {N : Type} [AddCommGroup N] [Module O N] [TopologicalSpace N]
    [ContinuousAdd N] [ContinuousSMul O N] (g : A →ₗ[O] N) : Continuous g := by
  have := hO.ring; have := hO.compact; have := hA.t2; have := hA.csmul; have := hA.fg
  obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' O A
  have hfc : Continuous f := LinearMap.continuous_on_pi f
  have hq : Topology.IsQuotientMap f := hfc.isClosedMap.isQuotientMap hfc hf
  exact hq.continuous_iff.2 (LinearMap.continuous_on_pi (g ∘ₗ f))

variable {n : Type} [Fintype n] [DecidableEq n]

def piA (ρ : A →ₐ[O] Matrix n n O) (w : n → O) : A →ₗ[O] (n → O) where
  toFun b := Matrix.vecMul w (ρ b)
  map_add' b b' := by rw [map_add (f := _), Matrix.vecMul_add]
  map_smul' c b := by rw [map_smul, Matrix.vecMul_smul, RingHom.id_apply]

theorem piM_cont (hO : PadicCoeff ℓ O) (hA : IsFGTop O A) (ρ : A →ₐ[O] Matrix n n O) (e₁ : A) (w : n → O) :
    Continuous (piM ρ e₁ w) := by
  have := hO.ring
  exact (lin_cont hO hA (piA ρ w)).comp continuous_subtype_val

end Cont

end Formalism.MainNotions.N.K
end
end

section
open Classical

namespace Formalism.MainNotions.N.K.TBa

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N TensorProduct

section Crys

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem tens_subsingleton {V C : Type} [AddCommGroup V] [Module Qp V] [AddCommGroup C] [Module Qp C]
    [Subsingleton V] (z : V ⊗[Qp] C) : z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rfl
  | tmul v c => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
  | add x y hx hy => rw [hx, hy, add_zero]

section Fil

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
  (ρ : Representation LL G V)

theorem filV_anti (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  unfold FilV
  rintro _ ⟨z, rfl⟩
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul v f => exact ⟨v ⊗ₜ ⟨(f : BdR), PD.Fil_anti a f.2⟩, by simp⟩
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

theorem fildR_anti (τ : K →ₐ[Qp] LL) (a : ℤ) : FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a := inf_le_inf_left _ (filV_anti PD a)

theorem fildR_le (τ : K →ₐ[Qp] LL) (a : ℤ) : FildR PD ρ τ a ≤ DdR PD ρ := inf_le_left.trans inf_le_left

theorem fd_DdR [FiniteDimensional LL V] (h : IsDR PD ρ) : FiniteDimensional LL ↥(DdR PD ρ) := by
  haveI := PD.finK
  by_cases hV : Module.finrank LL V = 0
  · haveI : Subsingleton V := Module.finrank_zero_iff.mp hV
    haveI : Subsingleton (V ⊗[Qp] BdR) := ⟨fun x y => by rw [tens_subsingleton x, tens_subsingleton y]⟩
    infer_instance
  · apply Module.finite_of_finrank_pos
    rw [h]
    exact Nat.mul_pos Module.finrank_pos (Nat.pos_of_ne_zero hV)

theorem jump_of_mult (τ : K →ₐ[Qp] LL) (a : ℤ) (h : multV PD ρ τ a ≠ 0) : IsJumpV PD ρ τ a := by
  intro heq
  apply h
  unfold multV
  rw [heq, sub_self]

variable [FiniteDimensional LL ↥(DdR PD ρ)]

theorem fd_fildR (τ : K →ₐ[Qp] LL) (a : ℤ) : FiniteDimensional LL ↥(FildR PD ρ τ a) := Submodule.finiteDimensional_of_le (fildR_le PD ρ τ a)

theorem mult_nonneg (τ : K →ₐ[Qp] LL) (a : ℤ) : 0 ≤ multV PD ρ τ a := by
  haveI := fd_fildR PD ρ τ a
  have h1 := Submodule.finrank_mono (fildR_anti PD ρ τ a)
  unfold multV
  omega

theorem mult_pos (τ : K →ₐ[Qp] LL) (a : ℤ) (h : IsJumpV PD ρ τ a) : 0 < multV PD ρ τ a := by
  haveI := fd_fildR PD ρ τ a
  have h1 : FildR PD ρ τ (a + 1) < FildR PD ρ τ a := lt_of_le_of_ne (fildR_anti PD ρ τ a) h
  have h2 := Submodule.finrank_lt_finrank_of_lt h1
  unfold multV
  omega

end Fil

section Sums

variable {ι : Type} {k : ℕ} (Ms : ι → G →* Matrix (Fin k) (Fin k) LL)

def sumRep {m : ℕ} (xs : Fin m → ι) : Representation LL G (Fin m → Fin k → LL) where
  toFun g :=
    { toFun := fun s a => (Ms (xs a) g).mulVec (s a)
      map_add' := fun s t => funext fun a => Matrix.mulVec_add _ _ _
      map_smul' := fun c s => funext fun a => by simp [Matrix.mulVec_smul] }
  map_one' := LinearMap.ext fun s => funext fun a => by simp
  map_mul' g h := LinearMap.ext fun s => funext fun a => by simp [Matrix.mulVec_mulVec]

variable (hMc : ∀ x, Continuous (Ms x))
include hMc

theorem cont_mulVec (x : ι) (v : Fin k → LL) : Continuous fun g => (Ms x g).mulVec v := by
  exact (hMc x).matrix_mulVec continuous_const

def sumG {m : ℕ} (xs : Fin m → ι) : GRep G Qp LL O where
  V := Fin m → Fin k → LL
  ρ := sumRep Ms xs
  cont s := continuous_pi fun a => cont_mulVec Ms hMc (xs a) (s a)

def matG (x : ι) : GRep G Qp LL O where
  V := Fin k → LL
  ρ := matRep (Ms x)
  cont v := cont_mulVec Ms hMc x v

end Sums

section Quot

def quotRep {V : Type} [AddCommGroup V] [Module LL V] (ρ : Representation LL G V) (U : Submodule LL V)
    (hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U) : Representation LL G (V ⧸ U) where
  toFun g := U.mapQ U (ρ g) (fun u hu => hU g u hu)
  map_one' := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H v => simp
  map_mul' g h := by
    refine LinearMap.ext fun x => ?_
    induction x using Submodule.Quotient.induction_on with
    | H v => simp

def QV (A : GRep G Qp LL O) (U : Submodule LL A.V) : Type := A.V ⧸ U

variable (A : GRep G Qp LL O) (U : Submodule LL A.V)

instance : AddCommGroup (QV A U) := inferInstanceAs (AddCommGroup (A.V ⧸ U))
instance : Module LL (QV A U) := inferInstanceAs (Module LL (A.V ⧸ U))
instance : Module Qp (QV A U) := inferInstanceAs (Module Qp (A.V ⧸ U))
instance instQVtowQp : IsScalarTower Qp LL (QV A U) := ⟨fun a b x => by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    change (a • b) • (Submodule.Quotient.mk v : A.V ⧸ U) = a • (b • (Submodule.Quotient.mk v : A.V ⧸ U))
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, smul_assoc]⟩
instance : Module O (QV A U) := inferInstanceAs (Module O (A.V ⧸ U))
instance instQVtowO : IsScalarTower O LL (QV A U) := ⟨fun a b x => by
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    change (a • b) • (Submodule.Quotient.mk v : A.V ⧸ U) = a • (b • (Submodule.Quotient.mk v : A.V ⧸ U))
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, smul_assoc]⟩
instance : FiniteDimensional LL (QV A U) := inferInstanceAs (FiniteDimensional LL (A.V ⧸ U))
instance : TopologicalSpace (QV A U) := moduleTopology LL (QV A U)
instance : IsModuleTopology LL (QV A U) := ⟨rfl⟩
instance : ContinuousAdd (QV A U) := IsModuleTopology.toContinuousAdd LL (QV A U)
instance : ContinuousSMul LL (QV A U) := IsModuleTopology.toContinuousSMul LL (QV A U)

def qmk : A.V →ₗ[LL] QV A U := U.mkQ

def quotG (hU : ∀ g, ∀ u ∈ U, A.ρ g u ∈ U) : GRep G Qp LL O where
  V := QV A U
  towQp := instQVtowQp A U
  towO := instQVtowO A U
  ρ := quotRep A.ρ U hU
  cont x := by
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      have hq : Continuous (qmk A U) := IsModuleTopology.continuous_of_linearMap (qmk A U)
      exact hq.comp (A.cont v)

end Quot

section Cons

variable {W : Type} [AddCommGroup W] [Module LL W]

def consZ (m : ℕ) : (Fin m → W) →ₗ[LL] (Fin (m + 1) → W) where
  toFun s := Fin.cons 0 s
  map_add' s t := funext fun a => Fin.cases (by simp) (fun j => by simp) a
  map_smul' c s := funext fun a => Fin.cases (by simp) (fun j => by simp) a

def consV (m : ℕ) : W →ₗ[LL] (Fin (m + 1) → W) where
  toFun v := Fin.cons v 0
  map_add' s t := funext fun a => Fin.cases (by simp) (fun j => by simp) a
  map_smul' c s := funext fun a => Fin.cases (by simp) (fun j => by simp) a

theorem consZ_apply (m : ℕ) (s : Fin m → W) : consZ (LL := LL) m s = Fin.cons 0 s := rfl

theorem consZ_inj (m : ℕ) : Function.Injective (consZ (LL := LL) (W := W) m) := fun s t h => funext fun a => by
  have h1 := congrFun h a.succ
  simpa [consZ_apply] using h1

theorem proj_consV (m : ℕ) (v : W) : LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => W) 0 (consV (LL := LL) m v) = v := by
  rfl

theorem range_consZ (m : ℕ) : LinearMap.range (consZ (LL := LL) (W := W) m) =
    LinearMap.ker (LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => W) 0) := by
  ext x
  simp only [LinearMap.mem_range, LinearMap.mem_ker, LinearMap.proj_apply, consZ_apply]
  constructor
  · rintro ⟨s, rfl⟩
    rfl
  · intro hx
    refine ⟨Fin.tail x, ?_⟩
    rw [← hx, Fin.cons_self_tail]

end Cons

section Main

variable {ι : Type} {k : ℕ} (Ms : ι → G →* Matrix (Fin k) (Fin k) LL)
  (hF : TruncatedSeriesCountingIdentities.FontaineAt PD LL O)

include hF in
theorem fd_of_crys (A : GRep G Qp LL O) (h : IsCrys PD A.ρ) : FiniteDimensional LL ↥(DdR PD A.ρ) := by
  haveI := A.fd
  exact fd_DdR PD A.ρ (hF.2.2.2 A h)

variable (hMc : ∀ x, Continuous (Ms x)) (hMs : ∀ x, IsCrys PD (matRep (Ms x)))
include hF hMc hMs

theorem crys_sum : ∀ (m : ℕ) (xs : Fin m → ι), IsCrys PD (sumRep Ms xs) ∧
    ∀ τ a, IsJumpV PD (sumRep Ms xs) τ a → ∃ x, IsJumpV PD (matRep (Ms x)) τ a := by
  intro m
  induction m with
  | zero =>
    intro xs
    haveI hsub1 : Subsingleton ((Fin 0 → Fin k → LL) ⊗[Qp] BdR) :=
      ⟨fun x y => by rw [tens_subsingleton x, tens_subsingleton y]⟩
    haveI hsub2 : Subsingleton ((Fin 0 → Fin k → LL) ⊗[Qp] B) :=
      ⟨fun x y => by rw [tens_subsingleton x, tens_subsingleton y]⟩
    refine ⟨?_, fun τ a hj => absurd (Subsingleton.elim _ _) hj⟩
    unfold IsCrys
    have h1 : Module.finrank LL (Fin 0 → Fin k → LL) = 0 := Module.finrank_zero_of_subsingleton
    have h2 : Module.finrank LL ↥(Dcris PD (sumRep Ms xs)) = 0 := Module.finrank_zero_of_subsingleton
    rw [h1, h2, mul_zero]
  | succ m ih =>
    intro xs
    obtain ⟨ht1, ht2⟩ := ih (fun a => xs a.succ)
    have eqι : ∀ (g : G) (x : Fin m → Fin k → LL), consZ (LL := LL) (W := Fin k → LL) m ((sumG (Qp := Qp) (O := O) Ms hMc (fun a : Fin m => xs a.succ)).ρ g x) =
        (sumG (Qp := Qp) (O := O) Ms hMc xs).ρ g (consZ (LL := LL) (W := Fin k → LL) m x) := by
      intro g x
      funext a
      refine Fin.cases ?_ (fun j => ?_) a
      · show (Fin.cons 0 (fun a : Fin m => (Ms (xs a.succ) g).mulVec (x a)) : Fin (m + 1) → Fin k → LL) 0 =
            (Ms (xs 0) g).mulVec ((Fin.cons 0 x : Fin (m + 1) → Fin k → LL) 0)
        rw [Fin.cons_zero, Fin.cons_zero, Matrix.mulVec_zero]
      · show (Fin.cons 0 (fun a : Fin m => (Ms (xs a.succ) g).mulVec (x a)) : Fin (m + 1) → Fin k → LL) j.succ =
            (Ms (xs j.succ) g).mulVec ((Fin.cons 0 x : Fin (m + 1) → Fin k → LL) j.succ)
        rw [Fin.cons_succ, Fin.cons_succ]
    have eqπ : ∀ (g : G) (x : Fin (m + 1) → Fin k → LL), LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0
        ((sumG (Qp := Qp) (O := O) Ms hMc xs).ρ g x) = (matG (Qp := Qp) (O := O) Ms hMc (xs 0)).ρ g (LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0 x) := fun g x => rfl
    have hsurj : Function.Surjective (LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0) :=
      fun v => ⟨consV (LL := LL) m v, proj_consV m v⟩
    have hsplit : ∃ s : (Fin k → LL) →ₗ[LL] (Fin (m + 1) → Fin k → LL),
        (∀ (g : G) (x : Fin k → LL), s ((matG (Qp := Qp) (O := O) Ms hMc (xs 0)).ρ g x) = (sumG (Qp := Qp) (O := O) Ms hMc xs).ρ g (s x)) ∧
        ∀ x, LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0 (s x) = x := by
      refine ⟨consV (LL := LL) m, fun g x => ?_, proj_consV m⟩
      funext a
      refine Fin.cases ?_ (fun j => ?_) a
      · show (Fin.cons ((Ms (xs 0) g).mulVec x) 0 : Fin (m + 1) → Fin k → LL) 0 =
            (Ms (xs 0) g).mulVec ((Fin.cons x 0 : Fin (m + 1) → Fin k → LL) 0)
        rw [Fin.cons_zero, Fin.cons_zero]
      · show (Fin.cons ((Ms (xs 0) g).mulVec x) 0 : Fin (m + 1) → Fin k → LL) j.succ =
            (Ms (xs j.succ) g).mulVec ((Fin.cons x 0 : Fin (m + 1) → Fin k → LL) j.succ)
        rw [Fin.cons_succ, Fin.cons_succ, Pi.zero_apply, Matrix.mulVec_zero]
    obtain ⟨hF1, hF2⟩ := hF.1 (sumG (Qp := Qp) (O := O) Ms hMc (fun a : Fin m => xs a.succ)) (sumG (Qp := Qp) (O := O) Ms hMc xs) (matG (Qp := Qp) (O := O) Ms hMc (xs 0))
      (consZ (LL := LL) m) (LinearMap.proj (R := LL) (φ := fun _ : Fin (m + 1) => Fin k → LL) 0) eqι eqπ (consZ_inj m) hsurj (range_consZ m)
    have hcrys : IsCrys PD (sumRep Ms xs) := hF2 hsplit ht1 (hMs (xs 0))
    refine ⟨hcrys, fun τ a hj => ?_⟩
    obtain ⟨_, _, hmult⟩ := hF1 hcrys
    haveI : FiniteDimensional LL ↥(DdR PD (sumRep Ms xs)) := fd_of_crys PD hF (sumG (Qp := Qp) (O := O) Ms hMc xs) hcrys
    have hpos := mult_pos PD (sumRep Ms xs) τ a hj
    have hm : multV PD (sumRep Ms xs) τ a =
        multV PD (sumRep Ms (fun a : Fin m => xs a.succ)) τ a + multV PD (matRep (Ms (xs 0))) τ a := hmult τ a
    rw [hm] at hpos
    by_cases h0 : multV PD (sumRep Ms (fun a : Fin m => xs a.succ)) τ a = 0
    · rw [h0, zero_add] at hpos
      exact ⟨xs 0, jump_of_mult PD _ τ a hpos.ne'⟩
    · exact ht2 τ a (jump_of_mult PD _ τ a h0)

theorem crys_of_inj (A : GRep G Qp LL O) {m : ℕ} (xs : Fin m → ι) (φ : A.V →ₗ[LL] (Fin m → Fin k → LL))
    (hφ : Function.Injective φ) (heq : ∀ g v, φ (A.ρ g v) = fun a => (Ms (xs a) g).mulVec (φ v a)) :
    IsCrys PD A.ρ ∧ ∀ τ a, IsJumpV PD A.ρ τ a → ∃ x, IsJumpV PD (matRep (Ms x)) τ a := by
  have hU : ∀ g, ∀ u ∈ LinearMap.range φ, (sumG (Qp := Qp) (O := O) Ms hMc xs).ρ g u ∈ LinearMap.range φ := by
    rintro g _ ⟨v, rfl⟩
    exact ⟨A.ρ g v, by rw [heq]; rfl⟩
  have eqι : ∀ (g : G) (x : A.V), φ (A.ρ g x) = (sumG (Qp := Qp) (O := O) Ms hMc xs).ρ g (φ x) := fun g x => by rw [heq]; rfl
  have eqπ : ∀ (g : G) (x : Fin m → Fin k → LL), qmk (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ) ((sumG (Qp := Qp) (O := O) Ms hMc xs).ρ g x) =
      (quotG (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ) hU).ρ g (qmk _ _ x) := fun g x => rfl
  have hsurj : Function.Surjective (qmk (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ)) := Submodule.mkQ_surjective _
  have hrk : LinearMap.range φ = LinearMap.ker (qmk (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ)) :=
    (Submodule.ker_mkQ _).symm
  obtain ⟨hF1, -⟩ := hF.1 A (sumG (Qp := Qp) (O := O) Ms hMc xs) (quotG (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ) hU) φ
    (qmk _ _) eqι eqπ hφ hsurj hrk
  obtain ⟨hs1, hs2⟩ := crys_sum PD Ms hF hMc hMs m xs
  obtain ⟨hA, hA2, hmult⟩ := hF1 hs1
  refine ⟨hA, fun τ a hj => ?_⟩
  haveI : FiniteDimensional LL ↥(DdR PD A.ρ) := fd_of_crys PD hF A hA
  haveI : FiniteDimensional LL ↥(DdR PD (quotG (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ) hU).ρ) :=
    fd_of_crys PD hF _ hA2
  have hp := mult_pos PD A.ρ τ a hj
  have hn := mult_nonneg PD (quotG (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ) hU).ρ τ a
  have hm : multV PD (sumRep Ms xs) τ a =
      multV PD A.ρ τ a + multV PD (quotG (sumG (Qp := Qp) (O := O) Ms hMc xs) (LinearMap.range φ) hU).ρ τ a := hmult τ a
  exact hs2 τ a (jump_of_mult PD (sumRep Ms xs) τ a (by rw [hm]; omega))

end Main

end Crys

end Formalism.MainNotions.N.K.TBa
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.MainNotions.N.K

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR (divBy unrH1 yY)
open Formalism.RepresentationBoundsCohomology.JL (LiftO ev_equiv ev_equiv_triv mapH1)
open Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology (kRow lcH1)
open Formalism.RepresentationBoundsCohomology.FIN
  (InChiFixReal InChiLoc InRhoFixReal2 IsCycG RealLat decs gRow)
open Formalism.RepresentationBoundsCohomology.LOC (LatData pairKO)
open NumberField IsDedekindDomain
open Formalism.ConjugateSelfDual (IsPlaceOver)
open ReciprocityTheory.Gal (H1 Ine)
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
def RealDisplayAllK (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R')
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (colIdx : ι → ℕ), Function.Injective colIdx →
    ∀ (Aw : ℕ → ValuationSubring Ω) (pl : ℕ → HeightOneSpectrum (𝓞 Ek))
      (Av : HeightOneSpectrum (𝓞 Ek) → ValuationSubring Ω) (j e' : ℕ → ℕ)
      (what₂ qs : Finset ℕ) (s H0 : ℕ∞) (Sha : ℕ → ℕ∞)
      (cB : ℕ) (cT : Fin (t + 1) → ℕ → ℕ),
    let cols : Finset ℕ := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card {a // bl a = 0}
    let h0 : ℕ → ℕ∞ := fun w =>
      Module.length O (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ ((decs Ek Aw) w)))
    let c1 : Fin (t + 1) := ⟨1, by omega⟩

    ∀ (L : Type) [AddCommGroup L] [Module R' L] [Module O L] [SMulCommClass R' O L]
      (tens : L →ₗ[O] KO O →ₗ[O] blockRestrictedRepresentationType bl ρk 0) (v₁ : L) (κ : ∀ l, Fin (j (colIdx l)) → (Ω ≃ₐ[Ek] Ω) → L)
      (V : Type) [AddCommGroup V] [Module R' V] [Module O V] [Module (FractionRing O) V]
      [IsScalarTower O (FractionRing O) V] [SMulCommClass R' (FractionRing O) V]
      (iL : L →ₗ[O] V) (qV : V →ₗ[O] blockRestrictedRepresentationType bl ρk 0)
      (Ff : ∀ l, Submodule O (H1z (resRep (uRep O (M := L) r χ) ((decs Ek Aw) (colIdx l)))))
      (κz : ∀ l, Fin (j (colIdx l)) → coZ1s (resRep (uRep O (M := L) r χ) ((decs Ek Aw) (colIdx l))))
      (F : ∀ c w, Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w))))
      (Vo VS : Type) (Io : Vo → Subgroup (Ω ≃ₐ[Ek] Ω)) (IS : VS → Subgroup (Ω ≃ₐ[Ek] Ω))
      (T₁ T₂ : Type) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
      [TopologicalSpace T₁] [IsTopologicalAddGroup T₁] [ContinuousConstSMul O T₁]
      (ρ₁ : Representation O (Ω ≃ₐ[Ek] Ω) T₁) (ρ₂ : Representation O (Ω ≃ₐ[Ek] Ω) T₂) (inc : T₁ →ₗ[O] R')
      (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O) (lam : blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O)

      (VT VT' : ℕ → Type)
      [∀ w, AddCommGroup (VT w)] [∀ w, Module O (VT w)] [∀ w, TopologicalSpace (VT w)]
      [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul O (VT w)]
      [∀ w, Module (FractionRing O) (VT w)] [∀ w, IsScalarTower O (FractionRing O) (VT w)]
      [∀ w, AddCommGroup (VT' w)] [∀ w, Module O (VT' w)] [∀ w, TopologicalSpace (VT' w)]
      [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul O (VT' w)]
      [∀ w, Module (FractionRing O) (VT' w)] [∀ w, IsScalarTower O (FractionRing O) (VT' w)]
      (Dat : ∀ w, LatData O ((decs Ek Aw) w) (VT w) (VT' w))
      (uD : ∀ w, blockRestrictedRepresentationType bl ρk 0 ≃ₗ[O] (VT w ⧸ (Dat w).T))
      (huD : ∀ w g m, uD w (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ) ((decs Ek Aw) w) g m) = (Dat w).ρA g (uD w m))
      (vD : ∀ w, T₂ ≃ₗ[O] (Dat w).T') (hpD : ∀ w, Continuous fun t => vD w (π t))
      (heD : ∀ w g t, vD w (π (resRep ρ₁ ((decs Ek Aw) w) g t)) = (Dat w).ρTl' g (vD w (π t)))

      (Fs : ∀ w, Submodule O (H1 (Dat w).ρTl')) (Hf₁ : ∀ w, Submodule O (H1 (resRep ρ₁ ((decs Ek Aw) w))))
      (I : ∀ w, Subgroup ((decs Ek Aw) w)) (γQ : ∀ w, (decs Ek Aw) w) (ζ : ℕ → Tc)
      (ζO : ℕ → O) (nQ : ∀ w, (decs Ek Aw) w → ℕ) (u : ι → (Ω ≃ₐ[Ek] Ω) → O)
      (s₀ : ℕ) (y : Oˣ)

      [∀ w, Module (FractionRing O) (H1 (Dat w).ρT)] [∀ w, IsScalarTower O (FractionRing O) (H1 (Dat w).ρT)]
      [∀ w, Module (FractionRing O) (H1 (Dat w).ρT')] [∀ w, IsScalarTower O (FractionRing O) (H1 (Dat w).ρT')]
      (HfW : ∀ w, Submodule (FractionRing O) (H1 (Dat w).ρT))
      (Hf₂ : ∀ w, Submodule (FractionRing O) (H1 (Dat w).ρT')),

    let gR : ∀ w, H1 (resRep ρ₁ ((decs Ek Aw) w)) →ₗ[O] H1 (Dat w).ρTl' :=
      fun w => gRow (Dat w) (resRep ρ₁ ((decs Ek Aw) w)) π (vD w) (hpD w) (heD w)
    let Im : ∀ w, Submodule O (H1 (Dat w).ρTl') := fun w => (Hf₁ w).map (gR w)

    ∀ (Pe : Type) [AddCommGroup Pe] [Module R' Pe] [Module O Pe] [SMulCommClass R' O Pe]
      (ince : Pe →ₗ[R'] R') (eve : Pe →ₗ[O] L) (heve : ∀ a, eve a = ince a • v₁)
      (PE : Type) [AddCommGroup PE] [Module R' PE] [Module O PE] [SMulCommClass R' O PE]
      (incE : PE →ₗ[R'] R') (evE : PE →ₗ[O] ↥(Ideal.span {δO}))
      (hevE : ∀ g a, evE (uElt r χ g • a) = evE a)
      (Hfe₁ : ∀ l : ι, Submodule O (H1z (resRep (uRep O (M := Pe) r χ) ((decs Ek Aw) (colIdx l)))))
      (HfE₁ : ∀ l : ι, Submodule O (H1z (resRep (uRep O (M := PE) r χ) ((decs Ek Aw) (colIdx l)))))
      (HfE₂ : ∀ l : ι,
        Submodule O (H1z (Representation.trivial O ((decs Ek Aw) (colIdx l)) ↥(Ideal.span {δO}))))
      (uz : ∀ l : ι, coZ1s (Representation.trivial O ((decs Ek Aw) (colIdx l)) ↥(Ideal.span {δO}))),

    Function.Injective (algebraMap ℤ_[ℓ] O) → PadicCoeff ℓ O → FracTop O → IsFGTop O R' → IsCycG ℓ ε →
    Continuous inc → (Continuous fun g : (Ω ≃ₐ[Ek] Ω) => uElt r χ g) →
    (∀ v, IsPlaceOver (Av v) v) → (ℓ ≠ 2 ∨ InfinitePlace.nrRealPlaces Ek = 0) →
    1 ≤ s₀ → (ℓ = 2 → 2 ≤ s₀) →
    ((ε gI : Oˣ) : O) - 1 = (ℓ : O) ^ s₀ * (y : O) →

    Function.Surjective eve → Function.Surjective evE → (∀ a, ∃ c : R', incE a = c * E) →
    (∀ a (m : blockRestrictedRepresentationType bl ρk c1), incE a • m = ((evE a : ↥(Ideal.span {δO})) : O) • m) →

    (∀ l (g : (decs Ek Aw) (colIdx l)),
      (((uz l : (decs Ek Aw) (colIdx l) → ↥(Ideal.span {δO})) g : ↥(Ideal.span {δO})) : O) = δO * u l g) →
    (∀ l, Submodule.mkQ _ (uz l) ∈ HfE₂ l) →

    (∀ l, LiftO ℓ (Hfe₁ l) (Ff l)
      (mapH1 _ _ eve (ev_equiv r χ ((decs Ek Aw) (colIdx l)) ince v₁ eve heve)) (e' (colIdx l))) →
    (∀ l, LiftO ℓ (HfE₁ l) (HfE₂ l)
      (mapH1 _ _ evE (ev_equiv_triv r χ ((decs Ek Aw) (colIdx l)) evE hevE)) (e' (colIdx l))) →

    (∀ x', p x' ∉ Z →
      (∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E), η ≠ 0 →
        ∃ g : (Ω ≃ₐ[Ek] Ω), ((((χ g)⁻¹ : Tcˣ) : Tc) • r g) • η ≠ η) ∧
      (∀ l, ∃ Lx : Submodule (FractionRing O) ((decs Ek Aw) (colIdx l) → EvalSp O d R' x'),
        LinearMap.range (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ ((decs Ek Aw) (colIdx l))) ≤ Lx ∧
        (∀ (f : Pe →ₗ[R'] EvalSp O d R' x')
          (z : coZ1s (resRep (uRep O (M := Pe) r χ) ((decs Ek Aw) (colIdx l)))), Submodule.mkQ _ z ∈ Hfe₁ l →
          (fun g : (decs Ek Aw) (colIdx l) => f ((z : (decs Ek Aw) (colIdx l) → Pe) g)) ∈ Lx) ∧
        (∀ (f : PE →ₗ[R'] EvalSp O d R' x')
          (z : coZ1s (resRep (uRep O (M := PE) r χ) ((decs Ek Aw) (colIdx l)))), Submodule.mkQ _ z ∈ HfE₁ l →
          (fun g : (decs Ek Aw) (colIdx l) => f ((z : (decs Ek Aw) (colIdx l) → PE) g)) ∈ Lx) ∧
        Module.rank (FractionRing O)
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ ((decs Ek Aw) (colIdx l)))).comap
              Lx.subtype) ≤
          (j (colIdx l) + Module.finrank (FractionRing O)
            (LinearMap.ker
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ ((decs Ek Aw) (colIdx l)))) : ℕ))) →

    InRhoFixReal2 (blockRestrictedRepresentationType bl ρk 0) r χ e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz (F 0)
      Io ε ρ₁ ρ₂ inc π γ lam →

    (∀ w ∈ what₂, (Aw w).valuation (ℓ : Ω) < 1 ∧ IsPlaceOver (Aw w) (pl w) ∧
      (∀ g : (decs Ek Aw) w, (Dat w).ε g = ε g) ∧ RealLat (Dat w) ∧
      (∀ (g : (decs Ek Aw) w) t, vD w (ρ₂ g t) = (Dat w).ρTl' g (vD w t)) ∧
      (∀ t m, γ t m = pairKO (Dat w).bT (Dat w).T (uD w m) (vD w t)) ∧
      (∀ a, a ∈ HfW w ↔ ∀ b ∈ Hf₂ w, cupFG (Dat w) a b = 0) ∧
      F 0 w = (((HfW w).restrictScalars O).map (Dat w).q).map (kRow (Dat w) _ (uD w) (huD w)) ∧
      Fs w = ((Hf₂ w).restrictScalars O).comap (Dat w).j' ∧ Im w ≤ Fs w) →

    (∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      (∀ w ∈ cols, Module.length O
        (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ ((decs Ek Aw) w))) ≤ H0) ∧
      (∀ w ∈ what₂, F c w = ⊥ ∧
        cT c w ≤ cB ∧
        (∀ ψ : Ymod r χ E →ₗ[O] blockRestrictedRepresentationType bl ρk c, (∀ g ∈ (decs Ek Aw) w, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
          ∀ z : coZ1s (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w)),
            (∀ g : (decs Ek Aw) w, (z : (decs Ek Aw) w → blockRestrictedRepresentationType bl ρk c) g = ψ (yY r χ E (g : (Ω ≃ₐ[Ek] Ω)))) →
            ((ℓ : O) ^ cT c w) • (Submodule.mkQ _ z : H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w))) ∈ F c w) ∧
        Module.length O (↥(lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w)) ⊓ divBy (F c w) ((ℓ : O) ^ cT c w)) ⧸ (F c w).comap (lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ((decs Ek Aw) w)) ⊓ divBy (F c w) ((ℓ : O) ^ cT c w)).subtype) ≤
          eO * (cT c w : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (pl w) : ℕ∞) + 1)) ∧
      InChiFixReal (blockRestrictedRepresentationType bl ρk c) r χ E colIdx (decs Ek Aw) what₂ qs
        (Sha ((c : ℕ) - 1)) (F c) Io IS I γQ ζ ζO nQ) →

    ((∀ l, ∀ g ∈ I (colIdx l), u l (g : (Ω ≃ₐ[Ek] Ω)) = 0) ∧ (∀ l, ∃ g ∈ (decs Ek Aw) (colIdx l), u l g = 1) ∧
     (∀ l, unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) (colIdx l))) (I (colIdx l)) ≤
       F c1 (colIdx l)) ∧
     (∀ w ∈ what₂, F c1 w = lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ⊓
         unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ((Ine (F := Ek) (Aw w)).subgroupOf ((decs Ek Aw) w)) ∧
       cT c1 w ≤ cB ∧
       (∀ ψ : Ymod r χ E →ₗ[O] blockRestrictedRepresentationType bl ρk c1, (∀ g ∈ (decs Ek Aw) w, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
         ∀ z : coZ1s (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)),
           (∀ g : (decs Ek Aw) w, (z : (decs Ek Aw) w → blockRestrictedRepresentationType bl ρk c1) g = ψ (yY r χ E (g : (Ω ≃ₐ[Ek] Ω)))) →
           ((ℓ : O) ^ cT c1 w) • (Submodule.mkQ _ z : H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w))) ∈ F c1 w) ∧
       Module.length O (↥(lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ⊓ divBy (F c1 w) ((ℓ : O) ^ cT c1 w)) ⧸ (F c1 w).comap (lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) ⊓ divBy (F c1 w) ((ℓ : O) ^ cT c1 w)).subtype) ≤
         eO * (cT c1 w : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (pl w) : ℕ∞) + 1)) ∧
     InChiLoc (blockRestrictedRepresentationType bl ρk c1) r χ E (decs Ek Aw) qs (F c1) Io IS I γQ ζ ζO nQ ∧

     (∀ v, (∃ a, Ine (F := Ek) (Av v) ≤ Io a) ∨ (∃ a, Ine (F := Ek) (Av v) ≤ IS a) ∨
        ∃ w ∈ what₂ ∪ qs ∪ univ.image colIdx, ∃ J : Subgroup ((decs Ek Aw) w),
          F c1 w ≤ unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) ((decs Ek Aw) w)) J ∧
          Ine (F := Ek) (Av v) ≤ J.map ((decs Ek Aw) w).subtype)) →
    (lhs ≤
      ∑ w ∈ what₂, Module.length O (Fs w ⧸ (Im w).comap (Fs w).subtype) +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + eO * (padicValNat ℓ (classNumber Ek) : ℕ∞) +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((ReciprocityTheory.Gal.locDeg (pl w) : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, IsDiscreteValuationRing.addVal O (ζO w - 1)) ∧
    vδ = eO * ((∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) : ℕ) : ℕ∞) ∧
    vδ ≤ eO * ((t * s₀ + padicValNat ℓ t.factorial : ℕ) : ℕ∞)

end Formalism.MainNotions.N.K
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem nonempty_pl : Nonempty (HeightOneSpectrum (𝓞 D.host.E)) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 D.host.E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM
    (NumberField.RingOfIntegers.not_isField _)⟩⟩

def plSet : Finset (HeightOneSpectrum (𝓞 D.host.E)) := dc.row ∪ dc.col ∪ D.nd.Q i

def idx (v : HeightOneSpectrum (𝓞 D.host.E)) : ℕ :=
  if h : v ∈ plSet i dc then ((plSet i dc).equivFin ⟨v, h⟩ : ℕ) else (plSet i dc).card

def plOf (n : ℕ) : HeightOneSpectrum (𝓞 D.host.E) :=
  if h : n < (plSet i dc).card then ((plSet i dc).equivFin.symm ⟨n, h⟩ : HeightOneSpectrum (𝓞 D.host.E))
  else Classical.choice nonempty_pl

theorem plOf_idx {v : HeightOneSpectrum (𝓞 D.host.E)} (h : v ∈ plSet i dc) : plOf i dc (idx i dc v) = v := by
  unfold plOf idx
  rw [dite_eq_left h, dite_eq_left ((plSet i dc).equivFin ⟨v, h⟩).isLt]
  simp

theorem idx_inj {v w : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ plSet i dc) (hw : w ∈ plSet i dc)
    (h : idx i dc v = idx i dc w) : v = w := by
  calc v = plOf i dc (idx i dc v) := (plOf_idx i dc hv).symm
    _ = plOf i dc (idx i dc w) := by rw [h]
    _ = w := plOf_idx i dc hw

def rowsN : Finset ℕ := dc.row.image (idx i dc)
def colsN : Finset ℕ := dc.col.image (idx i dc)
def qsN : Finset ℕ := (D.nd.Q i).image (idx i dc)

abbrev Col : Type := {u : HeightOneSpectrum (𝓞 D.host.E) // u ∈ dc.col}

def colIdx (l : Col i dc) : ℕ := idx i dc l.1

theorem colIdx_inj : Function.Injective (colIdx i dc) := by
  intro l₁ l₂ h
  apply Subtype.ext
  have m₁ : l₁.1 ∈ plSet i dc := by
    unfold plSet
    exact Finset.mem_union_left _ (Finset.mem_union_right _ l₁.2)
  have m₂ : l₂.1 ∈ plSet i dc := by
    unfold plSet
    exact Finset.mem_union_left _ (Finset.mem_union_right _ l₂.2)
  exact idx_inj i dc m₁ m₂ h

def Aw (n : ℕ) : ValuationSubring D.nd.Om := D.nd.plOm.1 (plOf i dc n)
def Av (v : HeightOneSpectrum (𝓞 D.host.E)) : ValuationSubring D.nd.Om := D.nd.plOm.1 v

end Formalism.MainNotions.N.K

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.N

def SelfGood {D : D7} (i : D.nd.Loc) : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).IsGood

end Formalism.MainNotions.N.K

end
end

section
open Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JT

open Formalism.NG Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem bkbConv : StatBKbConv := by
  intro O _ _ _ A HV HT' HV' _ _ _ _ _ _ _ _ _ _ _ _ _ q j' pr pair HfV HfV' h1 h2 h3 h4
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    rw [_root_.Formalism.NG.IdempotentNormalFormsRhoFacts.mem_annih]
    intro t ht
    rw [h3, (h1 a).1 ha _ ht, Submodule.Quotient.mk_zero]
  · intro hx
    rw [_root_.Formalism.NG.IdempotentNormalFormsRhoFacts.mem_annih] at hx
    let ψ : HT' →ₗ[O] HV' ⧸ HfV' := (HfV'.mkQ.restrictScalars O) ∘ₗ j'
    have hle : LinearMap.ker ψ ≤ LinearMap.ker (pr x) := by
      intro t ht
      rw [LinearMap.mem_ker] at ht ⊢
      apply hx t
      show j' t ∈ HfV'
      exact (Submodule.Quotient.mk_eq_zero HfV' (x := j' t)).1 ht
    let φ0 := (LinearMap.ker ψ).liftQ (pr x) hle
    let e := ψ.quotKerEquivRange
    let φbar : LinearMap.range ψ →ₗ[O] KO O := φ0 ∘ₗ e.symm.toLinearMap
    have hφ : ∀ t, φbar ⟨ψ t, LinearMap.mem_range_self ψ t⟩ = pr x t := by
      intro t
      show φ0 (e.symm ⟨ψ t, LinearMap.mem_range_self ψ t⟩) = pr x t
      rw [LinearMap.quotKerEquivRange_symm_apply_image]
      try rfl
    haveI hnz : NoZeroSMulDivisors O (HV' ⧸ HfV') := by
      refine ⟨fun {c v} hcv => ?_⟩
      by_cases hc : c = 0
      · exact Or.inl hc
      · right
        have hc' : algebraMap O (FractionRing O) c ≠ 0 :=
          (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hc
        have h' : algebraMap O (FractionRing O) c • v = 0 := by
          rw [algebraMap_smul]
          exact hcv
        exact (smul_eq_zero.1 h').resolve_left hc'
    haveI : Module.Free O (LinearMap.range ψ) := Module.free_of_finite_type_torsion_free'
    let b := Module.Free.chooseBasis O (LinearMap.range ψ)
    have hcex : ∀ i, ∃ y : FractionRing O, Formalism.RepresentationBoundsCohomology.LOC.toKO O y = φbar (b i) :=
      fun i => Submodule.mkQ_surjective _ _
    choose c hc using hcex
    have hli0 : LinearIndependent O (fun i => ((b i : LinearMap.range ψ) : HV' ⧸ HfV')) :=
      b.linearIndependent.map' (LinearMap.range ψ).subtype (Submodule.ker_subtype _)
    have hli : LinearIndependent (FractionRing O)
        (fun i => ((b i : LinearMap.range ψ) : HV' ⧸ HfV')) := by
      first
      | exact (LinearIndependent.iff_fractionRing O (FractionRing O)).1 hli0
    obtain ⟨G, hG⟩ : ∃ G : (HV' ⧸ HfV') →ₗ[FractionRing O] FractionRing O,
        ∀ i, G ((b i : LinearMap.range ψ) : HV' ⧸ HfV') = c i := by
      obtain ⟨G, hG⟩ :=
        LinearMap.exists_extend ((Finsupp.linearCombination (FractionRing O) c) ∘ₗ hli.repr)
      refine ⟨G, fun i => ?_⟩
      have h := LinearMap.congr_fun hG ⟨_, Submodule.subset_span ⟨i, rfl⟩⟩
      rw [LinearMap.comp_apply, LinearMap.comp_apply, hli.repr_eq_single i _ rfl,
        Finsupp.linearCombination_single, one_smul] at h
      exact h
    obtain ⟨a, ha⟩ := h2 (G ∘ₗ HfV'.mkQ)
    have haV : a ∈ HfV := (h1 a).2 fun bb hbb => by
      rw [ha, LinearMap.comp_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero HfV').2 hbb, map_zero]
    have key : (Formalism.RepresentationBoundsCohomology.LOC.toKO O) ∘ₗ (G.restrictScalars O) ∘ₗ (LinearMap.range ψ).subtype = φbar :=
      b.ext fun i => by
        show Formalism.RepresentationBoundsCohomology.LOC.toKO O (G ((b i : LinearMap.range ψ) : HV' ⧸ HfV')) = φbar (b i)
        rw [hG i, hc i]
    have hpr : ∀ t, pr (q a) t = pr x t := by
      intro t
      rw [h3, ha, ← hφ t]
      exact LinearMap.congr_fun key ⟨ψ t, LinearMap.mem_range_self ψ t⟩
    refine ⟨a, haV, ?_⟩
    have hz := h4 (q a - x) (fun t => by rw [map_sub, LinearMap.sub_apply, hpr t, sub_self])
    exact sub_eq_zero.1 hz

theorem rowBK : StatRowBK := by
  intro O _ _ _ X _ _ Hc HV Cs HV' _ _ _ _ _ _ _ _ _ _ _ q j' pr pair HfV HfV' F Fs h1 h2 h3 h4 hF hFs
  rw [hF, hFs, bkbConv O Hc HV Cs HV' q j' pr pair HfV HfV' h1 h2 h3 h4]

end Formalism.RepresentationBoundsCohomology.JT
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

def StatPowSubOneO : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ), ℓ.Prime →
    ¬ IsUnit (ℓ : O) → ∀ s₀ : ℕ, 1 ≤ s₀ → (ℓ = 2 → 2 ≤ s₀) →
    ∀ (x : O) (y : Oˣ), x - 1 = (ℓ : O) ^ s₀ * (y : O) → ∀ n : ℕ, n ≠ 0 →
      IsDiscreteValuationRing.addVal O (x ^ n - 1) =
        IsDiscreteValuationRing.addVal O (ℓ : O) * ((s₀ + padicValNat ℓ n : ℕ) : ℕ∞)

def WachTwistTheoremDeltaClause : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ℓ : ℕ), ℓ.Prime →
    ¬ IsUnit (ℓ : O) → ∀ s₀ : ℕ, 1 ≤ s₀ → (ℓ = 2 → 2 ≤ s₀) →
    ∀ x y u₁ : Oˣ, (x : O) - 1 = (ℓ : O) ^ s₀ * (y : O) → ∀ t : ℕ,
    let δO : O := ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * ((x⁻¹ ^ i : Oˣ) : O))
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    IsDiscreteValuationRing.addVal O δO =
      eO * ((∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) : ℕ) : ℕ∞) ∧
    IsDiscreteValuationRing.addVal O δO ≤ eO * ((t * s₀ + padicValNat ℓ t.factorial : ℕ) : ℕ∞)

def WachTwistTheoremDeltaSum : Prop :=
  ∀ (ℓ : ℕ), ℓ.Prime → ∀ s₀ t : ℕ,
    ∑ i ∈ Finset.Ioo 0 (t + 1), (s₀ + padicValNat ℓ i) = t * s₀ + padicValNat ℓ t.factorial

section Defs
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type*} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

def InRhoTensor (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') {ι : Type*} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → A)
    (k0 : ι → G → A) (ℓ : ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    {L : Type*} [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    {V : Type*} [AddCommGroup V] [Module A V] [Module O V] [Module (FractionRing O) V]
    (iL : L →ₗ[O] V) (qV : V →ₗ[O] M)
    (Ff : ∀ l, Submodule O (H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))))
    (κz : ∀ l, Fin (j (colIdx l)) → coZ1s (resRep (uRep O (M := L) r χ) (D (colIdx l))))
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo : Type*} (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    {T₁ T₂ : Type*} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    {Cs : ℕ → Type*} [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
    (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc w →ₗ[O] Cs w →ₗ[O] KO O)
    (Fs Im : ∀ w, Submodule O (Cs w)) : Prop :=
  (∀ (a : A) v x, tens (a • v) x = a • tens v x) ∧
  (∀ m : M, e₁ • m = m → ∃ x, m = tens v₁ x) ∧
  (∀ l a, ∀ g ∈ D (colIdx l), Kc l a g • v₁ = ((ℓ : O) ^ e' (colIdx l)) • κ l a g) ∧
  (∀ l (z : coZ1s (resRep (uRep O (M := M) r χ) (D (colIdx l)))) (x : Fin (j (colIdx l)) → KO O),
    (∀ g : D (colIdx l), (z : D (colIdx l) → M) g = ∑ a, tens (κ l a g) (x a)) →
    Submodule.mkQ _ z ∈ F (colIdx l)) ∧
  ((∀ (a : A) v, iL (a • v) = a • iL v) ∧ (∀ (a : A) v, qV (a • v) = a • qV v) ∧
    (∀ v (x : FractionRing O), tens v (Submodule.Quotient.mk x) = qV (x • iL v)) ∧
    Function.Injective iL ∧ Function.Surjective qV ∧ LinearMap.ker qV = LinearMap.range iL ∧
    (∀ v : V, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range iL) ∧
    ∀ l, (∀ a (g : D (colIdx l)), (κz l a : D (colIdx l) → L) g = κ l a g) ∧
      (∀ (c : O) z, c ≠ 0 → c • z ∈ Ff l → z ∈ Ff l) ∧
      (∀ a, Submodule.mkQ _ (κz l a) ∈ Ff l) ∧
      (∀ z ∈ Ff l, ∃ (b : Fin (j (colIdx l)) → O) (c : O), c ≠ 0 ∧
        c • (z - ∑ a, b a • (Submodule.mkQ _ (κz l a) :
          H1z (resRep (uRep O (M := L) r χ) (D (colIdx l))))) = 0) ∧
      (∀ (b : Fin (j (colIdx l)) → O) (c : O), c ≠ 0 →
        c • ∑ a, b a • (Submodule.mkQ _ (κz l a) :
          H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))) = 0 → b = 0)) ∧
  (∀ φ, Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ (fun l => D (colIdx l))
    (fun l => j (colIdx l)) Kc k0 φ) ∈ HcG) ∧
  (∀ w ∈ what₂, HcG ≤ (Hc w).comap (resH1 (uRep O (M := M) r χ) (D w))) ∧
  (∀ v, ∀ g ∈ Io v, r g = 1 ∧ χ g = 1) ∧
  (∀ g b, inc (ρ₁ g b) = ((ε g : Oˣ) : O) • (((χ g : T'ˣ) : T') • (inc b * r g⁻¹))) ∧
  IsEquivMap ρ₁ ρ₂ π ∧ (∀ b m, γ (π b) m = lam (inc b • m)) ∧
  (∀ w ∈ what₂, InRowRho M r χ E (D w) ε ρ₁ inc π γ (Hc w) (F w) (cls w) (pr w) (Fs w) (Im w)) ∧
  Module.length O ↥((HcG ⊓ ⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
    ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤ s

end Defs

def SelmerInjConditions : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T') (ι : Type*) [Fintype ι]
    [DecidableEq ι] (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (j e' : ℕ → ℕ)
    (Kc : ∀ l, Fin (j (colIdx l)) → G → A) (k0 : ι → G → A) (ℓ : ℕ) (what₂ : Finset ℕ) (s : ℕ∞)
    (L : Type*) [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    (tens : L →ₗ[O] KO O →ₗ[O] M) (v₁ : L)
    (κ : ∀ l, Fin (j (colIdx l)) → G → L)
    (V : Type*) [AddCommGroup V] [Module A V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [SMulCommClass A (FractionRing O) V]
    (iL : L →ₗ[O] V) (qV : V →ₗ[O] M)
    (Ff : ∀ l, Submodule O (H1z (resRep (uRep O (M := L) r χ) (D (colIdx l)))))
    (κz : ∀ l, Fin (j (colIdx l)) → coZ1s (resRep (uRep O (M := L) r χ) (D (colIdx l))))
    (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
    (Hc F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    (Vo : Type*) (Io : Vo → Subgroup G) (ε : G →* Oˣ)
    (T₁ T₂ : Type*) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] A)
    (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] M →ₗ[O] KO O) (lam : M →ₗ[O] KO O)
    (Cs : ℕ → Type*) [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
    (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc w →ₗ[O] Cs w →ₗ[O] KO O)
    (Fs Im : ∀ w, Submodule O (Cs w)),
    InRhoTensor M r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ iL qV Ff κz HcG Hc F Io ε ρ₁ ρ₂ inc
      π γ lam cls pr Fs Im →
    InRho M r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ HcG Hc F Io ε ρ₁ ρ₂ inc π γ lam
      cls pr Fs Im

end Formalism.RepresentationBoundsCohomology.BR
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

def SelmerInjTensorForm : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (D : Type*) [Group D] (L V M : Type*) [AddCommGroup L] [Module O L] [AddCommGroup V]
    [Module O V] [Module (FractionRing O) V] [IsScalarTower O (FractionRing O) V]
    [AddCommGroup M] [Module O M]
    (ρL : Representation O D L) (ρV : Representation (FractionRing O) D V)
    (ρM : Representation O D M) (i : L →ₗ[O] V) (q : V →ₗ[O] M)
    (tens : L →ₗ[O] KO O →ₗ[O] M),
    (∀ v (x : FractionRing O), tens v (Submodule.Quotient.mk x) = q (x • i v)) →
    Function.Injective i → Function.Surjective q → LinearMap.ker q = LinearMap.range i →
    (∀ v : V, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range i) →
    (∀ g v, i (ρL g v) = ρV g (i v)) → (∀ g v, q (ρV g v) = ρM g (q v)) →
    ∀ (Ff : Submodule O (H1z ρL)) (j : ℕ) (κ : Fin j → coZ1s ρL),
    (∀ (c : O) z, c ≠ 0 → c • z ∈ Ff → z ∈ Ff) →
    (∀ a, (Submodule.mkQ _ (κ a) : H1z ρL) ∈ Ff) →
    (∀ z ∈ Ff, ∃ (b : Fin j → O) (c : O), c ≠ 0 ∧
      c • (z - ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL)) = 0) →
    (∀ (b : Fin j → O) (c : O), c ≠ 0 →
      c • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL) = 0 → b = 0) →
    ∀ (x : Fin j → KO O) (m : M),
      (∀ g, ∑ a, tens ((κ a : D → L) g) (x a) = ρM g m - m) → ∀ a, x a = 0

def SelmerInjColumnPlace : Prop :=
  ∀ (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (A T' G : Type*) [Ring A] [CommRing T'] [Algebra T' A] [Group G]
    (M : Type*) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (L : Type*) [AddCommGroup L] [Module A L] [Module O L] [SMulCommClass A O L]
    (V : Type*) [AddCommGroup V] [Module A V] [Module O V] [Module (FractionRing O) V]
    [IsScalarTower O (FractionRing O) V] [SMulCommClass A (FractionRing O) V]
    (r : G →* A) (χ : G →* T'ˣ) (Dl : Subgroup G) (i : L →ₗ[O] V) (q : V →ₗ[O] M)
    (tens : L →ₗ[O] KO O →ₗ[O] M),
    (∀ (a : A) v, i (a • v) = a • i v) → (∀ (a : A) v, q (a • v) = a • q v) →
    (∀ v (x : FractionRing O), tens v (Submodule.Quotient.mk x) = q (x • i v)) →
    Function.Injective i → Function.Surjective q → LinearMap.ker q = LinearMap.range i →
    (∀ v : V, ∃ c : O, c ≠ 0 ∧ c • v ∈ LinearMap.range i) →
    ∀ (Ff : Submodule O (H1z (resRep (uRep O (M := L) r χ) Dl))) (j : ℕ) (κ : Fin j → G → L)
      (κz : Fin j → coZ1s (resRep (uRep O (M := L) r χ) Dl)),
    (∀ a (g : Dl), (κz a : Dl → L) g = κ a g) →
    (∀ (c : O) z, c ≠ 0 → c • z ∈ Ff → z ∈ Ff) →
    (∀ a, Submodule.mkQ _ (κz a) ∈ Ff) →
    (∀ z ∈ Ff, ∃ (b : Fin j → O) (c : O), c ≠ 0 ∧
      c • (z - ∑ a, b a • (Submodule.mkQ _ (κz a) : H1z (resRep (uRep O (M := L) r χ) Dl))) = 0) →
    (∀ (b : Fin j → O) (c : O), c ≠ 0 →
      c • ∑ a, b a • (Submodule.mkQ _ (κz a) : H1z (resRep (uRep O (M := L) r χ) Dl)) = 0 →
      b = 0) →
    ∀ x : Fin j → KO O, (fun g : Dl => ∑ a, tens (κ a g) (x a)) ∈
      LinearMap.range (colDO (O := O) (M := M) r χ Dl) → ∀ a, x a = 0

end Formalism.RepresentationBoundsCohomology.BR
end
end

section
open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

theorem c3 : SelmerFInjective := by
  intro O _ _ _ D _ L V M _ _ _ _ _ _ _ _ ρL ρV ρM i q hi hq hker hsat hiρ hqρ Ff j κ hF1 hF2 hF3 hF4
    x m hx

  obtain ⟨⟨c, hc⟩, hcx⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O)
    (Finset.univ : Finset (Fin j)) x
  have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
  have hcx' : ∀ a, ∃ t : O, algebraMap O (FractionRing O) t = c • x a :=
    fun a => RingHom.mem_rangeS.mp (hcx a (Finset.mem_univ a))
  choose y hy using hcx'
  obtain ⟨v, rfl⟩ := hq m
  obtain ⟨d, hd0, hw'⟩ := hsat (c • v)
  obtain ⟨w, hw⟩ := LinearMap.mem_range.mp hw'
  have he0 : d * c ≠ 0 := mul_ne_zero hd0 hc0
  have hK0 : algebraMap O (FractionRing O) (d * c) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr he0

  have cancelV : ∀ u u' : V, (d * c) • u = (d * c) • u' → u = u' := by
    intro u u' h
    rw [← algebraMap_smul (FractionRing O) (d * c) u, ← algebraMap_smul (FractionRing O) (d * c) u'] at h
    exact smul_right_injective V hK0 h
  have cancelL : ∀ a b : L, (d * c) • a = (d * c) • b → a = b := by
    intro a b h
    apply hi
    apply cancelV
    have h' := congrArg i h
    rwa [map_smul, map_smul] at h'

  have hf : ∀ g : D, ∃ zg : L, i zg = ∑ a, x a • i ((κ a : D → L) g) - (ρV g v - v) := by
    intro g
    have hmem : ∑ a, x a • i ((κ a : D → L) g) - (ρV g v - v) ∈ LinearMap.ker q := by
      rw [LinearMap.mem_ker, map_sub, map_sub, hx g, hqρ]
      exact sub_self _
    rw [hker] at hmem
    exact LinearMap.mem_range.mp hmem
  choose z hz using hf
  obtain ⟨Y, hYdef⟩ : ∃ Y : coZ1s ρL, Y = ∑ a, (d * y a) • κ a - cobZ ρL w := ⟨_, rfl⟩
  have hYg : ∀ g, (Y : D → L) g = ∑ a, (d * y a) • (κ a : D → L) g - (ρL g w - w) := by
    intro g
    rw [hYdef, Submodule.coe_sub, Submodule.coe_sum, Pi.sub_apply, Finset.sum_apply]
    rfl
  have hY : ∀ g, (d * c) • z g = (Y : D → L) g := by
    intro g
    apply hi

    rw [hYg g, map_smul, hz g, map_sub, map_sub, map_sum, hiρ, hw, smul_sub, smul_sub, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, mul_smul, mul_smul, ← smul_assoc c (x a), ← hy a, algebraMap_smul]
    · rw [LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, mul_smul, mul_smul]

  have hzc : z ∈ coZ1s ρL := by
    show ∀ g h, z (g * h) = z g + ρL g (z h)
    intro g h
    apply cancelL
    rw [smul_add, ← map_smul, hY, hY, hY]
    exact Y.2 g h
  have hZY : (d * c) • (⟨z, hzc⟩ : coZ1s ρL) = Y := Subtype.ext (funext hY)
  have hYcl : (Submodule.mkQ _ Y : H1z ρL) = ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL) := by

    rw [hYdef, map_sub, mkQ_cobZ, sub_zero, map_sum]
    simp only [map_smul]
  have h2 : (d * c) • (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) =
      ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    rw [← map_smul, hZY, hYcl]
  have hZF : (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) ∈ Ff := by
    apply hF1 (d * c) _ he0
    rw [h2]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hF2 a)
  obtain ⟨b, c', hc'0, hc'⟩ := hF3 _ hZF
  have h1 : c' • (Submodule.mkQ _ ⟨z, hzc⟩ : H1z ρL) =
      c' • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    rw [smul_sub, sub_eq_zero] at hc'
    exact hc'
  have hsplit : ∑ a, (d * y a - d * c * b a) • (Submodule.mkQ _ (κ a) : H1z ρL) =
      ∑ a, (d * y a) • (Submodule.mkQ _ (κ a) : H1z ρL) -
        (d * c) • ∑ a, b a • (Submodule.mkQ _ (κ a) : H1z ρL) := by
    simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, Finset.smul_sum]
  have h3 : c' • ∑ a, (d * y a - d * c * b a) • (Submodule.mkQ _ (κ a) : H1z ρL) = 0 := by
    rw [hsplit, ← h2, smul_sub, smul_comm c' (d * c), h1, smul_comm c' (d * c), sub_self]
  have hb := hF4 (fun a => d * y a - d * c * b a) c' hc'0 h3
  intro a
  have h4 : d * y a - d * c * b a = 0 := congrFun hb a
  have h5 : y a = c * b a := by
    apply mul_left_cancel₀ hd0
    rw [← mul_assoc]
    exact sub_eq_zero.mp h4
  have hc'' : algebraMap O (FractionRing O) c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hc0
  rw [Submodule.mem_one]
  refine ⟨b a, ?_⟩
  apply mul_left_cancel₀ hc''
  rw [← map_mul, ← h5, hy a, Algebra.smul_def]

end Formalism.RepresentationBoundsCohomology.BR
end
end

section
open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG

theorem selmer_inj_tensor_form : SelmerInjTensorForm := by
  intro O _ _ _ D _ L V M _ _ _ _ _ _ _ _ ρL ρV ρM i q tens htens hi hq hker hsat hiρ hqρ Ff j κ
    hF1 hF2 hF3 hF4 x m hx a
  choose y hy using fun b => Submodule.Quotient.mk_surjective (1 : Submodule O (FractionRing O)) (x b)
  have hsum : ∀ g, q (∑ b, y b • i ((κ b : D → L) g)) = ρM g m - m := by
    intro g

    rw [← hx g, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← hy b, htens]
  have key := c3 O D L V M ρL ρV ρM i q hi hq hker hsat hiρ hqρ Ff j κ hF1 hF2 hF3 hF4 y m hsum a
  rw [← hy a]
  exact (Submodule.Quotient.mk_eq_zero _).mpr key

theorem selmer_inj_column_place : SelmerInjColumnPlace := by
  intro O _ _ _ A T' G _ _ _ _ M _ _ _ _ L _ _ _ _ V _ _ _ _ _ _ r χ Dl i q tens hiA hqA htens hi hq
    hker hsat Ff j κ κz hκ hF1 hF2 hF3 hF4 x hx
  obtain ⟨m, hm⟩ := LinearMap.mem_range.mp hx
  refine selmer_inj_tensor_form O Dl L V M (resRep (uRep O (M := L) r χ) Dl)
    (resRep (uRep (FractionRing O) (M := V) r χ) Dl) (resRep (uRep O (M := M) r χ) Dl) i q tens
    htens hi hq hker hsat ?_ ?_ Ff j κz hF1 hF2 hF3 hF4 x m ?_
  · intro g v
    exact hiA (uElt r χ (g : G)) v
  · intro g v
    exact hqA (uElt r χ (g : G)) v
  · intro g
    have h1 := congrFun hm g
    simp only [hκ]
    exact h1.symm

end Formalism.RepresentationBoundsCohomology.BR
end
end

section
open Finset

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.BR

open Formalism.NG IsDiscreteValuationRing

namespace DeltaValuation

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

lemma unit_add {w a : O} (hw : IsUnit w) (ha : ¬ IsUnit a) : IsUnit (w + a) := by
  by_contra h
  have h1 : w + a ∈ nonunits O := h
  have h2 : -a ∈ nonunits O := by
    intro hh
    exact ha (by simpa using hh.neg)
  have h3 := IsLocalRing.nonunits_add h1 h2
  rw [add_neg_cancel_right] at h3
  exact h3 hw

lemma nonunit_mul {a : O} (ha : ¬ IsUnit a) (b : O) : ¬ IsUnit (a * b) :=
  fun h => ha (isUnit_of_mul_isUnit_left h)

lemma unit_of_coprime {l m : ℕ} (hl : ¬ IsUnit (l : O)) (h : Nat.Coprime m l) : IsUnit (m : O) := by
  have h1 : IsCoprime (m : ℤ) (l : ℤ) := Nat.isCoprime_iff_coprime.mpr h
  obtain ⟨a, b, hab⟩ := h1
  have h2 : (a : O) * (m : O) + (b : O) * (l : O) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → O) hab
  by_contra hm
  have h3 : (a : O) * (m : O) + (b : O) * (l : O) ∈ nonunits O :=
    IsLocalRing.nonunits_add (by rw [mul_comm]; exact nonunit_mul hm _)
      (by rw [mul_comm]; exact nonunit_mul hl _)
  rw [h2] at h3
  exact h3 isUnit_one

lemma geom_unit {l m : ℕ} (hl : ¬ IsUnit (l : O)) (h : Nat.Coprime m l) {x : O}
    (hx : ¬ IsUnit (x - 1)) : IsUnit (∑ i ∈ range m, x ^ i) := by
  have h1 : x - 1 ∣ (∑ i ∈ range m, x ^ i) - m := by
    have : (∑ i ∈ range m, x ^ i) - m = ∑ i ∈ range m, (x ^ i - 1) := by
      rw [Finset.sum_sub_distrib]; simp
    rw [this]
    exact Finset.dvd_sum fun i _ => by simpa using sub_dvd_pow_sub_pow x 1 i
  obtain ⟨c, hc⟩ := h1
  have : ∑ i ∈ range m, x ^ i = (m : O) + (x - 1) * c := by rw [← hc]; ring
  rw [this]
  exact unit_add (unit_of_coprime hl h) (nonunit_mul hx c)

lemma step {l : ℕ} (hp : l.Prime) (hl : ¬ IsUnit (l : O)) (x : O) (s : ℕ) (hs : 1 ≤ s)
    (hs2 : l = 2 → 2 ≤ s) (h : ∃ y : Oˣ, x - 1 = (l : O) ^ s * y) :
    ∃ y : Oˣ, x ^ l - 1 = (l : O) ^ (s + 1) * y := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  have hx : x = 1 + (l : O) * ((l : O) ^ s' * y) := by
    have : x = 1 + (x - 1) := by ring
    rw [this, hy]; ring
  have hsum : ∃ w : Oˣ, ∑ i ∈ range l, x ^ i = (l : O) * w := by
    by_cases h2 : l = 2
    · subst h2
      obtain ⟨s'', rfl⟩ : ∃ s'', s' = s'' + 1 := ⟨s' - 1, by have := hs2 rfl; omega⟩
      have hu : IsUnit (1 + ((2 : ℕ) : O) * (((2 : ℕ) : O) ^ s'' * y)) :=
        unit_add isUnit_one (nonunit_mul hl _)
      refine ⟨hu.unit, ?_⟩
      rw [IsUnit.unit_spec, Finset.sum_range_succ, Finset.sum_range_one, hx]
      push_cast
      ring
    · have hodd : Odd l := hp.odd_of_ne_two h2
      obtain ⟨c, hc⟩ := odd_sq_dvd_geom_sum₂_sub (R := O) (a := 1) (b := (l : O) ^ s' * y) hodd
      have hu : IsUnit (1 + (l : O) * c) := unit_add isUnit_one (nonunit_mul hl _)
      refine ⟨hu.unit, ?_⟩
      rw [IsUnit.unit_spec]
      simp only [one_pow, mul_one] at hc
      rw [← hx] at hc
      have : ∑ i ∈ range l, x ^ i = (l : O) + (l : O) ^ 2 * c := by rw [← hc]; ring
      rw [this]; ring
  obtain ⟨w, hw⟩ := hsum
  refine ⟨y * w, ?_⟩
  rw [← mul_geom_sum, hy, hw]
  push_cast
  ring

lemma iter {l : ℕ} (hp : l.Prime) (hl : ¬ IsUnit (l : O)) (x : O) (s : ℕ) (hs : 1 ≤ s)
    (hs2 : l = 2 → 2 ≤ s) (h : ∃ y : Oˣ, x - 1 = (l : O) ^ s * y) (k : ℕ) :
    ∃ y : Oˣ, x ^ (l ^ k) - 1 = (l : O) ^ (s + k) * y := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have := step hp hl (x ^ (l ^ k)) (s + k) (by omega) (fun h2 => by have := hs2 h2; omega) ih
    rwa [← pow_mul, ← pow_succ, add_assoc] at this

lemma pow_sub_one {l : ℕ} (hp : l.Prime) (hl : ¬ IsUnit (l : O)) (x : O) (s : ℕ) (hs : 1 ≤ s)
    (hs2 : l = 2 → 2 ≤ s) (h : ∃ y : Oˣ, x - 1 = (l : O) ^ s * y) (n : ℕ) (hn : n ≠ 0) :
    ∃ y : Oˣ, x ^ n - 1 = (l : O) ^ (s + padicValNat l n) * y := by
  have : Fact l.Prime := ⟨hp⟩
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn l hp.ne_one
  have hm0 : m ≠ 0 := fun h0 => hm (by rw [h0]; exact dvd_zero _)
  have hv : padicValNat l (l ^ k * m) = k := by
    rw [Nat.padicValNat_def, Nat.multiplicity_mul (pow_ne_zero _ hp.ne_zero) hm0,
      Nat.multiplicity_prime_pow, multiplicity_eq_zero_of_not_dvd hm, add_zero]
  obtain ⟨y, hy⟩ := iter hp hl x s hs hs2 h k
  have hnu : ¬ IsUnit (x ^ (l ^ k) - 1) := by
    rw [hy, show s + k = (s + k - 1) + 1 by omega, pow_succ', mul_assoc]
    exact nonunit_mul hl _
  have hg := geom_unit hl ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm).symm hnu
  refine ⟨y * hg.unit, ?_⟩
  rw [hv, pow_mul, ← mul_geom_sum, hy]
  push_cast
  rw [IsUnit.unit_spec]
  ring

end DeltaValuation

theorem powSubOneO : StatPowSubOneO := by
  intro O _ _ _ ℓ hℓ hℓu s₀ hs hs2 x y hx n hn
  obtain ⟨w, hw⟩ := DeltaValuation.pow_sub_one hℓ hℓu x s₀ hs hs2 ⟨y, hx⟩ n hn
  rw [hw, addVal_mul, addVal_pow, addVal_eq_zero_of_unit, add_zero, nsmul_eq_mul, mul_comm]

theorem theorem_n_five_delta_sum : WachTwistTheoremDeltaSum := by
  intro ℓ hℓ s₀ t
  have : Fact ℓ.Prime := ⟨hℓ⟩
  induction t with
  | zero =>
    rw [show Finset.Ioo 0 (0 + 1) = ∅ from by
      ext i; simp only [Finset.mem_Ioo, Finset.notMem_empty, iff_false]; omega]
    simp [Nat.padicValNat_def]
  | succ t ih =>
    have h : Finset.Ioo 0 (t + 1 + 1) = insert (t + 1) (Finset.Ioo 0 (t + 1)) := by
      ext i; simp only [Finset.mem_Ioo, Finset.mem_insert]; omega
    rw [h, Finset.sum_insert (by simp), ih, Nat.factorial_succ,
      (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero t) (Nat.factorial_ne_zero t)]
    ring

theorem theorem_n_five_delta_clause : WachTwistTheoremDeltaClause := by
  intro O _ _ _ ℓ hℓ hℓu s₀ hs hs2 x y u₁ hx t δO eO
  have he : eO = addVal O (ℓ : O) := IdempotentNormalFormsLenFacts.length_quot_span _
  have hfac : ∀ i ∈ Finset.Ioo 0 t, addVal O ((u₁ : O) - (u₁ : O) * ((x⁻¹ ^ i : Oˣ) : O)) =
      eO * ((s₀ + padicValNat ℓ i : ℕ) : ℕ∞) := by
    intro i hi
    have hi0 : i ≠ 0 := by rw [Finset.mem_Ioo] at hi; omega
    have h1 : ((x⁻¹ ^ i : Oˣ) : O) * (x : O) ^ i = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one]
    have h2 : (u₁ : O) - (u₁ : O) * ((x⁻¹ ^ i : Oˣ) : O) =
        ((u₁ * x⁻¹ ^ i : Oˣ) : O) * ((x : O) ^ i - 1) := by
      rw [Units.val_mul, mul_sub, mul_assoc, h1]; ring
    rw [h2, addVal_mul, addVal_eq_zero_of_unit, zero_add,
      powSubOneO O ℓ hℓ hℓu s₀ hs hs2 x y hx i hi0, he]
  have hval : addVal O δO = eO * ((∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) : ℕ) : ℕ∞) := by
    show addVal O (∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * ((x⁻¹ ^ i : Oˣ) : O))) = _
    rw [IdempotentNormalFormsLenFacts.addVal_prod, Finset.sum_congr rfl hfac, ← Finset.mul_sum, Nat.cast_sum]
  refine ⟨hval, ?_⟩
  rw [hval]
  have hle : ∑ i ∈ Finset.Ioo 0 t, (s₀ + padicValNat ℓ i) ≤ t * s₀ + padicValNat ℓ t.factorial := by
    have : Fact ℓ.Prime := ⟨hℓ⟩
    cases t with
    | zero => simp
    | succ t =>
      rw [theorem_n_five_delta_sum ℓ hℓ s₀ t, Nat.factorial_succ,
        (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) (Nat.succ_ne_zero t) (Nat.factorial_ne_zero t)]
      exact add_le_add (Nat.mul_le_mul_right _ (Nat.le_succ t)) (Nat.le_add_left _ _)
  gcongr

theorem inputs_from_selmer_inj : SelmerInjConditions := by
  intro O _ _ _ A T' G _ _ _ _ _ M _ _ _ _ r χ E e₁ δ ι _ _ colIdx D j e' Kc k0 ℓ what₂ s
    L _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz HcG Hc F Vo Io ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ lam
    Cs _ _ cls pr Fs Im h
  obtain ⟨h1, h2, h3, h4, ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩, h6⟩ := h
  refine ⟨h1, h2, h3, h4, fun l => ?_, h6⟩
  obtain ⟨b1, b2, b3, b4, b5⟩ := a8 l
  exact selmer_inj_column_place O A T' G M L V r χ (D (colIdx l)) iL qV tens a1 a2 a3 a4 a5 a6 a7 (Ff l)
    (j (colIdx l)) (κ l) (κz l) b1 b2 b3 b4 b5

end Formalism.RepresentationBoundsCohomology.BR
end
end

section
open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

def StatVhEInChi : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (Av : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω), (∀ v, IsPlaceOver (Av v) v) →
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[l] O]
      [Module.Finite ℤ_[l] O], (l ≠ 2 ∨ InfinitePlace.nrRealPlaces E = 0) →
    ∀ (A T' : Type) [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A]
      (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M],
      Nonempty (M ≃ₗ[O] KO O) →
    ∀ (r : G E Ω →* A) (χ : G E Ω →* T'ˣ), (∀ g (m : M), uElt r χ g • m = m) →
    ∀ (D : ℕ → Subgroup (G E Ω)) (places : Finset ℕ)
      (HcG : Submodule O (H1z (uRep O (M := M) r χ)))
      (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
      (Vo VS : Type) (Io : Vo → Subgroup (G E Ω)) (IS : VS → Subgroup (G E Ω)),
      (∀ x ∈ HcG, ∃ z : coZ1s (uRep O (M := M) r χ), Submodule.mkQ _ z = x ∧
        IsLocallyConstant (z : G E Ω → M)) →
      (∀ v, (∃ a, Ine (F := E) (Av v) ≤ Io a) ∨ (∃ a, Ine (F := E) (Av v) ≤ IS a) ∨
        ∃ w ∈ places, ∃ I : Subgroup (D w), F w ≤ unrH1 (resRep (uRep O (M := M) r χ) (D w)) I ∧
          Ine (F := E) (Av v) ≤ I.map (D w).subtype) →
      Module.length O ↥((HcG ⊓ (⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
          ⨅ v, unrH1 (uRep O (M := M) r χ) (IS v)) ⊓
        ⨅ w ∈ places, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))) ≤
      Module.length O (O ⧸ Ideal.span {(l : O)}) * (padicValNat l (classNumber E) : ℕ∞)

end Formalism.RepresentationBoundsCohomology.T2
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

section Triv

variable {O : Type*} [CommRing O] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module O M]

theorem coboundary_trivial_action_zero (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) (c : Γ → M) (hc : c ∈ coB1 ρ) : c = 0 := by
  obtain ⟨v, rfl⟩ := hc
  funext g
  show ρ g v - v = 0
  rw [h, sub_self]

theorem unr_vanish (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) (I : Subgroup Γ) (z : coZ1s ρ)
    (hz : (Submodule.mkQ _ z : H1z ρ) ∈ unrH1 ρ I) (g : Γ) (hg : g ∈ I) : (z : Γ → M) g = 0 := by
  have h1 : resH1 ρ I (Submodule.mkQ _ z) = 0 := hz
  have h2 : (Submodule.mkQ _ (restrictCocycles1 ρ I z) : H1z (resRep ρ I)) = 0 := h1
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  have h3 := coboundary_trivial_action_zero (resRep ρ I) (fun g m => h g m) _ h2
  exact congrFun h3 ⟨g, hg⟩

end Triv

theorem vhE : ReciprocityTheory.ChartRestriction.T2.VhE := hT2Core.out.vhE

theorem unramified_H1_antitone {O : Type*} [CommRing O] {Γ : Type*} [Group Γ] {M : Type*} [AddCommGroup M] [Module O M]
    (ρ : Representation O Γ M) (h : ∀ g m, ρ g m = m) {I J : Subgroup Γ} (hIJ : I ≤ J) : unrH1 ρ J ≤ unrH1 ρ I := by
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
  show resH1 ρ I (Submodule.mkQ _ z) = 0
  have : restrictCocycles1 ρ I z = 0 := Subtype.ext (funext fun g => unr_vanish ρ h J z hx g (hIJ g.2))
  show (Submodule.mkQ _ (restrictCocycles1 ρ I z) : H1z (resRep ρ I)) = 0
  rw [this, map_zero]

theorem vhEInChi : StatVhEInChi := by
  intro E Ω _ _ _ _ _ Av hA l _ O _ _ _ _ _ hl A T' _ _ _ _ M _ _ _ _ e r χ htr D places HcG F Vo VS Io IS hc hcov
  have hρ : ∀ g m, uRep O (M := M) r χ g m = m := fun g m => htr g m
  refine vhE E Ω Av hA l O hl M e (uRep O (M := M) r χ) hρ _ (fun x hx => hc x hx.1.1.1) (fun v x hx => ?_)
  rcases hcov v with ⟨a, ha⟩ | ⟨a, ha⟩ | ⟨w, hw, I, hF, hI⟩
  · exact unramified_H1_antitone _ hρ ha ((Submodule.mem_iInf _).1 hx.1.1.2 a)
  · exact unramified_H1_antitone _ hρ ha ((Submodule.mem_iInf _).1 hx.1.2 a)
  · have h1 : resH1 (uRep O (M := M) r χ) (D w) x ∈ F w :=
      (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hx.2 w) hw
    have h2 := hF h1
    obtain ⟨z, rfl⟩ := Submodule.mkQ_surjective _ x
    show Formalism.NG.resH1 (uRep O (M := M) r χ) (Ine (F := E) (Av v)) (Submodule.mkQ _ z) = 0
    have : Formalism.NG.restrictCocycles1 (uRep O (M := M) r χ) (Ine (F := E) (Av v)) z = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      obtain ⟨g', hg', hgg⟩ := hI g.2
      have h3 := unr_vanish (resRep (uRep O (M := M) r χ) (D w)) (fun g m => hρ g m) I
        (Formalism.NG.restrictCocycles1 (uRep O (M := M) r χ) (D w) z) h2 g' hg'
      show (z : G E Ω → M) g = 0
      rw [← hgg]
      exact h3
    show (Submodule.mkQ _ (Formalism.NG.restrictCocycles1 (uRep O (M := M) r χ) (Ine (F := E) (Av v)) z) :
      H1z (resRep (uRep O (M := M) r χ) (Ine (F := E) (Av v)))) = 0
    rw [this, map_zero]

end Formalism.RepresentationBoundsCohomology.T2
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

theorem ko_tors (O : Type) [CommRing O] [IsDomain O] (z : KO O) : ∃ c : O, c ≠ 0 ∧ c • z = 0 := by
  obtain ⟨q, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨⟨a, ⟨b, hb⟩⟩, hq⟩ := IsLocalization.surj (nonZeroDivisors O) q
  refine ⟨b, nonZeroDivisors.ne_zero hb, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine Submodule.mem_one.2 ⟨a, ?_⟩
  rw [Algebra.smul_def, mul_comm]
  exact hq.symm

theorem psiCont (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    (A : Type) [Ring A] [Algebra O A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [ContinuousConstSMul O A] (Y : Submodule A A) (hO : PadicCoeff p O) (hA : IsFGTop O A)
    (ψ : Y →ₗ[O] KO O) : Continuous ψ := by
  have hfg : IsFGTop O Y := by
    have := hA.fg
    have := hA.t2
    have := hA.csmul
    refine ⟨?_, inferInstance, ?_⟩
    · exact Module.Finite.of_injective (Y.subtype.restrictScalars O) Subtype.val_injective
    · exact ⟨Continuous.subtype_mk (f := fun q : O × Y => q.1 • (q.2 : A))
        (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  obtain ⟨a, ha, hka⟩ : ∃ a : O, a ≠ 0 ∧ ∀ y : Y, a • ψ y = 0 := by
    obtain ⟨s, hs⟩ := hfg.fg.fg_top
    choose f hf0 hf using fun y : Y => ko_tors O (ψ y)
    refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), fun y => ?_⟩
    have hy : y ∈ Submodule.span O (s : Set Y) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f hx
      rw [hc, mul_comm, mul_smul, hf, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, smul_comm, hx, smul_zero]
  have hopen := hfg.isOpen_mulSub hO ha
  refine continuous_of_continuousAt_zero ψ.toAddMonoidHom ?_
  intro U hU
  have hU0 : (0 : KO O) ∈ U := by
    have := mem_of_mem_nhds hU
    simpa using this
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (hopen.mem_nhds (zero_mem _)) ?_
  rintro _ ⟨z, rfl⟩
  show ψ (a • z) ∈ U
  rw [map_smul, hka]
  exact hU0

theorem inRowReal_of (p : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace A]
    [IsTopologicalAddGroup A] [ContinuousConstSMul O A] [ContinuousMul A]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) [TopologicalSpace Dw]
    {T₁ T₂ : Type} [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
    [TopologicalSpace T₁] [IsTopologicalAddGroup T₁] [ContinuousConstSMul O T₁]
    (ρ₁ : Representation O G T₁) (inc : T₁ →ₗ[O] A) (π : T₁ →ₗ[O] T₂)
    (D : LatData O Dw VT VT') (v : T₂ ≃ₗ[O] D.T') (hc : Continuous fun t => v (π t))
    (he : ∀ g t, v (π (resRep ρ₁ Dw g t)) = D.ρTl' g (v (π t)))
    (Fs : Submodule O (H1 D.ρTl')) (Hf₁ : Submodule O (H1 (resRep ρ₁ Dw)))
    (hO : PadicCoeff p O) (hA : IsFGTop O A) (hinc : Continuous inc)
    (hur : Continuous fun g : Dw => uElt r χ (g : G)) (hIm : Hf₁.map (gRow D _ π v hc he) ≤ Fs) :
    InRowReal r χ E Dw ρ₁ inc π D v Fs (Hf₁.map (gRow D _ π v hc he)) := by
  refine ⟨fun a => Continuous a, fun a ha => ?_, fun a ha => ?_, fun ψ f hf => ?_, fun a ha => hc.comp ha, ?_, hIm⟩
  · refine Continuous.subtype_mk (f := fun q : Dw × Dw =>
      inc (a q.1) * (uElt r χ (q.1 : G) * ((uElt r χ (q.2 : G) - 1) * E))) ?_ _
    exact (hinc.comp (ha.comp continuous_fst)).mul ((hur.comp continuous_fst).mul
      (((hur.comp continuous_snd).sub continuous_const).mul continuous_const))
  · exact ((hinc.comp ha).mul (hur.mul continuous_const)).neg
  · exact (psiCont p O A (Ymod r χ E) hO hA ψ).comp hf
  · rintro _ ⟨y, _, rfl⟩
    induction y using Submodule.Quotient.induction_on with
    | _ c =>
      have h : (fun g => v (π (c.1 g))) ∈ Z1 D.ρTl' :=
        (cocycles1MapOfEquivariant (resRep ρ₁ Dw) D.ρTl' (v.toLinearMap ∘ₗ π) hc he c).2
      refine ⟨c.1, c.2.2, c.2.1, ?_⟩
      rw [clsRow_of_mem D v _ h]
      rfl

end Formalism.RepresentationBoundsCohomology.FIN
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsFGTop NatInv)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

theorem h2Map_injective_statement : H2MapInjective := by
  intro O _ _ _ _ Γ _ _ ε hNat Y R _ _ _ _ _ _ _ _ _ _ hY hR i hic hii z hz hzc hfz
  obtain ⟨f, hf, hfz⟩ := hfz
  obtain ⟨θ⟩ := hNat
  have htw : ∀ (M : Type) [AddCommGroup M] [Module O M] (g : Γ) (m : M),
      Formalism.RepresentationBoundsCohomology.LOC.twist ε M g m = ((ε g : Oˣ) : O) • m := fun M _ _ g m => rfl

  let zz : ReciprocityTheory.Gal.Z2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y) := ⟨fun p => z p.1 p.2, hzc, fun g h k => hz g h k⟩
  have hzero : ReciprocityTheory.Gal.mapH2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y) (Formalism.RepresentationBoundsCohomology.LOC.twist ε R) i hic
      (ReciprocityTheory.ChartRestriction.T2.twist_map ε i) (Submodule.Quotient.mk zz) = 0 := by
    rw [ReciprocityTheory.Gal.mapH2, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem]
    refine ⟨f, hf, ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    rw [ReciprocityTheory.Gal.d1_apply, htw]
    exact (hfz g h).symm
  have hθ := θ.nat Y R hY hR i hic (Submodule.Quotient.mk zz)
  rw [hzero, map_zero] at hθ
  have h0 : θ.θ Y hY (Submodule.Quotient.mk zz) = 0 := hii (hθ.symm.trans (map_zero i).symm)
  have hmk : (Submodule.Quotient.mk zz : ReciprocityTheory.Gal.H2 (Formalism.RepresentationBoundsCohomology.LOC.twist ε Y)) = 0 :=
    (θ.θ Y hY).injective (by rw [h0, map_zero])
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem] at hmk
  obtain ⟨c, hc, hcz⟩ := hmk
  refine ⟨c, hc, fun g h => ?_⟩
  have e := congrFun hcz (g, h)
  rw [ReciprocityTheory.Gal.d1_apply, htw] at e
  exact e.symm

theorem clause4 : CupClause := by
  intro O _ _ _ _ A T' G _ _ _ _ _ _ _ _ r χ E Dw _ ε hA hNat z hz hzc hfz
  haveI : IsNoetherian O A := by
    haveI := hA.fg
    infer_instance
  haveI := hA.t2
  haveI := hA.csmul
  haveI : ContinuousConstSMul O (Ymod r χ E) :=
    ⟨fun a => continuous_induced_rng.2 ((continuous_const_smul a).comp continuous_subtype_val)⟩
  let i : Ymod r χ E →ₗ[O] A := (Ymod r χ E).subtype.restrictScalars O
  have hYfg : ReciprocityTheory.ChartRestriction.T2.IsFGTop O (Ymod r χ E) :=
    ⟨Module.Finite.of_injective i Subtype.val_injective, inferInstance,
      ⟨continuous_induced_rng.2 (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))⟩⟩
  exact h2Map_injective_statement O Dw (ε.comp Dw.subtype) hNat (Ymod r χ E) A hYfg hA i continuous_subtype_val
    Subtype.val_injective z hz hzc hfz

end Formalism.RepresentationBoundsCohomology.T2
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsFGTop NatInv)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

theorem clause4GK : CupClauseGK := by
  intro p _ K O _ _ _ _ A T' G _ _ _ _ _ _ _ _ r χ E Dw _ ε hK hO e hε hA
  obtain ⟨F⟩ := ReciprocityTheory.ChartRestriction.T2.natInv_all_iso hK hO e (ε := ε.comp Dw.subtype) hε
  exact clause4 O A T' G r χ E Dw ε hA ⟨F⟩

end Formalism.RepresentationBoundsCohomology.T2
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.BR

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

theorem kRow_rel {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (D : LatData O Γ VT VT') {M : Type} [AddCommGroup M] [Module O M] (ρM : Representation O Γ M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m)) (x : Z1 D.ρA) (b : coZ1s ρM)
    (hy : kRow D ρM u hu (Submodule.Quotient.mk x) = Submodule.mkQ _ b) :
    ∃ m' : VT ⧸ D.T, ∀ g, u ((b : Γ → M) g) = x.1 g - (D.ρA g m' - m') := by
  have hsym : ∀ g y, u.symm (D.ρA g y) = ρM g (u.symm y) := fun g y => by
    rw [LinearEquiv.symm_apply_eq, hu, LinearEquiv.apply_symm_apply]
  let b' : coZ1s ρM := ⟨fun g => u.symm (x.1 g), fun g h => by
    show u.symm (x.1 (g * h)) = u.symm (x.1 g) + ρM g (u.symm (x.1 h))
    rw [((mem_Z1_iff_cocycle _ _).1 x.2).2 g h, map_add (f := _), hsym]⟩
  have hk0 : kRow D ρM u hu (Submodule.Quotient.mk x) = Submodule.mkQ _ b' := rfl
  have hy' : Submodule.mkQ _ b' = Submodule.mkQ _ b := hk0.symm.trans hy
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap,
    coB1, LinearMap.mem_range] at hy'
  obtain ⟨m, hm⟩ := hy'
  refine ⟨u m, fun g => ?_⟩
  have h1 := congrFun hm g
  rw [Submodule.coe_subtype, Submodule.coe_sub, Pi.sub_apply] at h1
  have h2 : ρM g m - m = u.symm (x.1 g) - (b : Γ → M) g := h1
  have h3 : (b : Γ → M) g = u.symm (x.1 g) - (ρM g m - m) := by rw [h2]; abel
  rw [h3, map_sub, map_sub, LinearEquiv.apply_symm_apply, hu]

theorem clause5Gen {O Γ VT VT' : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT] [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT'] [ContinuousSMul O VT']
    (D : LatData O Γ VT VT') {M : Type} [AddCommGroup M] [Module O M] (ρM : Representation O Γ M)
    (u : M ≃ₗ[O] (VT ⧸ D.T)) (hu : ∀ g m, u (ρM g m) = D.ρA g (u m)) (hA : ContAction D.ρA)
    (hk : Function.Injective (kRow D ρM u hu)) (b : coZ1s ρM)
    (hb : Submodule.mkQ _ b ∈ LinearMap.range (kRow D ρM u hu)) (t : Γ → D.T') (ht : t ∈ Z1 D.ρTl')
    (c : Γ → KO O) (hc : Continuous c)
    (h : ∀ g k, pairKO D.bT D.T (D.ρA g (u ((b : Γ → M) k))) (t g) =
      ((D.ε g : Oˣ) : O) • c k - c (g * k) + c g) :
    prK D _ hk ⟨Submodule.mkQ _ b, hb⟩ (Submodule.Quotient.mk ⟨t, ht⟩) = 0 := by
  have hb0 := hb
  obtain ⟨y, hy⟩ := hb0
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨m', hbg⟩ := kRow_rel D _ u hu x b hy
  have hx' : (fun g => u ((b : Γ → M) g)) ∈ Z1 D.ρA := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨?_, fun g h => ?_⟩
    · have hxc : Continuous x.1 := ((mem_Z1_iff_cocycle _ _).1 x.2).1
      have hc2 : Continuous fun g : Γ => D.ρA g m' := hA.comp (continuous_id.prodMk continuous_const)
      have : (fun g => u ((b : Γ → M) g)) = fun g => x.1 g - (D.ρA g m' - m') := funext hbg
      rw [this]
      exact hxc.sub (hc2.sub continuous_const)
    · rw [b.2 g h, map_add (f := _), hu]
  have hxx : (Submodule.Quotient.mk x : ReciprocityTheory.Gal.H1 D.ρA) = Submodule.Quotient.mk ⟨_, hx'⟩ := by
    refine (Submodule.Quotient.eq _).2 ((mem_coboundaries1 _ _).2 ⟨m', fun g => ?_⟩)
    change x.1 g - u ((b : Γ → M) g) = _
    rw [hbg]; abel
  have e1 : (⟨Submodule.mkQ _ b, hb⟩ : LinearMap.range (kRow D _ u hu)) =
      LinearEquiv.ofInjective _ hk (Submodule.Quotient.mk x) := Subtype.ext hy.symm
  rw [e1]
  change D.pr ((LinearEquiv.ofInjective _ hk).symm (LinearEquiv.ofInjective _ hk (Submodule.Quotient.mk x))) _ = 0
  rw [LinearEquiv.symm_apply_apply, hxx]
  exact ReciprocityTheory.ChartRestriction.T2.pr_eq_zero_of_swap_cob D ⟨_, hx'⟩ ⟨_, ht⟩ c hc h

theorem clause5Row : StatClause5Row := by
  intro O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ A T' G _ _ _ _ _ M _ _ _ _ r χ Dw _ ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ π γ
    D u hu v hε hT hπ hv hγ hk C₁ hC a b hb ha hCa ⟨c, hc, hcob⟩
  have ht : (fun g => v (π (a g))) ∈ Z1 D.ρTl' := by
    refine (mem_Z1_iff_cocycle _ _).2 ⟨hC a hCa, fun g h => ?_⟩
    have e1 : a (g * h) = a g + ρ₁ (g : G) (a h) := ha g h
    rw [e1, map_add (f := _), map_add (f := _), hπ, hv]
  have e2 : clsRow D v (fun g => π (a g)) = Submodule.Quotient.mk ⟨_, ht⟩ := by
    unfold clsRow
    exact dite_eq_left ht
  rw [e2]
  refine clause5Gen D _ u hu (ReciprocityTheory.ChartRestriction.T2.contAction_quotient hT D.T D.stT) hk b hb _ ht c hc fun g k => ?_
  have h4 := hcob g k
  rw [hγ] at h4
  have h5 : u (uElt r χ (g : G) • (b : Dw → M) k) = D.ρA g (u ((b : Dw → M) k)) := hu g _
  rw [h5] at h4
  rw [hε g]
  exact h4

end Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG RealLatG fracBilinear)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

theorem rowRhoReal : StatRowRhoReal := by
  intro p _ O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ek Ω _ _ _ _ _ Aw hp A T' _ _ _ _ _ _ _
    M _ _ _ _ r χ E ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ D u hu v familyMassRatio iS1 familyMassSecondLine iS2 HfV HfV' Fs Im hO hF hA hcyc hε hD hπ
    hv hγ hBK hFs hRow hk
  obtain ⟨K, hK, i, h1, -, -⟩ := ReciprocityTheory.ChartRestriction.T2.exists_dec_equiv (F := Ek) Aw hp
  have hεD : D.ε = ε.comp (Aw.decompositionSubgroup Ek).subtype := by
    ext g; simp [hε g]
  have hcD : IsCyc p K (ReciprocityTheory.ChartRestriction.T2.carry i D.ε) := h1 O D.ε (hεD ▸ hcyc)
  obtain ⟨inv, invF, hc⟩ := ReciprocityTheory.ChartRestriction.T2.exists_invariants_iso hK hO hF i hcD
  have hD' : RealLatG i (withInv D inv.toLinearMap invF.toLinearMap) :=
    ⟨hcD, hD.lat, hD.perf, hD.contT, hD.openT, hD.t2, hD.t2', hD.cs, hD.cs'⟩
  let j1 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT) := familyMassRatio
  have j2 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT) := iS1
  let j3 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT') := familyMassSecondLine
  have j4 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT') := iS2
  have hBK' : ∀ a, a ∈ HfV ↔ ∀ b ∈ HfV',
      fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap)) a b = 0 := by
    intro a
    rw [hBK a]
    refine forall₂_congr fun b _ => ?_
    show _ ↔ invF (cupFG D a b) = 0
    rw [LinearEquiv.map_eq_zero_iff]
  obtain ⟨_, hbk⟩ := bkInRow p K O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek)
    (withInv D inv.toLinearMap invF.toLinearMap) i u hu HfV HfV' hK hO hF hD' inv.injective invF.injective hc hBK'
  obtain ⟨C₁, c1, c2, c3, c3', c6, c7⟩ := hRow
  let pairD := fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap))
  refine ⟨prK (withInv D inv.toLinearMap invF.toLinearMap) _ hk, pairD, ?_, ?_⟩
  · rw [hFs]; exact hbk
  · refine ⟨C₁, fun z => Continuous fun q : _ × _ => z q.1 q.2, fun f => Continuous f, fun f => Continuous f,
      fun f => Continuous f, c1, c2, c3, ?_, ?_, c6, c7⟩
    · exact clause4GK p K O A T' _ r χ E (Aw.decompositionSubgroup Ek) ε hK hO i (hεD ▸ hcD) hA
    · exact clause5Row O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek) ε T₁ T₂ ρ₁ ρ₂ π γ
        (withInv D inv.toLinearMap invF.toLinearMap) u hu v hε hD.contT hπ hv hγ hk C₁ c3'

end Formalism.RepresentationBoundsCohomology.FIN
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG

theorem blk_ko {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X' : Type} {d : Type}
    [Fintype d] [DecidableEq d] {R' : Subalgebra O (X' → Matrix d d (FractionRing O))} {α : Type}
    [DecidableEq α] (bl : d → α)
    (ρk : ∀ k : α, R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O) (k : α)
    (h : Fintype.card {a // bl a = k} = 1) : Nonempty (blockRestrictedRepresentationType bl ρk k ≃ₗ[O] KO O) := by
  obtain ⟨hu⟩ := Fintype.card_eq_one_iff_nonempty_unique.1 h
  exact ⟨(LinearEquiv.funUnique {a // bl a = k} O (KO O) : ({a // bl a = k} → KO O) ≃ₗ[O] KO O)⟩

end Formalism.RepresentationBoundsCohomology.FIN
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

open Formalism.NG (uElt Ymod ColNNJ colPsi uRep colRelJ KO)
open Formalism.RepresentationBoundsCohomology.BR (yY)
open Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology (lcH1)
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff IsFGTop)

theorem lc_of_torsion (p : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A] [ContinuousMul A]
    (r : G →* A) (χ : G →* T'ˣ) (E : A)
    (hO : PadicCoeff p O) (hA : IsFGTop O A) (hur : Continuous fun g : G => uElt r χ g)
    {M : Type} [AddCommGroup M] [Module O M] (htors : ∀ m : M, ∃ c : O, c ≠ 0 ∧ c • m = 0)
    (ψ : Ymod r χ E →ₗ[O] M) : IsLocallyConstant fun g => ψ (yY r χ E g) := by
  have hfg : IsFGTop O (Ymod r χ E) := by
    have := hA.fg
    have := hA.t2
    have := hA.csmul
    refine ⟨?_, inferInstance, ?_⟩
    · exact Module.Finite.of_injective ((Ymod r χ E).subtype.restrictScalars O) Subtype.val_injective
    · exact ⟨Continuous.subtype_mk (f := fun q : O × (Ymod r χ E) => q.1 • (q.2 : A))
        (continuous_fst.smul (continuous_subtype_val.comp continuous_snd)) _⟩
  obtain ⟨a, ha, hka⟩ : ∃ a : O, a ≠ 0 ∧ ∀ y : Ymod r χ E, a • ψ y = 0 := by
    obtain ⟨s, hs⟩ := hfg.fg.fg_top
    choose f hf0 hf using fun y : Ymod r χ E => htors (ψ y)
    refine ⟨∏ y ∈ s, f y, Finset.prod_ne_zero_iff.2 (fun y _ => hf0 y), fun y => ?_⟩
    have hy : y ∈ Submodule.span O (s : Set (Ymod r χ E)) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f hx
      rw [hc, mul_comm, mul_smul, hf, smul_zero]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, smul_comm, hx, smul_zero]
  have hopen := hfg.isOpen_mulSub hO ha
  have hy : Continuous fun g => yY r χ E g :=
    Continuous.subtype_mk (f := fun g => (uElt r χ g - 1) * E)
      ((hur.sub continuous_const).mul continuous_const) _
  rw [IsLocallyConstant.iff_exists_open]
  intro g₀
  refine ⟨(fun g => yY r χ E g - yY r χ E g₀) ⁻¹' _, hopen.preimage (hy.sub continuous_const), ?_, ?_⟩
  · show yY r χ E g₀ - yY r χ E g₀ ∈ Formalism.RepresentationBoundsCohomology.LOC.mulSub a (Ymod r χ E)
    rw [sub_self]
    exact zero_mem _
  · rintro g ⟨z, hz⟩
    have hz' : a • z = yY r χ E g - yY r χ E g₀ := hz
    have h1 : ψ (yY r χ E g - yY r χ E g₀) = 0 := by
      rw [← hz', map_smul, hka]
    rw [map_sub, sub_eq_zero] at h1
    exact h1

theorem colPsi_lc (p : ℕ) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]
    [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousConstSMul O A] [ContinuousMul A]
    (r : G →* A) (χ : G →* T'ˣ) (E e₁ : A) (δ : T')
    (hO : PadicCoeff p O) (hA : IsFGTop O A) (hur : Continuous fun g : G => uElt r χ g)
    {M : Type} [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M] [IsScalarTower O A M]
    (htors : ∀ m : M, ∃ c : O, c ≠ 0 ∧ c • m = 0)
    {ι : Type} [DecidableEq ι] (D : ι → Subgroup G) (j : ι → ℕ) (Kc : ∀ l, Fin (j l) → G → A) (k0 : ι → G → A)
    (φ : ColNNJ r χ E e₁ δ D j Kc k0 →ₗ[A] M) :
    Submodule.mkQ _ (colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ) ∈ lcH1 (uRep O (M := M) r χ) := by
  refine ⟨colPsi (O := O) (M := M) r χ E e₁ δ D j Kc k0 φ, ?_, rfl⟩
  let ψ : Ymod r χ E →ₗ[O] M :=
    (φ ∘ₗ (colRelJ r χ E e₁ δ D j Kc k0).mkQ ∘ₗ LinearMap.inl A (Ymod r χ E) _).restrictScalars O
  exact lc_of_torsion p r χ E hO hA hur htors ψ

theorem pi_ko_torsion (O : Type) [CommRing O] [IsDomain O] (d : Type) [Fintype d] (m : d → KO O) :
    ∃ c : O, c ≠ 0 ∧ c • m = 0 := by
  classical
  have h1 : ∀ y : KO O, ∃ c : O, c ≠ 0 ∧ c • y = 0 := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) x
      refine ⟨b, nonZeroDivisors.ne_zero b.2, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, Submodule.mem_one]
      exact ⟨a, by rw [Algebra.smul_def, mul_comm]; exact hab.symm⟩
  choose c hc0 hc using fun i => h1 (m i)
  refine ⟨∏ i, c i, Finset.prod_ne_zero_iff.2 fun i _ => hc0 i, ?_⟩
  funext i
  rw [Pi.smul_apply, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), mul_smul, hc i, smul_zero]
  rfl

end Formalism.RepresentationBoundsCohomology.FIN
end
end

section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.JL

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

theorem liftCoc : StatLiftCoc := by
  intro O D M₁ M₂ _ _ _ _ _ _ ρ₁ ρ₂ p hp hs Hf₁ Hf₂ ℓ e hL κ hκ
  obtain ⟨x, hx, hxe⟩ := hL _ hκ
  obtain ⟨K₀, rfl⟩ := Submodule.mkQ_surjective _ x
  have h1 : (Submodule.Quotient.mk (cocycles1MapOfEquivariant ρ₁ ρ₂ p hp K₀ - ((ℓ : O) ^ e) • κ) : H1z ρ₂) = 0 := by
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, sub_eq_zero]
    exact hxe
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
  obtain ⟨v, hv⟩ := h1
  obtain ⟨w, rfl⟩ := hs v
  let cb : coZ1s ρ₁ := ⟨fun g => ρ₁ g w - w, fun g h => by
    simp only [map_mul, Module.End.mul_apply, map_sub]
    abel⟩
  refine ⟨K₀ - cb, ?_, fun g => ?_⟩
  · have hcb : Submodule.mkQ _ cb = (0 : H1z ρ₁) := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
      exact ⟨w, by funext g; rfl⟩
    rw [map_sub, hcb, sub_zero]
    exact hx
  · have h2 : ρ₂ g (p w) - p w = p ((K₀ : D → M₁) g) - ((ℓ : O) ^ e) • (κ : D → M₂) g :=
      congrFun hv g
    show p ((K₀ : D → M₁) g - (ρ₁ g w - w)) = _
    rw [map_sub, map_sub, hp, h2]
    abel

theorem colK : StatColK := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ L _ _ _ _ r χ Dl inc v₁ ev hev hs Hf₁ Hf₂ ℓ e' j κ κz hκ hκf hL
  have key := fun a => liftCoc O Dl P L _ _ ev (ev_equiv r χ Dl inc v₁ ev hev) hs Hf₁ Hf₂ ℓ e' hL
    (κz a) (hκf a)
  choose Kz hKz1 hKz2 using key
  refine ⟨fun a g => if h : g ∈ Dl then inc ((Kz a : Dl → P) ⟨g, h⟩) else 0, Kz, ?_, hKz1, ?_⟩
  · intro a g
    dsimp only
    rw [dite_eq_left g.2]
  · intro a g hg
    dsimp only
    rw [dite_eq_left hg, ← hev, hKz2 a ⟨g, hg⟩, hκ a ⟨g, hg⟩]

theorem colk : StatColk := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ M _ _ _ r χ E δO Dl inc ev hE hM hev hs Hf₁ Hf₂ ℓ e' u uz huz hmem hL
  obtain ⟨kz, hk1, hk2⟩ := liftCoc O Dl P _ _ _ ev (ev_equiv_triv r χ Dl ev hev) hs Hf₁ Hf₂ ℓ e' hL
    uz hmem
  refine ⟨fun g => if h : g ∈ Dl then inc ((kz : Dl → P) ⟨g, h⟩) else 0, kz, ?_, hk1, ?_, ?_⟩
  · intro g
    dsimp only
    rw [dite_eq_left g.2]
  · intro g
    dsimp only
    split_ifs with h
    · exact hE _
    · exact ⟨0, (zero_mul E).symm⟩
  · intro g hg m
    dsimp only
    rw [dite_eq_left hg, hM, hk2 ⟨g, hg⟩, Submodule.coe_smul, huz ⟨g, hg⟩, smul_eq_mul, mul_assoc]

theorem colFun : StatColFun := by
  intro O A T' G _ _ _ _ _ P _ _ _ _ V _ _ r χ Dl inc Hf₁ Lf H K Kz hK hKz s
  have h := H ((LinearMap.toSpanSingleton A V s).comp inc) Kz hKz
  have e : (fun g : Dl => K g • s) =
      fun g : Dl => ((LinearMap.toSpanSingleton A V s).comp inc) ((Kz : Dl → P) g) := by
    funext g
    rw [hK g]
    rfl
  rw [e]
  exact h

end Formalism.RepresentationBoundsCohomology.JL
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Finset Classical

noncomputable section

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain
open Formalism.NG
open Formalism.RepresentationBoundsCohomology.BR
  (InChi InRowRho inputs_from_selmer_inj theorem_n_five_delta_clause)
open Formalism.RepresentationBoundsCohomology.FIN
  (InRhoFixReal blk_ko colPsi_lc decs inRowReal_of kRowRange pi_ko_torsion resLC rowRhoReal)
open Formalism.RepresentationBoundsCohomology.JL (colFun colK colk)
open Formalism.RepresentationBoundsCohomology.JT (BKIn InRowRhoNoBK rowBK)
open Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology (clsRow kRow kRowInj lcH1 qK)
open Formalism.RepresentationBoundsCohomology.SplitClassesAll (InRhoFix)
open Formalism.RepresentationBoundsCohomology.T2 (vhEInChi)
open ReciprocityTheory.ChartRestriction.T2 (IsCycOn)
open ReciprocityTheory.Gal (H1)

theorem realDisplayAllK_of (ℓ : ℕ) [Fact ℓ.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[ℓ] O] [Module.Finite ℤ_[ℓ] O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)] (X X' : Type)
    (Z : Set X) (p : X' → X)
    (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [IsNoetherian R' R'] [TopologicalSpace R'] [IsTopologicalAddGroup R'] [ContinuousConstSMul O R'] [ContinuousMul R']
    (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
    [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
    (Ek Ω : Type) [Field Ek] [NumberField Ek] [Field Ω] [Algebra Ek Ω] [IsAlgClosure Ek Ω]
    (r : (Ω ≃ₐ[Ek] Ω) →* R') (χ : (Ω ≃ₐ[Ek] Ω) →* Tcˣ) (E e₁ : R') (δ : Tc)
    (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1))
    (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O)
    [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)]
    [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)]
    (δO : O) (ε : (Ω ≃ₐ[Ek] Ω) →* Oˣ) (gI : (Ω ≃ₐ[Ek] Ω)) (lhs : ℕ∞)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (q : ℕ) (b : Fin q → (X' → O)) (π' : X')
    (ρπ : R' →ₐ[O] Matrix d d O) (sE : Finset (Ω ≃ₐ[Ek] Ω)) (tE : (Ω ≃ₐ[Ek] Ω) → Tc) (u₁ : Oˣ)
    (hR : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingTop O X X' T T' p q b d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' ρπ t ht bl ρk sE tE δO)
    (hF : Formalism.RepresentationBoundsCohomology.ringDataObjects.LocalToDisplayFree O X X' T Z p d R' Tc (Ω ≃ₐ[Ek] Ω) r χ E e₁ δ π' t ht bl ρk δO)
    (hδO : δO = ∏ i ∈ Finset.Ioo 0 t, ((u₁ : O) - (u₁ : O) * (((ε gI)⁻¹ ^ i : Oˣ) : O)))
    (hl : lhs = vcc T Z (p π')) :
    RealDisplayAllK ℓ O X X' Z p d R' Tc Ek Ω r χ E e₁ t ht bl ρk δO ε gI lhs := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hcard1, -, -, -, -, -, -, hOne0⟩ := hR
  obtain ⟨p1, -, -, -⟩ := hOne0
  subst hl
  intro ι _ _ colIdx hinj Aw pl Av j e' what₂ qs s H0 Sha cB cT cols eO vδ N h0 c1
    L _ _ _ _ tens v₁ κ V _ _ _ _ _ _ iL qV Ff κz F Vo VS Io IS T₁ T₂ _ _ _ _ _ _ _ ρ₁ ρ₂ inc π
    γ lam VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Dat uD huD vD hpD heD Fs Hf₁ I γQ ζ ζO nQ u s₀ y
    _ _ _ _ HfW Hf₂ gR Im
    Pe _ _ _ _ ince eve heve PE _ _ _ _ incE evE hevE Hfe₁ HfE₁ HfE₂ uz
    hinjO hO hFr hA hcyc hinc hur hAv hreal hs1 hs2 hε hse hsE hincE hact huz hu hLe hLE hrat0
    hFix hRows hC hOne

  obtain ⟨f1, f2, f3, f4, f6, f7, f8, f9, f11⟩ := hFix
  have hres : ∀ (c : Fin (t + 1)) (w : ℕ), lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) ≤
      (lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))).comap
        (resH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)) :=
    fun c w => resLC O _ _ (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w)
  have hFix2 : InRhoFixReal (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz
      (lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk 0) r χ)) (F 0) Io ε ρ₁ ρ₂ inc π γ lam Dat uD huD vD Fs Im := by
    refine ⟨f1, f2, f3, f4, fun w hw => ?_, f6, f7, f8, f9, fun w hw => ?_, f11⟩
    · rw [kRowRange O (VT w) (VT' w) _ (Dat w) _ _ (uD w) (huD w) (hRows w hw).2.2.2.1.openT]
      exact hres 0 w
    · exact inRowReal_of ℓ r χ E (decs Ek Aw w) ρ₁ inc π (Dat w) (vD w) (hpD w) (heD w) (Fs w) (Hf₁ w) hO hA hinc
        (hur.comp continuous_subtype_val) (hRows w hw).2.2.2.2.2.2.2.2.2
  have hk : ∀ w, Function.Injective (kRow (Dat w) _ (uD w) (huD w)) :=
    fun w => kRowInj O (VT w) (VT' w) _ (Dat w) _ _ (uD w) (huD w)
  have hcycw : ∀ w, IsCycOn ℓ (decs Ek Aw w) (ε.comp (decs Ek Aw w).subtype) :=
    fun w g n ζ h => hcyc g.1 n ζ h
  have hnu : ¬ IsUnit (ℓ : O) := fun h => (mem_nonunits_iff.1 ((IsLocalRing.mem_maximalIdeal _).1 hO.p_mem)) h
  have hKO : ∀ c : Fin (t + 1), c ≠ 0 → Nonempty (blockRestrictedRepresentationType bl ρk c ≃ₗ[O] KO O) :=
    fun c hc => blk_ko bl ρk c (hcard1 c hc)
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hFix2
  have key : ∀ w, w ∈ what₂ →
      ∃ (pr : LinearMap.range (kRow (Dat w) _ (uD w) (huD w)) →ₗ[O] H1 (Dat w).ρTl' →ₗ[O] KO O)
      (pair : H1 (Dat w).ρT →ₗ[FractionRing O] H1 (Dat w).ρT' →ₗ[FractionRing O] FractionRing O),
      BKIn (LinearMap.range (kRow (Dat w) _ (uD w) (huD w))) (qK (Dat w) _ (hk w)) (Dat w).j' pr pair (HfW w) (Hf₂ w)
        ((((HfW w).restrictScalars O).map (Dat w).q).map (kRow (Dat w) _ (uD w) (huD w))) (Fs w) ∧
      InRowRhoNoBK (blockRestrictedRepresentationType bl ρk 0) r χ E (decs Ek Aw w) ε ρ₁ inc π γ
        (LinearMap.range (kRow (Dat w) _ (uD w) (huD w))) (clsRow (Dat w) (vD w)) pr (Fs w) (Im w) := by
    intro w hw
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, -⟩ := hRows w hw
    exact rowRhoReal ℓ O (VT w) (VT' w) Ek Ω (Aw w) a1 R' Tc (blockRestrictedRepresentationType bl ρk 0) r χ E ε T₁ T₂ ρ₁ ρ₂ inc π γ
      (Dat w) (uD w) (huD w) (vD w) (HfW w) (Hf₂ w) (Fs w) (Im w) hO hFr hA (hcycw w) a3 a4 e8 a5 a6 a7 a9
      (e10 w hw) (hk w)
  choose! pr pair hpp using key
  let HcG : ∀ c : Fin (t + 1), Submodule O (H1z (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)) :=
    fun c => lcH1 (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)
  let HcR : ∀ (c : Fin (t + 1)) (w : ℕ),
      Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))) := fun c =>
    Fin.cases (motive := fun c => ∀ w : ℕ,
        Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (decs Ek Aw w))))
      (fun w => LinearMap.range (kRow (Dat w) _ (uD w) (huD w)))
      (fun c' w => lcH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c'.succ) r χ) (decs Ek Aw w))) c
  have hBK' : ∀ w ∈ what₂, BKIn (HcR 0 w) (qK (Dat w) _ (hk w)) (Dat w).j' (pr w) (pair w) (HfW w) (Hf₂ w)
      (F 0 w) (Fs w) := by
    intro w hw
    rw [(hRows w hw).2.2.2.2.2.2.2.1]
    exact (hpp w hw).1
  have hFix' : InRhoFix (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ colIdx (decs Ek Aw) j what₂ s tens v₁ κ iL qV Ff κz (HcG 0)
      (HcR 0) (F 0) Io ε ρ₁ ρ₂ inc π γ lam (fun w => clsRow (Dat w) (vD w)) pr Fs Im :=
    ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, fun w hw => (hpp w hw).2, e11⟩
  obtain ⟨a1, a2, a4, ⟨c1', c2, c3, c4, c5, c6, c7, c8⟩, a7, a8, a9, a10, a11, a12, a13⟩ := hFix'

  choose Kc Kz hKc1 hKc2 hKc3 using fun l => colK O R' Tc (Ω ≃ₐ[Ek] Ω) Pe L r χ (decs Ek Aw (colIdx l)) ince v₁ eve heve hse
    (Hfe₁ l) (Ff l) ℓ (e' (colIdx l)) (j (colIdx l)) (κ l) (κz l) (c8 l).1 (c8 l).2.2.1 (hLe l)
  choose k0 kz hk01 hk02 hk03 hk04 using fun l => colk O R' Tc (Ω ≃ₐ[Ek] Ω) PE (blockRestrictedRepresentationType bl ρk c1) r χ E δO (decs Ek Aw (colIdx l)) incE
    evE hincE hact hevE hsE (HfE₁ l) (HfE₂ l) ℓ (e' (colIdx l)) (u l) (uz l) (huz l) (hu l) (hLE l)
  have hcont : ∀ (c : Fin (t + 1)) φ, Submodule.mkQ _ (colPsi (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ
      (fun l => decs Ek Aw (colIdx l)) (fun l => j (colIdx l)) Kc k0 φ) ∈ HcG c :=
    fun c φ => colPsi_lc ℓ (M := blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ hO hA hur (fun m => pi_ko_torsion O _ m) _ _ Kc k0 φ
  have hRowsA : ∀ w ∈ what₂, InRowRho (blockRestrictedRepresentationType bl ρk 0) r χ E (decs Ek Aw w) ε ρ₁ inc π γ (HcR 0 w) (F 0 w)
      (clsRow (Dat w) (vD w)) (pr w) (Fs w) (Im w) := by
    intro w hw
    obtain ⟨C₁, CN2, CN, CA, CP, b1, b2, b3, b4, b5, b6, b7⟩ := a12 w hw
    obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := hBK' w hw
    exact ⟨C₁, CN2, CN, CA, CP, b1, b2, b3, b4, b5, b6, b7,
      rowBK O _ (HcR 0 w) (H1 (Dat w).ρT) (H1 (Dat w).ρTl') (H1 (Dat w).ρT') (qK (Dat w) _ (hk w)) (Dat w).j'
        (pr w) (pair w) (HfW w) (Hf₂ w) (F 0 w) (Fs w) f2 f3 f4 f5 f6 f7⟩

  have hC' : ∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      InChi (blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ colIdx (decs Ek Aw) j Kc k0 ℓ cB what₂ qs (fun w => ReciprocityTheory.Gal.locDeg (pl w))
        (cT c) (Sha ((c : ℕ) - 1)) (HcG c) (HcR c) (F c) Io IS I γQ ζ ζO nQ := by
    intro c hc2
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc2
    obtain ⟨c', rfl⟩ : ∃ c', c = Fin.succ c' := ⟨c.pred hc0, (Fin.succ_pred _ _).symm⟩
    obtain ⟨-, hrw, ⟨i1, i3, i4⟩, i5⟩ := hC _ hc2
    refine ⟨fun w hw => ⟨?_, (hrw w hw).2.1, (hrw w hw).2.2.1, (hrw w hw).2.2.2⟩, i1, hcont _, fun w _ => hres _ w,
      i3, i4, i5⟩
    rw [(hrw w hw).1]
    exact bot_le
  obtain ⟨o4, o5, o6, o7, ⟨i1, i3, i4⟩, o10⟩ := hOne
  have hc1 : c1 ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp [c1] at this
  have hOneA : InChi (blockRestrictedRepresentationType bl ρk c1) r χ E e₁ δ colIdx (decs Ek Aw) j Kc k0 ℓ cB what₂ qs
      (fun w => ReciprocityTheory.Gal.locDeg (pl w)) (cT c1) (eO * (padicValNat ℓ (classNumber Ek) : ℕ∞))
      (HcG c1) (HcR c1) (F c1) Io IS I γQ ζ ζO nQ := by
    refine ⟨fun w hw => ⟨?_, (o7 w hw).2.1, (o7 w hw).2.2.1, (o7 w hw).2.2.2⟩, i1, hcont _, fun w _ => hres _ w,
      i3, i4, ?_⟩
    · rw [(o7 w hw).1]
      exact inf_le_left
    · refine vhEInChi Ek Ω Av hAv ℓ O hreal R' Tc (blockRestrictedRepresentationType bl ρk c1) (hKO _ hc1) r χ p1
        (decs Ek Aw) (what₂ ∪ qs ∪ univ.image colIdx) (HcG c1) (F c1) Vo VS Io IS ?_ o10
      rintro _ ⟨c, hc, rfl⟩
      exact ⟨c, rfl, hc⟩
  obtain ⟨hv1, hv2⟩ := theorem_n_five_delta_clause O ℓ Fact.out hnu s₀ hs1 hs2 (ε gI) y u₁ hε t
  refine ⟨?_, ?_, ?_⟩
  · exact hF ι colIdx hinj (decs Ek Aw) j e' Kc k0
      (fun x' hx' => by
        obtain ⟨q5, q6⟩ := hrat0 x' hx'
        refine ⟨q5, fun l => ?_⟩
        obtain ⟨Lx, w1, w2, w3, w4⟩ := q6 l
        exact ⟨Lx, w1, fun a s _ => colFun O R' Tc (Ω ≃ₐ[Ek] Ω) Pe (EvalSp O d R' x') r χ (decs Ek Aw (colIdx l)) ince
            (Hfe₁ l) (Lx : Set _) w2 (Kc l a) (Kz l a) (hKc1 l a) (hKc2 l a) s,
          fun s _ => colFun O R' Tc (Ω ≃ₐ[Ek] Ω) PE (EvalSp O d R' x') r χ (decs Ek Aw (colIdx l)) incE (HfE₁ l)
            (Lx : Set _) w3 (k0 l) (kz l) (hk01 l) (hk02 l) s, w4⟩)
      ℓ cB what₂ qs (fun w => ReciprocityTheory.Gal.locDeg (pl w)) s (eO * (padicValNat ℓ (classNumber Ek) : ℕ∞)) H0 Sha
      (fun l g => hk03 l g) L tens v₁ κ HcG HcR F Vo VS Io IS ε T₁ T₂ ρ₁ ρ₂
      inc π γ lam (fun w => H1 (Dat w).ρTl') (fun w => clsRow (Dat w) (vD w)) pr Fs Im cT I γQ ζ ζO nQ u
      (inputs_from_selmer_inj O R' Tc (Ω ≃ₐ[Ek] Ω) (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ ι colIdx (decs Ek Aw) j e' Kc k0 ℓ what₂ s L tens v₁ κ V
        iL qV Ff κz (HcG 0) (HcR 0) (F 0) Vo Io ε T₁ T₂ ρ₁ ρ₂ inc π γ lam (fun w => H1 (Dat w).ρTl')
        (fun w => clsRow (Dat w) (vD w)) pr Fs Im
        ⟨a1, a2, fun l a g hg => hKc3 l a g hg, a4, ⟨c1', c2, c3, c4, c5, c6, c7, c8⟩, hcont 0, a7, a8,
          a9, a10, a11, hRowsA, a13⟩)
      (fun c hc2 => ⟨(hC c hc2).1, hC' c hc2⟩)
      ⟨fun l g hg m => hk04 l g hg m, o4, o5, o6, hOneA⟩
  · show IsDiscreteValuationRing.addVal O δO = _
    rw [hδO]
    exact hv1
  · show IsDiscreteValuationRing.addVal O δO ≤ _
    rw [hδO]
    exact hv2

end Formalism.MainNotions.N.K
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KHf

open Module TensorProduct Formalism.WeaklyAdmissibleFiltrations

section Onto

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [IsDomain O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem toLLK_surj : Function.Surjective (Br.toLLK Bw) := by
  intro y
  have halg : IsAlgebraic ℚ_[l] y := Algebra.IsAlgebraic.isAlgebraic y
  have halg' : IsAlgebraic ℤ_[l] y := (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] (Br.LLw Bw)).mpr halg
  obtain ⟨n, hn, hint⟩ := IsAlgebraic.exists_integral_multiple halg'
  let x : Formalism.BasicNotions.Loc.OL Bw.LL := ⟨n • y, hint⟩
  have hn' : algebraMap ℤ_[l] (Br.LLw Bw) n ≠ 0 := by
    intro h0
    apply hn
    have : algebraMap ℚ_[l] (Br.LLw Bw) (algebraMap ℤ_[l] ℚ_[l] n) = 0 := by
      rw [← IsScalarTower.algebraMap_apply]; exact h0
    have h2 := (algebraMap ℚ_[l] (Br.LLw Bw)).injective (this.trans (map_zero _).symm)
    exact (IsFractionRing.injective ℤ_[l] ℚ_[l]) (h2.trans (map_zero _).symm)
  refine ⟨algebraMap O (FractionRing O) (Bw.eO.symm x) /
    algebraMap O (FractionRing O) (Bw.eO.symm (algebraMap ℤ_[l] (Formalism.BasicNotions.Loc.OL Bw.LL) n)), ?_⟩
  rw [map_div₀, Br.toLLK_alg, Br.toLLK_alg, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  rw [← IsScalarTower.algebraMap_apply, div_eq_iff hn']
  change n • y = y * _
  rw [Algebra.smul_def, mul_comm]

def eK : FractionRing O ≃+* Br.LLw Bw :=
  RingEquiv.ofBijective (Br.toLLK Bw) ⟨(Br.toLLK Bw).injective, toLLK_surj Bw⟩

theorem eK_apply (k : FractionRing O) : eK Bw k = Br.toLLK Bw k := rfl

end Onto

section Tr

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] (e : FractionRing O ≃+* LL)

def TrV (_e : FractionRing O ≃+* LL) (V : Type) : Type := V

variable {V : Type} [AddCommGroup V] [Module (FractionRing O) V]

instance : AddCommGroup (TrV e V) := ‹AddCommGroup V›

instance instModLL : Module LL (TrV e V) := Module.compHom V e.symm.toRingHom

theorem smulLL_def (c : LL) (v : TrV e V) : c • v = (e.symm c • (show V from v) : V) := rfl

variable {Qp : Type} [Field Qp] [Algebra Qp LL]

instance instModQp : Module Qp (TrV e V) := Module.compHom V (e.symm.toRingHom.comp (algebraMap Qp LL))

instance : IsScalarTower Qp LL (TrV e V) :=
  ⟨fun c a v => by
    show (e.symm (c • a)) • (show V from v) = (e.symm (algebraMap Qp LL c)) • ((e.symm a) • (show V from v))
    rw [Algebra.smul_def, map_mul, mul_smul]⟩

variable [TopologicalSpace LL]

instance instTop : TopologicalSpace (TrV e V) := moduleTopology LL (TrV e V)

instance : IsModuleTopology LL (TrV e V) := ⟨rfl⟩

instance : ContinuousAdd (TrV e V) := IsModuleTopology.toContinuousAdd LL (TrV e V)

instance : ContinuousSMul LL (TrV e V) := IsModuleTopology.toContinuousSMul LL (TrV e V)

instance : ContinuousNeg (TrV e V) := ⟨by
  have h : (fun v : TrV e V => -v) = fun v => (-1 : LL) • v := by
    funext v
    rw [neg_one_smul]
  rw [h]
  exact continuous_const_smul _⟩

instance : IsTopologicalAddGroup (TrV e V) where

variable [Module O V] [IsScalarTower O (FractionRing O) V]
  {W : Type} [AddCommGroup W] [Module (FractionRing O) W] [Module O W] [IsScalarTower O (FractionRing O) W]

theorem smulK (f : V →ₗ[O] W) (k : FractionRing O) (v : V) : f (k • v) = k • f v :=
  (LinearMap.extendScalarsOfIsLocalization (nonZeroDivisors O) (FractionRing O) f).map_smul k v

def trL (f : V →ₗ[O] W) : TrV e V →ₗ[LL] TrV e W where
  toFun v := (f v : W)
  map_add' u v := f.map_add u v
  map_smul' c v := smulK f (e.symm c) v

theorem trL_apply (f : V →ₗ[O] W) (v : TrV e V) : trL e f v = (f v : W) := rfl

theorem trL_cont (f : V →ₗ[O] W) : Continuous (trL e f) :=
  IsModuleTopology.continuous_of_linearMap (trL e f)

variable {Γ G : Type} [Group Γ] [Group G]

def repL (ρ : Representation O Γ V) (ι : G →* Γ) : Representation LL G (TrV e V) where
  toFun g := trL e (ρ (ι g))
  map_one' := LinearMap.ext fun v => by
    show ρ (ι 1) v = v
    simp only [map_one]
    rfl
  map_mul' g h := LinearMap.ext fun v => by
    show ρ (ι (g * h)) v = ρ (ι g) (ρ (ι h) v)
    simp only [map_mul]
    rfl

theorem repL_apply (ρ : Representation O Γ V) (ι : G →* Γ) (g : G) (v : TrV e V) :
    repL e ρ ι g v = (ρ (ι g) v : V) := rfl

variable [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR)

def finZ (ρ : Representation O Γ V) (ι : G →* Γ) : Submodule (FractionRing O) (Γ → V) where
  carrier := {c | (fun g => (c (ι g) : TrV e V)) ∈ finiteCocycles PD (repL e ρ ι)}
  zero_mem' := (finiteCocycles PD (repL e ρ ι)).zero_mem
  add_mem' ha hb := (finiteCocycles PD (repL e ρ ι)).add_mem ha hb
  smul_mem' k c hc := by
    have h := (finiteCocycles PD (repL e ρ ι)).smul_mem (e k) hc
    have heq : (show G → TrV e V from fun g => (k • c) (ι g)) =
        e k • (show G → TrV e V from fun g => c (ι g)) := by
      funext g
      show k • c (ι g) = e.symm (e k) • c (ι g)
      rw [RingEquiv.symm_apply_apply]
    show (show G → TrV e V from fun g => (k • c) (ι g)) ∈ finiteCocycles PD (repL e ρ ι)
    rw [heq]
    exact h

theorem mem_finZ (ρ : Representation O Γ V) (ι : G →* Γ) (c : Γ → V) :
    c ∈ finZ e PD ρ ι ↔ (fun g => (c (ι g) : TrV e V)) ∈ finiteCocycles PD (repL e ρ ι) := Iff.rfl

theorem finZ_map (ρ : Representation O Γ V) (ρ' : Representation O Γ W) (ι : G →* Γ) (f : V →ₗ[O] W)
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (c : Γ → V) (hc : c ∈ finZ e PD ρ ι) :
    (fun g => f (c g)) ∈ finZ e PD ρ' ι :=
  (cocyclesFunctorial_holds G Qp K₀ Kk B BdR PD LL (TrV e V) (TrV e W) (repL e ρ ι) (repL e ρ' ι) (trL e f)
    (trL_cont e f) (fun g v => hf (ι g) v) _).2 hc

end Tr

section Cls

variable {O : Type} [CommRing O] [IsDomain O] {LL : Type} [Field LL] [TopologicalSpace LL]
  (e : FractionRing O ≃+* LL) {Qp : Type} [Field Qp] [Algebra Qp LL]
  {Γ G : Type} [Group Γ] [Group G] [TopologicalSpace G] {K₀ Kk B BdR : Type} [Field K₀] [Field Kk]
    [Algebra Qp K₀] [Algebra Qp Kk] [Algebra K₀ Kk] [IsScalarTower Qp K₀ Kk]
    [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra Kk BdR] [IsScalarTower Qp Kk BdR]
    [IsScalarTower K₀ Kk BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ Kk B BdR) (ι : G →* Γ)
  {V : Type} [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
  (ρ : Representation O Γ V)
  {M : Type} [AddCommGroup M] [Module O M]

def finPre (φ : M →ₗ[O] V) : Submodule O (Γ → M) :=
  ((finZ e PD ρ ι).restrictScalars O).comap (LinearMap.compLeft φ Γ)

def finiteClassesModel (ρM : Representation O Γ M) (φ : M →ₗ[O] V) : Submodule O (Formalism.NG.H1z ρM) :=
  ((finPre e PD ι ρ φ).comap (Formalism.NG.coZ1s ρM).subtype).map (Submodule.mkQ _)

def finiteClassesContinuous [TopologicalSpace Γ] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M]
    (ρM : Representation O Γ M) (φ : M →ₗ[O] V) : Submodule O (ReciprocityTheory.Gal.H1 ρM) :=
  ((finPre e PD ι ρ φ).comap (ReciprocityTheory.Gal.Z1 ρM).subtype).map (Submodule.mkQ _)

abbrev MK (M : Type) [AddCommGroup M] [Module O M] : Type := LocalizedModule (nonZeroDivisors O) M

abbrev mkK : M →ₗ[O] MK (O := O) M := LocalizedModule.mkLinearMap (nonZeroDivisors O) M

def locRep (ρM : Representation O Γ M) : Representation O Γ (MK (O := O) M) where
  toFun g := (LocalizedModule.map (nonZeroDivisors O) (ρM g)).restrictScalars O
  map_one' := LinearMap.ext fun x => by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      show LocalizedModule.map (nonZeroDivisors O) (ρM 1) (LocalizedModule.mk m s) = LocalizedModule.mk m s
      rw [LocalizedModule.map_mk, map_one]
      rfl
  map_mul' g h := LinearMap.ext fun x => by
    induction x using LocalizedModule.induction_on with
    | h m s =>
      show LocalizedModule.map (nonZeroDivisors O) (ρM (g * h)) (LocalizedModule.mk m s) =
        LocalizedModule.map (nonZeroDivisors O) (ρM g)
          (LocalizedModule.map (nonZeroDivisors O) (ρM h) (LocalizedModule.mk m s))
      rw [LocalizedModule.map_mk, LocalizedModule.map_mk, LocalizedModule.map_mk, map_mul]
      rfl

theorem locRep_mkK (ρM : Representation O Γ M) (g : Γ) (m : M) :
    locRep ρM g (mkK m) = mkK (ρM g m) :=
  LocalizedModule.map_mk _ _ _ _

def finLoc (ρM : Representation O Γ M) : Submodule O (Γ → M) :=
  finPre e PD ι (locRep ρM) mkK

def finiteClassesContinuousLattice [TopologicalSpace Γ] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M]
    (ρM : Representation O Γ M) : Submodule O (ReciprocityTheory.Gal.H1 ρM) :=
  finiteClassesContinuous e PD ι (locRep ρM) ρM mkK

theorem isUnit_end (s : nonZeroDivisors O) :
    IsUnit ((algebraMap O (Module.End O V)) (s : O)) := by
  have hs : algebraMap O (FractionRing O) (s : O) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
  rw [Module.End.isUnit_iff]
  constructor
  · intro a b hab
    have hab' : algebraMap O (FractionRing O) (s : O) • a = algebraMap O (FractionRing O) (s : O) • b := by
      simpa [algebraMap_smul] using hab
    exact smul_right_injective V hs hab'
  · intro y
    refine ⟨(algebraMap O (FractionRing O) (s : O))⁻¹ • y, ?_⟩
    show (s : O) • ((algebraMap O (FractionRing O) (s : O))⁻¹ • y) = y
    rw [← algebraMap_smul (FractionRing O) (s : O), smul_smul, mul_inv_cancel₀ hs, one_smul]

def liftK (f : M →ₗ[O] V) : MK (O := O) M →ₗ[O] V :=
  IsLocalizedModule.lift (nonZeroDivisors O) mkK f (isUnit_end (V := V))

theorem liftK_mkK (f : M →ₗ[O] V) (m : M) : liftK f (mkK m) = f m :=
  IsLocalizedModule.lift_apply _ _ _ _ _

theorem liftK_equiv (ρM : Representation O Γ M) (f : M →ₗ[O] V) (hf : ∀ g m, f (ρM g m) = ρ g (f m))
    (g : Γ) (x : MK (O := O) M) : liftK f (locRep ρM g x) = ρ g (liftK f x) := by
  have h : (liftK f) ∘ₗ (locRep ρM g) = (ρ g) ∘ₗ (liftK f) := by
    apply IsLocalizedModule.ext (nonZeroDivisors O) (mkK (O := O) (M := M)) (isUnit_end (V := V))
    refine LinearMap.ext fun m => ?_
    simp only [LinearMap.comp_apply]
    rw [locRep_mkK, liftK_mkK, liftK_mkK, hf]
  exact congrArg (fun F : MK (O := O) M →ₗ[O] V => F x) h

theorem finLoc_map (ρM : Representation O Γ M) (f : M →ₗ[O] V) (hf : ∀ g m, f (ρM g m) = ρ g (f m))
    (c : Γ → M) (hc : c ∈ finLoc e PD ι ρM) : (fun g => f (c g)) ∈ finZ e PD ρ ι := by
  have h := finZ_map e PD (locRep ρM) ρ ι (liftK f) (liftK_equiv ρ ρM f hf) _ hc
  have e2 : (fun g => f (c g)) = (fun g => liftK f (mkK (c g))) := by
    funext g
    rw [liftK_mkK]
  rw [e2]
  exact h

end Cls

section Rec

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

abbrev Γn (n : ℕ) : Subgroup (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) := Formalism.RepresentationBoundsCohomology.FIN.decs D.host.E (K.Aw i dc) n

def fZ (n : ℕ) {V : Type} [AddCommGroup V] [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V) :
    Submodule (FractionRing (D.nd.O i)) (↥(Γn i dc n) → V) :=
  if hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i) then
    finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) ρ (Br.iota D.nbr i _ hn)
  else ⊤

section Gen

variable {n : ℕ} {V : Type} [AddCommGroup V] [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V)
  {M : Type} [AddCommGroup M] [Module (D.nd.O i) M]

theorem fZ_pos (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    fZ i dc n ρ = finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) ρ (Br.iota D.nbr i _ hn) :=
  dite_eq_left hn

variable (n) in
def fPre (φ : M →ₗ[D.nd.O i] V) : Submodule (D.nd.O i) (↥(Γn i dc n) → M) :=
  ((fZ i dc n ρ).restrictScalars (D.nd.O i)).comap (LinearMap.compLeft φ _)

variable (n) in
def finiteClassesCocyclesMap (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M) (φ : M →ₗ[D.nd.O i] V) :
    Submodule (D.nd.O i) (Formalism.NG.H1z ρM) :=
  ((fPre i dc n ρ φ).comap (Formalism.NG.coZ1s ρM).subtype).map (Submodule.mkQ _)

variable (n) in
def finiteClassesContinuousMap [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul (D.nd.O i) M]
    (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M) (φ : M →ₗ[D.nd.O i] V) :
    Submodule (D.nd.O i) (ReciprocityTheory.Gal.H1 ρM) :=
  ((fPre i dc n ρ φ).comap (ReciprocityTheory.Gal.Z1 ρM).subtype).map (Submodule.mkQ _)

end Gen

section GenL

variable (n : ℕ) {M : Type} [AddCommGroup M] [Module (D.nd.O i) M]

def finiteClassesLocalModel (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M) : Submodule (D.nd.O i) (Formalism.NG.H1z ρM) :=
  finiteClassesCocyclesMap i dc n (locRep ρM) ρM mkK

def finiteClassesContinuousLocal [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul (D.nd.O i) M]
    (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M) : Submodule (D.nd.O i) (ReciprocityTheory.Gal.H1 ρM) :=
  finiteClassesContinuousMap i dc n (locRep ρM) ρM mkK

end GenL

end Rec

section Dict

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem smulComm_O {A V : Type} [Ring A] [AddCommGroup V] [Module A V] [Module (FractionRing (D.nd.O i)) V]
    [SMulCommClass A (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] : SMulCommClass A (D.nd.O i) V :=
  ⟨fun a c v => by
    rw [← algebraMap_smul (FractionRing (D.nd.O i)) c v, ← algebraMap_smul (FractionRing (D.nd.O i)) c (a • v),
      smul_comm]⟩

section Rows

variable [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [IsDiscreteValuationRing (D.nd.O i)]
  (VT VT' : ℕ → Type)
  [∀ w, AddCommGroup (VT w)] [∀ w, Module (D.nd.O i) (VT w)] [∀ w, TopologicalSpace (VT w)]
  [∀ w, IsTopologicalAddGroup (VT w)] [∀ w, ContinuousSMul (D.nd.O i) (VT w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT w)]
  [∀ w, AddCommGroup (VT' w)] [∀ w, Module (D.nd.O i) (VT' w)] [∀ w, TopologicalSpace (VT' w)]
  [∀ w, IsTopologicalAddGroup (VT' w)] [∀ w, ContinuousSMul (D.nd.O i) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)] [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  (Dat : ∀ w, Formalism.RepresentationBoundsCohomology.LOC.LatData (D.nd.O i) ↥(Γn i dc w) (VT w) (VT' w))
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

def HfW (w : ℕ) : Submodule (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT) :=
  Submodule.span (FractionRing (D.nd.O i))
    (finiteClassesContinuousMap i dc w (Dat w).ρT (Dat w).ρT LinearMap.id : Set (ReciprocityTheory.Gal.H1 (Dat w).ρT))

def Hf₂ (w : ℕ) : Submodule (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT') :=
  Submodule.span (FractionRing (D.nd.O i))
    (finiteClassesContinuousMap i dc w (Dat w).ρT' (Dat w).ρT' LinearMap.id : Set (ReciprocityTheory.Gal.H1 (Dat w).ρT'))

def Fs (w : ℕ) : Submodule (D.nd.O i) (ReciprocityTheory.Gal.H1 (Dat w).ρTl') :=
  ((Hf₂ i dc VT VT' Dat w).restrictScalars (D.nd.O i)).comap (Dat w).j'

def BKa (w : ℕ) : Prop :=
  ∀ a, a ∈ HfW i dc VT VT' Dat w ↔ ∀ b ∈ Hf₂ i dc VT VT' Dat w, ReciprocityTheory.ChartRestriction.T2.cupFG (Dat w) a b = 0

end Rows

def Hf₁ {T₁ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁] [IsTopologicalAddGroup T₁]
    [ContinuousConstSMul (D.nd.O i) T₁] (ρ₁ : Representation (D.nd.O i) (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) T₁)
    (w : ℕ) : Submodule (D.nd.O i) (ReciprocityTheory.Gal.H1 (resRep ρ₁ (Γn i dc w))) :=
  finiteClassesContinuousLocal i dc w (resRep ρ₁ (Γn i dc w))

section Cols

variable {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

def Ff {L : Type} [AddCommGroup L] [Module R' L] [Module (D.nd.O i) L] [SMulCommClass R' (D.nd.O i) L]
    {V : Type} [AddCommGroup V] [Module R' V] [Module (D.nd.O i) V] [Module (FractionRing (D.nd.O i)) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] [SMulCommClass R' (FractionRing (D.nd.O i)) V]
    (iL : L →ₗ[D.nd.O i] V) (l : K.Col i dc) :
    Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := L) r χ) (Γn i dc (K.colIdx i dc l)))) :=
  haveI := smulComm_O i (A := R') (V := V)
  finiteClassesCocyclesMap i dc (K.colIdx i dc l) (resRep (uRep (D.nd.O i) (M := V) r χ) (Γn i dc (K.colIdx i dc l)))
    (resRep (uRep (D.nd.O i) (M := L) r χ) (Γn i dc (K.colIdx i dc l))) iL

def Hfe₁ {Pe : Type} [AddCommGroup Pe] [Module R' Pe] [Module (D.nd.O i) Pe] [SMulCommClass R' (D.nd.O i) Pe]
    (l : K.Col i dc) :
    Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := Pe) r χ) (Γn i dc (K.colIdx i dc l)))) :=
  finiteClassesLocalModel i dc (K.colIdx i dc l) (resRep (uRep (D.nd.O i) (M := Pe) r χ) (Γn i dc (K.colIdx i dc l)))

def HfE₂ (δO : D.nd.O i) (l : K.Col i dc) :
    Submodule (D.nd.O i)
      (H1z (Representation.trivial (D.nd.O i) ↥(Γn i dc (K.colIdx i dc l)) ↥(Ideal.span {δO}))) :=
  finiteClassesLocalModel i dc (K.colIdx i dc l) (Representation.trivial (D.nd.O i) ↥(Γn i dc (K.colIdx i dc l)) ↥(Ideal.span {δO}))

abbrev evalModO (x' : X') : Module (D.nd.O i) (Formalism.NG.EvalSp (D.nd.O i) d R' x') :=
  Module.compHom _ (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))

end Cols

end Dict

section Cols2

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem evalTower (x' : X') :
    letI := evalModO i (R' := R') x'
    IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (EvalSp (D.nd.O i) d R' x') :=
  letI := evalModO i (R' := R') x'
  ⟨fun a b v => by
    show (a • b) • v = algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) a • (b • v)
    rw [Algebra.smul_def, mul_smul]⟩

theorem evalComm (x' : X') : SMulCommClass R' (FractionRing (D.nd.O i)) (EvalSp (D.nd.O i) d R' x') :=
  ⟨fun a c v => by
    show (Formalism.NG.matEnd (FractionRing (D.nd.O i)) (FractionRing (D.nd.O i)) d (Formalism.NG.evalAt (D.nd.O i) d R' x' a))
        (c • v) = c • (Formalism.NG.matEnd (FractionRing (D.nd.O i)) (FractionRing (D.nd.O i)) d
          (Formalism.NG.evalAt (D.nd.O i) d R' x' a)) v
    exact map_smul _ c v⟩

def repE (x' : X') (n : ℕ) :
    letI := evalModO i (R' := R') x'
    Representation (D.nd.O i) ↥(Γn i dc n) (EvalSp (D.nd.O i) d R' x') :=
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  haveI := evalComm i (R' := R') x'
  haveI := smulComm_O i (A := R') (V := EvalSp (D.nd.O i) d R' x')
  resRep (uRep (D.nd.O i) (M := EvalSp (D.nd.O i) d R' x') r χ) (Γn i dc n)

def Lx (x' : X') (l : K.Col i dc) :
    Submodule (FractionRing (D.nd.O i)) (↥(Γn i dc (K.colIdx i dc l)) → EvalSp (D.nd.O i) d R' x') :=
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  fZ i dc (K.colIdx i dc l) (repE i dc r χ x' (K.colIdx i dc l))

def F0col {V : Type} [AddCommGroup V] [Module (D.nd.O i) V] [Module (FractionRing (D.nd.O i)) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V] {M : Type} [AddCommGroup M] [Module (D.nd.O i) M]
    (n : ℕ) (ρV : Representation (D.nd.O i) ↥(Γn i dc n) V) (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M)
    (qV : V →ₗ[D.nd.O i] M) : Submodule (D.nd.O i) (H1z ρM) :=
  ((((fZ i dc n ρV).restrictScalars (D.nd.O i)).map (LinearMap.compLeft qV _) ⊔ coB1 ρM).comap
    (coZ1s ρM).subtype).map (Submodule.mkQ _)

def Fρ {M : Type} [AddCommGroup M] [Module (D.nd.O i) M] (what₂ : Finset ℕ)
    (ρM : ∀ n, Representation (D.nd.O i) ↥(Γn i dc n) M) (Frow Fcol : ∀ n, Submodule (D.nd.O i) (H1z (ρM n)))
    (n : ℕ) : Submodule (D.nd.O i) (H1z (ρM n)) :=
  if n ∈ what₂ then Frow n else Fcol n

def LiftCol {P Q : ∀ _ : K.Col i dc, Type} [∀ l, AddCommGroup (P l)] [∀ l, Module (D.nd.O i) (P l)]
    [∀ l, AddCommGroup (Q l)] [∀ l, Module (D.nd.O i) (Q l)]
    (Hp : ∀ l, Submodule (D.nd.O i) (P l)) (Hq : ∀ l, Submodule (D.nd.O i) (Q l))
    (g : ∀ l, P l →ₗ[D.nd.O i] Q l) (e' : ℕ → ℕ) : Prop :=
  ∀ l, Formalism.RepresentationBoundsCohomology.JL.LiftO (D.nd.l i) (Hp l) (Hq l) (g l) (e' (K.colIdx i dc l))

def UnrFin (δO : D.nd.O i)
    (uz : ∀ l : K.Col i dc,
      coZ1s (Representation.trivial (D.nd.O i) ↥(Γn i dc (K.colIdx i dc l)) ↥(Ideal.span {δO}))) : Prop :=
  ∀ l, Submodule.mkQ _ (uz l) ∈ HfE₂ i dc δO l

def jK (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (n : ℕ) : ℕ :=
  if hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i) then Br.jW D.loc D.nbr i _ hn ρ π else 0

def DimLx (j : ℕ → ℕ) (x' : X') (l : K.Col i dc) : Prop :=
  Module.rank (FractionRing (D.nd.O i))
      (↥(Lx i dc r χ x' l) ⧸ (LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x')
        r χ (Γn i dc (K.colIdx i dc l)))).comap (Lx i dc r χ x' l).subtype) ≤
    (j (K.colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
      (LinearMap.ker (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x')
        r χ (Γn i dc (K.colIdx i dc l)))) : ℕ)

def FinRhoAt {L : Type} [AddCommGroup L] [Module R' L] [Module (D.nd.O i) L] [SMulCommClass R' (D.nd.O i) L]
    (Ff : ∀ l : K.Col i dc, Submodule (D.nd.O i)
      (H1z (resRep (uRep (D.nd.O i) (M := L) r χ) (Γn i dc (K.colIdx i dc l)))))
    (j : ℕ → ℕ) (κ : ∀ l : K.Col i dc, Fin (j (K.colIdx i dc l)) → (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) → L)
    (κz : ∀ l : K.Col i dc, Fin (j (K.colIdx i dc l)) →
      coZ1s (resRep (uRep (D.nd.O i) (M := L) r χ) (Γn i dc (K.colIdx i dc l))))
    (l : K.Col i dc) : Prop :=
  (∀ a (g : Γn i dc (K.colIdx i dc l)), (κz l a : Γn i dc (K.colIdx i dc l) → L) g = κ l a g) ∧
    (∀ (c : D.nd.O i) z, c ≠ 0 → c • z ∈ Ff l → z ∈ Ff l) ∧
    (∀ a, Submodule.mkQ _ (κz l a) ∈ Ff l) ∧
    (∀ z ∈ Ff l, ∃ (b : Fin (j (K.colIdx i dc l)) → D.nd.O i) (c : D.nd.O i), c ≠ 0 ∧
      c • (z - ∑ a, b a • (Submodule.mkQ _ (κz l a) :
        H1z (resRep (uRep (D.nd.O i) (M := L) r χ) (Γn i dc (K.colIdx i dc l))))) = 0) ∧
    (∀ (b : Fin (j (K.colIdx i dc l)) → D.nd.O i) (c : D.nd.O i), c ≠ 0 →
      c • ∑ a, b a • (Submodule.mkQ _ (κz l a) :
        H1z (resRep (uRep (D.nd.O i) (M := L) r χ) (Γn i dc (K.colIdx i dc l)))) = 0 → b = 0)

end Cols2

section Prf

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) {n : ℕ}
  {V : Type} [AddCommGroup V] [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
  {W : Type} [AddCommGroup W] [Module (FractionRing (D.nd.O i)) W] [Module (D.nd.O i) W]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) W]
  {M : Type} [AddCommGroup M] [Module (D.nd.O i) M]

theorem fZ_map (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V) (ρ' : Representation (D.nd.O i) ↥(Γn i dc n) W)
    (f : V →ₗ[D.nd.O i] W) (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (c : ↥(Γn i dc n) → V)
    (hc : c ∈ fZ i dc n ρ) : (fun g => f (c g)) ∈ fZ i dc n ρ' := by
  by_cases hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)
  · rw [fZ_pos i dc ρ hn] at hc
    rw [fZ_pos i dc ρ' hn]
    exact finZ_map _ _ ρ ρ' _ f hf c hc
  · unfold fZ
    rw [dite_eq_right hn]
    trivial

theorem fLoc_map (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M) (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V)
    (f : M →ₗ[D.nd.O i] V) (hf : ∀ g m, f (ρM g m) = ρ g (f m)) (c : ↥(Γn i dc n) → M)
    (hc : c ∈ fPre i dc n (locRep ρM) mkK) : (fun g => f (c g)) ∈ fZ i dc n ρ := by
  by_cases hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)
  · unfold fPre at hc
    rw [fZ_pos i dc (locRep ρM) hn] at hc
    rw [fZ_pos i dc ρ hn]
    exact finLoc_map _ _ _ ρ ρM f hf c hc
  · unfold fZ
    rw [dite_eq_right hn]
    trivial

def OrbC (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V) : Prop :=
  ∀ hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i), ∀ v : TrV (eK (D.nbr i _ hn)) V,
    Continuous fun g => repL (eK (D.nbr i _ hn)) ρ (Br.iota D.nbr i _ hn) g v

theorem cob_mem_fZ (ρ : Representation (D.nd.O i) ↥(Γn i dc n) V) (h : OrbC i dc ρ) (v : V) :
    (fun g => ρ g v - v) ∈ fZ i dc n ρ := by
  by_cases hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)
  · rw [fZ_pos i dc ρ hn]
    exact coboundaryMap_mem_finiteCocycles (PD := Br.PD D.loc D.nbr i _ hn) (h hn) v
  · unfold fZ
    rw [dite_eq_right hn]
    trivial

end Prf

section PrfRow

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

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
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT)]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

theorem im_le_Fs (w : ℕ) {T₁ T₂ : Type} [AddCommGroup T₁] [Module (D.nd.O i) T₁] [TopologicalSpace T₁]
    [IsTopologicalAddGroup T₁] [ContinuousConstSMul (D.nd.O i) T₁] [AddCommGroup T₂] [Module (D.nd.O i) T₂]
    (ρ₁ : Representation (D.nd.O i) (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) T₁) (π : T₁ →ₗ[D.nd.O i] T₂)
    (vD : T₂ ≃ₗ[D.nd.O i] (Dat w).T') (hpD : Continuous fun t => vD (π t))
    (heD : ∀ g t, vD (π (resRep ρ₁ (Γn i dc w) g t)) = (Dat w).ρTl' g (vD (π t))) :
    (Hf₁ i dc ρ₁ w).map (Formalism.RepresentationBoundsCohomology.FIN.gRow (Dat w) (resRep ρ₁ (Γn i dc w)) π vD hpD heD) ≤
      Fs i dc VT VT' Dat w := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨z, hz, rfl⟩ := hx
  let f : T₁ →ₗ[D.nd.O i] VT' w := (Dat w).T'.subtype ∘ₗ vD.toLinearMap ∘ₗ π
  have hf : ∀ g t, f (resRep ρ₁ (Γn i dc w) g t) = (Dat w).ρT' g (f t) := by
    intro g t
    show (((vD (π (resRep ρ₁ (Γn i dc w) g t)) : (Dat w).T') : VT' w)) = _
    rw [heD]
    rfl
  have hmem := fLoc_map i dc (resRep ρ₁ (Γn i dc w)) (Dat w).ρT' f hf _ hz
  show _ ∈ Hf₂ i dc VT VT' Dat w
  refine Submodule.subset_span ⟨ReciprocityTheory.Gal.cocycles1MapOfEquivariant (Dat w).ρTl' (Dat w).ρT' (Dat w).T'.subtype
    continuous_subtype_val (fun _ _ => rfl)
    (ReciprocityTheory.Gal.cocycles1MapOfEquivariant _ _ (vD.toLinearMap ∘ₗ π) hpD heD z), hmem, rfl⟩

end PrfRow

section PrfCol

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem evalScalar (x' : X') (c : D.nd.O i) (v : EvalSp (D.nd.O i) d R' x') :
    (algebraMap (D.nd.O i) R' c) • v = (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c) • v := by
  funext j
  show ∑ k, (Formalism.NG.evalAt (D.nd.O i) d R' x' (algebraMap (D.nd.O i) R' c)) j k • v k =
    algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) c • v j
  simp [Formalism.NG.evalAt, Matrix.algebraMap_matrix_apply, Finset.sum_ite_eq, Pi.algebraMap_apply]

theorem colD_le_Lx (x' : X') (l : K.Col i dc) :
    letI := evalModO i (R' := R') x'
    haveI := evalTower i (R' := R') x'
    OrbC i dc (repE i dc r χ x' (K.colIdx i dc l)) →
      LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
        (Γn i dc (K.colIdx i dc l))) ≤ Lx i dc r χ x' l := by
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  intro hO
  rintro _ ⟨η, rfl⟩
  exact cob_mem_fZ i dc _ hO η

theorem comp_mem_Lx {P : Type} [AddCommGroup P] [Module R' P] [Module (D.nd.O i) P] [SMulCommClass R' (D.nd.O i) P]
    (hP : ∀ (c : D.nd.O i) (m : P), c • m = (algebraMap (D.nd.O i) R' c) • m) (x' : X') (l : K.Col i dc) :
    letI := evalModO i (R' := R') x'
    haveI := evalTower i (R' := R') x'
    OrbC i dc (repE i dc r χ x' (K.colIdx i dc l)) →
      ∀ (f : P →ₗ[R'] EvalSp (D.nd.O i) d R' x')
        (z : coZ1s (resRep (uRep (D.nd.O i) (M := P) r χ) (Γn i dc (K.colIdx i dc l)))),
        Submodule.mkQ _ z ∈ Hfe₁ i dc r χ (Pe := P) l →
        (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → P) g)) ∈ Lx i dc r χ x' l := by
  letI := evalModO i (R' := R') x'
  haveI := evalTower i (R' := R') x'
  intro hO f z hz
  obtain ⟨y, hy, hyz⟩ := Submodule.mem_map.1 hz
  have hb := (Submodule.Quotient.eq _).1 hyz
  obtain ⟨m, hm⟩ := hb
  let fO : P →ₗ[D.nd.O i] EvalSp (D.nd.O i) d R' x' :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun c m => by
        rw [hP, f.map_smul, evalScalar]
        rfl }
  have hfe : ∀ g m, fO (resRep (uRep (D.nd.O i) (M := P) r χ) (Γn i dc (K.colIdx i dc l)) g m) =
      repE i dc r χ x' (K.colIdx i dc l) g (fO m) := fun g m => f.map_smul _ _
  have h1 := fLoc_map i dc _ (repE i dc r χ x' (K.colIdx i dc l)) fO hfe _ hy
  have h2 := cob_mem_fZ i dc _ hO (f m)
  have heq : (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → P) g)) =
      (fun g => fO ((y : Γn i dc (K.colIdx i dc l) → P) g)) -
        (fun g => repE i dc r χ x' (K.colIdx i dc l) g (f m) - f m) := by
    funext g
    have hg : resRep (uRep (D.nd.O i) (M := P) r χ) (Γn i dc (K.colIdx i dc l)) g m - m =
        (y : Γn i dc (K.colIdx i dc l) → P) g - (z : Γn i dc (K.colIdx i dc l) → P) g := congrFun hm g
    have hz' : (z : Γn i dc (K.colIdx i dc l) → P) g = (y : Γn i dc (K.colIdx i dc l) → P) g -
        (resRep (uRep (D.nd.O i) (M := P) r χ) (Γn i dc (K.colIdx i dc l)) g m - m) := by
      rw [hg]
      abel
    simp only [Pi.sub_apply]
    rw [hz', map_sub, map_sub]
    rw [show f (resRep (uRep (D.nd.O i) (M := P) r χ) (Γn i dc (K.colIdx i dc l)) g m) =
      repE i dc r χ x' (K.colIdx i dc l) g (f m) from hfe g m]
    rfl
  show _ ∈ fZ i dc _ _
  rw [heq]
  exact sub_mem h1 h2

end PrfCol

section PrfKappa

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

end PrfKappa

end Formalism.MainNotions.N.KHf
end
end

namespace PI.UnitaryGroupMassFormula.FinExtTop

section
open PI.FinExtTop Topology Filter

section

variable {O' : Type} [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O']

def fracB (ϖ : O') (i : ℕ) : Submodule O' (FractionRing O') :=
  Submodule.span O' {algebraMap O' (FractionRing O') (ϖ ^ i)}

theorem mem_fracB {ϖ : O'} {i : ℕ} {x : FractionRing O'} :
    x ∈ fracB ϖ i ↔ ∃ c : O', x = algebraMap O' (FractionRing O') (c * ϖ ^ i) := by
  simp only [fracB, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Algebra.smul_def, map_mul]⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [Algebra.smul_def, map_mul]⟩

theorem algebraMap_mem_fracB {ϖ : O'} {i : ℕ} {x : O'} :
    algebraMap O' (FractionRing O') x ∈ fracB ϖ i ↔ ϖ ^ i ∣ x := by
  rw [mem_fracB]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [mul_comm]; exact IsFractionRing.injective O' (FractionRing O') hc⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, by rw [mul_comm]⟩

theorem fracB_anti (ϖ : O') {i j : ℕ} (h : i ≤ j) : fracB ϖ j ≤ fracB ϖ i := by
  intro x hx
  rw [mem_fracB] at hx ⊢
  obtain ⟨c, rfl⟩ := hx
  exact ⟨c * ϖ ^ (j - i), by rw [mul_assoc, ← pow_add, Nat.sub_add_cancel h]⟩

theorem exists_pow_mul_mem {ϖ : O'} (hϖ : Irreducible ϖ) (a : FractionRing O') :
    ∃ n : ℕ, ∃ c : O', algebraMap O' (FractionRing O') (ϖ ^ n) * a =
      algebraMap O' (FractionRing O') c := by
  obtain ⟨⟨x, y⟩, hxy⟩ := IsLocalization.surj (nonZeroDivisors O') a
  have hy : (y : O') ≠ 0 := nonZeroDivisors.ne_zero y.2
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  refine ⟨n, x * ↑u⁻¹, ?_⟩
  have hy' : algebraMap O' (FractionRing O') (y : O') =
      algebraMap O' (FractionRing O') (↑u) * algebraMap O' (FractionRing O') (ϖ ^ n) := by
    rw [hu, map_mul]
  have hu1 : algebraMap O' (FractionRing O') (↑u) * algebraMap O' (FractionRing O') (↑u⁻¹) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hxy' : a * algebraMap O' (FractionRing O') (y : O') = algebraMap O' (FractionRing O') x := hxy
  rw [map_mul, ← hxy']
  linear_combination (-(a * algebraMap O' (FractionRing O') (↑u⁻¹))) * hy' +
    (-(algebraMap O' (FractionRing O') (ϖ ^ n) * a)) * hu1

theorem fracB_basis {ϖ : O'} (hϖ : Irreducible ϖ) : SubmodulesRingBasis (fracB ϖ) := by
  constructor
  · intro i j
    exact ⟨max i j, le_inf (fracB_anti ϖ (le_max_left _ _)) (fracB_anti ϖ (le_max_right _ _))⟩
  · intro a i
    obtain ⟨n, c, hc⟩ := exists_pow_mul_mem hϖ a
    refine ⟨i + n, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨d, rfl⟩ := mem_fracB.1 hx
    refine mem_fracB.2 ⟨c * d, ?_⟩
    have e : algebraMap O' (FractionRing O') (d * ϖ ^ (i + n)) =
        algebraMap O' (FractionRing O') (d * ϖ ^ i) * algebraMap O' (FractionRing O') (ϖ ^ n) := by
      rw [← map_mul, pow_add, mul_assoc]
    show a * _ = _
    rw [e, mul_comm (algebraMap O' (FractionRing O') (d * ϖ ^ i)), ← mul_assoc, mul_comm a, hc,
      ← map_mul]
    congr 1
    ring
  · intro i
    refine ⟨i, ?_⟩
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := mem_fracB.1 hx
    obtain ⟨d, rfl⟩ := mem_fracB.1 hy
    exact mem_fracB.2 ⟨c * d * ϖ ^ i, by show _ * _ = _; rw [← map_mul]; congr 1; ring⟩

end
end

section
open PI.FinExtTop

theorem torsionFree_pi_matrix (O' : Type) [CommRing O'] [IsDomain O'] (X' d : Type) [Fintype d]
    [DecidableEq d] : Module.IsTorsionFree O' (X' → Matrix d d (FractionRing O')) where
  isSMulRegular r hr f g h := by
    have hr0 : algebraMap O' (FractionRing O') r ≠ 0 := by
      intro h0
      exact hr.ne_zero ((IsFractionRing.injective O' (FractionRing O')).eq_iff.1
        (h0.trans (map_zero _).symm))
    have h' : algebraMap O' (FractionRing O') r • f = algebraMap O' (FractionRing O') r • g := by
      simpa only [algebraMap_smul] using h
    exact ((IsUnit.mk0 _ hr0).smul_left_cancel).1 h'
end

end PI.UnitaryGroupMassFormula.FinExtTop

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

set_option linter.style.haveILetI false

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.K.Topo

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.NG (uElt)

section Gen

variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def unif : O := Classical.choose (IsDiscreteValuationRing.exists_irreducible O)

theorem unif_irr : Irreducible (unif O) := Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible O)

@[reducible] def fracTopology : TopologicalSpace (FractionRing O) :=
  (PI.UnitaryGroupMassFormula.FinExtTop.fracB_basis (unif_irr O)).topology

theorem fracTop_ring : @IsTopologicalRing (FractionRing O) (fracTopology O) _ :=
  (PI.UnitaryGroupMassFormula.FinExtTop.fracB_basis (unif_irr O)).toRing_subgroups_basis.toRingFilterBasis.isTopologicalRing

theorem fracTop_addGroup : @IsTopologicalAddGroup (FractionRing O) (fracTopology O) _ := by
  letI := fracTopology O
  haveI := fracTop_ring O
  infer_instance

section TopO

variable [TopologicalSpace O]

theorem algebraMap_openEmb (hA : IsAdic (IsLocalRing.maximalIdeal O)) :
    @Topology.IsOpenEmbedding O (FractionRing O) _ (fracTopology O) (algebraMap O (FractionRing O)) := by
  letI := fracTopology O
  have hm : ∀ n : ℕ, ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) = {x | unif O ^ n ∣ x} := by
    intro n
    ext x
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer (unif O)).1 (unif_irr O), Ideal.span_singleton_pow,
      SetLike.mem_coe, Ideal.mem_span_singleton]
    rfl
  have hB := PI.UnitaryGroupMassFormula.FinExtTop.fracB_basis (unif_irr O)
  have hR := hB.toRing_subgroups_basis
  set f := algebraMap O (FractionRing O) with hf
  have hnK := hR.hasBasis_nhds
  have hnO := hA.hasBasis_nhds
  have hcont : Continuous f := by
    rw [continuous_iff_continuousAt]
    intro x
    refine ((hnO x).tendsto_iff (hnK (f x))).2 fun i _ => ⟨i, trivial, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    rw [hm] at hz
    show f (x + z) - f x ∈ PI.UnitaryGroupMassFormula.FinExtTop.fracB (unif O) i
    rw [map_add (f := _), add_sub_cancel_left]
    exact PI.UnitaryGroupMassFormula.FinExtTop.algebraMap_mem_fracB.2 hz
  have hopen : IsOpenMap f := by
    refine IsOpenMap.of_nhds_le fun x => ?_
    refine Filter.le_map fun s hs => ?_
    obtain ⟨n, -, hn⟩ := (hnO x).mem_iff.1 hs
    refine Filter.mem_of_superset ((hnK (f x)).mem_of_mem (i := n) trivial) ?_
    intro b hb
    obtain ⟨c, hc⟩ := PI.UnitaryGroupMassFormula.FinExtTop.mem_fracB.1 (show b - f x ∈ PI.UnitaryGroupMassFormula.FinExtTop.fracB (unif O) n from hb)
    refine ⟨x + c * unif O ^ n, hn ⟨c * unif O ^ n, ?_, rfl⟩, ?_⟩
    · rw [hm]
      exact Dvd.intro_left c rfl
    · rw [map_add (f := _), ← hc, add_sub_cancel]
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont
    (IsFractionRing.injective O (FractionRing O)) hopen

theorem fracTop_smul (hA : IsAdic (IsLocalRing.maximalIdeal O)) :
    @ContinuousSMul O (FractionRing O) _ _ (fracTopology O) := by
  letI := fracTopology O
  haveI := fracTop_ring O
  exact continuousSMul_of_algebraMap O (FractionRing O) (algebraMap_openEmb O hA).continuous

theorem fracTop_open (hA : IsAdic (IsLocalRing.maximalIdeal O)) : @FracTop O _ _ (fracTopology O) :=
  @FracTop.mk O _ _ (fracTopology O) (algebraMap_openEmb O hA)

variable {X' d : Type} [Fintype d] [DecidableEq d]

@[reducible] def rTopology (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) : TopologicalSpace R' :=
  moduleTopology O R'

theorem rTop_isModuleTopology (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) :
    letI := rTopology O R'; IsModuleTopology O R' :=
  letI := rTopology O R'; ⟨rfl⟩

theorem rTop_ring (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsTopologicalRing O]
    (hfin : Module.Finite O R') : @IsTopologicalRing R' (rTopology O R') _ := by
  letI := rTopology O R'
  haveI := rTop_isModuleTopology O R'
  exact IsModuleTopology.isTopologicalRing O R'

theorem rTop_addGroup (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsTopologicalRing O]
    (hfin : Module.Finite O R') : @IsTopologicalAddGroup R' (rTopology O R') _ := by
  letI := rTopology O R'
  haveI := rTop_ring O R' hfin
  infer_instance

theorem rTop_mul (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsTopologicalRing O]
    (hfin : Module.Finite O R') : @ContinuousMul R' (rTopology O R') _ := by
  letI := rTopology O R'
  haveI := rTop_ring O R' hfin
  infer_instance

theorem rTop_smul (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsTopologicalRing O] :
    letI := rTopology O R'; ContinuousSMul O R' := by
  letI := rTopology O R'
  haveI := rTop_isModuleTopology O R'
  exact IsModuleTopology.toContinuousSMul O R'

theorem rTop_constSMul (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsTopologicalRing O] :
    letI := rTopology O R'; ContinuousConstSMul O R' := by
  letI := rTopology O R'
  haveI := rTop_smul O R'
  exact ContinuousSMul.continuousConstSMul

theorem rTop_fgTop (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) [IsTopologicalRing O] [T2Space O]
    (hfin : Module.Finite O R') : letI := rTopology O R'; IsFGTop O R' := by
  letI := rTopology O R'
  haveI := rTop_isModuleTopology O R'
  haveI := rTop_ring O R' hfin
  haveI := rTop_smul O R'
  have _ := PI.UnitaryGroupMassFormula.FinExtTop.torsionFree_pi_matrix O X' d
  have _ : Module.IsTorsionFree O R' := inferInstance
  have _ : Module.Free O R' := Module.free_of_finite_type_torsion_free'
  let b := Module.Free.chooseBasis O R'
  have hc : Continuous b.equivFun := IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap
  have _ : T2Space R' := T2Space.of_injective_continuous b.equivFun.injective hc
  exact ⟨hfin, inferInstance, inferInstance⟩

end TopO

theorem finite_of_int {X' d : Type} [Fintype d] [DecidableEq d] [Finite X'] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    (hint : ∀ a ∈ R', ∀ x' i j, ∃ c : O, algebraMap O (FractionRing O) c = a x' i j) : Module.Finite O R' := by
  let L : (X' → d → d → O) →ₗ[O] (X' → Matrix d d (FractionRing O)) :=
    { toFun := fun F x' => Matrix.of fun i j => algebraMap O (FractionRing O) (F x' i j)
      map_add' := fun F F' => by funext x'; ext i j; simp
      map_smul' := fun c F => by funext x'; ext i j; simp [Algebra.smul_def] }
  have hle : Subalgebra.toSubmodule R' ≤ LinearMap.range L := by
    intro a ha
    choose F hF using hint a ha
    exact ⟨F, by funext x'; ext i j; exact hF x' i j⟩
  haveI : IsNoetherian O (LinearMap.range L) := inferInstance
  haveI h1 : IsNoetherian O (Subalgebra.toSubmodule R') := isNoetherian_of_le hle
  haveI h2 : IsNoetherian O R' := h1
  infer_instance

end Gen

section Ring

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {X d G : Type} [Finite X]
  [Fintype d] [DecidableEq d] [Group G] {t : ℕ} {bl : d → Fin (t + 1)} {T : Subalgebra O (X → O)}
  {r₀ : G →* (X → Matrix d d O)} {π : X} {χ₁ ε : G →* Oˣ} {g₀ : G} {eB e₁ s : X → Matrix d d O}
  {Dd : RingData O X d G t bl}

theorem finite_X' (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s Dd) : Finite Dd.X' := by
  obtain ⟨h1, h2, -⟩ := hD
  let ι := algebraMap O (FractionRing O)
  let P : X → Polynomial (FractionRing O) := fun x => Formalism.RepresentationBoundsCohomology.ringDataObjects.blockPoly ((eB x).map ι)
    ((eB x * r₀ g₀ x * eB x + s x).map ι)
  let S : Set O := {a | ∃ x, ι a ∈ (P x).roots}
  have hS : S.Finite := by
    have : S ⊆ ⋃ x, ι ⁻¹' ((P x).roots.toFinset : Set (FractionRing O)) := by
      rintro a ⟨x, hx⟩
      exact Set.mem_iUnion.2 ⟨x, by simpa using hx⟩
    refine Set.Finite.subset (Set.finite_iUnion fun x => ?_) this
    exact Set.Finite.preimage (IsFractionRing.injective O (FractionRing O)).injOn (Finset.finite_toSet _)
  haveI : Finite S := hS.to_subtype
  have hmem : ∀ (y : Dd.X') (i : Fin t), ((Dd.rr i : Dd.X' → O) y) ∈ S := by
    intro y i
    refine ⟨Dd.p y, ?_⟩
    have hy : P (Dd.p y) = ∏ j ∈ Finset.range t, (Polynomial.X - Polynomial.C (ι ((Dd.rr j : Dd.X' → O) y))) := h1 y
    rw [Polynomial.mem_roots', hy]
    refine ⟨(Polynomial.monic_prod_of_monic _ _ fun j _ => Polynomial.monic_X_sub_C _).ne_zero, ?_⟩
    rw [Polynomial.IsRoot, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_range.2 i.2) (by simp)
  let f : Dd.X' → X × (Fin t → S) := fun y => (Dd.p y, fun i => ⟨(Dd.rr i : Dd.X' → O) y, hmem y i⟩)
  refine Finite.of_injective f fun y y' h => ?_
  have hp : Dd.p y = Dd.p y' := congrArg (fun z => z.1) h
  have hr : ∀ i : Fin t, (Dd.rr i : Dd.X' → O) y = (Dd.rr i : Dd.X' → O) y' :=
    fun i => congrArg (fun z => ((z.2 i : S) : O)) h
  obtain ⟨z, -, hz⟩ := h2 (Dd.p y) (fun i => (Dd.rr i : Dd.X' → O) y) (h1 y)
  have e1 := hz y ⟨rfl, fun i _ => rfl⟩
  have e2 := hz y' ⟨hp.symm, fun i hi => (hr ⟨i, hi⟩).symm⟩
  rw [e1, e2]

theorem int_R' (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s Dd) :
    ∀ a ∈ Dd.R', ∀ x' i j, ∃ c : O, algebraMap O (FractionRing O) c = a x' i j := by
  obtain ⟨-, -, -, -, -, -, h7, h8, -⟩ := hD
  intro a ha x' i j
  obtain ⟨S, c, -, rfl⟩ := (h8 a).1 ha
  refine ⟨∑ g ∈ S, c g x' * r₀ g (Dd.p x') i j, ?_⟩

  simp only [Finset.sum_apply, Matrix.sum_apply, map_sum, map_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  have := h7 g x'
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_coe, Function.comp_apply] at *
  rw [Matrix.smul_apply, smul_eq_mul]
  congr 1
  show _ = ((Dd.r g : Dd.R') : Dd.X' → Matrix d d (FractionRing O)) x' i j
  rw [this, Matrix.map_apply]

theorem finite_R' (hD : RingDef O T r₀ π χ₁ ε g₀ eB e₁ s Dd) : Module.Finite O Dd.R' := by
  haveI := finite_X' hD
  exact finite_of_int O Dd.R' (int_R' hD)

end Ring

section Entries

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O]
  [TopologicalSpace (FractionRing O)] [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]

theorem t2Space_fractionRing_of_padicCoeff (ℓ : ℕ) (hO : PadicCoeff ℓ O) (hF : FracTop O) : T2Space (FractionRing O) := by
  have := hO.t2
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x hx
  by_cases hxr : x ∈ Set.range (algebraMap O (FractionRing O))
  · obtain ⟨c, rfl⟩ := hxr
    have hc : c ≠ 0 := by rintro rfl; exact hx (map_zero _)
    refine ⟨algebraMap O (FractionRing O) '' {c}ᶜ, ?_, ?_⟩
    · have hopen : IsOpen (algebraMap O (FractionRing O) '' {c}ᶜ) :=
        hF.emb.isOpenMap _ isOpen_compl_singleton
      exact hopen.mem_nhds ⟨0, fun h => hc (h.symm), map_zero _⟩
    · rintro ⟨c', hc', he⟩
      exact hc' (hF.emb.injective he)
  · exact ⟨Set.range (algebraMap O (FractionRing O)), hF.emb.isOpen_range.mem_nhds ⟨0, map_zero _⟩, hxr⟩

variable {X' d : Type} [Fintype d] [DecidableEq d]

theorem continuous_of_entries (ℓ : ℕ) (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
    [TopologicalSpace R'] [IsTopologicalAddGroup R'] (hO : PadicCoeff ℓ O) (hF : FracTop O)
    (hR : IsFGTop O R') {G : Type} [TopologicalSpace G] (u : G → R')
    (hu : ∀ x' a b, Continuous fun g => ((u g : R') : X' → Matrix d d (FractionRing O)) x' a b) :
    Continuous u := by
  have := hO.compact
  have := hR.t2
  have := hR.csmul
  have := hR.fg
  have := t2Space_fractionRing_of_padicCoeff ℓ hO hF
  haveI : ContinuousAdd R' := ‹IsTopologicalAddGroup R'›.toContinuousAdd
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O R'
  have hfc : Continuous f := LinearMap.continuous_on_pi f
  have hq : Topology.IsQuotientMap f := Topology.IsQuotientMap.of_surjective_continuous hf hfc
  haveI : CompactSpace R' := Function.Surjective.compactSpace hfc hf
  have hval : Continuous (fun a : R' => (a : X' → Matrix d d (FractionRing O))) := by
    rw [hq.continuous_iff]
    exact LinearMap.continuous_on_pi (R'.val.toLinearMap.comp f)
  have hemb := (hval.isClosedEmbedding Subtype.val_injective).isEmbedding
  rw [hemb.continuous_iff]
  refine continuous_pi fun x' => ?_
  exact continuous_pi fun a => continuous_pi fun b => hu x' a b

end Entries

theorem continuous_of_isLocalHom {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
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

section Rec

open Formalism.RepresentationBoundsCohomology.FIN (IsCycG)

variable {D : D7} (i : D.nd.Loc)

theorem l_mem_max : ((D.nd.l i : ℕ) : D.nd.O i) ∈ IsLocalRing.maximalIdeal (D.nd.O i) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have h2 := Formalism.MainNotions.SumRepresentations.norm_iotaOQ_unit D.nd D.naut i u
  have h3 := Formalism.MainNotions.SumRepresentations.norm_iotaOQ_l D.nd D.naut i
  rw [hu] at h2
  rw [h2] at h3
  exact lt_irrefl _ h3

theorem l_ne_zero : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 :=
  Formalism.MainNotions.SumRepresentations.natCast_ne_zero_O D.nd i (D.nd.l i) (D.nd.lPrime i).out.ne_zero

theorem isLocalHom_alg : IsLocalHom (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
  refine ⟨fun z hz => ?_⟩
  by_contra hn
  have h1 : z ∈ IsLocalRing.maximalIdeal ℤ_[D.nd.l i] := hn
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h1
  obtain ⟨y, rfl⟩ := h1
  rw [map_mul, map_natCast] at hz
  exact (IsLocalRing.mem_maximalIdeal _).1 (l_mem_max i) (isUnit_of_mul_isUnit_left hz)

theorem continuous_alg : Continuous (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
  haveI := isLocalHom_alg i
  exact continuous_of_isLocalHom (ReciprocityTheory.ChartRestriction.T2.padicCoeff_padicInt (p := D.nd.l i)).adic (D.nd.O_adic i) _

theorem compact_O : CompactSpace (D.nd.O i) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' ℤ_[D.nd.l i] (D.nd.O i)
  have hc : Continuous f := by
    have : (f : (Fin n → ℤ_[D.nd.l i]) → D.nd.O i) = fun v =>
        ∑ k, algebraMap ℤ_[D.nd.l i] (D.nd.O i) (v k) * f (fun j => if k = j then 1 else 0) := by
      funext v
      rw [LinearMap.pi_apply_eq_sum_univ f v]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Algebra.smul_def]
    rw [this]
    exact continuous_finsetSum _ fun k _ =>
      ((continuous_alg i).comp (continuous_apply k)).mul continuous_const
  exact hf.compactSpace hc

theorem t2Space_nd_O : T2Space (D.nd.O i) := by
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

theorem padicCoeff_O : PadicCoeff (D.nd.l i) (D.nd.O i) :=
  ⟨D.nd.trO i, compact_O i, t2Space_nd_O i, D.nd.O_adic i, l_mem_max i, l_ne_zero i⟩

theorem fracTop_O : letI := fracTopology (D.nd.O i); FracTop (D.nd.O i) :=
  fracTop_open (D.nd.O i) (D.nd.O_adic i)

theorem fracTop_addGroup_O : letI := fracTopology (D.nd.O i); IsTopologicalAddGroup (FractionRing (D.nd.O i)) :=
  fracTop_addGroup (D.nd.O i)

theorem fracTop_smul_O : letI := fracTopology (D.nd.O i); ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i)) :=
  fracTop_smul (D.nd.O i) (D.nd.O_adic i)

theorem isCyc_eps : IsCycG (D.nd.l i) (epsU D.nd i) :=
  Formalism.AdicCompletionExports.isCycG_cycZ (D.nd.l i) D.host.E D.nd.Om (D.nd.O i) (algebraMap ℤ_[D.nd.l i] (D.nd.O i))

theorem av_over : ∀ v, IsPlaceOver (Formalism.MainNotions.N.K.Av (D := D) v) v := fun v => D.nd.plOm.2 v

theorem l_or_noReal : D.nd.l i ≠ 2 ∨ InfinitePlace.nrRealPlaces D.host.E = 0 := by
  have := D.host.isCMField_hostE
  exact Or.inr (NumberField.nrRealPlaces_eq_zero_iff.mpr inferInstance)

theorem one_le_localLevel : 1 ≤ D.nd.s0 i := by
  exact UpperTheory.KStar.S0.one_le_localLevel D.nd i

theorem restNLevelExponent_of_two : D.nd.l i = 2 → 2 ≤ D.nd.s0 i := by
  exact UpperTheory.KStar.S0.two_le_localLevel_of_eq_two D.nd i

def yU (u : ℤ_[D.nd.l i]ˣ) : (D.nd.O i)ˣ := Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom u

variable (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i)

theorem rows_over : ∀ w ∈ Formalism.MainNotions.N.K.rowsN i dc,
    (Formalism.MainNotions.N.K.Aw i dc w).valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 ∧
      IsPlaceOver (Formalism.MainNotions.N.K.Aw i dc w) (Formalism.MainNotions.N.K.plOf i dc w) := by
  intro w hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
  have hmemS : v ∈ Formalism.MainNotions.N.K.plSet i dc := Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  have hpl := Formalism.MainNotions.N.K.plOf_idx i dc hmemS
  have hAw : Formalism.MainNotions.N.K.Aw i dc (Formalism.MainNotions.N.K.idx i dc v) = D.nd.plOm.1 v := by
    unfold Formalism.MainNotions.N.K.Aw; rw [hpl]
  rw [hAw, hpl]
  refine ⟨?_, D.nd.plOm.2 v⟩
  have hmem : ((D.nd.l i : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal := (dc.cover v).1 (Or.inl hv)
  have h := (D.nd.plOm.2 v ((D.nd.l i : ℕ) : 𝓞 D.host.E)).2 hmem
  simpa using h

end Rec

section RecRing

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem finite_RD (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    Module.Finite (D.nd.O i) Dd.R' :=
  finite_R' hD

theorem rTop_addGroup_RD (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    letI := rTopology (D.nd.O i) Dd.R'; IsTopologicalAddGroup Dd.R' :=
  rTop_addGroup (D.nd.O i) Dd.R' (finite_R' hD)

theorem rTop_constSMul_RD : letI := rTopology (D.nd.O i) Dd.R'; ContinuousConstSMul (D.nd.O i) Dd.R' :=
  rTop_constSMul (D.nd.O i) Dd.R'

theorem rTop_mul_RD (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    letI := rTopology (D.nd.O i) Dd.R'; ContinuousMul Dd.R' :=
  rTop_mul (D.nd.O i) Dd.R' (finite_R' hD)

theorem fgTop_RD (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd) :
    letI := rTopology (D.nd.O i) Dd.R'; IsFGTop (D.nd.O i) Dd.R' := by
  haveI := t2Space_nd_O i
  exact rTop_fgTop (D.nd.O i) Dd.R' (finite_R' hD)

theorem uElt_cont (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) :
    letI := fracTopology (D.nd.O i); letI := rTopology (D.nd.O i) Dd.R';
    Continuous fun g : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) => uElt Dd.r Dd.χ g := by
  letI := fracTopology (D.nd.O i)
  letI := rTopology (D.nd.O i) Dd.R'
  haveI := fracTop_addGroup (D.nd.O i)
  haveI := fracTop_smul (D.nd.O i) (D.nd.O_adic i)
  haveI := rTop_addGroup (D.nd.O i) Dd.R' (finite_R' hD)
  have hι : Continuous (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) :=
    (algebraMap_openEmb (D.nd.O i) (D.nd.O_adic i)).continuous
  refine continuous_of_entries (D.nd.l i) Dd.R' (padicCoeff_O i) (fracTop_O i) (fgTop_RD i r π g0 eB e₁ s Dd hD) _ ?_
  intro x' a b
  have h7 := hD.2.2.2.2.2.2.1
  have h9 := hD.2.2.2.2.2.2.2.2.1
  have h12 := hD.2.2.2.2.2.2.2.2.2.2.2.1
  have key : ∀ g : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om),
      ((uElt Dd.r Dd.χ g : Dd.R') : Dd.X' → Matrix (Fin D.R.nV) (Fin D.R.nV) (FractionRing (D.nd.O i))) x' a b =
        algebraMap (D.nd.O i) (FractionRing (D.nd.O i))
          (((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * Formalism.MainNotions.N.rO D.nd i r (Dd.p x') g a b) := by
    intro g
    simp only [uElt]
    rw [h9, h7, ← map_inv, h12]
    simp [RepresentationBoundsCohomology.repX_apply, Matrix.map_apply, smul_eq_mul, map_mul]
  simp_rw [key]
  refine hι.comp (Continuous.mul ?_ ?_)
  · exact (D.nd.chi_cont i 1).comp continuous_inv
  · exact (hc (Dd.p x')).matrix_elem a b

end RecRing

end Formalism.MainNotions.N.K.Topo

end
end

section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

namespace Formalism.MainNotions.N.K.Norm

section Split

variable {O : Type} [CommRing O] {r t : ℕ}

def splitMat (A : Matrix (Fin r) (Fin r) O) (d : Fin t → O) : Matrix (Fin (r + t)) (Fin (r + t)) O :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 (Matrix.diagonal d))

theorem splitMat_mul (A A' : Matrix (Fin r) (Fin r) O) (d d' : Fin t → O) :
    splitMat A d * splitMat A' d' = splitMat (A * A') (d * d') := by
  simp only [splitMat, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    Matrix.diagonal_mul_diagonal, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rfl

theorem splitMat_one : splitMat (1 : Matrix (Fin r) (Fin r) O) (1 : Fin t → O) = 1 := by
  simp only [splitMat, Matrix.reindex_apply]
  rw [show (Matrix.diagonal (1 : Fin t → O)) = 1 from rfl, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem splitMat_map {O' : Type} [CommRing O'] (f : O →+* O') (A : Matrix (Fin r) (Fin r) O) (d : Fin t → O) :
    (splitMat A d).map f = splitMat (A.map f) (fun c => f (d c)) := by
  rw [splitMat, splitMat, Matrix.reindex_apply, Matrix.reindex_apply, ← Matrix.submatrix_map, Matrix.fromBlocks_map,
    Matrix.map_zero _ f.map_zero, Matrix.map_zero _ f.map_zero, Matrix.diagonal_map f.map_zero]

theorem splitMat_castAdd (A : Matrix (Fin r) (Fin r) O) (d : Fin t → O) (a b : Fin r) :
    splitMat A d (Fin.castAdd t a) (Fin.castAdd t b) = A a b := by
  simp [splitMat, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem splitMat_natAdd (A : Matrix (Fin r) (Fin r) O) (d : Fin t → O) (c : Fin t) :
    splitMat A d (Fin.natAdd r c) (Fin.natAdd r c) = d c := by
  simp [splitMat, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem splitMat_off (A : Matrix (Fin r) (Fin r) O) (d : Fin t → O) (a b : Fin (r + t))
    (h : RepresentationBoundsCohomology.blkG r t a ≠ RepresentationBoundsCohomology.blkG r t b) : splitMat A d a b = 0 := by
  obtain ⟨a', rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b', rfl⟩ := finSumFinEquiv.surjective b
  rcases a' with a' | a' <;> rcases b' with b' | b'
  · exact absurd (by simp [RepresentationBoundsCohomology.blkG_castAdd]) h
  · simp [splitMat, Matrix.reindex_apply, Matrix.submatrix_apply]
  · simp [splitMat, Matrix.reindex_apply, Matrix.submatrix_apply]
  · simp only [finSumFinEquiv_apply_right, RepresentationBoundsCohomology.blkG_natAdd, ne_eq] at h
    have hab : a' ≠ b' := fun e => h (by rw [e])
    simp [splitMat, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ hab]

variable {Γ : Type} [Group Γ]

def chiVec (t : ℕ) (χ : ℕ → Γ →* Oˣ) (g : Γ) : Fin t → O := fun c => ((χ ((c : ℕ) + 1) g : Oˣ) : O)

theorem chiVec_mul (χ : ℕ → Γ →* Oˣ) (g h : Γ) : chiVec t χ (g * h) = chiVec t χ g * chiVec t χ h := by
  funext c
  simp [chiVec]

theorem chiVec_one (χ : ℕ → Γ →* Oˣ) : chiVec t χ 1 = 1 := by
  funext c
  simp [chiVec]

def splitRep (ρ : Γ →* GL (Fin r) O) (χ : ℕ → Γ →* Oˣ) : Γ →* GL (Fin (r + t)) O where
  toFun g := ⟨splitMat ((ρ g : GL _ _) : Matrix _ _ O) (chiVec t χ g),
    splitMat ((ρ g⁻¹ : GL _ _) : Matrix _ _ O) (chiVec t χ g⁻¹),
    by rw [splitMat_mul, ← chiVec_mul, mul_inv_cancel, chiVec_one, ← Units.val_mul, ← map_mul, mul_inv_cancel,
      map_one, Units.val_one, splitMat_one],
    by rw [splitMat_mul, ← chiVec_mul, inv_mul_cancel, chiVec_one, ← Units.val_mul, ← map_mul, inv_mul_cancel,
      map_one, Units.val_one, splitMat_one]⟩
  map_one' := by
    apply Units.ext
    show splitMat _ _ = 1
    rw [map_one, Units.val_one, chiVec_one, splitMat_one]
  map_mul' g h := by
    apply Units.ext
    show splitMat _ _ = splitMat _ _ * splitMat _ _
    rw [splitMat_mul, ← chiVec_mul, map_mul, Units.val_mul]

end Split

section Rec

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical in
def rN : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)) :=
  Function.update r π (splitRep (t := D.R.t) (ρ π) (D.nd.chi i))

def RhoCont : Prop := Continuous (fun g => rhoO D.nd i ρ π g)

end Rec

section RecN

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical

theorem rN_self : rN i r ρ π π = splitRep (t := D.R.t) (ρ π) (D.nd.chi i) := by
  unfold rN
  exact Function.update_self ..

theorem rN_ne {x : D.nd.X i} (hx : x ≠ π) : rN i r ρ π x = r x := by
  unfold rN
  exact Function.update_of_ne hx ..

theorem rO_rN_self (g : GE D.nd) : rO D.nd i (rN i r ρ π) π g =
    splitMat (t := D.R.t) (rhoO D.nd i ρ π g) (chiVec D.R.t (D.nd.chi i) g) := by
  show ((rN i r ρ π π g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) = _
  rw [rN_self]
  rfl

theorem rO_rN_ne {x : D.nd.X i} (hx : x ≠ π) : rO D.nd i (rN i r ρ π) x = rO D.nd i r x := by
  simp only [rO, rN_ne i r ρ π hx]

theorem normAt_rN : RepresentationBoundsCohomology.NormAt D.nd (rN i r ρ π) ρ π := by
  refine ⟨fun g a b h => ?_, fun g c => ?_, fun g a b => ?_⟩
  · rw [rO_rN_self]
    exact splitMat_off _ _ a b h
  · rw [rO_rN_self]
    exact splitMat_natAdd _ _ c
  · rw [rO_rN_self]
    exact splitMat_castAdd _ _ a b

end RecN

section DecConj

variable {Γ : Type} {K : Type} [CommRing K] {r t : ℕ}

theorem conj_of_decomp (M : Γ → Matrix (Fin (r + t)) (Fin (r + t)) K) (A : Γ → Matrix (Fin r) (Fin r) K)
    (d : Γ → Fin t → K) (e : (Fin (r + t) → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K)))
    (he : ∀ g u, e ((M g).mulVec u) = ((A g).mulVec (e u).1, fun c => d g c * (e u).2 c)) :
    IsConjM M (fun g => splitMat (A g) (d g)) := by
  let f : (Fin (r + t) → K) ≃ₗ[K] (Fin (r + t) → K) := e.trans (RepresentationBoundsCohomology.eG r t K).symm
  refine ⟨LinearMap.toMatrix' (f : (Fin (r + t) → K) →ₗ[K] (Fin (r + t) → K)),
    LinearMap.toMatrix' (f.symm : (Fin (r + t) → K) →ₗ[K] (Fin (r + t) → K)), ?_, ?_, fun g => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self, LinearEquiv.refl_toLinearMap,
      LinearMap.toMatrix'_id]
  · rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm, LinearEquiv.refl_toLinearMap,
      LinearMap.toMatrix'_id]
  · apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro u
    rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', LinearMap.comp_apply, LinearMap.comp_apply,
      Matrix.toLin'_apply, Matrix.toLin'_apply]
    apply (RepresentationBoundsCohomology.eG r t K).injective
    have hoff : ∀ a b, RepresentationBoundsCohomology.blkG r t a ≠ RepresentationBoundsCohomology.blkG r t b → splitMat (A g) (d g) a b = 0 :=
      fun a b h => splitMat_off _ _ a b h
    have hsub : (splitMat (A g) (d g)).submatrix (Fin.castAdd t) (Fin.castAdd t) = A g := by
      ext a b
      exact splitMat_castAdd _ _ a b
    have hdiag : ∀ c, splitMat (A g) (d g) (Fin.natAdd r c) (Fin.natAdd r c) = d g c :=
      fun c => splitMat_natAdd _ _ c
    rw [RepresentationBoundsCohomology.eG_mulVec _ hoff]
    simp only [f, LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, he, hsub, hdiag]

end DecConj

section ConjFacts

variable {Γ : Type} {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]

theorem IsConjM.charpoly_eq {M M' : Γ → Matrix n n K} (h : IsConjM M M') (g : Γ) :
    (M' g).charpoly = (M g).charpoly := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  let u : (Matrix n n K)ˣ := ⟨P, Q, h1, h2⟩
  have hQ : Q = (u.val)⁻¹ := (Matrix.inv_eq_right_inv h1).symm
  have : M' g = u.val * M g * (u.val)⁻¹ := by
    rw [← hQ]
    show M' g = P * M g * Q
    rw [h3, Matrix.mul_assoc, h1, Matrix.mul_one]
  rw [this, Matrix.charpoly_units_conj]

theorem IsConjM.congr_right {M M₁ M₂ : Γ → Matrix n n K} (h : IsConjM M M₁) (hM : ∀ g, M₁ g = M₂ g) :
    IsConjM M M₂ := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  exact ⟨P, Q, h1, h2, fun g => by rw [h3, hM]⟩

theorem IsConjM.apply_eq {M M' : Γ → Matrix n n K} (h : IsConjM M M') (g : Γ) :
    ∃ P Q : Matrix n n K, P * Q = 1 ∧ Q * P = 1 ∧ M' g = P * M g * Q := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  exact ⟨P, Q, h1, h2, by rw [h3, Matrix.mul_assoc, h1, Matrix.mul_one]⟩

theorem IsConjM.eigen {M M' : Γ → Matrix n n K} (h : IsConjM M M') (c : Γ → K)
    (hu : ∃ u : n → K, u ≠ 0 ∧ ∀ g, (M' g).mulVec u = c g • u) :
    ∃ u : n → K, u ≠ 0 ∧ ∀ g, (M g).mulVec u = c g • u := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h.symm
  obtain ⟨u, hu0, hu⟩ := hu
  refine ⟨P.mulVec u, fun h0 => hu0 ?_, fun g => ?_⟩
  · have := congrArg (Matrix.mulVec Q) h0
    rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  · rw [Matrix.mulVec_mulVec, ← h3, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul]

end ConjFacts

section MapFacts

variable {Γ : Type} [Group Γ] {O K : Type} [CommRing O] [CommRing K] {k : ℕ} (f : O →+* K)

theorem map_twistM (M : Γ →* Matrix (Fin k) (Fin k) O) (χ : Γ →* Oˣ) (g : Γ) :
    (twistM M χ g).map f = f ((χ g : Oˣ) : O) • (M g).map f := by
  ext a b
  simp [twistM]

theorem map_dualM (M : Γ →* Matrix (Fin k) (Fin k) O) (g : Γ) :
    (dualM M g).map f = ((M g⁻¹).map f).transpose := by
  ext a b
  simp [dualM]

theorem conj_twistM {M M' : Γ →* Matrix (Fin k) (Fin k) O} (h : IsConjM (fun g => (M g).map f) (fun g => (M' g).map f))
    (χ : Γ →* Oˣ) : IsConjM (fun g => (twistM M χ g).map f) (fun g => (twistM M' χ g).map f) := by
  simp only [map_twistM]
  exact h.smul _

theorem conj_dualM {M M' : Γ →* Matrix (Fin k) (Fin k) O} (h : IsConjM (fun g => (M g).map f) (fun g => (M' g).map f)) :
    IsConjM (fun g => (dualM M g).map f) (fun g => (dualM M' g).map f) := by
  simp only [map_dualM]
  exact h.dual

end MapFacts

section RecC

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical

theorem conjK_self (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) :
    IsConjM (fun g => (rO D.nd i r π g).map (toK D.nd i))
      (fun g => (rO D.nd i (rN i r ρ π) π g).map (toK D.nd i)) := by
  obtain ⟨e, he⟩ := hd
  have h := conj_of_decomp (r := D.R.r) (t := D.R.t) (fun g => (rO D.nd i r π g).map (toK D.nd i))
    (fun g => (rhoO D.nd i ρ π g).map (toK D.nd i))
    (fun g c => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i)) e he
  refine h.congr_right (fun g => ?_)
  have e1 := rO_rN_self i r ρ π g
  have e2 := splitMat_map (toK D.nd i) (rhoO D.nd i ρ π g) (chiVec D.R.t (D.nd.chi i) g)
  exact ((congrArg (fun A => Matrix.map A (toK D.nd i)) e1).trans e2).symm

theorem conjK (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (x : D.nd.X i) :
    IsConjM (fun g => (rO D.nd i r x g).map (toK D.nd i))
      (fun g => (rO D.nd i (rN i r ρ π) x g).map (toK D.nd i)) := by
  by_cases hx : x = π
  · subst hx
    exact conjK_self i r ρ x hd
  · rw [rO_rN_ne i r ρ π hx]
    exact IsConjM.refl _

theorem toK_inj : Function.Injective (toK D.nd i) := IsFractionRing.injective (D.nd.O i) (KK D.nd i)

theorem charpoly_rN (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (x : D.nd.X i) (g : GE D.nd) :
    (rO D.nd i (rN i r ρ π) x g).charpoly = (rO D.nd i r x g).charpoly := by
  apply Polynomial.map_injective _ (toK_inj i)
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map]
  exact (conjK i r ρ π hd x).charpoly_eq g

end RecC

section RecT

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical

theorem IsConjM.congr' {Γ K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n]
    {M₁ M₂ N₁ N₂ : Γ → Matrix n n K} (h : IsConjM M₁ M₂) (e1 : ∀ g, M₁ g = N₁ g) (e2 : ∀ g, M₂ g = N₂ g) :
    IsConjM N₁ N₂ := by
  obtain ⟨P, Q, h1, h2, h3⟩ := h
  exact ⟨P, Q, h1, h2, fun g => by rw [← e1, ← e2, h3]⟩

theorem admG1_rN (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (h : TruncatedSeriesCountingIdentities.admG1 i r) : TruncatedSeriesCountingIdentities.admG1 i (rN i r ρ π) := by
  intro g k
  have e : (fun x : D.nd.X i => ((rO D.nd i (rN i r ρ π) x g).charpolyRev).coeff k) =
      (fun x : D.nd.X i => ((rO D.nd i r x g).charpolyRev).coeff k) := by
    funext x
    rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly, charpoly_rN i r ρ π hd x g]
  rw [e]
  exact h g k

theorem admG4_rN (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (h : TruncatedSeriesCountingIdentities.admG4 i r) : TruncatedSeriesCountingIdentities.admG4 i (rN i r ρ π) := by
  intro x v h1 h2 h3 g hg
  have hr := h x v h1 h2 h3 g hg
  by_cases hx : x = π
  · subst hx
    obtain ⟨P, Q, hPQ, _, he⟩ := (conjK i r ρ x hd x).apply_eq g
    have h1' : rO D.nd i r x g = 1 := by
      show ((r x g : GL (Fin D.R.nV) (D.nd.O i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)) = 1
      rw [hr]
      rfl
    simp only [h1', Matrix.map_one _ (map_zero (toK D.nd i)) (map_one (toK D.nd i)), Matrix.mul_one, hPQ] at he
    apply Units.ext
    rw [Units.val_one]
    change rO D.nd i (rN i r ρ x) x g = 1
    apply Matrix.map_injective (toK_inj i)
    show (rO D.nd i (rN i r ρ x) x g).map (toK D.nd i) = (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (toK D.nd i)
    rw [he, Matrix.map_one _ (map_zero (toK D.nd i)) (map_one (toK D.nd i))]
  · rw [rN_ne i r ρ π hx]
    exact hr

theorem admG6_rN (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (h : TruncatedSeriesCountingIdentities.admG6 i r) : TruncatedSeriesCountingIdentities.admG6 i (rN i r ρ π) := by
  intro x hx
  exact h x ((conjK i r ρ π hd x).eigen (fun g => toK D.nd i ((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i)) hx)

theorem eG_splitMat {K : Type} [CommRing K] {r t : ℕ} (A : Matrix (Fin r) (Fin r) K) (d : Fin t → K)
    (u : Fin (r + t) → K) :
    RepresentationBoundsCohomology.eG r t K ((splitMat A d).mulVec u) = (A.mulVec (RepresentationBoundsCohomology.eG r t K u).1, fun c => d c * (RepresentationBoundsCohomology.eG r t K u).2 c) := by
  have hsub : (splitMat A d).submatrix (Fin.castAdd t) (Fin.castAdd t) = A := by
    ext a b
    exact splitMat_castAdd _ _ a b
  have hdiag : ∀ c, splitMat A d (Fin.natAdd r c) (Fin.natAdd r c) = d c := fun c => splitMat_natAdd _ _ c
  rw [RepresentationBoundsCohomology.eG_mulVec _ (fun a b h => splitMat_off _ _ a b h)]
  simp only [hsub, hdiag]

theorem decomposes_normalized : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i (rN i r ρ π) ρ π := by
  refine ⟨RepresentationBoundsCohomology.eG D.R.r D.R.t (KK D.nd i), fun g u => ?_⟩
  have e1 := rO_rN_self i r ρ π g
  have e2 := splitMat_map (toK D.nd i) (rhoO D.nd i ρ π g) (chiVec D.R.t (D.nd.chi i) g)
  have hM : (mapM (toK D.nd i) (rO D.nd i (rN i r ρ π) π)) g =
      splitMat (t := D.R.t) ((rhoO D.nd i ρ π g).map (toK D.nd i))
        (fun c => toK D.nd i ((chiU D.nd i ((c : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i)) :=
    (congrArg (fun A => Matrix.map A (toK D.nd i)) e1).trans e2
  rw [hM]
  exact eG_splitMat _ _ u

theorem continuity_normalized (hc : RhoCont i ρ π) (h : TruncatedSeriesCountingIdentities.FamilyContinuous i r) : TruncatedSeriesCountingIdentities.FamilyContinuous i (rN i r ρ π) := by
  intro x
  by_cases hx : x = π
  · subst hx
    have hc2 : Continuous (fun g => splitMat (t := D.R.t) (rhoO D.nd i ρ x g) (chiVec D.R.t (D.nd.chi i) g)) := by
      unfold splitMat
      refine Continuous.matrix_reindex ?_ _ _
      refine Continuous.matrix_fromBlocks hc continuous_const continuous_const ?_
      refine Continuous.matrix_diagonal ?_
      exact continuous_pi fun c => D.nd.chi_cont i ((c : ℕ) + 1)
    exact hc2.congr (fun g => (rO_rN_self i r ρ x g).symm)
  · have e : (fun g => rO D.nd i (rN i r ρ π) x g) = fun g => rO D.nd i r x g := by
      rw [rO_rN_ne i r ρ π hx]
    rw [e]
    exact h x

section LocalC

variable {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)}

theorem locC_eq (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))
    (g : Br.G D.nbr i w hw) :
    TruncatedSeriesCountingIdentities.locC C M g = ((M (decS D.nd w (Br.ι (D.nbr i w hw) g))).map (toK D.nd i)).map
      (C.inc.comp (Br.toLLK (D.nbr i w hw))) := by
  ext a b
  simp only [Matrix.map_apply, RingHom.comp_apply, Br.toLLK_alg]
  rfl

theorem conj_locC (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) {k : ℕ} {M M' : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)}
    (h : IsConjM (fun g => (M g).map (toK D.nd i)) (fun g => (M' g).map (toK D.nd i))) :
    IsConjM ⇑(TruncatedSeriesCountingIdentities.locC C M) ⇑(TruncatedSeriesCountingIdentities.locC C M') :=
  ((h.map (C.inc.comp (Br.toLLK (D.nbr i w hw)))).comp
    (fun g => decS D.nd w (Br.ι (D.nbr i w hw) g))).congr' (fun g => (locC_eq i C M g).symm)
    (fun g => (locC_eq i C M' g).symm)

end LocalC

section JD

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL : Type} [Field LL] [Algebra Qp LL] {k : ℕ}

theorem jd {N N' : G →* Matrix (Fin k) (Fin k) LL} (h : IsConjM ⇑N ⇑N') :
    (IsCrys PD (matRep N) → IsCrys PD (matRep N')) ∧
    (∀ τ a, multV PD (matRep N) τ a = multV PD (matRep N') τ a) ∧
    (∀ τ a, IsJumpV PD (matRep N) τ a ↔ IsJumpV PD (matRep N') τ a) := by
  obtain ⟨e, he⟩ := exists_equiv_of_conj h
  exact ⟨isCrys_congr PD e he, multV_congr PD e he, isJumpV_congr PD e he⟩

theorem conj_twLL {N N' : G →* Matrix (Fin k) (Fin k) LL} (h : IsConjM ⇑N ⇑N') (χ : G →* LLˣ) :
    IsConjM ⇑(twistM N χ) ⇑(twistM N' χ) :=
  h.smul (fun g => ((χ g : LLˣ) : LL))

end JD

theorem admG2_rN (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (h : TruncatedSeriesCountingIdentities.admG2 i r ρ π) : TruncatedSeriesCountingIdentities.admG2 i (rN i r ρ π) ρ π := by
  intro w hw C
  obtain ⟨⟨g1, g2, g3, g4, g5, g6, g7⟩, g8⟩ := h w hw C
  have hc : ∀ x, IsConjM ⇑(TruncatedSeriesCountingIdentities.locC C (rO D.nd i r x)) ⇑(TruncatedSeriesCountingIdentities.locC C (rO D.nd i (rN i r ρ π) x)) :=
    fun x => conj_locC i C (conjK i r ρ π hd x)
  have ht := fun x => conj_twLL (hc x) (TruncatedSeriesCountingIdentities.chi1C C)⁻¹
  refine ⟨⟨fun x => (jd _ (hc x)).1 (g1 x), fun τ x y a => ?_, fun τ x a => ?_, g4, fun τ x => ?_, g6, g7⟩,
    fun x => (jd _ (ht x)).1 (g8 x)⟩
  · rw [← (jd _ (ht x)).2.1, ← (jd _ (ht y)).2.1]
    exact g2 τ x y a
  · rw [← (jd _ (ht x)).2.1]
    exact g3 τ x a
  · rw [← (jd _ (ht x)).2.2]
    exact g5 τ x

theorem row_normalized (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (h : TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow) :
    TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (rN i r ρ π) ρ π dc lenRow := by
  intro w hw hrow C hC V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 T2 hc2 hm2 V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 T1 hc1 hs1 F hF
  exact h w hw hrow C hC V2 ρ2 T2 hc2 hm2 V1 ρ1 T1 hc1
    (isSubOfSums_of_conj ρ1 _ _ (fun x => conj_locC i C (conj_twistM _ (conj_dualM _ (conjK i r ρ π hd x)) _)) hs1)
    F hF

theorem lift_normalized (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (dc : TruncatedSeriesCountingIdentities.Decl D i)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (h : TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i r dc e') :
    TruncatedSeriesCountingIdentities.LiftExponentAtPlaces i (rN i r ρ π) dc e' := by
  intro w hw hcol C hC V1 _ _ _ _ _ _ _ _ _ _ _ ρ1 L1 hc1 hs1 V2 _ _ _ _ _ _ _ _ _ _ _ ρ2 L2 hc2 hs2 F hF
  have hcx := fun x => conj_locC i C (conj_twistM _ (conjK i r ρ π hd x) ((chiU D.nd i 1)⁻¹))
  exact h w hw hcol C hC V1 ρ1 L1 hc1 (isSubquotOfSums_of_conj ρ1 _ _ hcx hs1)
    V2 ρ2 L2 hc2 (isSubquotOfSums_of_conj ρ2 _ _ hcx hs2) F hF

end RecT

section G5gen

variable {O K : Type} [CommRing O] [CommRing K] [Algebra O K] {n : Type} [Fintype n] [DecidableEq n]

theorem map_smul_one' (c : O) : (c • (1 : Matrix n n O)).map (algebraMap O K) = algebraMap O K c • (1 : Matrix n n K) := by
  ext a b
  by_cases h : a = b
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

theorem map_quad (A : Matrix n n O) (c : O) :
    ((A - 1) * (A - c • 1)).map (algebraMap O K) =
      (A.map (algebraMap O K) - 1) * (A.map (algebraMap O K) - algebraMap O K c • 1) := by
  rw [Matrix.map_mul, Matrix.map_sub _ (map_sub _), Matrix.map_sub _ (map_sub _),
    Matrix.map_one _ (map_zero _) (map_one _), map_smul_one']

def conjAlg (P Q : Matrix n n K) (h1 : P * Q = 1) (h2 : Q * P = 1) : Matrix n n K →ₐ[O] Matrix n n K where
  toFun X := P * X * Q
  map_one' := by rw [Matrix.mul_one, h1]
  map_mul' X Y := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Q P, h2, Matrix.one_mul]
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  commutes' c := by
    show P * algebraMap O (Matrix n n K) c * Q = algebraMap O (Matrix n n K) c
    rw [← Algebra.commutes c P, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem conjAlg_apply (P Q : Matrix n n K) (h1 : P * Q = 1) (h2 : Q * P = 1) (X : Matrix n n K) :
    conjAlg (O := O) P Q h1 h2 X = P * X * Q := rfl

theorem aeval_map (A : Matrix n n O) (p : Polynomial O) :
    (Polynomial.aeval A p).map (algebraMap O K) = Polynomial.aeval (A.map (algebraMap O K)) p := by
  have := Polynomial.aeval_algHom_apply ((Algebra.ofId O K).mapMatrix (m := n)) A p
  exact (this.trans (AlgHom.mapMatrix_apply _ _)).symm

theorem conj_smul_one (P Q : Matrix n n K) (h1 : P * Q = 1) (c : K) : P * (c • (1 : Matrix n n K)) * Q = c • 1 := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h1]

theorem conj_sub_smul (P Q : Matrix n n K) (h1 : P * Q = 1) (X : Matrix n n K) (c : K) :
    P * X * Q - c • 1 = P * (X - c • 1) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, conj_smul_one P Q h1]

theorem conj_sub_one (P Q : Matrix n n K) (h1 : P * Q = 1) (X : Matrix n n K) :
    P * X * Q - 1 = P * (X - 1) * Q := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, h1]

end G5gen

section G5rec

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

open Classical

theorem admG5_rN (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (h : TruncatedSeriesCountingIdentities.admG5 i r) : TruncatedSeriesCountingIdentities.admG5 i (rN i r ρ π) := by
  intro w hw
  obtain ⟨hA, hB⟩ := h w hw
  have hK := conjK_self i r ρ π hd
  obtain ⟨P, Q, hPQ, hQP, hconj⟩ := hK
  have hA' : ∀ g, (rO D.nd i (rN i r ρ π) π g).map (toK D.nd i) = P * (rO D.nd i r π g).map (toK D.nd i) * Q :=
    fun g => by rw [hconj, Matrix.mul_assoc, hPQ, Matrix.mul_one]
  refine ⟨fun hc x => ?_, fun hk hS hT => ?_⟩
  · obtain ⟨h1, Pm, hPm⟩ := hA hc x
    by_cases hx : x = π
    · subst hx
      let uP : GL (Fin D.R.nV) (KK D.nd i) := ⟨P, Q, hPQ, hQP⟩
      refine ⟨fun γ hγ => ?_, uP * Pm, fun γ hγ => ?_⟩
      · apply Matrix.map_injective (toK_inj i)
        show (((rO D.nd i (rN i r ρ x) x γ) - 1) * ((rO D.nd i (rN i r ρ x) x γ) - chi1 D.nd i γ • 1)).map
          (algebraMap (D.nd.O i) (KK D.nd i)) = (0 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (toK D.nd i)
        rw [map_quad, Matrix.map_zero _ (map_zero _)]
        have e1 : (rO D.nd i (rN i r ρ x) x γ).map (algebraMap (D.nd.O i) (KK D.nd i)) =
            P * (rO D.nd i r x γ).map (toK D.nd i) * Q := hA' γ
        rw [e1, conj_sub_one P Q hPQ, conj_sub_smul P Q hPQ]
        have e2 := congrArg (fun M => M.map (algebraMap (D.nd.O i) (KK D.nd i))) (h1 γ hγ)
        beta_reduce at e2
        rw [map_quad, Matrix.map_zero _ (map_zero _)] at e2
        have e3 : P * ((rO D.nd i r x γ).map (toK D.nd i) - 1) * Q *
            (P * ((rO D.nd i r x γ).map (toK D.nd i) - algebraMap (D.nd.O i) (KK D.nd i) (chi1 D.nd i γ) • 1) * Q) =
            P * (((rO D.nd i r x γ).map (toK D.nd i) - 1) *
              ((rO D.nd i r x γ).map (toK D.nd i) - algebraMap (D.nd.O i) (KK D.nd i) (chi1 D.nd i γ) • 1)) * Q := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
        rw [e3]
        erw [e2]
        rw [Matrix.mul_zero, Matrix.zero_mul]
      · have key : (((uP * Pm)⁻¹ * mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (rN i r ρ x x) γ * (uP * Pm) :
            GL (Fin D.R.nV) (KK D.nd i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
            ((Pm⁻¹ * mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r x) γ * Pm : GL (Fin D.R.nV) (KK D.nd i)) :
              Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := by
          simp only [Units.val_mul, mul_inv_rev]
          have e1 : ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (rN i r ρ x x) γ : GL (Fin D.R.nV) (KK D.nd i)) :
              Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) =
              P * ((mapRep (algebraMap (D.nd.O i) (KK D.nd i)) (r x) γ : GL (Fin D.R.nV) (KK D.nd i)) :
                Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) * Q := hA' γ
          have e2 : ((uP⁻¹ : GL (Fin D.R.nV) (KK D.nd i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = Q := rfl
          have e3 : ((uP : GL (Fin D.R.nV) (KK D.nd i)) : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) = P := rfl
          rw [e1, e2, e3]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul, ← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
        rw [key]
        exact hPm γ hγ
    · rw [rN_ne i r ρ π hx]
      exact ⟨h1, Pm, hPm⟩
  · obtain ⟨Pp, hu, hP⟩ := hB hk hS hT
    refine ⟨Pp, hu, fun x γ hγ => ?_⟩
    have h0 := hP x γ hγ
    by_cases hx : x = π
    · subst hx
      set p := Pp.map ((Pi.evalRingHom (fun _ : D.nd.X i => D.nd.O i) x).comp (D.nd.T i).val.toRingHom) with hp
      apply Matrix.map_injective (toK_inj i)
      show (Polynomial.aeval (rO D.nd i (rN i r ρ x) x (D.nd.gam0 i w)) p *
          (rO D.nd i (rN i r ρ x) x γ - chi1 D.nd i γ • 1)).map (algebraMap (D.nd.O i) (KK D.nd i)) =
        (0 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (toK D.nd i)
      rw [Matrix.map_mul, Matrix.map_sub _ (map_sub _), map_smul_one', aeval_map, Matrix.map_zero _ (map_zero _)]
      have e1 : ∀ g, (rO D.nd i (rN i r ρ x) x g).map (algebraMap (D.nd.O i) (KK D.nd i)) =
          conjAlg (O := D.nd.O i) P Q hPQ hQP ((rO D.nd i r x g).map (toK D.nd i)) := hA'
      rw [e1, e1, Polynomial.aeval_algHom_apply, conjAlg_apply, conjAlg_apply, conj_sub_smul P Q hPQ]
      have e2 := congrArg (fun M => M.map (algebraMap (D.nd.O i) (KK D.nd i))) h0
      beta_reduce at e2
      rw [Matrix.map_mul, Matrix.map_sub _ (map_sub _), map_smul_one', aeval_map, Matrix.map_zero _ (map_zero _)] at e2
      have e3 : ∀ X Y : Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i), P * X * Q * (P * Y * Q) = P * (X * Y) * Q := by
        intro X Y
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc Q P, hQP, Matrix.one_mul]
      rw [e3]
      erw [e2]
      rw [Matrix.mul_zero, Matrix.zero_mul]
    · rw [rN_ne i r ρ π hx]
      exact h0

end G5rec

section Final

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

end Final

end Formalism.MainNotions.N.K.Norm
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.K

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N

section Arith

def qU (e : ℕ) (x : ℕ∞) : ℚ := (x.toNat : ℚ) / e

theorem qU_mono {e : ℕ} {x y : ℕ∞} (h : x ≤ y) (hy : y ≠ ⊤) : qU e x ≤ qU e y := by
  unfold qU
  have h1 : x.toNat ≤ y.toNat := ENat.toNat_le_toNat h hy
  have h2 : (x.toNat : ℚ) ≤ y.toNat := by exact_mod_cast h1
  gcongr

theorem qU_eO_mul {e : ℕ} (he : e ≠ 0) (x : ℕ∞) : qU e ((e : ℕ∞) * x) = (x.toNat : ℚ) := by
  induction x using ENat.recTopCoe with
  | top =>
    rw [ENat.mul_top (by exact_mod_cast he)]
    simp only [qU, ENat.toNat_top, Nat.cast_zero, zero_div]
  | coe n =>
    have he0 : (e : ℚ) ≠ 0 := by exact_mod_cast he
    rw [← Nat.cast_mul]
    simp only [qU, ENat.toNat_natCast]
    push_cast
    first | (field_simp; ring) | field_simp

theorem inequality_of_finite_terms (e : ℕ) (he : e ≠ 0) (eO : ℕ∞) (heO : eO = e) (lhs : ℕ∞) (what₂ cols qs : Finset ℕ)
    (rowLen h0d z : ℕ → ℕ∞) (e' j deg : ℕ → ℕ) (vδ s H0 : ℕ∞) (Sha : ℕ → ℕ∞) (hE t cB Nn : ℕ)
    (hR : ∀ w ∈ what₂, rowLen w ≠ ⊤) (hH : ∀ w ∈ cols, h0d w ≠ ⊤) (hv : vδ ≠ ⊤) (hs : s ≠ ⊤)
    (hSha : ∀ k ∈ Finset.Ioo 0 t, Sha k ≠ ⊤) (hH0 : H0 ≠ ⊤) (hz : ∀ w ∈ qs, z w ≠ ⊤)
    (hd : lhs ≤
      ∑ w ∈ what₂, rowLen w +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0d w) + s +
        ∑ k ∈ Finset.Ioo 0 t, Sha k + eO * (hE : ℕ∞) +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * ((Nn : ℕ∞) + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, z w) :
    qU e lhs ≤
      ∑ w ∈ what₂, qU e (rowLen w) +
        ∑ w ∈ cols, ((e' w : ℚ) + (j w : ℚ) * ((e' w : ℚ) + qU e vδ) + 2 * qU e vδ + qU e (h0d w)) +
        qU e s + ∑ k ∈ Finset.Ioo 0 t, qU e (Sha k) + (hE : ℚ) +
        (t : ℚ) * (∑ w ∈ what₂, ((deg w : ℚ) + 2) * (cB : ℚ)) +
        4 * ((Nn : ℚ) + t) * ((cols.card : ℚ) + 1) * qU e vδ +
        (t : ℚ) * (cols.card : ℚ) * qU e H0 + (t : ℚ) * ∑ w ∈ qs, qU e (z w) := by
  subst heO
  obtain ⟨v, rfl⟩ := ENat.ne_top_iff_exists.mp hv
  obtain ⟨sn, rfl⟩ := ENat.ne_top_iff_exists.mp hs
  obtain ⟨h0n, rfl⟩ := ENat.ne_top_iff_exists.mp hH0
  have h1 : ∑ w ∈ what₂, rowLen w = ((∑ w ∈ what₂, (rowLen w).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun w hw => (ENat.natCast_toNat (hR w hw)).symm
  have h2 : ∑ w ∈ cols, ((e : ℕ∞) * (e' w : ℕ∞) + (j w : ℕ∞) * ((e : ℕ∞) * (e' w : ℕ∞) + (v : ℕ∞)) +
      2 * (v : ℕ∞) + h0d w) =
      ((∑ w ∈ cols, (e * e' w + j w * (e * e' w + v) + 2 * v + (h0d w).toNat) : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [← ENat.natCast_toNat (hH w hw)]
    simp only [ENat.toNat_natCast]
    push_cast; ring
  have h3 : ∑ k ∈ Finset.Ioo 0 t, Sha k = ((∑ k ∈ Finset.Ioo 0 t, (Sha k).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun k hk => (ENat.natCast_toNat (hSha k hk)).symm
  have h4 : ∑ w ∈ qs, z w = ((∑ w ∈ qs, (z w).toNat : ℕ) : ℕ∞) := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun w hw => (ENat.natCast_toNat (hz w hw)).symm
  have h5 : ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) = ((∑ w ∈ what₂, (deg w + 2) : ℕ) : ℕ∞) := by
    push_cast; rfl
  rw [h1, h2, h3, h4, h5] at hd
  norm_cast at hd
  have hl : lhs ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top _) hd
  obtain ⟨L, rfl⟩ := ENat.ne_top_iff_exists.mp hl
  have hL := (ENat.natCast_le_natCast).mp hd
  have hq := (Nat.cast_le (α := ℚ)).mpr hL
  have heq : (e : ℚ) ≠ 0 := by exact_mod_cast he
  have hs1 : ∑ w ∈ what₂, qU e (rowLen w) = ((∑ w ∈ what₂, (rowLen w).toNat : ℕ) : ℚ) / e := by
    rw [Nat.cast_sum, Finset.sum_div]; rfl
  have hs2 : ∑ w ∈ cols, ((e' w : ℚ) + (j w : ℚ) * ((e' w : ℚ) + qU e (v : ℕ∞)) + 2 * qU e (v : ℕ∞) +
      qU e (h0d w)) =
      ((∑ w ∈ cols, (e * e' w + j w * (e * e' w + v) + 2 * v + (h0d w).toNat) : ℕ) : ℚ) / e := by
    rw [Nat.cast_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun w _ => ?_
    simp only [qU, ENat.toNat_natCast]
    push_cast
    field_simp
  have hs3 : ∑ k ∈ Finset.Ioo 0 t, qU e (Sha k) = ((∑ k ∈ Finset.Ioo 0 t, (Sha k).toNat : ℕ) : ℚ) / e := by
    rw [Nat.cast_sum, Finset.sum_div]; rfl
  have hs4 : ∑ w ∈ qs, qU e (z w) = ((∑ w ∈ qs, (z w).toNat : ℕ) : ℚ) / e := by
    rw [Nat.cast_sum, Finset.sum_div]; rfl
  have hs5 : ∑ w ∈ what₂, ((deg w : ℚ) + 2) * (cB : ℚ) = ((∑ w ∈ what₂, (deg w + 2) : ℕ) : ℚ) * cB := by
    rw [Nat.cast_sum, Finset.sum_mul]; push_cast; rfl
  rw [hs1, hs2, hs3, hs4, hs5]
  simp only [qU, ENat.toNat_natCast]
  rw [div_le_iff₀ (by positivity)]
  refine hq.trans (le_of_eq ?_)
  push_cast
  field_simp

end Arith

section Rec

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i)

open Formalism.MainNotions.N.Glob Formalism.BasicNotions.Loc

def eON : ℕ∞ := Module.length (D.nd.O i) (D.nd.O i ⧸ Ideal.span {((D.nd.l i : ℕ) : D.nd.O i)})

def jN (n : ℕ) : ℕ :=
  if h : plOf i dc n ∈ placesOver D.host.E (D.nd.l i) then Br.jW D.loc D.nbr i (plOf i dc n) h ρ π else 0

def e'N (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (n : ℕ) : ℕ := e' (plOf i dc n)

def sN : ℕ∞ := Module.length (D.nd.O i) ↥(Br.selPi D.loc D.nbr i ρ π)

def ShaN (e : ℕ) : ℕ∞ := eON i * Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ)

def twistInvariantsLength (w : HeightOneSpectrum (𝓞 D.host.E)) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(Representation.invariants ((Br.WKO i ρ π).comp (decS D.nd w)))

def invLen (w : HeightOneSpectrum (𝓞 D.host.E)) (e : ℕ) : ℕ∞ :=
  Module.length (D.nd.O i) ↥(Representation.invariants ((KOtw D.nd i (e : ℤ)).comp (decS D.nd w)))

def invariantsLengthSup : ℕ∞ := (dc.col ×ˢ Finset.Ioo 0 D.R.t).sup fun p => invLen i p.1 p.2

def zetaN (n : ℕ) : D.nd.O i := D.nd.zeta i (plOf i dc n)

def LeTwistInvariantsAtColumns (h0d : ℕ → ℕ∞) : Prop := ∀ n ∈ colsN i dc, h0d n ≤ twistInvariantsLength i ρ π (plOf i dc n)

def TieRow (rowLen : ℕ → ℕ∞) (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) : Prop :=
  ∀ n ∈ rowsN i dc, rowLen n ≠ ⊤ ∧ ((rowLen n).toNat : ℚ) ≤ ((eON i).toNat : ℚ) * lenRow (plOf i dc n)

def FiniteTwistInvariants : Prop := ∀ w ∈ dc.col, twistInvariantsLength i ρ π w < ⊤

def FiniteCharacterInvariants : Prop := ∀ w ∈ dc.col, ∀ e ∈ Finset.Ioo 0 D.R.t, invLen i w e < ⊤

def ZetaNe : Prop := ∀ v ∈ D.nd.Q i, D.nd.zeta i v ≠ 1

end Rec

section Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Finset

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]

def selRho (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (what₂ : Finset ℕ)
    (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo : Type} (Io : Vo → Subgroup G) : Submodule O (H1z (uRep O (M := M) r χ)) :=
  (lcH1 (uRep O (M := M) r χ) ⊓ ⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
    ⨅ w ∈ what₂ ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))

def selChi (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (D : ℕ → Subgroup G) (what₂ qs : Finset ℕ)
    (F : ∀ w, Submodule O (H1z (resRep (uRep O (M := M) r χ) (D w))))
    {Vo VS : Type} (Io : Vo → Subgroup G) (IS : VS → Subgroup G) : Submodule O (H1z (uRep O (M := M) r χ)) :=
  (lcH1 (uRep O (M := M) r χ) ⊓ (⨅ v, unrH1 (uRep O (M := M) r χ) (Io v)) ⊓
      ⨅ v, unrH1 (uRep O (M := M) r χ) (IS v)) ⊓
    ⨅ w ∈ what₂ ∪ qs ∪ univ.image colIdx, (F w).comap (resH1 (uRep O (M := M) r χ) (D w))

def InjTie {H H' : Type} [AddCommGroup H] [Module O H] [AddCommGroup H'] [Module O H']
    (S : Submodule O H) (S' : Submodule O H') : Prop :=
  ∃ f : ↥S →ₗ[O] ↥S', Function.Injective f

theorem length_le_of_injTie {H H' : Type} [AddCommGroup H] [Module O H] [AddCommGroup H'] [Module O H']
    {S : Submodule O H} {S' : Submodule O H'} (h : InjTie S S') :
    Module.length O ↥S ≤ Module.length O ↥S' := by
  obtain ⟨f, hf⟩ := h
  exact Module.length_le_of_injective f hf

end Sel

section SelRec

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  {A T' G : Type} [Ring A] [Algebra (D.nd.O i) A] [CommRing T'] [Algebra T' A] [Group G] [TopologicalSpace G]

def TieSel1 (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (Dw : ℕ → Subgroup G) (what₂ : Finset ℕ)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (Dw w))))
    {Vo : Type} (Io : Vo → Subgroup G) : Prop :=
  InjTie (selRho M r χ colIdx Dw what₂ F Io) (Br.selPi D.loc D.nbr i ρ π)

theorem selRho_le_sN (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M]
    [SMulCommClass A (D.nd.O i) M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (Dw : ℕ → Subgroup G) (what₂ : Finset ℕ)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (Dw w))))
    {Vo : Type} (Io : Vo → Subgroup G) (h : TieSel1 i ρ π M r χ colIdx Dw what₂ F Io) :
    Module.length (D.nd.O i) ↥(selRho M r χ colIdx Dw what₂ F Io) ≤ sN i ρ π := length_le_of_injTie h

def TieSel2 (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
    (r : G →* A) (χ : G →* T'ˣ) {ι : Type} [Fintype ι] [DecidableEq ι]
    (colIdx : ι → ℕ) (Dw : ℕ → Subgroup G) (what₂ qs : Finset ℕ)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := M) r χ) (Dw w))))
    {Vo VS : Type} (Io : Vo → Subgroup G) (IS : VS → Subgroup G) (c : ℕ) : Prop :=
  Module.length (D.nd.O i) ↥(selChi M r χ colIdx Dw what₂ qs F Io IS) ≤ ShaN i (c - 1)

end SelRec

section N9Rec

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i)

open Formalism.MainNotions.N.Glob Formalism.BasicNotions.Loc

theorem eON_eq : ∃ e : ℕ, e ≠ 0 ∧ eON i = e := by
  obtain ⟨e, he0, he⟩ := Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.exists_eO D.nd i
  exact ⟨e, he0, by unfold eON; rw [Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span, he]⟩

theorem lenUnit_eq_qU (M : Type) [AddCommGroup M] [Module (D.nd.O i) M] :
    lenUnit (O := D.nd.O i) (D.nd.l i) M = qU (eON i).toNat (Module.length (D.nd.O i) M) := rfl

theorem row_mem_plSet {v : HeightOneSpectrum (𝓞 D.host.E)} (h : v ∈ dc.row) : v ∈ plSet i dc := by
  unfold plSet
  exact Finset.mem_union_left _ (Finset.mem_union_left _ h)

theorem col_mem_plSet {v : HeightOneSpectrum (𝓞 D.host.E)} (h : v ∈ dc.col) : v ∈ plSet i dc := by
  unfold plSet
  exact Finset.mem_union_left _ (Finset.mem_union_right _ h)

theorem q_mem_plSet {v : HeightOneSpectrum (𝓞 D.host.E)} (h : v ∈ D.nd.Q i) : v ∈ plSet i dc := by
  unfold plSet
  exact Finset.mem_union_right _ h

theorem sum_rowsN {β : Type} [AddCommMonoid β] (f : ℕ → β) :
    ∑ n ∈ rowsN i dc, f n = ∑ v ∈ dc.row, f (idx i dc v) := by
  unfold rowsN
  exact Finset.sum_image (by
    intro x hx y hy hxy
    exact idx_inj i dc (row_mem_plSet i dc hx) (row_mem_plSet i dc hy) hxy)

theorem sum_qsN {β : Type} [AddCommMonoid β] (f : ℕ → β) :
    ∑ n ∈ qsN i dc, f n = ∑ v ∈ D.nd.Q i, f (idx i dc v) := by
  unfold qsN
  exact Finset.sum_image (by
    intro x hx y hy hxy
    exact idx_inj i dc (q_mem_plSet i dc hx) (q_mem_plSet i dc hy) hxy)

private theorem image_colIdx_eq_image_idx : Finset.univ.image (colIdx i dc) = dc.col.image (idx i dc) := by
  unfold colIdx
  ext n
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨l, rfl⟩
    exact ⟨l.1, l.2, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨⟨v, hv⟩, rfl⟩

theorem sum_cols {β : Type} [AddCommMonoid β] (f : ℕ → β) :
    ∑ n ∈ Finset.univ.image (colIdx i dc), f n = ∑ v ∈ dc.col, f (idx i dc v) := by
  rw [image_colIdx_eq_image_idx i dc]
  exact Finset.sum_image (by
    intro x hx y hy hxy
    exact idx_inj i dc (col_mem_plSet i dc hx) (col_mem_plSet i dc hy) hxy)

theorem card_cols : (Finset.univ.image (colIdx i dc)).card = dc.col.card := by
  rw [image_colIdx_eq_image_idx i dc]
  exact Finset.card_image_of_injOn (by
    intro x hx y hy hxy
    exact idx_inj i dc (col_mem_plSet i dc hx) (col_mem_plSet i dc hy) hxy)

theorem cols_eq : Finset.univ.image (colIdx i dc) = colsN i dc := by
  unfold colsN
  exact image_colIdx_eq_image_idx i dc

theorem plOf_mem_col {n : ℕ} (hn : n ∈ colsN i dc) : plOf i dc n ∈ dc.col := by
  unfold colsN at hn
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hn
  rw [plOf_idx i dc (col_mem_plSet i dc hv)]
  exact hv

theorem le_H0N {x : ℕ∞} {n : ℕ} (hn : n ∈ colsN i dc) {k : ℕ} (hk : k ∈ Finset.Ioo 0 D.R.t)
    (h : x ≤ invLen i (plOf i dc n) k) : x ≤ invariantsLengthSup i dc := by
  refine h.trans ?_
  unfold invariantsLengthSup
  have hm : (plOf i dc n, k) ∈ dc.col ×ˢ Finset.Ioo 0 D.R.t :=
    Finset.mem_product.2 ⟨plOf_mem_col i dc hn, hk⟩
  have h2 := Finset.le_sup (f := fun p : HeightOneSpectrum (𝓞 D.host.E) × ℕ => invLen i p.1 p.2) hm
  exact h2

theorem invariants_length_sup_ne_top (hF : FiniteCharacterInvariants i dc) : invariantsLengthSup i dc ≠ ⊤ := by
  rw [← lt_top_iff_ne_top]
  unfold invariantsLengthSup
  rw [Finset.sup_lt_iff (bot_lt_top : (⊥ : ℕ∞) < ⊤)]
  rintro ⟨w, k⟩ hp
  rw [Finset.mem_product] at hp
  exact hF w hp.1 k hp.2

theorem qU_H0N_le : qU (eON i).toNat (invariantsLengthSup i dc) ≤ h0 D.nd i dc.col := by
  unfold Formalism.MainNotions.N.h0
  rcases (dc.col ×ˢ Finset.Ioo 0 D.R.t).eq_empty_or_nonempty with hs | hs
  · unfold invariantsLengthSup
    rw [hs]
    simp [qU]
  · obtain ⟨p, hp, hpeq⟩ := Finset.exists_mem_eq_sup _ hs (fun p => invLen i p.1 p.2)
    have hH : invariantsLengthSup i dc = invLen i p.1 p.2 := by
      unfold invariantsLengthSup
      exact hpeq
    rw [hH]
    have hm : qU (eON i).toNat (invLen i p.1 p.2) ∈ Finset.image (fun p => lenUnit (D.nd.l i)
        ↥(Representation.invariants (MonoidHom.comp (KOtw D.nd i ↑p.2) (decS D.nd p.1))))
        (dc.col ×ˢ Finset.Ioo 0 D.R.t) := Finset.mem_image.2 ⟨p, hp, rfl⟩
    obtain ⟨m, hmax⟩ := Finset.max_of_mem hm
    rw [hmax, WithBot.unbotD_coe]
    exact Finset.le_max_of_eq hm hmax

theorem vcc_eq_qU : D.nd.vcc i π =
    qU (eON i).toNat (Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)) := rfl

theorem sPi_eq_qU : Br.sPi D.loc D.nbr i ρ π = qU (eON i).toNat (sN i ρ π) := rfl

theorem twist_invariants_unit_change (w : HeightOneSpectrum (𝓞 D.host.E)) :
    Br.h0W i w ρ π = qU (eON i).toNat (twistInvariantsLength i ρ π w) := rfl

theorem qU_ShaN {k : ℕ} (hk : k ∈ Finset.Ioo 0 D.R.t)
    (hf : Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (k : ℤ) < ⊤) :
    qU (eON i).toNat (ShaN i k) = D.what₂.shaLen (D.nd.l i) k := by
  obtain ⟨e, he0, he⟩ := eON_eq i
  unfold ShaN
  rw [he, ENat.toNat_natCast, qU_eO_mul he0]
  obtain ⟨hk0, hkt⟩ := Finset.mem_Ioo.mp hk
  rw [D.nd.sha_eq (D.nd.l i) k hk0 hkt _ (ENat.natCast_toNat hf.ne).symm]

theorem lenUnit_zeta (v : HeightOneSpectrum (𝓞 D.host.E)) :
    lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) =
      qU (eON i).toNat (IsDiscreteValuationRing.addVal (D.nd.O i) (D.nd.zeta i v - 1)) := by
  rw [lenUnit_eq_qU, Formalism.NG.IdempotentNormalFormsLenFacts.length_quot_span]

theorem zeta_ne_top (hz : ZetaNe i) {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∈ D.nd.Q i) :
    IsDiscreteValuationRing.addVal (D.nd.O i) (D.nd.zeta i v - 1) ≠ ⊤ := by
  rw [Ne, IsDiscreteValuationRing.addVal_eq_top_iff]
  exact sub_ne_zero.mpr (hz v hv)

theorem card_first_block : Fintype.card {a // RepresentationBoundsCohomology.blk D.R a = 0} = D.R.r :=
  (Fintype.card_congr (Formalism.MainNotions.N.RepresentationBoundsCohomology.blockZeroEquiv D.R.r D.R.t).symm).trans (Fintype.card_fin _)

end N9Rec

section N9Main

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i)

open Formalism.MainNotions.N.Glob Formalism.BasicNotions.Loc

theorem qU_vdel {vδ : ℕ∞}
    (hvδ : vδ = eON i * ((∑ k ∈ Finset.Ioo 0 D.R.t, (D.nd.s0 i + padicValNat (D.nd.l i) k) : ℕ) : ℕ∞)) :
    qU (eON i).toNat vδ = D.nd.vdel i := by
  unfold Formalism.BasicNotions.NData.vdel
  obtain ⟨e, he, hE⟩ := eON_eq i
  rw [hvδ, hE, ENat.toNat_natCast, qU_eO_mul he, ENat.toNat_natCast]
  push_cast
  first | rfl

theorem selmer_length_inequality (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (cB : ℕ) (rowLen h0d : ℕ → ℕ∞) (vδ : ℕ∞) (Nn : ℕ)
    (hvδ : vδ = eON i * ((∑ k ∈ Finset.Ioo 0 D.R.t, (D.nd.s0 i + padicValNat (D.nd.l i) k) : ℕ) : ℕ∞))
    (hN : Nn = D.R.r)
    (hd : Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ≤
      ∑ w ∈ rowsN i dc, rowLen w +
        ∑ w ∈ Finset.univ.image (colIdx i dc), (eON i * (e'N i dc e' w : ℕ∞) +
          (jN i ρ π dc w : ℕ∞) * (eON i * (e'N i dc e' w : ℕ∞) + vδ) + 2 * vδ + h0d w) + sN i ρ π +
        ∑ e ∈ Finset.Ioo 0 D.R.t, ShaN i e +
        eON i * (padicValNat (D.nd.l i) (classNumber D.host.E) : ℕ∞) +
        (D.R.t : ℕ∞) * eON i * (cB : ℕ∞) * ∑ w ∈ rowsN i dc, ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 2) +
        4 * ((Nn : ℕ∞) + D.R.t) * (((Finset.univ.image (colIdx i dc)).card : ℕ∞) + 1) * vδ +
        (D.R.t : ℕ∞) * ((Finset.univ.image (colIdx i dc)).card : ℕ∞) * invariantsLengthSup i dc +
        (D.R.t : ℕ∞) * ∑ w ∈ qsN i dc, IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc w - 1))
    (hT4 : TieRow i dc rowLen lenRow) (hT3 : LeTwistInvariantsAtColumns i ρ π dc h0d) (hF1 : FiniteTwistInvariants i ρ π dc)
    (hF2 : FiniteCharacterInvariants i dc) (hz : ZetaNe i) (hs : Br.sFin D.loc D.nbr i ρ π)
    (hsha : ∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) :
    D.nd.vcc i π ≤
      (∑ w ∈ dc.row ∪ dc.col, TruncatedSeriesCountingIdentities.lenW i ρ π dc lenRow e' w) + Br.sPi D.loc D.nbr i ρ π +
      (∑ e ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) e) +
      (padicValNat (D.nd.l i) (Formalism.MainNotions.N.hE D.host) : ℚ) +
      (D.R.t : ℚ) * (∑ w ∈ dc.row, ((Formalism.MainNotions.N.locDeg D.host.E w : ℚ) + 2) * (cB : ℚ)) +
      4 * (D.R.nV : ℚ) * ((dc.col.card : ℚ) + 1) * D.nd.vdel i +
      (D.R.t : ℚ) * (dc.col.card : ℚ) * h0 D.nd i dc.col +
      (D.R.t : ℚ) * (∑ v ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i)
        (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1})) := by
  obtain ⟨e, he0, he⟩ := eON_eq i
  have hEt : (eON i).toNat = e := by rw [he, ENat.toNat_natCast]
  have hEpos : (0 : ℚ) < ((eON i).toNat : ℚ) := by rw [hEt]; exact_mod_cast Nat.pos_of_ne_zero he0

  have hR : ∀ w ∈ rowsN i dc, rowLen w ≠ ⊤ := fun w hw => (hT4 w hw).1
  have hH : ∀ w ∈ Finset.univ.image (colIdx i dc), h0d w ≠ ⊤ := by
    intro n hn
    rw [cols_eq] at hn
    exact ne_top_of_le_ne_top (hF1 _ (plOf_mem_col i dc hn)).ne (hT3 n hn)
  have hv : vδ ≠ ⊤ := by rw [hvδ, he, ← Nat.cast_mul]; exact ENat.natCast_ne_top _
  have hs' : sN i ρ π ≠ ⊤ := (show sN i ρ π < ⊤ from hs).ne
  have hSha : ∀ k ∈ Finset.Ioo 0 D.R.t, ShaN i k ≠ ⊤ := by
    intro k hk
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (hsha k hk).ne
    unfold ShaN
    rw [← hm, he, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  have hz' : ∀ n ∈ qsN i dc, IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc n - 1) ≠ ⊤ := by
    intro n hn
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hn
    unfold zetaN
    rw [plOf_idx i dc (q_mem_plSet i dc hv)]
    exact zeta_ne_top i hz hv
  have key := inequality_of_finite_terms e he0 (eON i) he _ (rowsN i dc) (Finset.univ.image (colIdx i dc)) (qsN i dc) rowLen h0d
    (fun w => IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc w - 1)) (e'N i dc e') (jN i ρ π dc)
    (fun w => ReciprocityTheory.Gal.locDeg (plOf i dc w)) vδ (sN i ρ π) (invariantsLengthSup i dc) (ShaN i)
    (padicValNat (D.nd.l i) (classNumber D.host.E)) D.R.t cB Nn hR hH hv hs' hSha (invariants_length_sup_ne_top i dc hF2) hz' hd
  rw [← hEt] at key
  rw [vcc_eq_qU]

  have hvd := qU_vdel i hvδ
  have A0 : ∑ w ∈ dc.row ∪ dc.col, TruncatedSeriesCountingIdentities.lenW i ρ π dc lenRow e' w =
      ∑ w ∈ dc.row, lenRow w + ∑ w ∈ dc.col, TruncatedSeriesCountingIdentities.lenW i ρ π dc lenRow e' w := by
    rw [Finset.sum_union dc.disj]
    congr 1
    refine Finset.sum_congr rfl fun w hw => ?_
    unfold TruncatedSeriesCountingIdentities.lenW
    rw [dite_eq_right (Finset.disjoint_left.mp dc.disj hw)]
  have A1 : ∑ n ∈ rowsN i dc, qU (eON i).toNat (rowLen n) ≤ ∑ w ∈ dc.row, lenRow w := by
    rw [sum_rowsN]
    refine Finset.sum_le_sum fun v hv => ?_
    have hn : idx i dc v ∈ rowsN i dc := Finset.mem_image_of_mem _ hv
    have h2 := (hT4 _ hn).2
    rw [plOf_idx i dc (row_mem_plSet i dc hv)] at h2
    unfold qU
    rw [div_le_iff₀ hEpos]
    linarith
  have A2 : ∑ w ∈ Finset.univ.image (colIdx i dc),
      ((e'N i dc e' w : ℚ) + (jN i ρ π dc w : ℚ) * ((e'N i dc e' w : ℚ) + qU (eON i).toNat vδ) +
        2 * qU (eON i).toNat vδ + qU (eON i).toNat (h0d w)) ≤
      ∑ w ∈ dc.col, TruncatedSeriesCountingIdentities.lenW i ρ π dc lenRow e' w := by
    rw [sum_cols]
    refine Finset.sum_le_sum fun v hv => ?_
    have hpo := plOf_idx i dc (col_mem_plSet i dc hv)
    have hw : v ∈ placesOver D.host.E (D.nd.l i) := (dc.cover v).1 (Or.inr hv)
    have hjw : ∀ u (hu : u = v) (h : u ∈ placesOver D.host.E (D.nd.l i)),
        Br.jW D.loc D.nbr i u h ρ π = Br.jW D.loc D.nbr i v hw ρ π := by
      rintro u rfl h; rfl
    have hj : jN i ρ π dc (idx i dc v) = Br.jW D.loc D.nbr i v hw ρ π := by
      unfold jN
      rw [dite_eq_left (by rw [hpo]; exact hw)]
      exact hjw _ hpo _
    have he' : e'N i dc e' (idx i dc v) = e' v := by unfold e'N; rw [hpo]
    have hn : idx i dc v ∈ colsN i dc := Finset.mem_image_of_mem _ hv
    have hh : qU (eON i).toNat (h0d (idx i dc v)) ≤ Br.h0W i v ρ π := by
      rw [twist_invariants_unit_change]
      have h3 := hT3 _ hn
      rw [hpo] at h3
      exact qU_mono h3 (hF1 v hv).ne
    unfold TruncatedSeriesCountingIdentities.lenW
    rw [dite_eq_left hv]
    unfold Br.lenCol
    rw [hj, he', hvd]
    linarith
  have A3 : qU (eON i).toNat (sN i ρ π) = Br.sPi D.loc D.nbr i ρ π := (sPi_eq_qU i ρ π).symm
  have A4 : ∑ k ∈ Finset.Ioo 0 D.R.t, qU (eON i).toNat (ShaN i k) =
      ∑ k ∈ Finset.Ioo 0 D.R.t, D.what₂.shaLen (D.nd.l i) k :=
    Finset.sum_congr rfl fun k hk => qU_ShaN i hk (hsha k hk)
  have A5 : ((padicValNat (D.nd.l i) (classNumber D.host.E) : ℕ) : ℚ) =
      (padicValNat (D.nd.l i) (Formalism.MainNotions.N.hE D.host) : ℚ) := rfl
  have A6 : ∑ n ∈ rowsN i dc, ((ReciprocityTheory.Gal.locDeg (plOf i dc n) : ℚ) + 2) * (cB : ℚ) =
      ∑ w ∈ dc.row, ((Formalism.MainNotions.N.locDeg D.host.E w : ℚ) + 2) * (cB : ℚ) := by
    rw [sum_rowsN]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [plOf_idx i dc (row_mem_plSet i dc hv)]
    rfl
  have A7 : 4 * ((Nn : ℚ) + D.R.t) * (((Finset.univ.image (colIdx i dc)).card : ℕ) + 1 : ℚ) *
      qU (eON i).toNat vδ = 4 * (D.R.nV : ℚ) * ((dc.col.card : ℚ) + 1) * D.nd.vdel i := by
    rw [card_cols, hvd, hN]
    unfold Ranks.nV
    push_cast
    ring
  have A8 : (D.R.t : ℚ) * (((Finset.univ.image (colIdx i dc)).card : ℕ) : ℚ) * qU (eON i).toNat (invariantsLengthSup i dc) ≤
      (D.R.t : ℚ) * (dc.col.card : ℚ) * h0 D.nd i dc.col := by
    rw [card_cols]
    exact mul_le_mul_of_nonneg_left (qU_H0N_le i dc) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have A9 : ∑ n ∈ qsN i dc, qU (eON i).toNat (IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc n - 1)) =
      ∑ v ∈ D.nd.Q i, lenUnit (O := D.nd.O i) (D.nd.l i) (D.nd.O i ⧸ Ideal.span {D.nd.zeta i v - 1}) := by
    rw [sum_qsN]
    refine Finset.sum_congr rfl fun v hv => ?_
    unfold zetaN
    rw [plOf_idx i dc (q_mem_plSet i dc hv), lenUnit_zeta]
  rw [A3, A4, A5, A6, A7, A9] at key
  rw [A0]
  linarith

end N9Main

section N9Cor

variable {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i)

open Formalism.MainNotions.N.Glob Formalism.BasicNotions.Loc

def SelmerLengthInequality (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ)
    (cB : ℕ) : Prop :=
  ∃ (rowLen h0d : ℕ → ℕ∞) (vδ : ℕ∞) (Nn : ℕ),
    vδ = eON i * ((∑ k ∈ Finset.Ioo 0 D.R.t, (D.nd.s0 i + padicValNat (D.nd.l i) k) : ℕ) : ℕ∞) ∧
    Nn = D.R.r ∧
    Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π) ≤
      ∑ w ∈ rowsN i dc, rowLen w +
        ∑ w ∈ Finset.univ.image (colIdx i dc), (eON i * (e'N i dc e' w : ℕ∞) +
          (jN i ρ π dc w : ℕ∞) * (eON i * (e'N i dc e' w : ℕ∞) + vδ) + 2 * vδ + h0d w) + sN i ρ π +
        ∑ e ∈ Finset.Ioo 0 D.R.t, ShaN i e +
        eON i * (padicValNat (D.nd.l i) (classNumber D.host.E) : ℕ∞) +
        (D.R.t : ℕ∞) * eON i * (cB : ℕ∞) * ∑ w ∈ rowsN i dc, ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 2) +
        4 * ((Nn : ℕ∞) + D.R.t) * (((Finset.univ.image (colIdx i dc)).card : ℕ∞) + 1) * vδ +
        (D.R.t : ℕ∞) * ((Finset.univ.image (colIdx i dc)).card : ℕ∞) * invariantsLengthSup i dc +
        (D.R.t : ℕ∞) * ∑ w ∈ qsN i dc, IsDiscreteValuationRing.addVal (D.nd.O i) (zetaN i dc w - 1) ∧
    TieRow i dc rowLen lenRow ∧ LeTwistInvariantsAtColumns i ρ π dc h0d

theorem theorem_of_display_inequality (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (hD : D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → Br.sFin D.loc D.nbr i ρ π →
      (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
      SelmerLengthInequality i ρ π dc lenRow e' cB)
    (hF1 : FiniteTwistInvariants i ρ π dc) (hF2 : FiniteCharacterInvariants i dc) (hz : ZetaNe i) :
    TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := by
  unfold TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem
  intro h0 h1 hZ hs hsha
  obtain ⟨rowLen, h0d, vδ, Nn, hvδ, hN, hd, hT4, hT3⟩ := hD h0 h1 hZ hs hsha
  exact selmer_length_inequality i ρ π dc lenRow e' cB rowLen h0d vδ Nn hvδ hN hd hT4 hT3 hF1 hF2 hz hs hsha

theorem zeta_ne_one_of_g5_extra (h : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) : ZetaNe i := by
  unfold ZetaNe TruncatedSeriesCountingIdentities.TameGeneratorConditions at *
  intro v hv
  have h2 := h v (Or.inr hv)
  tauto

theorem theorem_of_display (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)
    (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (hD : D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → π ∈ D.nd.Z i → Br.sFin D.loc D.nbr i ρ π →
      (∀ e ∈ Finset.Ioo 0 D.R.t, Formalism.GaloisCohomology.shaLen (D.nd.ldat (D.nd.l i)) (e : ℤ) < ⊤) →
      SelmerLengthInequality i ρ π dc lenRow e' cB)
    (hF1 : FiniteTwistInvariants i ρ π dc) (hF2 : FiniteCharacterInvariants i dc) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) :
    TruncatedSeriesCountingIdentities.GlobalLatticeIndexTheorem i ρ π dc lenRow e' cB := theorem_of_display_inequality i ρ π dc lenRow e' cB hD hF1 hF2 (zeta_ne_one_of_g5_extra i h5x)

end N9Cor

end Formalism.MainNotions.N.K

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TB

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR

section Core

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {A T' G : Type} [Ring A] [Algebra O A] [CommRing T'] [Algebra T' A] [Group G]

def TBClause (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) (ℓ cB cT deg : ℕ)
    (Hc F : Submodule O (H1z (resRep (uRep O (M := M) r χ) Dw))) : Prop :=
  F ≤ Hc ∧ cT ≤ cB ∧
    (∀ ψ : Ymod r χ E →ₗ[O] M, (∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
      ∀ z : coZ1s (resRep (uRep O (M := M) r χ) Dw),
        (∀ g : Dw, (z : Dw → M) g = ψ (yY r χ E (g : G))) →
        ((ℓ : O) ^ cT) • (Submodule.mkQ _ z : H1z (resRep (uRep O (M := M) r χ) Dw)) ∈ F) ∧
    Module.length O (↥(Hc ⊓ divBy F ((ℓ : O) ^ cT)) ⧸
        F.comap (Hc ⊓ divBy F ((ℓ : O) ^ cT)).subtype) ≤
      Module.length O (O ⧸ Ideal.span {(ℓ : O)}) * (cT : ℕ∞) * ((deg : ℕ∞) + 1)

def YLoc (M : Type) [AddCommGroup M] [Module A M] [Module O M] [SMulCommClass A O M]
    (r : G →* A) (χ : G →* T'ˣ) (E : A) (Dw : Subgroup G) [TopologicalSpace Dw] : Prop :=
  ∀ ψ : Ymod r χ E →ₗ[O] M, (∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
    IsLocallyConstant fun g : Dw => ψ (yY r χ E (g : G))

end Core

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    (LL : Type) [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    (O : Type) [CommRing O] [Algebra O LL]

structure TwLat (e : ℕ) where
  V : Type
  [acg : AddCommGroup V]
  [mLL : Module LL V]
  [mQ : Module Qp V]
  [tQ : IsScalarTower Qp LL V]
  [mO : Module O V]
  [tO : IsScalarTower O LL V]
  [top : TopologicalSpace V]
  [cadd : ContinuousAdd V]
  [csm : ContinuousConstSMul LL V]
  [imt : IsModuleTopology LL V]
  [fd : FiniteDimensional LL V]
  ρ : Representation LL G V
  L : Lattice (O := O) ρ
  cont : ∀ x, Continuous fun g => ρ g x
  mat : IsMatLat (ρ := ρ) L.T (epsTw PD e)

attribute [instance] TwLat.acg TwLat.mLL TwLat.mQ TwLat.tQ TwLat.mO TwLat.tO TwLat.top TwLat.cadd TwLat.csm
  TwLat.imt TwLat.fd

structure YtLat where
  V : Type
  [acg : AddCommGroup V]
  [mLL : Module LL V]
  [mQ : Module Qp V]
  [tQ : IsScalarTower Qp LL V]
  [mO : Module O V]
  [tO : IsScalarTower O LL V]
  [top : TopologicalSpace V]
  [cadd : ContinuousAdd V]
  [csm : ContinuousConstSMul LL V]
  [imt : IsModuleTopology LL V]
  [fd : FiniteDimensional LL V]
  ρ : Representation LL G V
  L : Lattice (O := O) ρ
  cont : ∀ x, Continuous fun g => ρ g x
  p : V →ₗ[LL] LL
  p_inv : ∀ g v, p (ρ g v) = p v
  p_int : ∀ v ∈ L.T, p v ∈ Set.range (algebraMap O LL)
  e₀ : V
  e₀_mem : e₀ ∈ L.T
  p_e₀ : p e₀ = 1

attribute [instance] YtLat.acg YtLat.mLL YtLat.mQ YtLat.tQ YtLat.mO YtLat.tO YtLat.top YtLat.cadd YtLat.csm
  YtLat.imt YtLat.fd

variable {PD LL O}

def YtCrys (Y : YtLat (G := G) (Qp := Qp) LL O) (J : (K →ₐ[Qp] LL) → Set ℤ) : Prop :=
  IsCrys PD Y.ρ ∧ ∀ τ, JumpsInV PD Y.ρ τ (J τ)

end Local

section Transport

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]
    {O' : Type} [CommRing O'] (σ : O' ≃+* O)
    {A T' GG : Type} [Ring A] [Algebra O' A] [CommRing T'] [Algebra T' A] [Group GG]
    {M : Type} [AddCommGroup M] [Module A M] [Module O' M] [SMulCommClass A O' M]
    (r : GG →* A) (χ : GG →* T'ˣ) (E : A) (Dw : Subgroup GG) (eG : Dw ≃* G)

variable (PD LL O M) in
structure CoefDict (e : ℕ) where
  Ce : TwLat PD LL O e
  u : M ≃+ (Ce.V ⧸ Ce.L.T)
  u_smul : ∀ (a : O') (m : M), u (a • m) = σ a • u m
  u_act : ∀ (g : Dw) (m : M), u (uElt r χ (g : GG) • m) = actD Ce.L (eG g) (u m)

def PsiExt {e : ℕ} (Y : YtLat (G := G) (Qp := Qp) LL O) (Cd : CoefDict PD LL O σ M r χ Dw eG e) : Prop :=
  ∀ ψ : Ymod r χ E →ₗ[O'] M, (∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y) →
    ∃ φ : Y.V →ₗ[O] (Cd.Ce.V ⧸ Cd.Ce.L.T),
      (∀ g, ∀ y ∈ Y.L.T, Y.p y = 0 → φ (Y.ρ g y) = actD Cd.Ce.L g (φ y)) ∧
      ∀ g : Dw, φ (Y.ρ (eG g) Y.e₀ - Y.e₀) = Cd.u (ψ (yY r χ E (g : GG)))

variable {σ r χ E Dw eG}

def trC {e : ℕ} (Cd : CoefDict PD LL O σ M r χ Dw eG e) (z : Dw → M) : G → Cd.Ce.V ⧸ Cd.Ce.L.T :=
  fun g => Cd.u (z (eG.symm g))

theorem trC_hf {e t cB : ℕ} {I : Subgroup G} {J : (K →ₐ[Qp] LL) → Set ℤ}
    (hTB : Formalism.MainNotions.N.TBAt PD (O := O) I J t cB) (het : e < t)
    (Y : YtLat (G := G) (Qp := Qp) LL O) (hY : YtCrys (PD := PD) Y J)
    (Cd : CoefDict PD LL O σ M r χ Dw eG e) (hψ : PsiExt σ r χ E Dw eG Y Cd)
    (ψ : Ymod r χ E →ₗ[O'] M) (hψe : ∀ g ∈ Dw, ∀ y, ψ (uElt r χ g • y) = uElt r χ g • ψ y)
    (z : Dw → M) (hz : ∀ g : Dw, z g = ψ (yY r χ E (g : GG))) :
    ((PD.p : O) ^ cB) • trC Cd z ∈ HfD PD Cd.Ce.L := by
  obtain ⟨φ, hφ1, hφ2⟩ := hψ ψ hψe
  have hfun : trC Cd z = fun g => φ (Y.ρ g Y.e₀ - Y.e₀) := by
    funext g
    have h := hφ2 (eG.symm g)
    rw [MulEquiv.apply_symm_apply] at h
    rw [h]
    simp only [trC, hz]
  rw [hfun]
  exact hTB.1 Y.V Y.ρ Y.L Y.cont hY.1 hY.2 Y.p Y.p_inv Y.p_int Y.e₀ Y.e₀_mem Y.p_e₀ e het
    Cd.Ce.V Cd.Ce.ρ Cd.Ce.L Cd.Ce.cont Cd.Ce.mat φ hφ1

theorem trC_mem_Z1D {e : ℕ} (Cd : CoefDict PD LL O σ M r χ Dw eG e) [TopologicalSpace Dw]
    (heG : Continuous eG.symm) (z : coZ1s (resRep (uRep O' (M := M) r χ) Dw))
    (hz : IsLocallyConstant (z : Dw → M)) (c : O) : c • trC Cd (z : Dw → M) ∈ divisibleCocycles Cd.Ce.L := by
  apply Submodule.smul_mem
  show IsLocallyConstant (trC Cd (z : Dw → M)) ∧ ∀ g h, trC Cd (z : Dw → M) (g * h) =
    trC Cd (z : Dw → M) g + actD Cd.Ce.L g (trC Cd (z : Dw → M) h)
  refine ⟨(hz.comp_continuous heG).comp Cd.u, fun g h => ?_⟩
  have hc : (z : Dw → M) (eG.symm g * eG.symm h) = (z : Dw → M) (eG.symm g) +
      resRep (uRep O' (M := M) r χ) Dw (eG.symm g) ((z : Dw → M) (eG.symm h)) := z.2 _ _
  simp only [trC, map_mul]
  rw [hc, map_add (f := _)]
  congr 1
  have hu := Cd.u_act (eG.symm g) ((z : Dw → M) (eG.symm h))
  rw [MulEquiv.apply_symm_apply] at hu
  exact hu

end Transport

section Record

open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev Dw (n : ℕ) : Subgroup (GE D.nd) := (Aw i dc n).decompositionSubgroup D.host.E

abbrev Mc (c : Fin (D.R.t + 1)) : Type := blockRestrictedRepresentationType (Formalism.MainNotions.N.RepresentationBoundsCohomology.blk D.R) Dd.ρk c

abbrev ρc (c : Fin (D.R.t + 1)) (n : ℕ) : Representation (D.nd.O i) (Dw i dc n) (Mc i Dd c) :=
  resRep (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (Dw i dc n)

def Hc (c : Fin (D.R.t + 1)) (n : ℕ) : Submodule (D.nd.O i) (H1z (ρc i dc Dd c n)) :=
  Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (ρc i dc Dd c n)

def Fc (c : Fin (D.R.t + 1)) (n : ℕ) : Submodule (D.nd.O i) (H1z (ρc i dc Dd c n)) :=
  if (c : ℕ) = 1 then
    Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology.lcH1 (ρc i dc Dd c n) ⊓
      unrH1 (ρc i dc Dd c n) ((Ine (F := D.host.E) (Aw i dc n)).subgroupOf (Dw i dc n))
  else ⊥

def TBTarget (cB : ℕ) : Prop :=
  ∀ n ∈ rowsN i dc, ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
    TBClause (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc n) (D.nd.l i) cB cB (Formalism.MainNotions.N.locDeg D.host.E (plOf i dc n))
      (Hc i dc Dd c n) (Fc i dc Dd c n)

theorem mem_plSet {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    w ∈ plSet i dc := by
  simp only [plSet, Finset.mem_union]
  exact Or.inl ((dc.cover w).2 hw)

theorem Dw_idx {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Dw i dc (idx i dc w) = Dec (F := D.host.E) (D.nd.plOm.1 w) := by
  have hm := mem_plSet i dc hw
  have hpl : plOf i dc (idx i dc w) = w := by
    simp [plOf, idx, hm]
  simp only [Dw, Aw, hpl, ReciprocityTheory.Gal.Dec]

def eW {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    ↥(Dw i dc (idx i dc w)) ≃* Br.G D.nbr i w hw :=
  (MulEquiv.subgroupCongr (Dw_idx i dc hw)).trans (D.nbr i w hw).e

def Jr {w : HeightOneSpectrum (𝓞 D.host.E)} {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) :
    (Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1) → Set ℤ :=
  fun τ => {a | IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (TruncatedSeriesCountingIdentities.locC C (rTwO D.nd i r π))) τ a}

def selfO {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    D.nd.O i ≃+* ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) :=
  (D.nbr i w hw).eO

def TBDict : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
      ∃ (Y : YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL))
        (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
          ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL) (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w))
          (eW i dc hw) ((c : ℕ) - 1)),
        YtCrys (PD := Br.PD D.loc D.nbr i w hw) Y (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) ∧
        PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) Y Cd ∧
        YLoc (O := D.nd.O i) (Mc i Dd c) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w))

end Record

end Formalism.MainNotions.N.K.TB

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.QS

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Places
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

def Vo : Type :=
  {v : HeightOneSpectrum (𝓞 D.host.E) // v ∉ placesOver D.host.E (D.nd.l i) ∧ v ∉ D.nd.S i ∧ v ∉ D.nd.Q i}

def VS : Type := {v : HeightOneSpectrum (𝓞 D.host.E) // v ∈ D.nd.S i}

def Io (v : Vo i) : Subgroup (GE D.nd) := Ine (F := D.host.E) (D.nd.plOm.1 v.1)

def IS (v : VS i) : Subgroup (GE D.nd) := Ine (F := D.host.E) (D.nd.plOm.1 v.1)

def I (w : ℕ) : Subgroup (decs D.host.E (Aw i dc) w) :=
  (Ine (F := D.host.E) (Aw i dc w)).subgroupOf (decs D.host.E (Aw i dc) w)

def γQ (w : ℕ) : decs D.host.E (Aw i dc) w :=
  ⟨D.nd.gam0 i (plOf i dc w), Ine_le_Dec _ (D.nd.locNd_chebotarevPlace_mem i (plOf i dc w))⟩

def ζO (w : ℕ) : D.nd.O i := D.nd.zeta i (plOf i dc w)

def nQ (w : ℕ) (g : decs D.host.E (Aw i dc) w) : ℕ :=
  if h : ∃ n : ℕ, D.nd.chi i 1 (g : GE D.nd) = D.nd.chi i 1 (γQ i dc w : GE D.nd) ^ n then Nat.find h else 0

def QPow : Prop :=
  ∀ v ∈ D.nd.Q i, ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v),
    ∃ n : ℕ, D.nd.chi i 1 g = D.nd.chi i 1 (D.nd.gam0 i v) ^ n

end Places

section Ring
variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def ζ (w : ℕ) : Dd.T' := ((Dd.χ (γQ i dc w : GE D.nd) : Dd.T'ˣ) : Dd.T')

abbrev Mc (c : Fin (D.R.t + 1)) : Type := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c

abbrev resU (c : Fin (D.R.t + 1)) (w : ℕ) :=
  resRep (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ) (decs D.host.E (Aw i dc) w)

def Fpos (c : Fin (D.R.t + 1)) (w : ℕ) : Submodule (D.nd.O i) (H1z (resU i dc Dd c w)) :=
  if w ∈ qsN i dc then unrH1 (resU i dc Dd c w) (I i dc w)
  else if w ∈ rowsN i dc then
    (if (c : ℕ) = 1 then lcH1 (resU i dc Dd c w) ⊓
        unrH1 (resU i dc Dd c w) ((Ine (F := D.host.E) (Aw i dc w)).subgroupOf (decs D.host.E (Aw i dc) w))
      else ⊥)
  else if (c : ℕ) = 1 then unrH1 (resU i dc Dd c w) (I i dc w) else ⊥

def Fall (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1)) (w : ℕ) :
    Submodule (D.nd.O i) (H1z (resU i dc Dd c w)) :=
  Fin.cases (motive := fun c => Submodule (D.nd.O i) (H1z (resU i dc Dd c w))) (F0 w)
    (fun c' => Fpos i dc Dd c'.succ w) c

def c1 : Fin (D.R.t + 1) := ⟨1, by have := RepresentationBoundsCohomology.one_le_letterBlockLength D.R; omega⟩

def InertiaActsTrivially : Prop := ∀ v, ∀ g ∈ Io i v, Dd.r g = 1 ∧ Dd.χ g = 1

def LocClause (c : Fin (D.R.t + 1)) : Prop :=
  InChiLoc (Mc i Dd c) Dd.r Dd.χ Dd.E (decs D.host.E (Aw i dc)) (qsN i dc) (Fpos i dc Dd c) (Io i) (IS i)
    (I i dc) (γQ i dc) (ζ i dc Dd) (ζO i dc) (nQ i dc)

def CoverClause : Prop :=
  ∀ v, (∃ a, Ine (F := D.host.E) (Av v) ≤ Io i a) ∨ (∃ a, Ine (F := D.host.E) (Av v) ≤ IS i a) ∨
    ∃ w ∈ rowsN i dc ∪ qsN i dc ∪ univ.image (colIdx i dc), ∃ J : Subgroup (decs D.host.E (Aw i dc) w),
      Fpos i dc Dd (c1 (D := D)) w ≤ unrH1 (resU i dc Dd (c1 (D := D)) w) J ∧
      Ine (F := D.host.E) (Av v) ≤ J.map (decs D.host.E (Aw i dc) w).subtype

def NoFixedVectorOffZ : Prop :=
  ∀ x', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) →
    ∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing (D.nd.O i))
        (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.E), η ≠ 0 →
      ∃ g : GE D.nd, ((((Dd.χ g)⁻¹ : Dd.T'ˣ) : Dd.T') • Dd.r g) • η ≠ η

end Ring

end Formalism.MainNotions.N.K.QS

end
end
