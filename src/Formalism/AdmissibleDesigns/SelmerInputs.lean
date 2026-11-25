module

public import Formalism.AdmissibleDesigns.Base
public import Formalism.AdmissibleDesigns.Cohomology
public import Formalism.AdmissibleDesigns.DeRham
public import Formalism.AdmissibleDesigns.KernelLengthHigherColumns
public import Formalism.AdmissibleDesigns.LocalCohom
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypes
public import Formalism.SharpRestriction.LevelLetterCocycles.LargeLevelLemmas
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.WachLatticeTwists.RealDisplaySplitting.RealDisplayProofs.SurjectionOfRankOneIdempotent
import Formalism.WachLatticeTwists.SplitClassesAll.Statement
import Formalism.WachLatticeTwists.SplitLocalLifts.Statement
import Formalism.WeaklyAdmissibleFiltrations.CrystallineStableLifts.Galois
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.GaloisValuations.ArithOfA
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.N.K.Topo

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (dc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem topoHyps
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (u : ℤ_[D.nd.l i]ˣ)
    (hcyc : ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) =
      1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * (u : ℤ_[D.nd.l i])) :
    letI := fracTopology (D.nd.O i); letI := rTopology (D.nd.O i) Dd.R';
    Function.Injective (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) ∧ PadicCoeff (D.nd.l i) (D.nd.O i) ∧
      FracTop (D.nd.O i) ∧ IsFGTop (D.nd.O i) Dd.R' ∧ IsCycG (D.nd.l i) (epsU D.nd i) ∧
      (Continuous fun g : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) => uElt Dd.r Dd.χ g) ∧
      (∀ v, IsPlaceOver (Formalism.MainNotions.N.K.Av (D := D) v) v) ∧
      (D.nd.l i ≠ 2 ∨ InfinitePlace.nrRealPlaces D.host.E = 0) ∧
      1 ≤ D.nd.s0 i ∧ (D.nd.l i = 2 → 2 ≤ D.nd.s0 i) ∧
      ((epsU D.nd i g0 : (D.nd.O i)ˣ) : D.nd.O i) - 1 =
        ((D.nd.l i : ℕ) : D.nd.O i) ^ D.nd.s0 i * ((yU i u : (D.nd.O i)ˣ) : D.nd.O i) ∧
      (∀ w ∈ Formalism.MainNotions.N.K.rowsN i dc, (Formalism.MainNotions.N.K.Aw i dc w).valuation ((D.nd.l i : ℕ) : D.nd.Om) < 1 ∧
        IsPlaceOver (Formalism.MainNotions.N.K.Aw i dc w) (Formalism.MainNotions.N.K.plOf i dc w)) := by
  refine ⟨?_, padicCoeff_O i, fracTop_O i, fgTop_RD i r π g0 eB e₁ s Dd hD, ?_, uElt_cont i r π g0 eB e₁ s Dd hD hc,
    av_over, ?_, one_le_localLevel i, restNLevelExponent_of_two i, ?_, rows_over i dc⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 : algebraMap ℤ_[D.nd.l i] (D.nd.O i)
        ((PadicInt.unitCoeff h0 : ℤ_[D.nd.l i]) * (D.nd.l i : ℤ_[D.nd.l i]) ^ x.valuation) = 0 := by
      rw [← PadicInt.unitCoeff_spec h0]
      exact hx
    rw [map_mul, map_pow, map_natCast] at h1
    rcases mul_eq_zero.mp h1 with h | h
    · exact ((PadicInt.unitCoeff h0).isUnit.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))).ne_zero h
    · exact (padicCoeff_O i).p_ne (pow_eq_zero_iff'.mp h).1
  · apply isCyc_eps
  · apply l_or_noReal
  · have h2 : ((epsU D.nd i g0 : (D.nd.O i)ˣ) : D.nd.O i) = algebraMap ℤ_[D.nd.l i] (D.nd.O i)
        ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) := rfl
    rw [h2, hcyc]
    simp [yU]

end Formalism.MainNotions.N.K.Topo

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

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

abbrev HfWS (w : ℕ) :=
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  KHf.HfW i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) w

abbrev Hf₂S (w : ℕ) :=
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  KHf.Hf₂ i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) w

abbrev FsS (w : ℕ) :=
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  KHf.Fs i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) w

abbrev Hf₁S (w : ℕ) :
    haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
    Submodule (D.nd.O i) (H1 (resRep (rho1 i Dd) (KHf.Γn i dc w))) :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  KHf.Hf₁ i dc (rho1 i Dd) w

def FirstBlockLocalConditions (w : ℕ) : Submodule (D.nd.O i) (H1z (QS.resU i dc Dd 0 w)) :=
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  KHf.Fρ i dc (rowsN i dc) (fun n => QS.resU i dc Dd 0 n)
    (fun n => (((HfWS i r π dc g0 eB e₁ s Dd hD hc n).restrictScalars (D.nd.O i)).map (DatS i r π dc g0 eB e₁ s Dd hD hc n).q).map
      (kRow (DatS i r π dc g0 eB e₁ s Dd hD hc n) _ (uDS i r π dc g0 eB e₁ s Dd hD hc n) (huDS i r π dc g0 eB e₁ s Dd hD hc n)))
    (fun n => KHf.F0col i dc n (resRep (uRep (D.nd.O i) (M := Vr i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) n))
      (QS.resU i dc Dd 0 n) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)) w

abbrev FS := QS.Fall i dc Dd (FirstBlockLocalConditions i r π dc g0 eB e₁ s Dd hD hc)

theorem FS_pos (c : Fin (D.R.t + 1)) (hc0 : c ≠ 0) (w : ℕ) : FS i r π dc g0 eB e₁ s Dd hD hc c w = QS.Fpos i dc Dd c w := by
  obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.2 hc0
  exact Fin.cases_succ c'

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

abbrev ImS (w : ℕ) :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  (Hf₁S i r π dc g0 eB e₁ s Dd hD w).map (gRow (DatS i r π dc g0 eB e₁ s Dd hD hc w) (resRep (rho1 i Dd) (decs D.host.E (Aw i dc) w))
    (piS i Dd hT hrk) (vDS i r π dc g0 eB e₁ s Dd hD hc w) (hpDS i r π dc g0 eB e₁ s Dd hD hc hT hrk w) (heDS i r π dc g0 eB e₁ s Dd hD hc hT hrk w))

def rowLenS (w : ℕ) : ℕ∞ :=
  Module.length (D.nd.O i) (FsS i r π dc g0 eB e₁ s Dd hD hc w ⧸ (ImS i r π dc g0 eB e₁ s Dd hD hc hT hrk w).comap (FsS i r π dc g0 eB e₁ s Dd hD hc w).subtype)

set_option synthInstance.maxHeartbeats 400000 in
theorem selmer_inequality_of_inputs [IsNoetherian Dd.R' Dd.R']
    [∀ x', IsScalarTower Dd.T' Dd.R' (EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')]
    [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
    [∀ k, IsScalarTower (D.nd.O i) Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (hP : Formalism.RepresentationBoundsCohomology.ringDataObjects.PrimHyp (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (RepresentationBoundsCohomology.blk D.R) (chiU D.nd i 1) (epsU D.nd i))
    (u0 : ℤ_[D.nd.l i]ˣ)
    (hcyc : ((cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g0 : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i]) =
      1 + (D.nd.l i : ℤ_[D.nd.l i]) ^ D.nd.s0 i * (u0 : ℤ_[D.nd.l i]))
    (hK : ∀ [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
          [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))] [TopologicalSpace Dd.R']
          [IsTopologicalAddGroup Dd.R'] [ContinuousConstSMul (D.nd.O i) Dd.R'] [ContinuousMul Dd.R'],
          RealDisplayAllK (D.nd.l i) (D.nd.O i) (D.nd.X i) Dd.X' (D.nd.Z i : Set (D.nd.X i)) Dd.p (Fin D.R.nV)
            Dd.R' Dd.T' D.host.E D.nd.Om Dd.r Dd.χ Dd.E Dd.e₁ D.R.t (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) (RepresentationBoundsCohomology.blk D.R) Dd.ρk Dd.δO
            (epsU D.nd i) g0 (Module.length (D.nd.O i) (D.nd.O i ⧸ ccAt (D.nd.T i) (D.nd.Z i) π)))
    (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ) (e' : HeightOneSpectrum (𝓞 D.host.E) → ℕ) (cB : ℕ)
    (κ : ∀ l : Col i dc, Fin (jN i ρ π dc (colIdx i dc l)) → GE D.nd → Lr i Dd)
    (κz : ∀ l : Col i dc, Fin (jN i ρ π dc (colIdx i dc l)) →
      coZ1s (resRep (uRep (D.nd.O i) (M := Lr i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) (colIdx i dc l))))
    (u : Col i dc → GE D.nd → D.nd.O i)
    (uz : ∀ l : Col i dc,
      coZ1s (Representation.trivial (D.nd.O i) ↥(decs D.host.E (Aw i dc) (colIdx i dc l)) ↥(Ideal.span {Dd.δO})))
    (hUz : ∀ l (g : decs D.host.E (Aw i dc) (colIdx i dc l)),
      (((uz l : decs D.host.E (Aw i dc) (colIdx i dc l) → ↥(Ideal.span {Dd.δO})) g : ↥(Ideal.span {Dd.δO})) :
        D.nd.O i) = Dd.δO * u l g)
    (hUnr : KHf.UnrFin i dc Dd.δO uz)
    (hL1 : ∀ l, LiftO (D.nd.l i) (KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l)
      (KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l)
      (mapH1 _ _ (eveS i Dd hT hrk) (ev_equiv Dd.r Dd.χ (decs D.host.E (Aw i dc) (colIdx i dc l))
        (incl (D.nd.O i) Dd.e₁) (v1S i Dd hT hrk) (eveS i Dd hT hrk) (fun a => rfl))) (e'N i dc e' (colIdx i dc l)))
    (hL2 : ∀ l, LiftO (D.nd.l i) (KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l) (KHf.HfE₂ i dc Dd.δO l)
      (mapH1 _ _ (evES i Dd hT) (ev_equiv_triv Dd.r Dd.χ (decs D.host.E (Aw i dc) (colIdx i dc l)) (evES i Dd hT)
        (hevES i Dd hT))) (e'N i dc e' (colIdx i dc l)))
    (hG6 : QS.NoFixedVectorOffZ i Dd)
    (hLx : ∀ x' : Dd.X', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) → ∀ l : Col i dc,
      ∃ Lx : Submodule (FractionRing (D.nd.O i))
          ((decs D.host.E (Aw i dc)) (colIdx i dc l) → EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'),
        LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
          ((decs D.host.E (Aw i dc)) (colIdx i dc l))) ≤ Lx ∧
        (∀ (f : LeftId (D.nd.O i) Dd.e₁ →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.e₁) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.e₁) g)) ∈ Lx) ∧
        (∀ (f : LeftId (D.nd.O i) Dd.E →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.E) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.E) g)) ∈ Lx) ∧
        Module.rank (FractionRing (D.nd.O i))
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))).comap Lx.subtype) ≤
          (jN i ρ π dc (colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
            (LinearMap.ker
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))) : ℕ))
    (hRho : InRhoFixReal2 (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ Dd.e₁ (colIdx i dc) (decs D.host.E (Aw i dc))
      (jN i ρ π dc) (rowsN i dc) (sN i ρ π) (tensM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (v1S i Dd hT hrk) κ
      (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)
      (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) κz (FS i r π dc g0 eB e₁ s Dd hD hc 0)
      (QS.Io i) (epsU D.nd i) (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk)
      (gamM (Dd.ρk 0)) (lamS i Dd hT hrk))
    (hBKa : ∀ w ∈ rowsN i dc, ∀ a, a ∈ HfWS i r π dc g0 eB e₁ s Dd hD hc w ↔
      ∀ b ∈ Hf₂S i r π dc g0 eB e₁ s Dd hD hc w, cupFG (DatS i r π dc g0 eB e₁ s Dd hD hc w) a b = 0)
    (hTB : ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) → ∀ w ∈ rowsN i dc,
      (∀ ψ : Ymod Dd.r Dd.χ Dd.E →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c,
        (∀ g ∈ (decs D.host.E (Aw i dc)) w, ∀ y, ψ (uElt Dd.r Dd.χ g • y) = uElt Dd.r Dd.χ g • ψ y) →
        ∀ z : coZ1s (QS.resU i dc Dd c w),
          (∀ g : (decs D.host.E (Aw i dc)) w, (z : (decs D.host.E (Aw i dc)) w → blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) g =
            ψ (yY Dd.r Dd.χ Dd.E (g : GE D.nd))) →
          (((D.nd.l i : ℕ) : D.nd.O i) ^ cB) • (Submodule.mkQ _ z : H1z (QS.resU i dc Dd c w)) ∈ FS i r π dc g0 eB e₁ s Dd hD hc c w) ∧
      Module.length (D.nd.O i) (↥(lcH1 (QS.resU i dc Dd c w) ⊓ divBy (FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)) ⧸
        (FS i r π dc g0 eB e₁ s Dd hD hc c w).comap (lcH1 (QS.resU i dc Dd c w) ⊓ divBy (FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)).subtype) ≤
        eON i * (cB : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 1))
    (hChi : ∀ c : Fin (D.R.t + 1), 2 ≤ (c : ℕ) →
      InChiFixReal (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) Dd.r Dd.χ Dd.E (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc)
        (qsN i dc) (ShaN i ((c : ℕ) - 1)) (FS i r π dc g0 eB e₁ s Dd hD hc c) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd)
        (QS.ζO i dc) (QS.nQ i dc))
    (hU1 : (∀ l, ∀ g ∈ QS.I i dc (colIdx i dc l), u l (g : GE D.nd) = 0) ∧
      (∀ l, ∃ g ∈ (decs D.host.E (Aw i dc)) (colIdx i dc l), u l g = 1))
    (hLoc1 : InChiLoc (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk QS.c1) Dd.r Dd.χ Dd.E (decs D.host.E (Aw i dc)) (qsN i dc)
      (FS i r π dc g0 eB e₁ s Dd hD hc QS.c1) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd) (QS.ζO i dc) (QS.nQ i dc))
    (hCover : ∀ v, (∃ a, Ine (F := D.host.E) (Av (D := D) v) ≤ QS.Io i a) ∨
      (∃ a, Ine (F := D.host.E) (Av (D := D) v) ≤ QS.IS i a) ∨
        ∃ w ∈ rowsN i dc ∪ qsN i dc ∪ univ.image (colIdx i dc), ∃ J : Subgroup ((decs D.host.E (Aw i dc)) w),
          FS i r π dc g0 eB e₁ s Dd hD hc QS.c1 w ≤ unrH1 (QS.resU i dc Dd QS.c1 w) J ∧
          Ine (F := D.host.E) (Av (D := D) v) ≤ J.map ((decs D.host.E (Aw i dc)) w).subtype)
    (hCR : ∀ l : Col i dc, colIdx i dc l ∉ rowsN i dc) (hRQ : ∀ w ∈ rowsN i dc, w ∉ qsN i dc)
    (hTie : TieRow i dc (rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk) lenRow) :
    SelmerLengthInequality i ρ π dc lenRow e' cB := by
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  haveI := Topo.rTop_mul_RD i r π g0 eB e₁ s Dd hD
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩ := Topo.topoHyps i r π dc g0 eB e₁ s Dd hD hc u0 hcyc
  have hA := tensor_lattice_facts Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk (epsU D.nd i)
  have hL := fun w => KLat.rowLat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) (D.nd.l i) (Topo.padicCoeff_O i) (Topo.fracTop_O i) w
  have H := hK (Col i dc) (colIdx i dc) (colIdx_inj i dc) (Aw i dc) (plOf i dc) (Av (D := D)) (jN i ρ π dc)
    (e'N i dc e') (rowsN i dc) (qsN i dc) (sN i ρ π) (invariantsLengthSup i dc) (ShaN i) cB (fun _ _ => cB)
    (Lr i Dd) (tensM _ _ _) (v1S i Dd hT hrk) κ (Vr i Dd) (iLM _ _ _) (qVM _ _ _)
    (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) κz (FS i r π dc g0 eB e₁ s Dd hD hc)
    (QS.Vo i) (QS.VS i) (QS.Io i) (QS.IS i) (FirstSummandSubmodule (D.nd.O i) Dd.e₁) ({a // RepresentationBoundsCohomology.blk D.R a = 0} → D.nd.O i)
    (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk) (gamM (Dd.ρk 0)) (lamS i Dd hT hrk)
    (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) (uDS i r π dc g0 eB e₁ s Dd hD hc) (huDS i r π dc g0 eB e₁ s Dd hD hc) (vDS i r π dc g0 eB e₁ s Dd hD hc) (hpDS i r π dc g0 eB e₁ s Dd hD hc hT hrk) (heDS i r π dc g0 eB e₁ s Dd hD hc hT hrk)
    (FsS i r π dc g0 eB e₁ s Dd hD hc) (Hf₁S i r π dc g0 eB e₁ s Dd hD) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd) (QS.ζO i dc) (QS.nQ i dc)
    u (D.nd.s0 i) (Topo.yU i u0) (HfWS i r π dc g0 eB e₁ s Dd hD hc) (Hf₂S i r π dc g0 eB e₁ s Dd hD hc)
    (LeftId (D.nd.O i) Dd.e₁) (incl _ Dd.e₁) (eveS i Dd hT hrk) (fun a => rfl)
    (LeftId (D.nd.O i) Dd.E) (incl _ Dd.E) (evES i Dd hT) (hevES i Dd hT)
    (fun l => KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l)
    (fun l => KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l) (fun l => KHf.HfE₂ i dc Dd.δO l) uz
  have hrows : ∀ w ∈ rowsN i dc, FS i r π dc g0 eB e₁ s Dd hD hc 0 w = (((HfWS i r π dc g0 eB e₁ s Dd hD hc w).restrictScalars (D.nd.O i)).map (DatS i r π dc g0 eB e₁ s Dd hD hc w).q).map
      (kRow (DatS i r π dc g0 eB e₁ s Dd hD hc w) _ (uDS i r π dc g0 eB e₁ s Dd hD hc w) (huDS i r π dc g0 eB e₁ s Dd hD hc w)) := by
    intro w hw
    exact ite_eq_left hw
  have hc1_val : (QS.c1 (D := D) : ℕ) = 1 := rfl
  have hF1 := FS_pos i r π dc g0 eB e₁ s Dd hD hc QS.c1 (Fin.ne_of_val_ne Nat.one_ne_zero)
  have hdisplay := H t1 t2 t3 t4 t5 (inc_cont (O := D.nd.O i) Dd.e₁) t6 t7 t8 t9 t10 t11 hA.2.2.1 hA.2.2.2.2.1 hA.2.2.2.2.2.1
    hA.2.2.2.2.2.2.1 hUz hUnr hL1 hL2 (fun x' hx => ⟨hG6 x' hx, hLx x' hx⟩) hRho
    (fun w hw => ⟨(t12 w hw).1, (t12 w hw).2, (hL w).1, (hL w).2.1, (hL w).2.2.1, (hL w).2.2.2, hBKa w hw,
      hrows w hw, rfl,
      KHf.im_le_Fs i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (DatS i r π dc g0 eB e₁ s Dd hD hc) w (rho1 i Dd) (piS i Dd hT hrk) (vDS i r π dc g0 eB e₁ s Dd hD hc w) (hpDS i r π dc g0 eB e₁ s Dd hD hc hT hrk w)
        (heDS i r π dc g0 eB e₁ s Dd hD hc hT hrk w)⟩)
    (fun c hc2 => ⟨H0.kernel_length_higher_columns dc hN hD c hc2,
      fun w hw => by
        have hc_pos : 1 ≤ (c : ℕ) := Nat.le_trans (Nat.le_succ 1) hc2
        have hc0 : c ≠ 0 := Fin.ne_of_val_ne (Nat.ne_of_gt hc_pos)
        have hc1 : (c : ℕ) ≠ 1 := Nat.ne_of_gt hc2
        refine ⟨?_, le_rfl, hTB c hc_pos w hw⟩
        exact (FS_pos i r π dc g0 eB e₁ s Dd hD hc c hc0 w).trans
          ((ite_eq_right (hRQ w hw)).trans ((ite_eq_left hw).trans (ite_eq_right hc1))),
      hChi c hc2⟩)
    ⟨hU1.1, hU1.2, fun l => by
        refine le_of_eq ((hF1 (colIdx i dc l)).trans ?_).symm
        by_cases hq : colIdx i dc l ∈ qsN i dc
        · exact ite_eq_left hq
        · exact (ite_eq_right hq).trans ((ite_eq_right (hCR l)).trans (ite_eq_left hc1_val)),
      fun w hw => by
        refine ⟨?_, le_rfl, hTB QS.c1 le_rfl w hw⟩
        exact (hF1 w).trans ((ite_eq_right (hRQ w hw)).trans ((ite_eq_left hw).trans (ite_eq_left hc1_val))),
      hLoc1, hCover⟩
  exact ⟨rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk, H0.h0d i dc Dd, IsDiscreteValuationRing.addVal (D.nd.O i) Dd.δO,
    Fintype.card {a // RepresentationBoundsCohomology.blk D.R a = 0}, hdisplay.2.1, card_first_block (D := D),
    hdisplay.1, hTie,
    H0.invariants_display_match i r ρ π dc g0 eB e₁ s Dd hD hN⟩

end Formalism.MainNotions.N.K.St

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KOrb

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem contW_rec (hd : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (l : K.Col i dc) :
    KDim.ContW (i := i) (dc := dc) (ρ := ρ) (π := π) l :=
  contW_of i dc ρ π (K.Norm.rhoCont_of i r ρ π hd hc) l

end Formalism.MainNotions.N.KOrb

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KHf

open Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.NG

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  {X' : Type} {d : Type} [Fintype d] [DecidableEq d]
  {R' : Subalgebra (D.nd.O i) (X' → Matrix d d (FractionRing (D.nd.O i)))} {Tc : Type} [CommRing Tc] [Algebra Tc R']
  (r : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* R') (χ : (D.nd.Om ≃ₐ[D.host.E] D.nd.Om) →* Tcˣ)

theorem exists_Lx {Pe : Type} [AddCommGroup Pe] [Module R' Pe] [Module (D.nd.O i) Pe] [SMulCommClass R' (D.nd.O i) Pe]
    {PE : Type} [AddCommGroup PE] [Module R' PE] [Module (D.nd.O i) PE] [SMulCommClass R' (D.nd.O i) PE]
    (hPe : ∀ (c : D.nd.O i) (m : Pe), c • m = (algebraMap (D.nd.O i) R' c) • m)
    (hPE : ∀ (c : D.nd.O i) (m : PE), c • m = (algebraMap (D.nd.O i) R' c) • m)
    (j : ℕ → ℕ) (x' : X') (l : K.Col i dc)
    (hO : letI := evalModO i (R' := R') x'
      haveI := evalTower i (R' := R') x'
      OrbC i dc (repE i dc r χ x' (K.colIdx i dc l)))
    (hdim : DimLx i dc r χ j x' l) :
    ∃ Lx : Submodule (FractionRing (D.nd.O i)) (↥(Γn i dc (K.colIdx i dc l)) → EvalSp (D.nd.O i) d R' x'),
      LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
        (Γn i dc (K.colIdx i dc l))) ≤ Lx ∧
      (∀ (f : Pe →ₗ[R'] EvalSp (D.nd.O i) d R' x')
        (z : coZ1s (resRep (uRep (D.nd.O i) (M := Pe) r χ) (Γn i dc (K.colIdx i dc l)))),
        Submodule.mkQ _ z ∈ Hfe₁ i dc r χ (Pe := Pe) l →
        (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → Pe) g)) ∈ Lx) ∧
      (∀ (f : PE →ₗ[R'] EvalSp (D.nd.O i) d R' x')
        (z : coZ1s (resRep (uRep (D.nd.O i) (M := PE) r χ) (Γn i dc (K.colIdx i dc l)))),
        Submodule.mkQ _ z ∈ Hfe₁ i dc r χ (Pe := PE) l →
        (fun g : Γn i dc (K.colIdx i dc l) => f ((z : Γn i dc (K.colIdx i dc l) → PE) g)) ∈ Lx) ∧
      Module.rank (FractionRing (D.nd.O i))
          (Lx ⧸ (LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
            (Γn i dc (K.colIdx i dc l)))).comap Lx.subtype) ≤
        (j (K.colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
          (LinearMap.ker (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) d R' x') r χ
            (Γn i dc (K.colIdx i dc l)))) : ℕ) := by
  refine ⟨Lx i dc r χ x' l, ?_, ?_, ?_, hdim⟩
  · apply colD_le_Lx <;> assumption
  · intro f z hz
    apply comp_mem_Lx <;> assumption
  · intro f z hz
    apply comp_mem_Lx <;> assumption

end Formalism.MainNotions.N.KHf

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StA

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

theorem r_pos (D : D7) : 0 < D.R.r := by
  have h := D.R.m_add_three_le_k
  show 0 < D.R.k + D.R.m - 1
  omega

theorem card_pos (D : D7) : 0 < Fintype.card (Fin D.R.nV) := by
  rw [Fintype.card_fin]
  have h := D.R.m_add_three_le_k
  show 0 < D.R.k + D.R.m - 1 + D.R.t
  omega

theorem jN_eq {D : D7} (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (dc : TruncatedSeriesCountingIdentities.Decl D i) : jN i ρ π dc = KHf.jK i dc ρ π := rfl

theorem leftId_alg {O : Type} [CommRing O] {A : Type} [Ring A] [Algebra O A] (x : A) (c : O) (m : LeftId O x) :
    c • m = (algebraMap O A c) • m := by
  exact Subtype.ext (Algebra.smul_def c m.1)

section Cols

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))

theorem colUz : ∀ l (g : decs D.host.E (Aw i dc) (colIdx i dc l)),
    (((KFin.uz i dc Dd.δO l : decs D.host.E (Aw i dc) (colIdx i dc l) → ↥(Ideal.span {Dd.δO})) g :
      ↥(Ideal.span {Dd.δO})) : D.nd.O i) = Dd.δO * KFin.u i dc l g := by
  intro l g
  first
  | (show Dd.δO * KFin.uCol i dc l g = Dd.δO * KFin.u i dc l g
     rw [KFin.u, dite_eq_left (show ((g : GE D.nd)) ∈ KFin.Γc i dc l from g.2)])

theorem column_unramified_character : (∀ l, ∀ g ∈ QS.I i dc (colIdx i dc l), KFin.u i dc l (g : GE D.nd) = 0) ∧
    (∀ l, ∃ g ∈ (decs D.host.E (Aw i dc)) (colIdx i dc l), KFin.u i dc l g = 1) :=
  ⟨fun l => KFin.u_I i dc l (KUnr.unrHom i dc l), fun l => KFin.u_one i dc l (KUnr.unrHom i dc l)⟩

variable [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem colLx_of_ringDef
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hBK : TruncatedSeriesCountingIdentities.admBK i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hFont : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i)
    (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCr : ∀ x' l, KDim.CrysX i dc Dd.r Dd.χ x' l) (hNeg : ∀ x' l, KDim.NegX i dc Dd.r Dd.χ ρ π x' l)
    (hFin : ∀ x' l, KDim.FinX i dc Dd.r Dd.χ x' l) (hCrW : ∀ l, KDim.CrysW i dc ρ π l) :
    ∀ x' : Dd.X', Dd.p x' ∉ (D.nd.Z i : Set (D.nd.X i)) → ∀ l : Col i dc,
      ∃ Lx : Submodule (FractionRing (D.nd.O i))
          ((decs D.host.E (Aw i dc)) (colIdx i dc l) → EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x'),
        LinearMap.range (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
          ((decs D.host.E (Aw i dc)) (colIdx i dc l))) ≤ Lx ∧
        (∀ (f : LeftId (D.nd.O i) Dd.e₁ →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.e₁) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.e₁) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.e₁) g)) ∈ Lx) ∧
        (∀ (f : LeftId (D.nd.O i) Dd.E →ₗ[Dd.R'] EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x')
          (z : coZ1s (resRep (uRep (D.nd.O i) (M := LeftId (D.nd.O i) Dd.E) Dd.r Dd.χ)
            ((decs D.host.E (Aw i dc)) (colIdx i dc l)))),
          Submodule.mkQ _ z ∈ KHf.Hfe₁ i dc Dd.r Dd.χ (Pe := LeftId (D.nd.O i) Dd.E) l →
          (fun g : (decs D.host.E (Aw i dc)) (colIdx i dc l) =>
            f ((z : (decs D.host.E (Aw i dc)) (colIdx i dc l) → LeftId (D.nd.O i) Dd.E) g)) ∈ Lx) ∧
        Module.rank (FractionRing (D.nd.O i))
            (Lx ⧸ (LinearMap.range
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))).comap Lx.subtype) ≤
          (jN i ρ π dc (colIdx i dc l) + Module.finrank (FractionRing (D.nd.O i))
            (LinearMap.ker
              (colD (K := FractionRing (D.nd.O i)) (V := EvalSp (D.nd.O i) (Fin D.R.nV) Dd.R' x') Dd.r Dd.χ
                ((decs D.host.E (Aw i dc)) (colIdx i dc l)))) : ℕ) := by
  intro x' _ l
  have hO := KOrb.orbC_repE i dc r π g0 eB e₁ s Dd hD hc x' (colIdx i dc l)
  have hdim : KHf.DimLx i dc Dd.r Dd.χ (KHf.jK i dc ρ π) x' l :=
    KDim.dimLx_of_font i dc Dd.r Dd.χ ρ π r x' l (card_pos D) (r_pos D) hBK hG2 hFont
      (KDim.contX_of_orbC i dc Dd.r Dd.χ x' l hO) (hCr x' l) (hNeg x' l) (hFin x' l) (hCrW l)
      (KOrb.contW_rec i dc r ρ π hDec hc l)
  rw [jN_eq]
  exact KHf.exists_Lx i dc Dd.r Dd.χ (leftId_alg Dd.e₁) (leftId_alg Dd.E) (KHf.jK i dc ρ π) x' l hO hdim

end Cols

end Formalism.MainNotions.N.K.StA

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Font

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.KHf Formalism.MainNotions.N.KDim NumberField IsDedekindDomain Formalism.NG Formalism.BasicNotions

section RhoC

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

theorem rhoCont_of (hc : TruncatedSeriesCountingIdentities.FamilyContinuous i r) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) :
    Continuous fun g => rhoO D.nd i ρ π g := by
  have h : (fun g => rhoO D.nd i ρ π g) = fun g => (fun a b => rO D.nd i r π g (Fin.castAdd D.R.t a) (Fin.castAdd D.R.t b) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) := by
    funext g
    exact Matrix.ext fun a b => (hN.2.2 g a b).symm
  rw [h]
  exact continuous_pi fun a => continuous_pi fun b => (hc π).matrix_elem _ _

end RhoC

section Lat

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))]
  (hK : ContinuousMul (FractionRing (D.nd.O i)))
  (hε : Continuous fun g => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i))
  (hM : ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b)

def phiW (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    TrV (eK (D.nbr i _ hn)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R) n) ≃ₗ[Br.LL D.nbr i _ hn]
      (Fin D.R.r → Br.LL D.nbr i _ hn) where
  toFun v a := eK (D.nbr i _ hn) ((v : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 a))
  invFun w := (show {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i) from
    fun b => (eK (D.nbr i _ hn)).symm (w ((H0.e0 (D := D)).symm b)))
  map_add' u v := funext fun a => map_add (eK (D.nbr i _ hn)) _ _
  map_smul' c v := funext fun a => by
    show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm c * _) = c * _
    rw [map_mul, RingEquiv.apply_symm_apply]
  left_inv v := by
    funext b
    show (eK (D.nbr i _ hn)).symm (eK (D.nbr i _ hn) (_ : FractionRing (D.nd.O i))) = _
    rw [RingEquiv.symm_apply_apply, Equiv.apply_symm_apply]
  right_inv w := by
    funext a
    show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm (w ((H0.e0 (D := D)).symm (H0.e0 a)))) = w a
    rw [RingEquiv.apply_symm_apply, Equiv.symm_apply_apply]

theorem wpIso_dat (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    WpIso i dc ρ π n hn (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT := by
  refine ⟨phiW i dc n hn, fun g x => funext fun a => ?_⟩
  show eK (D.nbr i _ hn) ((KLat.matK (Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)))).mulVec
      (x : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 a)) =
    ∑ b, Br.loc D.nbr i _ hn (WpO D.nd i ρ π) g a b * eK (D.nbr i _ hn) ((x : {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i)) (H0.e0 b))
  refine (congrArg (eK (D.nbr i _ hn)) (KLat.matK_mulVec (Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : _) : GE D.nd)))
    (show {a // RepresentationBoundsCohomology.blk D.R a = 0} → FractionRing (D.nd.O i) from x) (H0.e0 a))).trans ?_

  rw [map_sum]
  refine (Equiv.sum_comp (H0.e0 (D := D)) _).symm.trans (Finset.sum_congr rfl fun b _ => ?_)
  rw [Algebra.smul_def, map_mul, loc_apply, H0.unipotent_block_zero_entry hD hN]

end Lat

section RowDR2

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (g0 : GE D.nd)
  (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))]
  (hK : ContinuousMul (FractionRing (D.nd.O i)))
  (hε : Continuous fun g => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i))
  (hM : ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b)

theorem isDR_dat (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hCont : TruncatedSeriesCountingIdentities.FamilyContinuous i r)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0
      eB e₁ s Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (n : ℕ) (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    IsDR (Br.PD D.loc D.nbr i _ hn) (repL (eK (D.nbr i _ hn))
      (KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (K.Aw i dc) hK hε hM n).ρT (Br.iota D.nbr i _ hn)) :=
  isDR_of_wpIso i dc r ρ π hF hG2 hDec hCont (rhoCont_of i r ρ π hCont hN) n hn _ (wpIso_dat i dc r ρ π g0 eB e₁ s Dd hK hε hM hD hN n hn)

end RowDR2

end Formalism.MainNotions.N.K.Font

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.ShaT

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K
open Formalism.MainNotions.N.K.QS Formalism.RepresentationBoundsCohomology.FIN Pointwise

section Coc

variable {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M] (ρ : Representation R G M)

theorem coc_one (c : coZ1s ρ) : (c : G → M) 1 = 0 := by
  have h := c.2 1 1
  simp only [mul_one, map_one, Module.End.one_apply] at h
  have h' : (c : G → M) 1 + (c : G → M) 1 = (c : G → M) 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel h'

theorem coc_conj (c : coZ1s ρ) (σ n : G) (hn : ∀ m, ρ n m = m) :
    (c : G → M) (σ * n * σ⁻¹) = ρ σ ((c : G → M) n) := by
  have h1 := c.2 (σ * n) σ⁻¹
  have h2 := c.2 σ n
  have h3 := c.2 σ σ⁻¹
  rw [mul_inv_cancel, coc_one] at h3
  rw [h1, h2, map_mul, Module.End.mul_apply, hn]
  have : (c : G → M) σ + ρ σ ((c : G → M) σ⁻¹) = 0 := h3.symm
  rw [← sub_eq_zero]
  have e : (c : G → M) σ + ρ σ ((c : G → M) n) + ρ σ ((c : G → M) σ⁻¹) - ρ σ ((c : G → M) n) =
      (c : G → M) σ + ρ σ ((c : G → M) σ⁻¹) := by abel
  rw [e, this]

theorem coc_zero_of_unr (c : coZ1s ρ) (J : Subgroup G) (hJ : ∀ g ∈ J, ∀ m, ρ g m = m)
    (h : resH1 ρ J (Submodule.Quotient.mk c) = 0) : ∀ g ∈ J, (c : G → M) g = 0 := by
  intro g hg
  have h' : restrictCocycles1 ρ J c ∈ (coB1 (resRep ρ J)).comap (coZ1s (resRep ρ J)).subtype :=
    (Submodule.Quotient.mk_eq_zero _).1 h
  obtain ⟨m, hm⟩ := h'
  have h2 : ρ g m - m = (c : G → M) g := congrFun hm ⟨g, hg⟩
  rw [← h2, hJ g hg, sub_self]

end Coc

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (e : ℕ)

abbrev SS : Set (HeightOneSpectrum (𝓞 D.host.E)) := ((D.nd.ldat (D.nd.l i)).S : Set (HeightOneSpectrum (𝓞 D.host.E)))

theorem qzE_eq (g : GE D.nd) (m : Formalism.GaloisCohomology.QZ (D.nd.l i)) :
    qzE i e g m = Formalism.GaloisCohomology.qzTw (D.nd.ldat (D.nd.l i)) (e : ℤ) (toGS D.nd.Om (SS i) g) m := by
  have h := congrArg (fun f => f g) (D.nd.ldat (D.nd.l i)).hchi
  simp only [MonoidHom.comp_apply] at h
  simp only [qzE, Formalism.GaloisCohomology.qzTw, Formalism.GaloisCohomology.scalRep_apply, MonoidHom.zpow_apply, cycE, h]

theorem qzE_NS {n : GE D.nd} (hn : n ∈ NS D.nd.Om (SS i)) (m : Formalism.GaloisCohomology.QZ (D.nd.l i)) : qzE i e n m = m := by
  have h1 : toGS D.nd.Om (SS i) n = 1 := (QuotientGroup.eq_one_iff n).2 hn
  rw [qzE_eq, h1, map_one, Module.End.one_apply]

theorem coc_NS (c : coZ1s (qzE i e)) (hc : IsLocallyConstant (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)))
    (h : ∀ v ∉ SS i, ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) g = 0) :
    ∀ n ∈ NS D.nd.Om (SS i), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) n = 0 := by
  have hNSn : (NS D.nd.Om (SS i)).Normal := inferInstance
  let K : Subgroup (GE D.nd) :=
    { carrier := {n | n ∈ NS D.nd.Om (SS i) ∧ (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) n = 0}
      one_mem' := ⟨(NS D.nd.Om (SS i)).one_mem, coc_one (qzE i e) c⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(NS D.nd.Om (SS i)).mul_mem ha hb, ?_⟩
        rw [c.2 a b, ha', hb', map_zero, add_zero]
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(NS D.nd.Om (SS i)).inv_mem ha, ?_⟩
        have h3 := c.2 a a⁻¹
        rw [mul_inv_cancel, coc_one (qzE i e) c, ha', zero_add, qzE_NS i e ha] at h3
        exact h3.symm }
  have hK : K.Normal := ⟨fun n hn σ => ⟨hNSn.conj_mem n hn.1 σ, by
    rw [coc_conj (qzE i e) c σ n (qzE_NS i e hn.1), hn.2, map_zero]⟩⟩
  have hgen : (⋃ v ∈ (SS i)ᶜ, ⋃ A ∈ {A : ValuationSubring D.nd.Om | IsPlaceOver A v}, Inertia (F := D.host.E) A) ⊆
      (K : Set (GE D.nd)) := by
    intro σ hσ
    have hNS : σ ∈ NS D.nd.Om (SS i) := Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hσ)
    refine ⟨hNS, ?_⟩
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hσ
    obtain ⟨v, hv, A, hA, hσA⟩ := hσ
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 v) hA
    have h1 : τ⁻¹ * σ * τ⁻¹⁻¹ ∈ Ine (F := D.host.E) (τ⁻¹ • A) := conj_mem_Ine_smul (γ := τ⁻¹) hσA
    rw [← hτ, inv_smul_smul, inv_inv] at h1
    have hn : τ⁻¹ * σ * τ ∈ NS D.nd.Om (SS i) := by
      have := hNSn.conj_mem σ hNS τ⁻¹
      simpa using this
    have e1 : σ = τ * (τ⁻¹ * σ * τ) * τ⁻¹ := by group
    rw [e1, coc_conj (qzE i e) c τ _ (qzE_NS i e hn), h v hv _ h1, map_zero]
  have hcl : IsClosed (K : Set (GE D.nd)) := by
    have e2 : (K : Set (GE D.nd)) = (NS D.nd.Om (SS i) : Set (GE D.nd)) ∩ (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) ⁻¹' {0} := rfl
    rw [e2]
    exact (Subgroup.isClosed_topologicalClosure _).inter (hc.isClosed_fiber 0)
  have hle : NS D.nd.Om (SS i) ≤ K :=
    Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal hgen) hcl
  exact fun n hn => (hle hn).2

end Rec

section Coc2

variable {R G M : Type} [CommRing R] [Group G] [AddCommGroup M] [Module R M] (ρ : Representation R G M)

theorem coc_conj_cob (c : coZ1s ρ) (τ k : G) (m0 : M) (hk : (c : G → M) k = ρ k m0 - m0) :
    (c : G → M) (τ * k * τ⁻¹) =
      ρ (τ * k * τ⁻¹) (ρ τ m0 - (c : G → M) τ) - (ρ τ m0 - (c : G → M) τ) := by
  have h1 := c.2 (τ * k) τ⁻¹
  have h2 := c.2 τ k
  have h3 := c.2 τ⁻¹ τ
  rw [inv_mul_cancel, coc_one ρ c] at h3
  have h4 : (c : G → M) τ⁻¹ = -ρ τ⁻¹ ((c : G → M) τ) := by
    rw [eq_neg_iff_add_eq_zero]; exact h3.symm
  rw [h1, h2, hk, h4]
  have h5 : ρ τ⁻¹ (ρ τ m0) = m0 := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  simp only [map_mul, Module.End.mul_apply, map_sub, map_neg, h5]
  abel

end Coc2

section Desc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (e : ℕ)

theorem selZ_mem {x : H1z (qzE i e)} (hx : x ∈ selZ i dc e) :
    x ∈ lcH1 (qzE i e) ∧ (∀ v, x ∈ unrH1 (qzE i e) (Io i v)) ∧ (∀ v, x ∈ unrH1 (qzE i e) (IS i v)) ∧
      ∀ w ∈ Pall i dc, NG.resH1 (qzE i e) (decs D.host.E (Aw i dc) w) x ∈
        Fsha (qzE i e) (decs D.host.E (Aw i dc)) (I i dc) (qsN i dc) w := by
  simp only [selZ, selRep2, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hx
  exact ⟨hx.1.1.1, hx.1.1.2, hx.1.2, hx.2⟩

theorem mem_SS_iff (v : HeightOneSpectrum (𝓞 D.host.E)) :
    v ∈ SS i ↔ v ∈ placesOver D.host.E (D.nd.l i) := by
  show v ∈ ((D.nd.ldat (D.nd.l i)).S : Set (HeightOneSpectrum (𝓞 D.host.E))) ↔ _
  rw [(D.nd.ldat (D.nd.l i)).hS]
  rfl

theorem ine_le_NS {v : HeightOneSpectrum (𝓞 D.host.E)} (hv : v ∉ SS i) :
    Ine (F := D.host.E) (D.nd.plOm.1 v) ≤ NS D.nd.Om (SS i) := fun g hg =>
  Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure (by
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    exact ⟨v, hv, _, D.nd.plOm.2 v, hg⟩))

theorem coc_ine (c : coZ1s (qzE i e)) (hx : Submodule.Quotient.mk c ∈ selZ i dc e)
    (v : HeightOneSpectrum (𝓞 D.host.E)) (hv : v ∉ SS i) :
    ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) g = 0 := by
  obtain ⟨-, hIo, hIS, hP⟩ := selZ_mem i dc e hx
  have htriv : ∀ g ∈ Ine (F := D.host.E) (D.nd.plOm.1 v), ∀ m, qzE i e g m = m :=
    fun g hg => qzE_NS i e (ine_le_NS i hv hg)
  by_cases hS : v ∈ D.nd.S i
  · exact coc_zero_of_unr _ c _ htriv (hIS ⟨v, hS⟩)
  by_cases hQ : v ∈ D.nd.Q i
  · have hvP : v ∈ plSet i dc := q_mem_plSet i dc hQ
    have hAw : Aw i dc (idx i dc v) = D.nd.plOm.1 v := by unfold Aw; rw [plOf_idx i dc hvP]
    have hwq : idx i dc v ∈ qsN i dc := Finset.mem_image_of_mem _ hQ
    have hwP : idx i dc v ∈ Pall i dc := Finset.mem_union_left _ (Finset.mem_union_right _ hwq)
    have h1 := hP _ hwP
    unfold Fsha at h1
    rw [ite_eq_left hwq] at h1
    intro g hg
    have hgD : g ∈ decs D.host.E (Aw i dc) (idx i dc v) := by
      show g ∈ (Aw i dc (idx i dc v)).decompositionSubgroup D.host.E
      rw [hAw]; exact Ine_le_Dec _ hg
    have hgI : (⟨g, hgD⟩ : decs D.host.E (Aw i dc) (idx i dc v)) ∈ I i dc (idx i dc v) := by
      show (⟨g, hgD⟩ : decs D.host.E (Aw i dc) (idx i dc v)) ∈
        (Ine (F := D.host.E) (Aw i dc (idx i dc v))).subgroupOf (decs D.host.E (Aw i dc) (idx i dc v))
      rw [Subgroup.mem_subgroupOf]
      show g ∈ Ine (F := D.host.E) (Aw i dc (idx i dc v))
      rw [hAw]; exact hg
    refine coc_zero_of_unr (resRep (qzE i e) (decs D.host.E (Aw i dc) (idx i dc v)))
      (NG.restrictCocycles1 _ _ c) (I i dc (idx i dc v)) ?_ h1 ⟨g, hgD⟩ hgI
    intro g' hg' m
    have hg'' : (g' : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 v) := by
      have := (Subgroup.mem_subgroupOf).1 hg'
      rw [hAw] at this
      exact this
    exact htriv _ hg'' m
  · have hl : v ∉ placesOver D.host.E (D.nd.l i) := fun h => hv ((mem_SS_iff i v).2 h)
    exact coc_zero_of_unr _ c _ htriv (hIo ⟨v, hl, hS, hQ⟩)

theorem coc_loc (c : coZ1s (qzE i e)) (hx : Submodule.Quotient.mk c ∈ selZ i dc e)
    (v : (D.nd.ldat (D.nd.l i)).S) :
    ∃ m, ∀ h ∈ Dec (F := D.host.E) ((D.nd.ldat (D.nd.l i)).A v),
      (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) h = qzE i e h m - m := by
  have hvA : v.1 ∈ placesOver D.host.E (D.nd.l i) := (mem_SS_iff i v.1).1 v.2
  have hrc := (dc.cover v.1).2 hvA
  have hvP : v.1 ∈ plSet i dc := by
    rcases hrc with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
  have hnq : idx i dc v.1 ∉ qsN i dc := by
    intro h
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 h
    have hqv := idx_inj i dc (q_mem_plSet i dc hq) hvP hqe
    exact D.nd.SQ_l i q (Or.inr hq) (hqv ▸ hvA)
  have hwP : idx i dc v.1 ∈ Pall i dc := by
    rcases hrc with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image_of_mem _ h))
    · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨⟨v.1, h⟩, Finset.mem_univ _, rfl⟩)
  obtain ⟨-, -, -, hP⟩ := selZ_mem i dc e hx
  have h1 := hP _ hwP
  unfold Fsha at h1
  rw [ite_eq_right hnq, Submodule.mem_bot] at h1
  obtain ⟨m0, hm0⟩ := (Submodule.Quotient.mk_eq_zero _).1 h1
  have hAw : Aw i dc (idx i dc v.1) = D.nd.plOm.1 v.1 := by unfold Aw; rw [plOf_idx i dc hvP]
  have hcob : ∀ k ∈ Dec (F := D.host.E) (D.nd.plOm.1 v.1),
      (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) k = qzE i e k m0 - m0 := by
    intro k hk
    have hkD : k ∈ decs D.host.E (Aw i dc) (idx i dc v.1) := by
      show k ∈ (Aw i dc (idx i dc v.1)).decompositionSubgroup D.host.E
      rw [hAw]; exact hk
    exact (congrFun hm0 ⟨k, hkD⟩).symm
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 v.1) ((D.nd.ldat (D.nd.l i)).hA v)
  refine ⟨qzE i e τ m0 - (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) τ, fun h hh => ?_⟩
  have hk : τ⁻¹ * h * τ ∈ Dec (F := D.host.E) (D.nd.plOm.1 v.1) := by
    show (τ⁻¹ * h * τ) • D.nd.plOm.1 v.1 = D.nd.plOm.1 v.1
    have hh' : h • ((D.nd.ldat (D.nd.l i)).A v) = (D.nd.ldat (D.nd.l i)).A v := hh
    rw [mul_smul, mul_smul, hτ, hh', ← hτ, inv_smul_smul]
  have e1 : h = τ * (τ⁻¹ * h * τ) * τ⁻¹ := by group
  rw [e1, coc_conj_cob (qzE i e) c τ _ m0 (hcob _ hk)]

theorem coc_coset (c : coZ1s (qzE i e))
    (hN : ∀ n ∈ NS D.nd.Om (SS i), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) n = 0) (a b : GE D.nd)
    (h : toGS D.nd.Om (SS i) a = toGS D.nd.Om (SS i) b) :
    (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) a = (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) b := by
  have hab : a⁻¹ * b ∈ NS D.nd.Om (SS i) := QuotientGroup.eq.1 h
  calc (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) a
      = (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) a + qzE i e a ((c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) (a⁻¹ * b)) := by
        rw [hN _ hab, map_zero, add_zero]
    _ = (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) (a * (a⁻¹ * b)) := (c.2 _ _).symm
    _ = (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) b := by rw [mul_inv_cancel_left]

theorem toGS_out (x : GS D.nd.Om (SS i)) : toGS D.nd.Om (SS i) x.out = x := QuotientGroup.out_eq' x

def descFun (c : coZ1s (qzE i e)) : GS D.nd.Om (SS i) → Formalism.GaloisCohomology.QZ (D.nd.l i) :=
  fun x => (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) x.out

theorem descFun_toGS (c : coZ1s (qzE i e))
    (hN : ∀ n ∈ NS D.nd.Om (SS i), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) n = 0) (g : GE D.nd) :
    descFun i e c (toGS D.nd.Om (SS i) g) = (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) g :=
  coc_coset i e c hN _ _ (toGS_out i _)

theorem descFun_lc (c : coZ1s (qzE i e))
    (hN : ∀ n ∈ NS D.nd.Om (SS i), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) n = 0)
    (hc : IsLocallyConstant (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i))) : IsLocallyConstant (descFun i e c) := by
  intro U
  have hU : descFun i e c ⁻¹' U = (toGS D.nd.Om (SS i)) '' ((c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) ⁻¹' U) := by
    ext x
    constructor
    · intro hx
      exact ⟨x.out, hx, toGS_out i x⟩
    · rintro ⟨g, hg, rfl⟩
      show descFun i e c (toGS D.nd.Om (SS i) g) ∈ U
      rw [descFun_toGS i e c hN]
      exact hg
  rw [hU]
  exact QuotientGroup.isOpenMap_coe _ (hc U)

def descendLocallyConstantCocycle (c : coZ1s (qzE i e))
    (hN : ∀ n ∈ NS D.nd.Om (SS i), (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i)) n = 0)
    (hc : IsLocallyConstant (c : GE D.nd → Formalism.GaloisCohomology.QZ (D.nd.l i))) :
    Z1 (Formalism.GaloisCohomology.qzTw (D.nd.ldat (D.nd.l i)) (e : ℤ)) :=
  ⟨descFun i e c, (descFun_lc i e c hN hc).continuous, fun x y => by
    have hxy : toGS D.nd.Om (SS i) (x.out * y.out) = x * y := by rw [map_mul, toGS_out, toGS_out]
    rw [← hxy, descFun_toGS i e c hN, c.2, qzE_eq, toGS_out]
    rfl⟩

def inflZ : Z1 (Formalism.GaloisCohomology.qzTw (D.nd.ldat (D.nd.l i)) (e : ℤ)) →ₗ[ℤ_[D.nd.l i]] coZ1s (qzE i e) where
  toFun f := ⟨fun g => f.1 (toGS D.nd.Om (SS i) g), fun g h => by
    show f.1 (toGS D.nd.Om (SS i) (g * h)) = f.1 (toGS D.nd.Om (SS i) g) + qzE i e g (f.1 (toGS D.nd.Om (SS i) h))
    rw [map_mul, f.2.2, qzE_eq]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def infl : H1 (Formalism.GaloisCohomology.qzTw (D.nd.ldat (D.nd.l i)) (e : ℤ)) →ₗ[ℤ_[D.nd.l i]] H1z (qzE i e) :=
  Submodule.mapQ _ _ (inflZ i e) (by
    intro f hf
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hf
    refine ⟨m, funext fun g => ?_⟩
    show qzE i e g m - m = f.1 (toGS D.nd.Om (SS i) g)
    rw [qzE_eq]
    exact (hm _).symm)

theorem selZ_le_map : selZ i dc e ≤ (Formalism.GaloisCohomology.Sha (D.nd.ldat (D.nd.l i)) (e : ℤ)).map (infl i e) := by
  intro x hx
  obtain ⟨c, hc, rfl⟩ := (selZ_mem i dc e hx).1
  have hN := coc_NS i e c hc (fun v hv => coc_ine i dc e c hx v hv)
  refine ⟨Submodule.Quotient.mk (descendLocallyConstantCocycle i e c hN hc), ?_, ?_⟩
  · rw [Formalism.GaloisCohomology.Sha, Sha1, SetLike.mem_coe, Submodule.mem_iInf]
    intro v
    rw [LinearMap.mem_ker]
    obtain ⟨m, hm⟩ := coc_loc i dc e c hx v
    refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨m, fun h => ?_⟩)
    show descFun i e c (toGS D.nd.Om (SS i) h.1) =
      Formalism.GaloisCohomology.qzTw (D.nd.ldat (D.nd.l i)) (e : ℤ) (toGS D.nd.Om (SS i) h.1) m - m
    rw [descFun_toGS i e c hN, ← qzE_eq]
    exact hm h.1 h.2
  · show Submodule.Quotient.mk (inflZ i e (descendLocallyConstantCocycle i e c hN hc)) = Submodule.Quotient.mk c
    congr 1
    exact Subtype.ext (funext fun g => descFun_toGS i e c hN g)

theorem zlSha : ZlSha i dc e := by
  unfold ZlSha Formalism.GaloisCohomology.shaLen
  calc Module.length ℤ_[D.nd.l i] ↥(selZ i dc e)
      ≤ Module.length ℤ_[D.nd.l i] ↥((Formalism.GaloisCohomology.Sha (D.nd.ldat (D.nd.l i)) (e : ℤ)).map (infl i e)) :=
        Module.length_le_of_injective (Submodule.inclusion (selZ_le_map i dc e))
          (Submodule.inclusion_injective _)
    _ ≤ Module.length ℤ_[D.nd.l i] ↥(Formalism.GaloisCohomology.Sha (D.nd.ldat (D.nd.l i)) (e : ℤ)) :=
        Module.length_le_of_surjective ((infl i e).submoduleMap _) (LinearMap.submoduleMap_surjective _ _)

end Desc

end Formalism.MainNotions.N.K.ShaT

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Finset IsLocalRing Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.GaloisCohomology

namespace Formalism.MainNotions.N.K.CoefT

open Formalism.MainNotions.N.K.ShaT

section MapX

variable {R S G M M' : Type} [CommRing R] [CommRing S] [Algebra S R] [Group G]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M] [AddCommGroup M'] [Module S M']
  (ρ : Representation R G M) (ρ' : Representation S G M') (φ : M →ₗ[S] M')
  (hφ : ∀ g m, φ (ρ g m) = ρ' g (φ m))

def cocycleMap : coZ1s ρ →ₗ[S] coZ1s ρ' where
  toFun c := ⟨fun g => φ ((c : G → M) g), fun g h => by
    show φ ((c : G → M) (g * h)) = φ ((c : G → M) g) + ρ' g (φ ((c : G → M) h))
    rw [c.2 g h, map_add (f := _), hφ]⟩
  map_add' a b := Subtype.ext <| funext fun g => map_add φ ((a : G → M) g) ((b : G → M) g)
  map_smul' r a := Subtype.ext <| funext fun g => map_smul φ r ((a : G → M) g)

def h1MapAlt : H1z ρ →ₗ[S] H1z ρ' :=
  (Submodule.mapQ (((coB1 ρ).comap (coZ1s ρ).subtype).restrictScalars S) ((coB1 ρ').comap (coZ1s ρ').subtype)
    (cocycleMap ρ ρ' φ hφ) (by
      rintro x ⟨v, hv⟩
      refine ⟨φ v, funext fun g => ?_⟩
      have h : ρ g v - v = (x : G → M) g := congrFun hv g
      show ρ' g (φ v) - φ v = φ ((x : G → M) g)
      rw [← h, map_sub, hφ])).comp
    (Submodule.Quotient.restrictScalarsEquiv S ((coB1 ρ).comap (coZ1s ρ).subtype)).symm.toLinearMap

theorem h1Map_mk_alt (c : coZ1s ρ) :
    h1MapAlt ρ ρ' φ hφ (Submodule.Quotient.mk c) = Submodule.Quotient.mk (cocycleMap ρ ρ' φ hφ c) := rfl

theorem res_h1MapX (Dg : Subgroup G) (x : H1z ρ) :
    resH1 ρ' Dg (h1MapAlt ρ ρ' φ hφ x) =
      h1MapAlt (resRep ρ Dg) (resRep ρ' Dg) φ (fun g m => hφ g m) (resH1 ρ Dg x) := by
  induction x using Submodule.Quotient.induction_on with
  | H c => rfl

theorem h1Map_mem_unramified {Dg : Subgroup G} {x : H1z ρ} (hx : x ∈ unrH1 ρ Dg) : h1MapAlt ρ ρ' φ hφ x ∈ unrH1 ρ' Dg := by
  unfold unrH1 at hx ⊢
  rw [LinearMap.mem_ker] at hx ⊢
  rw [res_h1MapX, hx, map_zero]

theorem h1Map_mem_locally_constant [TopologicalSpace G] {x : H1z ρ} (hx : x ∈ lcH1 ρ) : h1MapAlt ρ ρ' φ hφ x ∈ lcH1 ρ' := by
  obtain ⟨c, hc, rfl⟩ := hx
  exact ⟨cocycleMap ρ ρ' φ hφ c, IsLocallyConstant.comp hc φ, rfl⟩

theorem h1Map_mem_local_condition (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs : Finset ℕ) (w : ℕ) {x : H1z ρ}
    (hx : resH1 ρ (D w) x ∈ Fsha ρ D Iq qs w) : resH1 ρ' (D w) (h1MapAlt ρ ρ' φ hφ x) ∈ Fsha ρ' D Iq qs w := by
  rw [res_h1MapX]
  unfold Fsha at hx ⊢
  split_ifs at hx ⊢ with hw
  · exact h1Map_mem_unramified _ _ _ _ hx
  · rw [Submodule.mem_bot] at hx ⊢
    rw [hx, map_zero]

theorem h1Map_mem_selmer [TopologicalSpace G] {V VS : Type} (J : V → Subgroup G) (JS : VS → Subgroup G)
    (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs P : Finset ℕ) {x : H1z ρ}
    (hx : x ∈ selRep2 ρ J JS D (Fsha ρ D Iq qs) P) :
    h1MapAlt ρ ρ' φ hφ x ∈ selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P := by
  simp only [selRep2, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap] at hx ⊢
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hx
  exact ⟨⟨⟨h1Map_mem_locally_constant _ _ _ _ h1, fun v => h1Map_mem_unramified _ _ _ _ (h2 v)⟩, fun v => h1Map_mem_unramified _ _ _ _ (h3 v)⟩,
    fun w hw => h1Map_mem_local_condition _ _ _ _ D Iq qs w (h4 w hw)⟩

end MapX

section LenX

variable {R S G M M' : Type} [CommRing R] [CommRing S] [Algebra S R] [Group G] [TopologicalSpace G]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower S R M] [AddCommGroup M'] [Module S M']

theorem len_sel_le_of_equiv (ρ : Representation R G M) (ρ' : Representation S G M') {ι : Type} [Fintype ι]
    (Φ : M ≃ₗ[S] (ι → M')) (hΦ : ∀ g m j, Φ (ρ g m) j = ρ' g (Φ m j)) {V VS : Type} (J : V → Subgroup G)
    (JS : VS → Subgroup G) (D : ℕ → Subgroup G) (Iq : ∀ w, Subgroup (D w)) (qs P : Finset ℕ) :
    Module.length S ↥(selRep2 ρ J JS D (Fsha ρ D Iq qs) P) ≤
      (Fintype.card ι : ℕ∞) * Module.length S ↥(selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P) := by
  let π : ι → (M →ₗ[S] M') := fun j => (LinearMap.proj j).comp Φ.toLinearMap
  have hπ : ∀ j g m, π j (ρ g m) = ρ' g (π j m) := fun j g m => hΦ g m j
  let Fm : ↥(selRep2 ρ J JS D (Fsha ρ D Iq qs) P) →ₗ[S] (ι → ↥(selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P)) :=
    { toFun := fun x j => ⟨h1MapAlt ρ ρ' (π j) (hπ j) x, h1Map_mem_selmer ρ ρ' (π j) (hπ j) J JS D Iq qs P x.2⟩
      map_add' := fun x y => funext fun j => Subtype.ext (map_add (h1MapAlt ρ ρ' (π j) (hπ j)) (x : H1z ρ) (y : H1z ρ))
      map_smul' := fun a x => funext fun j => Subtype.ext (map_smul (h1MapAlt ρ ρ' (π j) (hπ j)) a (x : H1z ρ)) }
  have hinj : Function.Injective Fm := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    rintro ⟨x, hx⟩ h0
    rw [LinearMap.mem_ker] at h0
    have h0' : ∀ j, h1MapAlt ρ ρ' (π j) (hπ j) x = 0 := fun j => congrArg Subtype.val (congrFun h0 j)
    apply Subtype.ext
    show x = 0
    clear h0 hx
    induction x using Submodule.Quotient.induction_on with
    | H c =>
      have hj : ∀ j, ∃ v : M', ∀ g, ρ' g v - v = π j ((c : G → M) g) := by
        intro j
        have := h0' j
        rw [h1Map_mk_alt, Submodule.Quotient.mk_eq_zero] at this
        obtain ⟨v, hv⟩ := this
        exact ⟨v, fun g => congrFun hv g⟩
      choose v hv using hj
      rw [Submodule.Quotient.mk_eq_zero]
      refine ⟨Φ.symm v, funext fun g => ?_⟩
      show ρ g (Φ.symm v) - Φ.symm v = (c : G → M) g
      apply Φ.injective
      funext j
      rw [map_sub, Pi.sub_apply, hΦ, LinearEquiv.apply_symm_apply]
      exact hv j g
  calc Module.length S ↥(selRep2 ρ J JS D (Fsha ρ D Iq qs) P)
      ≤ Module.length S (ι → ↥(selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P)) := Module.length_le_of_injective Fm hinj
    _ = (Fintype.card ι : ℕ∞) * Module.length S ↥(selRep2 ρ' J JS D (Fsha ρ' D Iq qs) P) := by
      rw [Module.length_pi_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end LenX

section Ring

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

theorem smul_eq_zero_of_mem_max (hl : ((l : ℕ) : O) = 0) {a : ℤ_[l]} (ha : a ∈ maximalIdeal ℤ_[l]) (x : O) :
    a • x = 0 := by
  rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at ha
  obtain ⟨t, rfl⟩ := ha
  rw [Algebra.smul_def, map_mul, map_natCast, hl, mul_zero, zero_mul]

theorem alg_inj : Function.Injective (algebraMap ℤ_[l] O) := by
  by_contra hni
  have hl : ((l : ℕ) : O) = 0 := by
    rw [injective_iff_map_eq_zero] at hni
    push Not at hni
    obtain ⟨a, hfa, ha⟩ := hni
    have h := congrArg (algebraMap ℤ_[l] O) (PadicInt.unitCoeff_spec ha)
    rw [hfa, map_mul, map_pow, map_natCast] at h
    have hu : IsUnit (algebraMap ℤ_[l] O (PadicInt.unitCoeff ha : ℤ_[l])) := (Units.isUnit _).map _
    by_contra hl0
    exact pow_ne_zero _ hl0 ((hu.mul_right_eq_zero).mp h.symm)
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := O)
  have hsurj : Function.Surjective (fun v : Fin k → ZMod l => ∑ i, ((v i).cast : ℤ_[l]) • s i) := by
    intro x
    have hx : x ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).mp hx
    refine ⟨fun i => PadicInt.toZMod (c i), Finset.sum_congr rfl fun i _ => ?_⟩
    have h := smul_eq_zero_of_mem_max l O hl (PadicInt.toZMod_spec (c i)) (s i)
    rw [sub_smul, sub_eq_zero] at h
    exact h.symm
  have : Finite O := Finite.of_surjective _ hsurj
  exact IsDiscreteValuationRing.not_a_field O
    ((IsLocalRing.isField_iff_maximalIdeal_eq).mp (Finite.isField_of_domain O))

theorem faithful : FaithfulSMul ℤ_[l] O := (faithfulSMul_iff_algebraMap_injective _ _).mpr (alg_inj l O)

theorem torsionFree : Module.IsTorsionFree ℤ_[l] O := Module.isTorsionFree_iff_algebraMap_injective.mpr (alg_inj l O)

theorem l_mem_max [IsLocalHom (algebraMap ℤ_[l] O)] : ((l : ℕ) : O) ∈ maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] O)]
  intro hu
  have := (isUnit_map_iff (algebraMap ℤ_[l] O) _).mp hu
  exact (IsLocalRing.mem_maximalIdeal _).mp
    (by rw [PadicInt.maximalIdeal_eq_span_p]; exact Ideal.mem_span_singleton_self _) this

theorem dvd_pow_l [IsLocalHom (algebraMap ℤ_[l] O)] {t : O} (ht : t ≠ 0) : ∃ m : ℕ, t ∣ ((l : ℕ) : O) ^ m := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible ht hϖ
  have hl := l_mem_max l O
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hl
  exact ⟨m, hm.dvd.trans (pow_dvd_pow_of_dvd hl m)⟩

theorem len_quot_l [Module.Free ℤ_[l] O] :
    Module.length ℤ_[l] (O ⧸ Ideal.span {((l : ℕ) : O)}) = Module.finrank ℤ_[l] O := by
  let b := Module.finBasis ℤ_[l] O
  have hmap : (Submodule.restrictScalars ℤ_[l] (Ideal.span {((l : ℕ) : O)})).map b.equivFun.toLinearMap =
      Submodule.pi Set.univ (fun _ => maximalIdeal ℤ_[l]) := by
    ext v
    simp only [Submodule.mem_map, Submodule.restrictScalars_mem, Ideal.mem_span_singleton', Submodule.mem_pi,
      Set.mem_univ, true_implies, PadicInt.maximalIdeal_eq_span_p]
    constructor
    · rintro ⟨x, ⟨y, rfl⟩, rfl⟩ j
      refine ⟨b.equivFun y j, ?_⟩
      have : y * ((l : ℕ) : O) = (l : ℤ_[l]) • y := by rw [Algebra.smul_def, map_natCast, mul_comm]
      rw [LinearEquiv.coe_coe, this, map_smul, Pi.smul_apply, smul_eq_mul, mul_comm]
    · intro hv
      choose w hw using hv
      refine ⟨b.equivFun.symm w * ((l : ℕ) : O), ⟨_, rfl⟩, ?_⟩
      have : b.equivFun.symm w * ((l : ℕ) : O) = (l : ℤ_[l]) • b.equivFun.symm w := by
        rw [Algebra.smul_def, map_natCast, mul_comm]
      rw [LinearEquiv.coe_coe, this, map_smul, LinearEquiv.apply_symm_apply]
      funext j
      rw [Pi.smul_apply, smul_eq_mul, mul_comm, hw j]
  rw [((Submodule.Quotient.restrictScalarsEquiv ℤ_[l] (Ideal.span {((l : ℕ) : O)})).symm.trans
    ((Submodule.Quotient.equiv _ _ b.equivFun hmap).trans
      (Submodule.quotientPi (fun _ => maximalIdeal ℤ_[l])))).length_eq, Module.length_pi_of_fintype]
  have h1 : Module.length ℤ_[l] (ℤ_[l] ⧸ maximalIdeal ℤ_[l]) = 1 := by
    have := IsDiscreteValuationRing.length_quotient_pow_maximalIdeal ℤ_[l] 1
    rwa [pow_one, Nat.cast_one] at this
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

end Ring

section Iso

variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]

def iotaK : ℚ_[l] →+* FractionRing O :=
  IsFractionRing.lift (A := ℤ_[l]) (K := ℚ_[l])
    (g := (algebraMap O (FractionRing O)).comp (algebraMap ℤ_[l] O))
    ((IsFractionRing.injective O (FractionRing O)).comp (alg_inj l O))

theorem iotaK_alg (a : ℤ_[l]) :
    iotaK l O (algebraMap ℤ_[l] ℚ_[l] a) = algebraMap O (FractionRing O) (algebraMap ℤ_[l] O a) :=
  IsFractionRing.lift_algebraMap _ _

theorem smulK (a : ℤ_[l]) (z : FractionRing O) :
    a • z = algebraMap O (FractionRing O) (algebraMap ℤ_[l] O a) * z := by
  rw [← algebraMap_smul O a z, Algebra.smul_def]

variable {ι : Type} [Fintype ι] (b : Module.Basis ι ℤ_[l] O)

def psiQ (j : ι) : ℚ_[l] →ₗ[ℤ_[l]] KO O where
  toFun x := Submodule.Quotient.mk (iotaK l O x * algebraMap O (FractionRing O) (b j))
  map_add' x y := by rw [map_add (f := _), add_mul, Submodule.Quotient.mk_add]
  map_smul' a x := by
    rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul, smulK, Algebra.smul_def a x, map_mul, iotaK_alg,
      mul_assoc]

def PsiJ (j : ι) : QZ l →ₗ[ℤ_[l]] KO O :=
  (ZlSub l).liftQ (psiQ l O b j) (by
    rintro x ⟨a, rfl⟩
    rw [LinearMap.mem_ker, Algebra.linearMap_apply]
    show Submodule.Quotient.mk _ = _
    rw [iotaK_alg, ← map_mul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.mem_one.mpr ⟨_, rfl⟩)

theorem PsiJ_mk (j : ι) (x : ℚ_[l]) :
    PsiJ l O b j (QZ.mk l x) = Submodule.Quotient.mk (iotaK l O x * algebraMap O (FractionRing O) (b j)) := rfl

def Psi : (ι → QZ l) →ₗ[ℤ_[l]] KO O := ∑ j, (PsiJ l O b j).comp (LinearMap.proj j)

theorem Psi_apply (v : ι → QZ l) : Psi l O b v = ∑ j, PsiJ l O b j (v j) := by
  simp [Psi]

theorem Psi_inj : Function.Injective (Psi l O b) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  choose x hx using fun j => Submodule.Quotient.mk_surjective (ZlSub l) (v j)
  obtain ⟨s, hs⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ_[l]) x
  have hs' : ∀ j, ∃ cj : ℤ_[l], algebraMap ℤ_[l] ℚ_[l] cj = (s : ℤ_[l]) • x j := fun j => hs j
  choose c hc using hs'
  have h1 : (∑ j, iotaK l O (x j) * algebraMap O (FractionRing O) (b j)) ∈ (1 : Submodule O (FractionRing O)) := by

    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply, map_sum, ← hv, Psi_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hx j]
    rfl
  obtain ⟨o, ho⟩ := Submodule.mem_one.mp h1
  have h2 : algebraMap O (FractionRing O) ((s : ℤ_[l]) • o) =
      algebraMap O (FractionRing O) (∑ j, c j • b j) := by

    rw [Algebra.smul_def, map_mul, ho, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul, ← mul_assoc]
    congr 1
    rw [← iotaK_alg, ← map_mul, ← Algebra.smul_def, ← hc j, iotaK_alg]
  have h3 := IsFractionRing.injective O (FractionRing O) h2
  rw [← Module.Basis.equivFun_symm_apply] at h3
  have hs0 : algebraMap ℤ_[l] ℚ_[l] (s : ℤ_[l]) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℤ_[l] ℚ_[l])).mpr (nonZeroDivisors.coe_ne_zero s)
  funext j
  have h4 : (s : ℤ_[l]) * b.equivFun o j = c j := by
    have := congrArg (fun y => b.equivFun y j) h3
    simpa only [map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul] using this
  show v j = 0
  rw [← hx j]
  show Submodule.Quotient.mk (p := ZlSub l) (x j) = (0 : ℚ_[l] ⧸ ZlSub l)
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨b.equivFun o j, ?_⟩
  rw [Algebra.linearMap_apply]
  exact mul_left_cancel₀ hs0 (by rw [← map_mul, h4, hc j, Algebra.smul_def])

theorem Psi_surj [IsLocalHom (algebraMap ℤ_[l] O)] : Function.Surjective (Psi l O b) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨a, t, ht, rfl⟩ := IsFractionRing.div_surjective (A := O) z
  obtain ⟨m, w, hw⟩ := dvd_pow_l l O (nonZeroDivisors.ne_zero ht)
  refine ⟨fun j => QZ.mk l (algebraMap ℤ_[l] ℚ_[l] (b.equivFun (a * w) j) / ((l : ℕ) : ℚ_[l]) ^ m), ?_⟩
  rw [Psi_apply]
  simp only [PsiJ_mk, ← Submodule.mkQ_apply]

  rw [← map_sum]
  congr 1
  have hl0 : ((l : ℕ) : O) ≠ 0 := by
    rw [← map_natCast (algebraMap ℤ_[l] O)]
    exact (map_ne_zero_iff _ (alg_inj l O)).mpr (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hw
    exact pow_ne_zero m hl0 hw
  have hwK : algebraMap O (FractionRing O) w ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).mpr hw0
  have hlK : ((l : ℕ) : FractionRing O) ^ m =
      algebraMap O (FractionRing O) t * algebraMap O (FractionRing O) w := by
    rw [← map_mul, ← hw, map_pow, map_natCast]
  have hsum : ∑ j, algebraMap O (FractionRing O) (algebraMap ℤ_[l] O (b.equivFun (a * w) j)) *
      algebraMap O (FractionRing O) (b j) = algebraMap O (FractionRing O) (a * w) := by

    conv_rhs => rw [← b.sum_equivFun (a * w), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, map_mul (algebraMap O (FractionRing O))]
  calc ∑ j, iotaK l O (algebraMap ℤ_[l] ℚ_[l] (b.equivFun (a * w) j) / ((l : ℕ) : ℚ_[l]) ^ m) *
        algebraMap O (FractionRing O) (b j)
      = (∑ j, algebraMap O (FractionRing O) (algebraMap ℤ_[l] O (b.equivFun (a * w) j)) *
          algebraMap O (FractionRing O) (b j)) / ((l : ℕ) : FractionRing O) ^ m := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_div₀, map_pow, map_natCast, iotaK_alg, div_mul_eq_mul_div]
    _ = algebraMap O (FractionRing O) a / algebraMap O (FractionRing O) t := by
        rw [hsum, hlK, map_mul (algebraMap O (FractionRing O)), mul_div_mul_right _ _ hwK]

end Iso

theorem coefChange (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] : CoefChange l O := by
  intro G _ _ ψ V VS J JS D Iq qs P ψO ρO ρZ
  have : FaithfulSMul ℤ_[l] O := faithful l O
  have : Module.IsTorsionFree ℤ_[l] O := torsionFree l O
  have : Module.Free ℤ_[l] O := Module.free_of_finite_type_torsion_free'
  have : IsLocalHom (algebraMap ℤ_[l] O) := inferInstance
  let b := Module.finBasis ℤ_[l] O
  let Φ : KO O ≃ₗ[ℤ_[l]] (Fin (Module.finrank ℤ_[l] O) → QZ l) :=
    (LinearEquiv.ofBijective (Psi l O b) ⟨Psi_inj l O b, Psi_surj l O b⟩).symm
  have hΦ : ∀ g m j, Φ (ρO g m) j = ρZ g (Φ m j) := by
    intro g m j
    simp only [ρO, ρZ, ψO, scalRep_apply, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
      RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, algebraMap_smul, map_smul, Pi.smul_apply]
  have h1 := len_sel_le_of_equiv ρO ρZ Φ hΦ J JS D Iq qs P
  have h2 := IsLocalRing.length_restrictScalars ℤ_[l] (B := O) (M := ↥(selRep2 ρO J JS D (Fsha ρO D Iq qs) P))
  have h3 := IsLocalRing.length_restrictScalars ℤ_[l] (B := O) (M := O ⧸ Ideal.span {((l : ℕ) : O)})
  rw [len_quot_l l O] at h3
  have hn0 : Module.finrank ℤ_[l] O ≠ 0 := Module.finrank_pos.ne'
  have hf0 : Module.length (ResidueField ℤ_[l]) (ResidueField O) ≠ 0 := Module.length_pos.ne'
  have hft : Module.length (ResidueField ℤ_[l]) (ResidueField O) ≠ ⊤ := by
    intro hf
    rw [hf] at h3
    rcases eq_or_ne (Module.length O (O ⧸ Ideal.span {((l : ℕ) : O)})) 0 with he | he
    · rw [he, zero_mul, Nat.cast_eq_zero] at h3
      exact hn0 h3
    · rw [ENat.mul_top he] at h3
      exact ENat.natCast_ne_top _ h3
  rw [← ENat.mul_le_mul_right_iff hf0 hft, ← h2]
  calc _ ≤ _ := h1
    _ = _ := by rw [Fintype.card_fin, h3]; ring

end Formalism.MainNotions.N.K.CoefT

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

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem coefChange_rec : CoefChange (D.nd.l i) (D.nd.O i) :=
  CoefT.coefChange _ _

theorem tieSel2_full [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
    {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))} {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))}
    {π : D.nd.X i} {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (F0 : ∀ w, Submodule (D.nd.O i) (H1z (resU i dc Dd 0 w))) (c : Fin (D.R.t + 1)) (hc : 2 ≤ (c : ℕ)) :
    TieSel2 i (Mc i Dd c) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) (qsN i dc)
      (Fall i dc Dd F0 c) (Io i) (IS i) (c : ℕ) := by
  exact tieSel2_rec (i := i) (dc := dc) (Dd := Dd) (hD := hD) (hN := hN) (F0 := F0) (c := c) (hc := hc)
    (hC := coefChange_rec i) (hZ := fun e _ => zlSha i dc e)

end Formalism.MainNotions.N.K.ShaT

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StC

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Clauses

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (cB : ℕ)

set_option synthInstance.maxHeartbeats 400000 in
def ClauseTB : Prop :=
  ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) → ∀ w ∈ rowsN i dc,
      (∀ ψ : Ymod Dd.r Dd.χ Dd.E →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c,
        (∀ g ∈ (decs D.host.E (Aw i dc)) w, ∀ y, ψ (uElt Dd.r Dd.χ g • y) = uElt Dd.r Dd.χ g • ψ y) →
        ∀ z : coZ1s (QS.resU i dc Dd c w),
          (∀ g : (decs D.host.E (Aw i dc)) w, (z : (decs D.host.E (Aw i dc)) w → blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) g =
            ψ (yY Dd.r Dd.χ Dd.E (g : GE D.nd))) →
          (((D.nd.l i : ℕ) : D.nd.O i) ^ cB) • (Submodule.mkQ _ z : H1z (QS.resU i dc Dd c w)) ∈
            St.FS i r π dc g0 eB e₁ s Dd hD hc c w) ∧
      Module.length (D.nd.O i) (↥(lcH1 (QS.resU i dc Dd c w) ⊓
          divBy (St.FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)) ⧸
        (St.FS i r π dc g0 eB e₁ s Dd hD hc c w).comap (lcH1 (QS.resU i dc Dd c w) ⊓
          divBy (St.FS i r π dc g0 eB e₁ s Dd hD hc c w) (((D.nd.l i : ℕ) : D.nd.O i) ^ cB)).subtype) ≤
        eON i * (cB : ℕ∞) * ((ReciprocityTheory.Gal.locDeg (plOf i dc w) : ℕ∞) + 1)

def ClauseChi : Prop :=
  ∀ c : Fin (D.R.t + 1), 2 ≤ (c : ℕ) →
    InChiFixReal (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk c) Dd.r Dd.χ Dd.E (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc)
      (qsN i dc) (ShaN i ((c : ℕ) - 1)) (St.FS i r π dc g0 eB e₁ s Dd hD hc c) (QS.Io i) (QS.IS i) (QS.I i dc)
      (QS.γQ i dc) (QS.ζ i dc Dd) (QS.ζO i dc) (QS.nQ i dc)

def ClauseLoc1 : Prop :=
  InChiLoc (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk QS.c1) Dd.r Dd.χ Dd.E (decs D.host.E (Aw i dc)) (qsN i dc)
    (St.FS i r π dc g0 eB e₁ s Dd hD hc QS.c1) (QS.Io i) (QS.IS i) (QS.I i dc) (QS.γQ i dc) (QS.ζ i dc Dd)
    (QS.ζO i dc) (QS.nQ i dc)

end Clauses

section Proofs

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (cB : ℕ)

theorem locPos (hE : QS.Ev r π Dd) (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r)
    (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (hQP : QS.QPow i)
    (c : Fin (D.R.t + 1)) (hc0 : c ≠ 0) : QS.LocClause i dc Dd c := by
  obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.mpr hc0
  apply QS.locClause (dc := dc) (hE := hE) (hN := hN) (hG4 := hG4) (hdec := hdec) (hG5 := hG5) (h5x := h5x)
    (hQP := hQP) (c' := c') (hS := QS.locS (hE := hE) (hN := hN) (hG5 := hG5) (h5x := h5x) (c' := c'))

theorem FS_eq (c : Fin (D.R.t + 1)) (hc0 : c ≠ 0) :
    St.FS i r π dc g0 eB e₁ s Dd hD hc c = QS.Fpos i dc Dd c := by
  obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.mpr hc0
  funext w
  rfl

theorem first_character_index_ne_zero : (QS.c1 (D := D)) ≠ 0 := by
  intro h
  have h' := congrArg Fin.val h
  simp [QS.c1] at h'

theorem first_local_clause_of (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (hQP : QS.QPow i) :
    ClauseLoc1 i r π dc g0 eB e₁ s Dd hD hc := by
  have hE := QS.ev_of (hD := hD)
  unfold ClauseLoc1
  rw [FS_eq (dc := dc) (hD := hD) (hc := hc) (c := QS.c1) (hc0 := first_character_index_ne_zero)]
  exact locPos (dc := dc) (hE := hE) (hN := hN) (hG4 := hG4) (hdec := hdec) (hG5 := hG5) (h5x := h5x)
    (hQP := hQP) (c := QS.c1) (hc0 := first_character_index_ne_zero)

theorem chi_of (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hG5 : TruncatedSeriesCountingIdentities.admG5 i r) (h5x : TruncatedSeriesCountingIdentities.TameGeneratorConditions i) (hQP : QS.QPow i) :
    ClauseChi i r π dc g0 eB e₁ s Dd hD hc := by
  have hE := QS.ev_of (hD := hD)
  unfold ClauseChi
  intro c hc2
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc2
  refine And.intro ?_ ?_
  · rw [FS_eq (dc := dc) (hD := hD) (hc := hc) (c := c) (hc0 := hc0)]
    exact locPos (dc := dc) (hE := hE) (hN := hN) (hG4 := hG4) (hdec := hdec) (hG5 := hG5) (h5x := h5x)
      (hQP := hQP) (c := c) (hc0 := hc0)
  · exact ShaT.tieSel2_full (dc := dc) (hD := hD) (hN := hN) (F0 := St.FirstBlockLocalConditions i r π dc g0 eB e₁ s Dd hD hc)
      (c := c) (hc := hc2)

omit [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in

theorem FS_row (c : Fin (D.R.t + 1)) (hc0 : c ≠ 0) {w : ℕ} (hw : w ∈ rowsN i dc) :
    St.FS i r π dc g0 eB e₁ s Dd hD hc c w = TB.Fc i dc Dd c w := by
  obtain ⟨c', rfl⟩ := Fin.exists_succ_eq.mpr hc0
  show QS.Fpos i dc Dd c'.succ w = TB.Fc i dc Dd c'.succ w
  rw [QS.Fpos_row (Dd := Dd) (c := c'.succ) (hw := hw)]
  rfl

omit [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in

theorem tb_of_target (hT : TB.TBTarget i dc Dd cB) : ClauseTB i r π dc g0 eB e₁ s Dd hD hc cB := by
  intro c hc1 w hw
  have hc0 : c ≠ 0 := fun h => by
    have := congrArg Fin.val h
    simp only [Fin.val_zero] at this
    omega
  have hF : St.FS i r π dc g0 eB e₁ s Dd hD hc c w = TB.Fc i dc Dd c w :=
    FS_row i r π dc g0 eB e₁ s Dd hD hc c hc0 hw
  have hx := hT w hw c hc1
  rewrite [← hF] at hx
  exact ⟨hx.2.2.1, hx.2.2.2⟩

end Proofs

section ForRN

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd (Norm.rN i r ρ π)) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π)) (cB : ℕ)

end ForRN

end Formalism.MainNotions.N.K.StC

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StB

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Rho

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

theorem first_block_column_condition (l : Col i dc) :
    FS i r π dc g0 eB e₁ s Dd hD hc 0 (colIdx i dc l) =
      KHf.F0col i dc (colIdx i dc l)
        (resRep (uRep (D.nd.O i) (M := Vr i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) (colIdx i dc l)))
        (QS.resU i dc Dd 0 (colIdx i dc l)) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom) := by
  have hnot : colIdx i dc l ∉ rowsN i dc := by
    intro h
    obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp h
    have h1 : l.1 ∈ plSet i dc := by
      unfold plSet
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr l.2)))
    have h2 : w ∈ plSet i dc := by
      unfold plSet
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hw)))
    have heq : w = l.1 := idx_inj i dc h2 h1 hwe
    have hwc : w ∈ dc.col := by
      rw [heq]
      exact l.2
    exact Finset.disjoint_left.mp dc.disj hw hwc
  simp only [FS, QS.Fall, Fin.cases_zero]
  unfold FirstBlockLocalConditions
  simp only [KHf.Fρ, ite_eq_right hnot]

theorem hRho_of
    (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hFf : ∀ l, KFin.FinFf i dc Dd l) (hRk : ∀ l, KFin.RankFf i dc Dd ρ π l)
    (hSel : TieSel1 i ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc))
      (rowsN i dc) (FS i r π dc g0 eB e₁ s Dd hD hc 0) (QS.Io i)) :
    InRhoFixReal2 (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ Dd.e₁ (colIdx i dc) (decs D.host.E (Aw i dc))
      (jN i ρ π dc) (rowsN i dc) (sN i ρ π) (tensM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (v1S i Dd hT hrk)
      (KFin.κ i dc Dd ρ π)
      (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)
      (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) (KFin.κz i dc Dd ρ π)
      (FS i r π dc g0 eB e₁ s Dd hD hc 0)
      (QS.Io i) (epsU D.nd i) (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk)
      (gamM (Dd.ρk 0)) (lamS i Dd hT hrk) := by
  have hA := tensor_lattice_facts Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk (epsU D.nd i)
  obtain ⟨⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, -⟩, -, -, -, -, -, -, hinc, -, hgam, -⟩ := hA
  have hOrb : ∀ l : Col i dc, KHf.OrbC i dc (KFin.ρV i dc Dd l) := fun l =>
    KOrb.orbC_uRep i dc r π g0 eB e₁ s Dd hD hc (fun c v => KOrb.latM_alg i Dd (Dd.ρk 0) c v) (colIdx i dc l)
  refine ⟨h1, h2, ?_, ⟨h3, h4, h5, h6, h7, h8, h9, fun l =>
      KFin.finRhoAt_of i dc Dd ρ π l (hOrb l) (hFf l) (hRk l)⟩,
    QS.inertia_triviality_clause i r ρ π Dd (QS.ev_of hD) hG4 hdec, hinc,
    fun g b => pi_equiv2 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) Dd.e₁ _ g b, hgam,
    selRho_le_sN i ρ π _ Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) _ (QS.Io i) hSel⟩
  intro l z x hz
  rw [first_block_column_condition]
  exact KFin.clause3 i dc Dd ρ π l z x hz

end Rho

end Formalism.MainNotions.N.K.StB

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Classical Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.NG

namespace Formalism.MainNotions.N.KTate

open Formalism.MainNotions.N.KHf

section RecIso2

open Formalism.MainNotions Formalism.MainNotions.N Formalism.RepresentationBoundsCohomology.SF NumberField IsDedekindDomain
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData)

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)

omit hH0Fin
  [∀ k, SMulCommClass Dd.R' (D.nd.O i)
    (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
theorem isoV_of (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (g0 : GE D.nd)
    (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (l : K.Col i dc) : IsoV i dc Dd ρ π l := by
  have hn := KDim.col_over i dc l
  let F : TrV (eK (D.nbr i _ hn)) (KFin.Vr i Dd) ≃ₗ[Br.LL D.nbr i _ hn] (Fin D.R.r → Br.LL D.nbr i _ hn) :=
    { toFun := fun v a => eK (D.nbr i _ hn) ((show KFin.Vr i Dd from v) (K.H0.e0 (D := D) a))
      invFun := fun w => (show KFin.Vr i Dd from fun j => (eK (D.nbr i _ hn)).symm (w ((K.H0.e0 (D := D)).symm j)))
      map_add' := fun u v => funext fun a => map_add (eK (D.nbr i _ hn)) _ _
      map_smul' := fun c v => funext fun a => by
        show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm c * (show KFin.Vr i Dd from v) (K.H0.e0 (D := D) a)) =
          c * eK (D.nbr i _ hn) ((show KFin.Vr i Dd from v) (K.H0.e0 (D := D) a))
        rw [map_mul, RingEquiv.apply_symm_apply]
      left_inv := fun v => funext fun j => by
        show (eK (D.nbr i _ hn)).symm (eK (D.nbr i _ hn)
          ((show KFin.Vr i Dd from v) (K.H0.e0 (D := D) ((K.H0.e0 (D := D)).symm j)))) = (show KFin.Vr i Dd from v) j
        rw [RingEquiv.symm_apply_apply, Equiv.apply_symm_apply]
      right_inv := fun w => funext fun a => by
        show eK (D.nbr i _ hn) ((eK (D.nbr i _ hn)).symm (w ((K.H0.e0 (D := D)).symm (K.H0.e0 (D := D) a)))) = w a
        rw [RingEquiv.apply_symm_apply, Equiv.symm_apply_apply] }
  refine ⟨F, fun g v => funext fun a => ?_⟩
  have h1 : F (repL (eK (D.nbr i _ hn)) (KFin.ρV i dc Dd l) (Br.iota D.nbr i _ hn) g v) a =
      eK (D.nbr i _ hn) (∑ j, Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hn g : KHf.Γn i dc (K.colIdx i dc l)) : GE D.nd))
        (K.H0.e0 (D := D) a) j • (show KFin.Vr i Dd from v) j) := rfl
  have h2 : KDim.repW i dc ρ π (K.colIdx i dc l) hn g (F v) a =
      ∑ b, algebraMap (Br.OLL D.nbr i _ hn) (Br.LL D.nbr i _ hn) ((D.nbr i _ hn).eO
        (WpO D.nd i ρ π ((Br.iota D.nbr i _ hn g : KHf.Γn i dc (K.colIdx i dc l)) : GE D.nd) a b)) * F v b := rfl

  rw [h1, h2, map_sum, ← Equiv.sum_comp (K.H0.e0 (D := D))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Algebra.smul_def, map_mul, KHf.eK_apply, Br.toLLK_alg, K.H0.unipotent_block_zero_entry hD hN _ a b]
  rfl

omit hH0Fin in
theorem rankFf_normAt (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (g0 : GE D.nd)
    (eB e₁ s : D.nd.X i → MatN D.nd i)
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (l : K.Col i dc) : KFin.RankFf i dc Dd ρ π l := by
  apply rankFf_iso (hD := hD) (hc := hc)
  exact isoV_of i dc Dd ρ π r g0 eB e₁ s hD hN l

end RecIso2

end Formalism.MainNotions.N.KTate
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Sel

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.NG Formalism.BasicNotions
  Formalism.RepresentationBoundsCohomology.FIN Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology

section Phi

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

omit hH0Fin
  [∀ k, SMulCommClass Dd.R' (D.nd.O i)
    (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
theorem toKOG_surjective : Function.Surjective (H0.toKOG (D := D) i Dd) := by
  intro y
  refine ⟨fun b => (H0.kogEq _ y) (H0.e0.symm b), ?_⟩
  show (H0.kogEq _).symm (fun a => (H0.kogEq _ y) (H0.e0.symm (H0.e0 a))) = y
  simp only [Equiv.symm_apply_apply]
  exact (H0.kogEq _).symm_apply_apply y

def phi0 : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0 ≃ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r :=
  LinearEquiv.ofBijective (H0.toKOG i Dd) ⟨H0.toKOG_injective i Dd, toKOG_surjective i Dd⟩

variable {i r ρ π g0 eB e₁ s Dd} in
omit hH0Fin in
theorem invariants_map_equivariant
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (g : GE D.nd) (m : blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) :
    phi0 i Dd (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ g m) = Br.WKO i ρ π g (phi0 i Dd m) := by
  exact H0.toKOG_equiv hD hN g m

variable {i r ρ π g0 eB e₁ s Dd} in
omit hH0Fin in
theorem tieSel1_rec
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ)
      (decs D.host.E (Aw i dc) w))))
    (hBk : BkAt i dc ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (phi0 i Dd) (invariants_map_equivariant hD hN) F) :
    TieSel1 i ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) F
      (K.QS.Io i) := by
  exact tieSel1_of (hBk := hBk)

variable {i r ρ π g0 eB e₁ s Dd} in
omit hH0Fin in
theorem tieSel1_rec_loc
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (F : ∀ w, Submodule (D.nd.O i) (H1z (resRep (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ)
      (decs D.host.E (Aw i dc) w))))
    (hBk : BkLoc i dc ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (phi0 i Dd) (invariants_map_equivariant hD hN) F) :
    TieSel1 i ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc) F
      (K.QS.Io i) := by
  exact tieSel1_rec (hD := hD) (hN := hN) (F := F) (hBk := bkAt_of_loc (h := hBk))

end Phi

end Formalism.MainNotions.N.K.Sel

end
end

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.WeaklyAdmissibleFiltrations
open NumberField IsDedekindDomain

section Phi

variable (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem phi_act {k : ℕ} (M : Gw D.nd w →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : ↥(GK (D.nbr i w hw).Kw))
    (x : KOG (D.nd.O i) k) :
    Br.phi (D.nbr i w hw) k (actD (stdLatG (IsFractionRing.injective (D.nd.O i) (FractionRing (D.nd.O i))) M)
      (Br.ι (D.nbr i w hw) g) x) = actD (Br.lat (D.nbr i w hw) M) g (Br.phi (D.nbr i w hw) k x) := by
  obtain ⟨u, rfl⟩ := Submodule.mkQ_surjective _ x
  have key : Br.vecS (D.nbr i w hw) k ((matRep (mapM (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) M)
      (Br.ι (D.nbr i w hw) g)) u) = (matRep (Br.locM (D.nbr i w hw) M) g) (Br.vecS (D.nbr i w hw) k u) := by
    funext p
    show Br.toLLK (D.nbr i w hw) (((mapM (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) M
        (Br.ι (D.nbr i w hw) g)).mulVec u) p) =
      ((Br.locM (D.nbr i w hw) M g).mulVec (fun j => Br.toLLK (D.nbr i w hw) (u j))) p

    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    show Br.toLLK (D.nbr i w hw) (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (M (Br.ι (D.nbr i w hw) g) p q)) = _
    rw [Br.toLLK_alg]
    rfl
  exact congrArg (fun z : Fin k → Br.LLw (D.nbr i w hw) =>
    (Submodule.Quotient.mk z : (Fin k → Br.LLw (D.nbr i w hw)) ⧸ stdG (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) k)) key

end Phi

def wLat (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
    (u : HeightOneSpectrum (𝓞 D.host.E)) (hu : u ∈ placesOver D.host.E (D.nd.l i))
    (hc : ∀ v, Continuous fun g => matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u))) g v) :
    LocLat ↥(GK (D.nbr i u hu).Kw) ℚ_[D.nd.l i] (Br.LLw (D.nbr i u hu)) (Br.Ow (D.nbr i u hu)) :=
  { V := Fin D.R.r → Br.LLw (D.nbr i u hu)
    ρ := matRep (Br.locM (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u)))
    cont := hc
    L := Br.lat (D.nbr i u hu) ((WpO D.nd i ρ π).comp (decS D.nd u)) }

end Formalism.MainNotions.N

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Sel

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N
  Formalism.MainNotions.N.K Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N.KHf

section Col

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) {A T' : Type} [Ring A] [Algebra (D.nd.O i) A] [CommRing T'] [Algebra T' A]
  (M : Type) [AddCommGroup M] [Module A M] [Module (D.nd.O i) M] [SMulCommClass A (D.nd.O i) M]
  (r : GE D.nd →* A) (χ : GE D.nd →* T'ˣ)
  (φ : M ≃ₗ[D.nd.O i] KOG (D.nd.O i) D.R.r)
  (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := M) r χ g m) = Br.WKO i ρ π g (φ m))

omit [Algebra (D.nd.O i) A] in
set_option synthInstance.maxHeartbeats 400000 in
theorem bkLoc_col (n : ℕ) (hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    {V : Type} [AddCommGroup V] [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
    (ρV : Representation (D.nd.O i) ↥(decs D.host.E (Aw i dc) n) V) (qV : V →ₗ[D.nd.O i] M)
    (Ψ : TrV (eK (D.nbr i _ hw)) V →ₗ[Br.LLw (D.nbr i _ hw)] (Fin D.R.r → Br.LLw (D.nbr i _ hw)))
    (hΨc : Continuous Ψ)
    (hΨe : ∀ g v, Ψ (repL (eK (D.nbr i _ hw)) ρV (Br.iota D.nbr i _ hw) g v) =
      matRep (Br.locM (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g (Ψ v))
    (hcomp : ∀ v, Br.phi (D.nbr i _ hw) D.R.r (φ (qV v)) = Submodule.Quotient.mk (Ψ v))
    (y : ReciprocityTheory.Gal.H1 ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))))
    (hy : psi (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n))
        ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) φ (fun g m => hφ g m) y ∈
      F0col i dc n ρV (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n)) qV) :
    y ∈ Br.bk D.loc D.nbr i (plOf i dc n) hw (WpO D.nd i ρ π) := by
  induction y using Submodule.Quotient.induction_on with
  | H f =>
    have hy' : Submodule.Quotient.mk (psiZ (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n))
        ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) φ (fun g m => hφ g m) f) ∈
        F0col i dc n ρV (resRep (uRep (D.nd.O i) (M := M) r χ) (decs D.host.E (Aw i dc) n)) qV := hy
    obtain ⟨c, hc, hceq⟩ := Submodule.mem_map.mp hy'
    have hd := (Submodule.Quotient.eq _).1 hceq
    have hpsi := Submodule.sub_mem _ hc (Submodule.mem_sup_right hd)
    simp only [Submodule.mem_comap, Submodule.coe_subtype, sub_sub_cancel] at hpsi
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hpsi
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨m, rfl⟩ := hb
    have hz' : z ∈ fZ i dc n ρV := hz
    unfold fZ at hz'
    rw [dite_eq_left hw] at hz'
    have hz2 : (fun g => (z (Br.iota D.nbr i _ hw g) : TrV (eK (D.nbr i _ hw)) V)) ∈
        finiteCocycles (Br.PD D.loc D.nbr i _ hw) (repL (eK (D.nbr i _ hw)) ρV (Br.iota D.nbr i _ hw)) := hz'
    have hpt : ∀ x, f.1 x = φ (qV (z x)) + ((Br.WKO i ρ π) (x : GE D.nd) (φ m) - φ m) := by
      intro x
      have e := congrFun hab x
      change qV (z x) + (uRep (D.nd.O i) (M := M) r χ (x : GE D.nd) m - m) = φ.symm (f.1 x) at e
      rw [← hφ, ← map_sub, ← map_add (f := _), e, LinearEquiv.apply_symm_apply]
    have h1 : (fun g => Submodule.Quotient.mk (Ψ (z (Br.iota D.nbr i _ hw g))) :
        ↥(GK (D.nbr i _ hw).Kw) → (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T) ∈
        HfD ((D.loc (D.nd.l i)).PD (D.nbr i _ hw).Kw)
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) :=
      Submodule.mem_sup_left ⟨fun g => Ψ (z (Br.iota D.nbr i _ hw g)),
        (cocyclesFunctorial_holds _ _ _ _ _ _ _ _ _ _ _ _ Ψ hΨc hΨe _).2 hz2, rfl⟩
    have h2 : (fun g => actD (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g
          (Br.phi (D.nbr i _ hw) D.R.r (φ m)) - (show (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸ (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T from
            Br.phi (D.nbr i _ hw) D.R.r (φ m))) ∈
        HfD ((D.loc (D.nd.l i)).PD (D.nbr i _ hw).Kw)
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) :=
      Submodule.mem_sup_right ⟨Br.phi (D.nbr i _ hw) D.R.r (φ m), rfl⟩
    have h3 := Submodule.add_mem _ h1 h2
    have hfun : (Br.Phi (D.nbr i _ hw) ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n))) f :
        ↥(GK (D.nbr i _ hw).Kw) → (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸
          (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T) =
        (fun g => Submodule.Quotient.mk (Ψ (z (Br.iota D.nbr i _ hw g)))) +
        (fun g => actD (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g
          (Br.phi (D.nbr i _ hw) D.R.r (φ m)) - (show (Fin D.R.r → Br.LLw (D.nbr i _ hw)) ⧸ (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))).T from
            Br.phi (D.nbr i _ hw) D.R.r (φ m))) := by
      funext g
      have hact : Br.phi (D.nbr i _ hw) D.R.r (Br.WKO i ρ π (Br.ι (D.nbr i _ hw) g : GE D.nd) (φ m)) =
          actD (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g
            (Br.phi (D.nbr i _ hw) D.R.r (φ m)) :=
        phi_act D i (plOf i dc n) hw ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n))) g (φ m)
      show Br.phi (D.nbr i _ hw) D.R.r (f.1 (Br.ι (D.nbr i _ hw) g)) = _
      rw [hpt, map_add (f := _), map_sub, hcomp]
      exact congrArg (fun t => Submodule.Quotient.mk (Ψ (z (Br.iota D.nbr i _ hw g))) +
        (t - Br.phi (D.nbr i _ hw) D.R.r (φ m))) hact
    have hmem : f ∈ (HfD ((D.loc (D.nd.l i)).PD (D.nbr i _ hw).Kw)
        (Br.lat (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n))))).comap
          (Br.Phi (D.nbr i _ hw) ((Br.WKO i ρ π).comp (decS D.nd (plOf i dc n)))) := by
      exact Submodule.mem_comap.mpr (hfun ▸ h3)
    exact ⟨f, hmem, rfl⟩

end Col

end Formalism.MainNotions.N.K.Sel

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.Bk

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N
  Formalism.MainNotions.N.K Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N.KHf Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.Sel

section Col

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

abbrev VB : Type :=
  LatM (D.nd.O i) (FractionRing (D.nd.O i)) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

abbrev qB : VB i Dd →ₗ[D.nd.O i] blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0 :=
  qVM (D.nd.O i) {a // RepresentationBoundsCohomology.blk D.R a = 0} (Dd.ρk 0).toRingHom

def psiB {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    TrV (eK (D.nbr i w hw)) (VB i Dd) →ₗ[Br.LLw (D.nbr i w hw)] (Fin D.R.r → Br.LLw (D.nbr i w hw)) where
  toFun v a := eK (D.nbr i w hw) ((show VB i Dd from v) (H0.e0 a))
  map_add' u v := by
    funext a
    exact map_add (eK (D.nbr i w hw)) _ _
  map_smul' c v := by
    funext a
    show eK (D.nbr i w hw) ((eK (D.nbr i w hw)).symm c * (show VB i Dd from v) (H0.e0 a)) =
      c * eK (D.nbr i w hw) ((show VB i Dd from v) (H0.e0 a))
    rw [map_mul, RingEquiv.apply_symm_apply]

omit hH0Fin
  [∀ k, SMulCommClass Dd.R' (D.nd.O i)
    (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
theorem psiB_apply {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (v : TrV (eK (D.nbr i w hw)) (VB i Dd)) (a : Fin D.R.r) :
    psiB i Dd hw v a = eK (D.nbr i w hw) ((show VB i Dd from v) (H0.e0 a)) := rfl

omit hH0Fin
  [∀ k, SMulCommClass Dd.R' (D.nd.O i)
    (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
theorem psiB_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) :
    Continuous (psiB i Dd hw) :=
  IsModuleTopology.continuous_of_linearMap (psiB i Dd hw)

omit hH0Fin
  [∀ k, SMulCommClass Dd.R' (D.nd.O i)
    (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
theorem psiB_comp {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (v : VB i Dd) :
    Br.phi (D.nbr i w hw) D.R.r (phi0 i Dd (qB i Dd v)) = Submodule.Quotient.mk (psiB i Dd hw v) := by
  have h1 : phi0 i Dd (qB i Dd v) =
      (Submodule.Quotient.mk (fun a => v (H0.e0 a)) : KOG (D.nd.O i) D.R.r) := by
    show (H0.kogEq D.R.r).symm (fun a => (qB i Dd v) (H0.e0 a)) = _
    apply (H0.kogEq D.R.r).injective
    rw [LinearEquiv.apply_symm_apply, H0.kogEq_apply, H0.kogTo_mk]
    rfl
  rw [h1]
  rfl

end Col

section Eqv

variable {D : D7} {i : D.nd.Loc} (dc : TruncatedSeriesCountingIdentities.Decl D i) {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
  {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
  {Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R)}
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

omit hH0Fin
  [∀ k, SMulCommClass Dd.R' (D.nd.O i)
    (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
theorem psiB_equiv
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (n : ℕ) (hw : plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    (g : ↥(GK (D.nbr i _ hw).Kw)) (v : TrV (eK (D.nbr i _ hw)) (VB i Dd)) :
    psiB i Dd hw (repL (eK (D.nbr i _ hw))
        (resRep (uRep (D.nd.O i) (M := VB i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) n))
        (Br.iota D.nbr i _ hw) g v) =
      matRep (Br.locM (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n)))) g (psiB i Dd hw v) := by
  funext a
  rw [psiB_apply]
  show _ = ∑ b, (Br.locM (D.nbr i _ hw) ((WpO D.nd i ρ π).comp (decS D.nd (plOf i dc n))) g) a b *
    psiB i Dd hw v b
  show eK (D.nbr i _ hw) (∑ c, (Dd.ρk 0 (uElt Dd.r Dd.χ ((Br.iota D.nbr i _ hw g : decs D.host.E (Aw i dc) n) : GE D.nd)))
      (H0.e0 a) c • (show VB i Dd from v) c) = _

  rw [map_sum, ← Equiv.sum_comp (H0.e0 (D := D))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [H0.unipotent_block_zero_entry hD hN, Algebra.smul_def, map_mul, eK_apply, Br.toLLK_alg]
  rfl

end Eqv

section Row

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))]
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

omit hH0Fin [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')] in
theorem hfW_rep (n : ℕ) [ContinuousConstSMul (FractionRing (D.nd.O i)) (VT n)] (h : ReciprocityTheory.Gal.H1 (Dat n).ρT)
    (hh : h ∈ HfW i dc VT VT' Dat n) :
    ∃ c : ReciprocityTheory.Gal.Z1 (Dat n).ρT,
      Submodule.mkQ ((ReciprocityTheory.Gal.B1 (Dat n).ρT).comap (ReciprocityTheory.Gal.Z1 (Dat n).ρT).subtype) c = h ∧
      c.1 ∈ fZ i dc n (Dat n).ρT := by
  let S : Submodule (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat n).ρT) :=
    { carrier := {a | ∃ c : ReciprocityTheory.Gal.Z1 (Dat n).ρT,
        Submodule.mkQ ((ReciprocityTheory.Gal.B1 (Dat n).ρT).comap (ReciprocityTheory.Gal.Z1 (Dat n).ρT).subtype) c = a ∧
        c.1 ∈ fZ i dc n (Dat n).ρT}
      zero_mem' := ⟨0, map_zero _, (fZ i dc n (Dat n).ρT).zero_mem⟩
      add_mem' := by
        rintro a b ⟨c, rfl, hc⟩ ⟨c', rfl, hc'⟩
        exact ⟨c + c', map_add _ _ _, (fZ i dc n (Dat n).ρT).add_mem hc hc'⟩
      smul_mem' := by
        rintro k a ⟨c, rfl, hc⟩
        obtain ⟨kc, hkc, hmk⟩ := KBKa.mk_smul (Dat n).ρT k c
        refine ⟨kc, hmk, ?_⟩
        rw [hkc]
        exact (fZ i dc n (Dat n).ρT).smul_mem k hc }
  have hle : HfW i dc VT VT' Dat n ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨c, rfl, hc⟩
  exact hle hh

omit hH0Fin [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (VT' w)]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, Module (FractionRing (D.nd.O i)) (VT' w)]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')] in
theorem frow_le_col (n : ℕ) [ContinuousConstSMul (FractionRing (D.nd.O i)) (VT n)]
    {M : Type} [AddCommGroup M] [Module (D.nd.O i) M] (ρM : Representation (D.nd.O i) ↥(Γn i dc n) M)
    (u : M ≃ₗ[D.nd.O i] (VT n ⧸ (Dat n).T)) (hu : ∀ g m, u (ρM g m) = (Dat n).ρA g (u m))
    {V : Type} [AddCommGroup V] [Module (FractionRing (D.nd.O i)) V] [Module (D.nd.O i) V]
    [IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) V]
    (ρV : Representation (D.nd.O i) ↥(Γn i dc n) V) (qV : V →ₗ[D.nd.O i] M) (f : VT n →ₗ[D.nd.O i] V)
    (hf : ∀ g v, f ((Dat n).ρT g v) = ρV g (f v))
    (hq : ∀ x, u.symm (Submodule.Quotient.mk x) = qV (f x)) :
    (((HfW i dc VT VT' Dat n).restrictScalars (D.nd.O i)).map (Dat n).q).map (kRow (Dat n) ρM u hu) ≤
      F0col i dc n ρV ρM qV := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
  obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.1 hy
  obtain ⟨c, rfl, hcZ⟩ := hfW_rep i dc VT VT' Dat n h hh
  have hsym : ∀ g v, u.symm (Submodule.Quotient.mk ((Dat n).ρT g v)) =
      ρM g (u.symm (Submodule.Quotient.mk v)) := fun g v =>
    ReciprocityTheory.ChartRestriction.T2.trCompat_symm (MulEquiv.refl _) u ρM (Dat n).ρA hu g (Submodule.Quotient.mk v)
  have hcoc : (fun g => u.symm (Submodule.Quotient.mk (c.1 g))) ∈ coZ1s ρM := by
    intro g g'
    have e := c.2.2 g g'
    simp only at e ⊢
    rw [e, Submodule.Quotient.mk_add, map_add (f := _), hsym]
  have hk : kRow (Dat n) ρM u hu ((Dat n).q (Submodule.mkQ _ c)) =
      Submodule.mkQ _ (⟨_, hcoc⟩ : coZ1s ρM) := by
    show ReciprocityTheory.ChartRestriction.T2.traceH1 (MulEquiv.refl _) u ρM (Dat n).ρA hu
      (ReciprocityTheory.ChartRestriction.T2.toH1Cocycles (Dat n).ρA ((Dat n).q (Submodule.mkQ _ c))) = _
    simp only [Formalism.RepresentationBoundsCohomology.LOC.LatData.q, ReciprocityTheory.Gal.mapH1, ReciprocityTheory.ChartRestriction.T2.toH1Cocycles, ReciprocityTheory.ChartRestriction.T2.traceH1,
      Submodule.mkQ_apply, Submodule.mapQ_apply]
    congr 1
  rw [hk]
  refine Submodule.mem_map_of_mem (Submodule.mem_comap.2 (Submodule.mem_sup_left
    ⟨fun g => f (c.1 g), fZ_map i dc (Dat n).ρT ρV f hf _ hcZ, ?_⟩))
  funext g
  exact (hq _).symm

end Row

section LatRec

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
  (hM : ∀ a b, Continuous fun g => KLat.M0 r χ bl ρk g a b)

def idV (w : ℕ) :
    KLat.VT (O := O) bl w →ₗ[O] LatM O (FractionRing O) {a // bl a = 0} (ρk 0).toRingHom where
  toFun v := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit hH0Fin in
theorem idV_equiv (w : ℕ) (g : decs Ek Aw w) (v : KLat.VT (O := O) bl w) :
    idV bl ρk w ((KLat.Dat r χ bl ρk ε Aw hK hε hM w).ρT g v) =
      resRep (uRep O (M := LatM O (FractionRing O) {a // bl a = 0} (ρk 0).toRingHom) r χ) (decs Ek Aw w) g
        (idV bl ρk w v) := by
  funext a
  exact KLat.matK_mulVec _ _ a

omit hH0Fin in
theorem uD_symm_mk (w : ℕ) (x : KLat.VT (O := O) bl w) :
    (KLat.uD r χ bl ρk ε Aw hK hε hM w).symm (Submodule.Quotient.mk x) =
      qVM O {a // bl a = 0} (ρk 0).toRingHom (idV bl ρk w x) := by
  rfl

end LatRec

section Final

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) {r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))}
  {ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))} {π : D.nd.X i}
  {g0 : GE D.nd} {eB e₁ s : D.nd.X i → MatN D.nd i}
  (Dd : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [TopologicalSpace (FractionRing (D.nd.O i))] [IsTopologicalAddGroup (FractionRing (D.nd.O i))]
  [ContinuousSMul (D.nd.O i) (FractionRing (D.nd.O i))]
  (hK : ContinuousMul (FractionRing (D.nd.O i)))
  (hε : Continuous fun g => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i))
  (hM : ∀ a b, Continuous fun g => KLat.M0 Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk g a b)

abbrev rhoM (n : ℕ) : Representation (D.nd.O i) ↥(Γn i dc n) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) :=
  resRep (uRep (D.nd.O i) (M := blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ) (decs D.host.E (Aw i dc) n)

abbrev rhoV (n : ℕ) : Representation (D.nd.O i) ↥(Γn i dc n) (VB i Dd) :=
  resRep (uRep (D.nd.O i) (M := VB i Dd) Dd.r Dd.χ) (decs D.host.E (Aw i dc) n)

abbrev DatK (w : ℕ) := KLat.Dat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) hK hε hM w

abbrev uDK (w : ℕ) := KLat.uD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) hK hε hM w

variable [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT)]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT)]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT')]

def FrowK (n : ℕ) : Submodule (D.nd.O i) (H1z (rhoM i dc Dd n)) :=
  (((HfW i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (DatK i dc Dd hK hε hM) n).restrictScalars (D.nd.O i)).map (DatK i dc Dd hK hε hM n).q).map
    (kRow (DatK i dc Dd hK hε hM n) (rhoM i dc Dd n) (uDK i dc Dd hK hε hM n)
      (KLat.huD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) hK hε hM n))

def FcolK (n : ℕ) : Submodule (D.nd.O i) (H1z (rhoM i dc Dd n)) :=
  F0col i dc n (rhoV i dc Dd n) (rhoM i dc Dd n) (qB i Dd)

def FK (n : ℕ) : Submodule (D.nd.O i) (H1z (rhoM i dc Dd n)) :=
  Fρ i dc (rowsN i dc) (rhoM i dc Dd) (FrowK i dc Dd hK hε hM) (FcolK i dc Dd) n

omit hH0Fin
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i))
    (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT')]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT')] in
theorem fK_le (n : ℕ) : FK i dc Dd hK hε hM n ≤ FcolK i dc Dd n := by
  unfold FK Fρ
  split_ifs
  · haveI : ContinuousMul (FractionRing (D.nd.O i)) := hK
    exact frow_le_col i dc _ _ (DatK i dc Dd hK hε hM) n (rhoM i dc Dd n) (uDK i dc Dd hK hε hM n)
      (KLat.huD Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) hK hε hM n)
      (rhoV i dc Dd n) (qB i Dd) (idV (RepresentationBoundsCohomology.blk D.R) Dd.ρk n)
      (idV_equiv Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) hK hε hM n)
      (uD_symm_mk Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) hK hε hM n)
  · exact le_rfl

omit hH0Fin
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i))
    (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT')]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT')] in
theorem bkLoc_rec
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) :
    BkLoc i dc ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (phi0 i Dd) (invariants_map_equivariant hD hN)
      (FK i dc Dd hK hε hM) := by
  intro n _ hw y hy
  exact bkLoc_col i dc ρ π _ Dd.r Dd.χ (phi0 i Dd) (invariants_map_equivariant hD hN) n hw (rhoV i dc Dd n) (qB i Dd)
    (psiB i Dd hw) (psiB_cont i Dd hw) (psiB_equiv dc hD hN n hw) (psiB_comp i Dd hw) y
    (fK_le i dc Dd hK hε hM n hy)

omit hH0Fin
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i))
    (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT')]
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (DatK i dc Dd hK hε hM w).ρT')] in
theorem tieSel1_K
    (hD : Formalism.RepresentationBoundsCohomology.ringDataObjects.RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) :
    TieSel1 i ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc)) (rowsN i dc)
      (FK i dc Dd hK hε hM) (K.QS.Io i) :=
  tieSel1_rec_loc dc hD hN _ (bkLoc_rec i dc Dd hK hε hM hD hN)

end Final

end Formalism.MainNotions.N.K.Bk

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StB

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Rho2

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

theorem selFS_of_normAt (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) :
    TieSel1 i ρ π (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ (colIdx i dc) (decs D.host.E (Aw i dc))
      (rowsN i dc) (FS i r π dc g0 eB e₁ s Dd hD hc 0) (QS.Io i) := by
  letI := fun w => modS i r π dc g0 eB e₁ s Dd hD hc w
  haveI := fun w => KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) w
  letI := fun w => modS' i r π dc g0 eB e₁ s Dd hD hc w
  haveI := fun w => KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) w
  exact Bk.tieSel1_K i dc Dd (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc) hD hN

end Rho2

end Formalism.MainNotions.N.K.StB

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StB

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Rho3

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

theorem hRho_full (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π)
    (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) :
    InRhoFixReal2 (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ Dd.e₁ (colIdx i dc) (decs D.host.E (Aw i dc))
      (jN i ρ π dc) (rowsN i dc) (sN i ρ π) (tensM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (v1S i Dd hT hrk)
      (KFin.κ i dc Dd ρ π)
      (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)
      (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) (KFin.κz i dc Dd ρ π)
      (FS i r π dc g0 eB e₁ s Dd hD hc 0)
      (QS.Io i) (epsU D.nd i) (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk)
      (gamM (Dd.ρk 0)) (lamS i Dd hT hrk) :=
  hRho_of i r ρ π dc g0 eB e₁ s Dd hD hc hT hrk hG4 hdec
    (fun l => KTate.finFf_rec (i := i) (dc := dc) (Dd := Dd) (r := r) (π := π) (g0 := g0) (eB := eB) (e₁ := e₁)
      (s := s) hFin hD hc l)
    (fun l => KTate.rankFf_normAt (i := i) (dc := dc) (Dd := Dd) (ρ := ρ) (π := π) (r := r) (g0 := g0) (eB := eB)
      (e₁ := e₁) (s := s) hD hN hc l)
    (selFS_of_normAt i r ρ π dc g0 eB e₁ s Dd hD hc hN)

end Rho3

section RhoN

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd (Norm.rN i r ρ π)) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i (Norm.rN i r ρ π))
  (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

theorem hRho_rN (hG4 : TruncatedSeriesCountingIdentities.admG4 i r) (hdec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π) (hFin : LargeLevelLemmas.tateH1FinitenessAtPlacesOver i) :
    InRhoFixReal2 (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk 0) Dd.r Dd.χ Dd.e₁ (colIdx i dc) (decs D.host.E (Aw i dc))
      (jN i ρ π dc) (rowsN i dc) (sN i ρ π) (tensM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (v1S i Dd hT hrk)
      (KFin.κ i dc Dd ρ π)
      (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) (qVM (D.nd.O i) _ (Dd.ρk 0).toRingHom)
      (fun l => KHf.Ff i dc Dd.r Dd.χ (iLM (D.nd.O i) _ (Dd.ρk 0).toRingHom) l) (KFin.κz i dc Dd ρ π)
      (FS i (Norm.rN i r ρ π) π dc g0 eB e₁ s Dd hD hc 0)
      (QS.Io i) (epsU D.nd i) (rho1 i Dd) (rho2 i Dd) (FirstSummandSubmodule (D.nd.O i) Dd.e₁).subtype (piS i Dd hT hrk)
      (gamM (Dd.ρk 0)) (lamS i Dd hT hrk) :=
  hRho_full i (Norm.rN i r ρ π) ρ π dc g0 eB e₁ s Dd hD hc hT hrk (Norm.normAt_rN i r ρ π)
    (Norm.admG4_rN i r ρ π hdec hG4) (Norm.decomposes_normalized i r ρ π) hFin

end RhoN

end Formalism.MainNotions.N.K.StB

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StD

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Clauses

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

def RowDR : Prop :=
  ∀ w ∈ rowsN i dc, ∀ hn : plOf i dc w ∈ placesOver D.host.E (D.nd.l i),
    IsDR (Br.PD D.loc D.nbr i _ hn)
      (KHf.repL (KHf.eK (D.nbr i _ hn)) (DatS i r π dc g0 eB e₁ s Dd hD hc w).ρT (Br.iota D.nbr i _ hn))

theorem bKa_clause (hBK : LargeLevelLemmas.BlochKatoAnnihilators i) (hG : K.SelfGood i) (hdR : RowDR i r π dc g0 eB e₁ s Dd hD hc) :
    ∀ w ∈ rowsN i dc, ∀ a, a ∈ HfWS i r π dc g0 eB e₁ s Dd hD hc w ↔
      ∀ b ∈ Hf₂S i r π dc g0 eB e₁ s Dd hD hc w, cupFG (DatS i r π dc g0 eB e₁ s Dd hD hc w) a b = 0 := by
  intro w hw
  letI := modS i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  have hreal := (KLat.rowLat Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i)
    (hM0 i r π g0 eB e₁ s Dd hD hc) (D.nd.l i) (Topo.padicCoeff_O i) (Topo.fracTop_O i) w).2.1
  have hin : KBKa.RowIn i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (DatS i r π dc g0 eB e₁ s Dd hD hc) w :=
    KBKa.rowIn_of i dc _ _ (DatS i r π dc g0 eB e₁ s Dd hD hc) (fun _ => rfl)
      (fun hn => ⟨KOrb.homeoK i hn, KOrb.topMatch_pi i hn _, KOrb.topMatch_pi i hn _⟩) (hdR w hw)
  exact KBKa.bk_a_of_admitted_bk_a i dc _ _ (DatS i r π dc g0 eB e₁ s Dd hD hc) hBK hG hw hreal hin

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)
  (lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ)

theorem tie_clause (hG : K.SelfGood i) (hR : TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i r ρ π dc lenRow)
    (hRT : Sel.RowTie i dc r ρ π (rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk)) :
    TieRow i dc (rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk) lenRow := by
  intro n hn
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hn
  have hpl : w ∈ plSet i dc := by
    unfold plSet
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hw)))
  have hwo : plOf i dc (idx i dc w) ∈ placesOver D.host.E (D.nd.l i) := by
    rw [plOf_idx i dc hpl]
    exact (dc.cover w).mp (Or.inl hw)
  have hrw : plOf i dc (idx i dc w) ∈ dc.row := by
    rw [plOf_idx i dc hpl]
    exact hw
  have hrow := hR (plOf i dc (idx i dc w)) hwo hrw (TruncatedSeriesCountingIdentities.CoefExt.self i _ hwo) (hG _ hwo)
  obtain ⟨h1, h2⟩ := hRT _ hn hwo _ hrow
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  rw [mul_comm, Sel.lenOlSelf i _ hwo]

end Clauses

end Formalism.MainNotions.N.K.StD

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Formalism.BasicNotions Classical

namespace Formalism.MainNotions.N.KUnr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

section Loc

variable {O : Type} [CommRing O] [IsDomain O] {Γ : Type} [Group Γ] {M : Type} [AddCommGroup M] [Module O M]

theorem locRep_triv (g : Γ) (x : KHf.MK (O := O) M) :
    KHf.locRep (Representation.trivial O Γ M) g x = x := by
  induction x using LocalizedModule.induction_on with
  | h m s =>
    show LocalizedModule.map (nonZeroDivisors O) (Representation.trivial O Γ M g) (LocalizedModule.mk m s) =
      LocalizedModule.mk m s
    rw [LocalizedModule.map_mk]
    rfl

end Loc

section Rec

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (δO : D.nd.O i)

theorem col_mem (l : K.Col i dc) : K.plOf i dc (K.colIdx i dc l) ∈ dc.col := by
  have h : l.1 ∈ K.plSet i dc := by
    unfold K.plSet
    simp [l.2]
  rw [K.colIdx, K.plOf_idx i dc h]
  exact l.2

end Rec

end Formalism.MainNotions.N.KUnr
end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.KRow

open Formalism.MainNotions.N.KHf Formalism.WeaklyAdmissibleFiltrations Module Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.BasicNotions Formalism.RepresentationBoundsCohomology.FIN Formalism.NG Formalism.BasicNotions.Loc

section Rec

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
  [∀ w, Module (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]
  [∀ w, IsScalarTower (D.nd.O i) (FractionRing (D.nd.O i)) (ReciprocityTheory.Gal.H1 (Dat w).ρT')]

theorem len_congr {O H : Type} [CommRing O] [AddCommGroup H] [Module O H] {A A' B B' : Submodule O H}
    (hA : A = A') (hB : B = B') :
    Module.length O (↥A ⧸ B.comap A.subtype) = Module.length O (↥A' ⧸ B'.comap A'.subtype) := by
  subst hA hB
  rfl

theorem fs_eq {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    Fs i dc VT VT' Dat n = FsG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Br.iota D.nbr i _ hn) (Dat n) := by
  have key : fZ i dc n (Dat n).ρT' = finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Dat n).ρT' (Br.iota D.nbr i _ hn) := by
    unfold fZ
    rw [dite_eq_left hn]
  unfold Fs FsG Hf₂ finiteClassesContinuousMap fPre finiteClassesContinuous finPre
  rw [key]

theorem finite_classes_row_eq_generic {n : ℕ} (hn : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    Hf₁ i dc ρ₁ n = finiteClassesContinuousLattice (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (Br.iota D.nbr i _ hn)
      (resRep ρ₁ (Γn i dc n)) := by
  have key : fZ i dc n (locRep (resRep ρ₁ (Γn i dc n))) = finZ (eK (D.nbr i _ hn)) (Br.PD D.loc D.nbr i _ hn) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hn) := by
    unfold fZ
    rw [dite_eq_left hn]
  unfold Hf₁ finiteClassesContinuousLocal finiteClassesContinuousLattice finiteClassesContinuousMap fPre finiteClassesContinuous finPre
  rw [key]
  rfl

variable (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (πx : D.nd.X i)

theorem rowLenD_eq_gen {n : ℕ} (hw : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i)) :
    rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD n =
      Module.length (D.nd.O i)
        (↥(FsG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw) (Dat n)) ⧸
          (imG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw) (Dat n)
            (resRep ρ₁ (Γn i dc n)) π (vD n) (hpD n) (heD n)).comap
            (FsG (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw)
              (Dat n)).subtype) := by
  unfold rowLenD
  exact len_congr (fs_eq i dc VT VT' Dat hw) (by unfold imRow; rw [finite_classes_row_eq_generic i dc ρ₁ hw]; rfl)

theorem rowLenD_eq {n : ℕ} (hw : K.plOf i dc n ∈ placesOver D.host.E (D.nd.l i))
    [Module.Finite (D.nd.O i) T₁] [Module.Free (D.nd.O i) T₁]
    [Module.Finite (D.nd.O i) (Dat n).T'] [Module.Free (D.nd.O i) (Dat n).T']
    (hsp : ∀ x : VT' n, ∃ c : D.nd.O i, c ≠ 0 ∧ ∃ m : (Dat n).T', (Dat n).T'.subtype m = c • x)
    (hcob : OrbC i dc (n := n) (Dat n).ρT')
    (htopV : ∀ c : ↥(Γn i dc n) → VT' n,
      Continuous (fun g => tr (eK (D.nbr i _ hw)) (c (Br.iota D.nbr i _ hw g))) → Continuous c)
    (htop1 : ∀ c : ↥(Γn i dc n) → T₁,
      Continuous (fun g => tr (eK (D.nbr i _ hw)) (mkK (O := D.nd.O i) (c (Br.iota D.nbr i _ hw g)))) →
        Continuous c) :
    rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD n =
      (FR (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n)
        (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n) hsp).col (Br.PD D.loc D.nbr i _ hw) := by
  have hbij : Function.Bijective (Br.iota D.nbr i _ hw) := (D.nbr i _ hw).e.symm.bijective
  have hcobn : ∀ x : VT' n, (fun γ => (Dat n).ρT' γ x - x) ∈
      finZ (eK (D.nbr i _ hw)) (Br.PD D.loc D.nbr i _ hw) (Dat n).ρT' (Br.iota D.nbr i _ hw) := by
    intro x
    have h := cob_mem_fZ i dc (Dat n).ρT' hcob x
    rwa [fZ_pos i dc _ hw] at h
  exact (rowLenD_eq_gen i dc VT VT' Dat ρ₁ π vD hpD heD hw).trans
    (len_eq_col (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw)
      (Br.PD D.loc D.nbr i _ hw) (Br.iota D.nbr i _ hw) (Dat n) (resRep ρ₁ (Γn i dc n)) π (vD n) (hpD n) (heD n) hsp
      hbij hcobn htopV htop1)

theorem rowTie_disp (hπ : Function.Surjective π)
    (hSub : RowSub (ρ₁ := ρ₁) i dc r) (hOrb : RowOrb (ρ₁ := ρ₁) i dc)
    (hMat : RowMat i dc VT VT' Dat ρ πx) (hTop : RowTop i dc VT' (T₁ := T₁))
    (hFin : RowFin i dc VT VT' Dat (T₁ := T₁))
    (hcob : ∀ n ∈ K.rowsN i dc, OrbC i dc (n := n) (Dat n).ρT') :
    K.Sel.RowTie i dc r ρ πx (rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD) := by
  intro n hn hw b hR
  obtain ⟨hF1, hF2, hFn⟩ := hFin
  obtain ⟨hF3, hF4, hsp⟩ := hFn n hn
  haveI := hF1
  haveI := hF2
  haveI := hF3
  haveI := hF4
  have hev : Function.Surjective ((vD n).toLinearMap ∘ₗ π) := (vD n).surjective.comp hπ
  have hrow := rowLenD_eq i dc VT VT' Dat ρ₁ π vD hpD heD hw hsp (hcob n hn) (hTop n hn hw).1 (hTop n hn hw).2
  have hR' : RowAt (Br.PD D.loc D.nbr i _ hw) (LL := Br.LLw (D.nbr i _ hw)) (O := Br.Ow (D.nbr i _ hw))
      (fun x : D.nd.X i => ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hw) (rDuO D.nd i r x)))
      ⇑(TruncatedSeriesCountingIdentities.locC (TruncatedSeriesCountingIdentities.CoefExt.self i _ hw) (T2O D.nd i ρ πx)) b := hR
  have hL1 := finDim_of_lat (Ow := Br.Ow (D.nbr i _ hw)) (Qp := ℚ_[D.nd.l i])
    (L1 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw)
      (resRep ρ₁ (Γn i dc n)))
  have hL2 := finDim_of_lat (Ow := Br.Ow (D.nbr i _ hw)) (Qp := ℚ_[D.nd.l i])
    (L2 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n) hsp)
  have hons : Function.Surjective (trL (eK (D.nbr i _ hw)) (f0 (Dat n) π (vD n))) :=
    trL_onto (hspQ := hsp) (hcomm := fun m => lift_map_mk (Dat n) π (vD n) m) hev
  have hc1 := hOrb n hn hw
  have hc2 : ∀ y, Continuous fun g => repL (eK (D.nbr i _ hw)) (Dat n).ρT' (Br.iota D.nbr i _ hw) g y := by
    intro y
    obtain ⟨x, rfl⟩ := hons y
    have h : (fun g => repL (eK (D.nbr i _ hw)) (Dat n).ρT' (Br.iota D.nbr i _ hw) g
        (trL (eK (D.nbr i _ hw)) (f0 (Dat n) π (vD n)) x)) =
        fun g => trL (eK (D.nbr i _ hw)) (f0 (Dat n) π (vD n))
          (repL (eK (D.nbr i _ hw)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hw) g x) :=
      funext fun g => (lift_map_equivariant (Dat n) (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n) (Br.iota D.nbr i _ hw g) x).symm
    rw [h]
    exact (trL_cont (eK (D.nbr i _ hw)) _).comp (hc1 x)
  have hOnto := latHom_onto (ρP := resRep ρ₁ (Γn i dc n)) (ρQ := (Dat n).ρTl') (Br.iota D.nbr i _ hw) (heO_br i dc hw) mkK_inj Subtype.val_injective
    (fun γ m => (locRep_mkK (resRep ρ₁ (Γn i dc n)) γ m).symm) (fun _ _ => rfl) mkK_span hsp
    (lift_map_equivariant (Dat n) (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n)) (fun m => lift_map_mk (Dat n) π (vD n) m) hev
  obtain ⟨m, k, hm, hk, hmk⟩ := hR' (TrV (eK (D.nbr i _ hw)) (VT' n))
    (repL (eK (D.nbr i _ hw)) (Dat n).ρT' (Br.iota D.nbr i _ hw))
    (L2 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n) hsp)
    hc2 (hMat n hn hw) (TrV (eK (D.nbr i _ hw)) (MK (O := D.nd.O i) T₁))
    (repL (eK (D.nbr i _ hw)) (locRep (resRep ρ₁ (Γn i dc n))) (Br.iota D.nbr i _ hw))
    (L1 (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw)
      (resRep ρ₁ (Γn i dc n)))
    hc1 (hSub n hn hw)
    (FR (Γ := ↥(Γn i dc n)) (eK (D.nbr i _ hw)) (D.nbr i _ hw).eO (heO_br i dc hw) (Br.iota D.nbr i _ hw) (Dat n)
      (resRep ρ₁ (Γn i dc n)) π (vD n) (heD n) hsp) hOnto
  have hm' : rowLenD i dc VT VT' Dat ρ₁ π vD hpD heD n = m := hrow.trans hm
  have hk' : lenOl (Br.PD D.loc D.nbr i (K.plOf i dc n) hw)
      (O := ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i (K.plOf i dc n) hw).LL)) = k := hk
  refine ⟨by rw [hm']; exact ENat.coe_ne_top m, ?_⟩
  rw [hm', hk']
  simp only [ENat.toNat_coe]
  exact hmk

end Rec

end Formalism.MainNotions.N.KRow

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StD

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Red

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

theorem rowTie_S
    (hSub : haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
      KRow.RowSub (ρ₁ := rho1 i Dd) i dc r)
    (hOrb : haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
      KRow.RowOrb (ρ₁ := rho1 i Dd) i dc)
    (hMat : KRow.RowMat i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (DatS i r π dc g0 eB e₁ s Dd hD hc) ρ π)
    (hTop : haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
      KRow.RowTop i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁))
    (hFin : KRow.RowFin i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
      (DatS i r π dc g0 eB e₁ s Dd hD hc) (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁))
    (hcob : ∀ n ∈ rowsN i dc, KHf.OrbC i dc (n := n) (DatS i r π dc g0 eB e₁ s Dd hD hc n).ρT') :
    Sel.RowTie i dc r ρ π (rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk) := by
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  letI := modS' i r π dc g0 eB e₁ s Dd hD hc
  haveI := KLat.towerT' Dd.r Dd.χ (RepresentationBoundsCohomology.blk D.R) Dd.ρk (epsU D.nd i) (Aw i dc) (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc)
  have hπ : Function.Surjective (piS i Dd hT hrk) :=
    (tensor_lattice_facts Dd (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R) hT hrk (epsU D.nd i)).2.2.2.2.2.2.2.2.2.2
  exact KRow.rowTie_disp i dc _ _ (DatS i r π dc g0 eB e₁ s Dd hD hc) (rho1 i Dd) (piS i Dd hT hrk)
    (vDS i r π dc g0 eB e₁ s Dd hD hc) (hpDS i r π dc g0 eB e₁ s Dd hD hc hT hrk)
    (heDS i r π dc g0 eB e₁ s Dd hD hc hT hrk) r ρ π hπ hSub hOrb hMat hTop hFin hcob

end Red

end Formalism.MainNotions.N.K.StD

end
end

section
variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core] [hH0Fin : Fact Formalism.MainNotions.N.K.H0.FinCore]

noncomputable section

open Finset Classical Formalism.BasicNotions

namespace Formalism.MainNotions.N.K.StD

section Unr

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i) (δO : D.nd.O i)

def UnrIn : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.col →
    Z1ur (1 : Representation ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (Br.G D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1)
        (Br.inert D.nbr i w hw) ≤
      finiteCocycles (Br.PD D.loc D.nbr i w hw)
        (1 : Representation ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 (Br.G D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1)

theorem unramified_input_of_admitted (h : EmbeddingTypes.UnramifiedTrivialH1f i dc) : UnrIn i dc := by
  intro w hw hc
  have h2 := h w hw hc (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)
  unfold UnrTriv at h2
  first
  | exact h2.ge

theorem unrFinIn_of (hA : UnrIn i dc) (l : K.Col i dc) : KFin.UnrFinIn i dc δO l := by
  intro f hf
  have hn := KUnr.col_over i dc l
  refine Submodule.mem_map_of_mem ?_
  show (fun g => KHf.mkK (((KFin.uzOf i dc δO l f hf.1 : _ → _) g))) ∈
    ((KHf.fZ i dc (K.colIdx i dc l) (KHf.locRep (Representation.trivial (D.nd.O i) ↥(KFin.Γc i dc l)
      ↥(Ideal.span {δO})))).restrictScalars (D.nd.O i))
  rw [Submodule.restrictScalars_mem, KHf.fZ_pos i dc _ hn]
  have hU := hA (K.plOf i dc (K.colIdx i dc l)) hn (KUnr.col_mem i dc l)
  let Bw := D.nbr i (K.plOf i dc (K.colIdx i dc l)) hn
  let V := KHf.MK (O := D.nd.O i) ↥(Ideal.span {δO})
  let c' : Br.G D.nbr i _ hn → Br.LLw Bw := fun g =>
    KHf.eK Bw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (f (Br.iota D.nbr i _ hn g)))
  have hc' : c' ∈ Z1ur (1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) (Br.inert D.nbr i _ hn) := by
    refine ⟨⟨hf.2.2 hn, fun g h => ?_⟩, 0, fun g hg => ?_⟩
    · show c' (g * h) = c' g + c' h
      have h1 : f (Br.iota D.nbr i _ hn g * Br.iota D.nbr i _ hn h) =
          f (Br.iota D.nbr i _ hn g) + f (Br.iota D.nbr i _ hn h) := hf.1 _ _
      simp only [c', map_mul]
      rw [h1, map_add (f := _), map_add (f := _)]
    · show c' g = 0 - 0
      rw [sub_zero]
      show KHf.eK Bw (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)) (f (Br.iota D.nbr i _ hn g))) = 0
      rw [hf.2.1 _ hg, map_zero, map_zero]
  have hcf : c' ∈ finiteCocycles (Br.PD D.loc D.nbr i _ hn) (1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) := by
    exact hU hc'
  let v0 : KHf.TrV (KHf.eK Bw) V := KHf.mkK (⟨δO, Ideal.mem_span_singleton_self δO⟩ : ↥(Ideal.span {δO}))
  let f0 : Br.LLw Bw →ₗ[Br.LLw Bw] KHf.TrV (KHf.eK Bw) V := LinearMap.toSpanSingleton _ _ v0
  have hf0 : Continuous f0 := continuous_id.smul continuous_const
  let ρ' := KHf.repL (KHf.eK Bw) (KHf.locRep (Representation.trivial (D.nd.O i) ↥(KFin.Γc i dc l) ↥(Ideal.span {δO})))
    (Br.iota D.nbr i _ hn)
  have heq : ∀ g x, f0 ((1 : Representation (Br.LLw Bw) (Br.G D.nbr i _ hn) (Br.LLw Bw)) g x) = ρ' g (f0 x) :=
    fun g x => (KUnr.locRep_triv (Br.iota D.nbr i _ hn g) (f0 x : V)).symm
  have key := (cocyclesFunctorial_holds _ _ _ _ _ _ (Br.PD D.loc D.nbr i _ hn) (Br.LLw Bw) (Br.LLw Bw) (KHf.TrV (KHf.eK Bw) V)
    1 ρ' f0 hf0 heq c').2 hcf
  let lhs : Br.G D.nbr i _ hn → KHf.TrV (KHf.eK Bw) V := fun g =>
    ((KHf.mkK ((KFin.uzOf i dc δO l f hf.1 : ↥(KFin.Γc i dc l) → ↥(Ideal.span {δO})) (Br.iota D.nbr i _ hn g)) : V) :
      KHf.TrV (KHf.eK Bw) V)
  show lhs ∈ finiteCocycles (Br.PD D.loc D.nbr i _ hn) ρ'
  suffices hfun : lhs = ⇑f0 ∘ c' by
    rw [hfun]
    exact key
  funext g
  show _ = f0 (c' g)
  rw [LinearMap.toSpanSingleton_apply]
  show _ = ((KHf.eK Bw).symm (c' g) • (show V from v0) : V)
  simp only [c', RingEquiv.symm_apply_apply]
  rw [algebraMap_smul]
  rw [← map_smul]
  show KHf.mkK ((KFin.uzOf i dc δO l f hf.1 : ↥(KFin.Γc i dc l) → ↥(Ideal.span {δO})) (Br.iota D.nbr i _ hn g)) =
    KHf.mkK _
  congr 1
  apply Subtype.ext
  show δO * f (Br.iota D.nbr i _ hn g) = f (Br.iota D.nbr i _ hn g) * δO
  ring

theorem unrFin_of (hA : UnrIn i dc) : KHf.UnrFin i dc δO (KFin.uz i dc δO) := by
  intro l
  refine unrFinIn_of i dc δO hA l _ ?_

  by_cases hU : KFin.UnrHom i dc l
  · unfold KFin.uCol; rw [dite_eq_left hU]; exact hU.choose_spec.1
  · have h0 : KFin.uCol i dc l = 0 := by unfold KFin.uCol; exact dite_eq_right hU
    rw [h0]; unfold KFin.UnrAdm
    refine ⟨fun g h => by simp, fun g _ => rfl, fun hn => ?_⟩
    first
    | exact Continuous.congr (f := fun _ => KHf.eK (D.nbr i (plOf i dc (colIdx i dc l)) hn)
        ((algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) 0)) continuous_const (fun _ => rfl)

end Unr

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Formalism.RepresentationBoundsCohomology.JL Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.SplitClassesAll Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.FIN
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (PadicCoeff FracTop IsFGTop cupFG)
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)
open Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.N.K Formalism.RepresentationBoundsCohomology.SF Formalism.MainNotions.N.K.St

attribute [local instance 2000] Topo.fracTopology Topo.rTopology

section Red3

variable {D : D7} (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
  (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i)
  (dc : TruncatedSeriesCountingIdentities.Decl D i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
  (hc : TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r)

theorem rowDR_of_fontaine (hF : TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i) (hG2 : TruncatedSeriesCountingIdentities.admG2 i r ρ π) (hDec : TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) : RowDR i r π dc g0 eB e₁ s Dd hD hc := fun w _ hn =>
  Font.isDR_dat i dc r ρ π g0 eB e₁ s Dd (hKm i) (hEps i) (hM0 i r π g0 eB e₁ s Dd hD hc) hF hG2 hDec hc hD hN w hn

variable (hT : Dd.Top (D.nd.T i) (RepresentationBoundsCohomology.one_le_letterBlockLength D.R))
  (hrk : ((Dd.ρk 0 Dd.e₁).map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))).rank = 1)

def RowTieIn : Prop :=
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  KRow.RowSub (ρ₁ := rho1 i Dd) i dc r ∧ KRow.RowOrb (ρ₁ := rho1 i Dd) i dc ∧
  KRow.RowMat i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
    (DatS i r π dc g0 eB e₁ s Dd hD hc) ρ π ∧
  KRow.RowTop1 i dc (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁) ∧
  KRow.RowFin i dc (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R)) (KLat.VT (O := D.nd.O i) (RepresentationBoundsCohomology.blk D.R))
    (DatS i r π dc g0 eB e₁ s Dd hD hc) (T₁ := FirstSummandSubmodule (D.nd.O i) Dd.e₁) ∧
  ∀ n ∈ rowsN i dc, KHf.OrbC i dc (n := n) (DatS i r π dc g0 eB e₁ s Dd hD hc n).ρT'

theorem row_match_from_comparison (h : RowTieIn i r ρ π dc g0 eB e₁ s Dd hD hc) :
    Sel.RowTie i dc r ρ π (rowLenS i r π dc g0 eB e₁ s Dd hD hc hT hrk) := by
  haveI := Topo.rTop_addGroup_RD i r π g0 eB e₁ s Dd hD
  obtain ⟨hSub, hOrb, hMat, hTop1, hFin, hcob⟩ := h
  exact rowTie_S i r ρ π dc g0 eB e₁ s Dd hD hc hT hrk hSub hOrb hMat
    (KRow.rowTop_of i dc _ (fun _ _ hw => KOrb.topMatch_pi i hw _) hTop1) hFin hcob

end Red3

end Formalism.MainNotions.N.K.StD

end
end
