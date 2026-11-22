module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueGlobalLatticeOfLocalLatticesStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NumberFieldLatticeDeterminedByLocalLatticesStatement

@[expose] public section

noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unfold.LatLoc

theorem isLattice_map {E V W : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (f : V ≃ₗ[E] W) (Λ : Submodule (𝓞 E) V) (h : Submodule.IsLattice E Λ) :
    Submodule.IsLattice E (Λ.map ((f : V →ₗ[E] W).restrictScalars (𝓞 E))) := by
  exact Submodule.IsLattice.of_fg E (h.fg.map _)

private theorem isFullLattice_map {E V W : Type} [Field E] [NumberField E] [AddCommGroup V] [Module E V] [Module (𝓞 E) V]
    [IsScalarTower (𝓞 E) E V] [AddCommGroup W] [Module E W] [Module (𝓞 E) W] [IsScalarTower (𝓞 E) E W]
    (f : V ≃ₗ[E] W) (Λ : Submodule (𝓞 E) V) (h : Submodule.IsFullLattice E Λ) :
    Submodule.IsFullLattice E (Λ.map ((f : V →ₗ[E] W).restrictScalars (𝓞 E))) := by
  refine { toIsLattice := isLattice_map f Λ h.toIsLattice, span_eq_top := ?_ }
  change Submodule.span E (f.toLinearMap '' (Λ : Set V)) = ⊤
  rw [Submodule.span_image, h.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
  exact f.surjective

variable {D : D7}

def cE (D : D7) : (VS D).V ≃ₗ[D.host.E] (Fin (nV D) → D.host.E) := (VS D).frame.equivFun

def cL (Λ : LV D) : Submodule (𝓞 D.host.E) (Fin (nV D) → D.host.E) :=
  Λ.map (((cE D) : (VS D).V →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E))

theorem baseChange_eq (Z : LocDat D) (p : PlF D) (x : (VS D).V) : baseChange₂ D p x = (GlobalTheory.HL.placesOf Z).bc p (cE D x) := rfl

theorem localLattice_eq (Z : LocDat D) (p : PlF D) (Λ : LV D) : lattice₂ D Z.M p Λ = (GlobalTheory.HL.placesOf Z).lat p (cL Λ) := by
  unfold lattice₂ GlobalTheory.HL.Places.lat cL
  rw [Submodule.map_coe, Set.image_image]
  rfl

theorem cL_injective : Function.Injective (cL (D := D)) := by
  intro Λ₁ Λ₂ h
  have := congrArg (Submodule.comap (((cE D) : (VS D).V →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E))) h
  unfold cL at this
  rwa [Submodule.comap_map_eq_of_injective (by exact (cE D).injective),
    Submodule.comap_map_eq_of_injective (by exact (cE D).injective)] at this

theorem std_finite (Z : LocDat D) (Λ : LV D) (h : Submodule.IsFullLattice D.host.E Λ) :
    {p | lattice₂ D Z.M p Λ ≠ Submodule.span ((GlobalTheory.HL.placesOf Z).L p).O
      (Set.range fun i => (Pi.single i 1 : Fin (nV D) → ((GlobalTheory.HL.placesOf Z).loc p).Ep))}.Finite := by
  have := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (cL Λ) (isFullLattice_map _ _ h)).2.2
  simp only [localLattice_eq]
  exact this

theorem lattices_local_global : ∀ (D : D7) (Z : LocDat D), (∀ Λ₁ Λ₂ : LV D, Submodule.IsFullLattice D.host.E Λ₁ →
    Submodule.IsFullLattice D.host.E Λ₂ → {p | lattice₂ D Z.M p Λ₁ ≠ lattice₂ D Z.M p Λ₂}.Finite ∧
      ((∀ p, lattice₂ D Z.M p Λ₁ = lattice₂ D Z.M p Λ₂) → Λ₁ = Λ₂)) ∧
    ∀ (Λ₀ : LV D), Submodule.IsFullLattice D.host.E Λ₀ → ∀ Lp : ∀ p : PlF D, Submodule (Z.M p).L.O (Vp D p),
      (∀ p, (Lp p).FG ∧ Submodule.span (D.s.atP p).Ep (Lp p : Set (Vp D p)) = ⊤) →
      {p | Lp p ≠ lattice₂ D Z.M p Λ₀}.Finite →
      ∃ Λ : LV D, Submodule.IsFullLattice D.host.E Λ ∧ ∀ p, lattice₂ D Z.M p Λ = Lp p := by
  intro D Z
  refine ⟨fun Λ₁ Λ₂ h₁ h₂ => ⟨?_, fun h => ?_⟩, fun Λ₀ h₀ Lp hL hfin => ?_⟩
  · refine ((std_finite Z Λ₁ h₁).union (std_finite Z Λ₂ h₂)).subset fun p hp => ?_
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    exact hp (hc.1.trans hc.2.symm)
  · apply cL_injective
    have r₁ := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (cL Λ₁) (isFullLattice_map _ _ h₁)).1
    have r₂ := (GlobalTheory.T.numberField_lattice_determined_by_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) (cL Λ₂) (isFullLattice_map _ _ h₂)).1
    ext x
    rw [r₁, r₂]
    refine forall_congr' fun p => ?_
    rw [← localLattice_eq, ← localLattice_eq, h p]
  · obtain ⟨Γ, ⟨hΓ, hΓp⟩, -⟩ := GlobalTheory.T.exists_unique_global_lattice_of_local_lattices (GlobalTheory.HL.placesOf Z) (nV D) Lp (fun p => hL p)
      (((std_finite Z Λ₀ h₀).union hfin).subset fun p hp => by
        by_contra hc
        simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
        exact hp (hc.2.trans hc.1))
    let A := GlobalTheory.HL.placesOf Z
    have hΓfull : Submodule.IsFullLattice D.host.E Γ := by
      refine { toIsLattice := hΓ, span_eq_top := ?_ }
      by_contra hspan
      obtain ⟨φ, hφ, hker⟩ := (Submodule.span D.host.E (Γ : Set (Fin (nV D) → D.host.E))).exists_le_ker_of_lt_top
        (lt_top_iff_ne_top.mpr hspan)
      obtain ⟨p⟩ := GlobalTheory.HL.GlueInt.nonempty_place' (F := D.host.F)
      have := GlobalTheory.HL.GlueInt.nontrivial_Ep A p
      -- A functional annihilating the global span extends by mapping its coefficients.
      let ψ : (Fin (nV D) → (A.loc p).Ep) →ₗ[(A.loc p).Ep] (A.loc p).Ep :=
        ∑ i, (A.loc p).ιE (φ (Pi.single i 1)) • LinearMap.proj i
      have hψ (x : Fin (nV D) → D.host.E) : ψ (A.bc p x) = (A.loc p).ιE (φ x) := by
        have hx : φ x = ∑ i, x i * φ (Pi.single i 1) := by
          have hi (i : Fin (nV D)) : (fun j : Fin (nV D) => if i = j then (1 : D.host.E) else 0) =
              Pi.single i 1 := by
            funext j
            simp [Pi.single_apply, eq_comm]
          simpa only [hi, smul_eq_mul] using LinearMap.pi_apply_eq_sum_univ φ x
        simp only [hx, ψ, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
          smul_eq_mul, map_sum, map_mul, mul_comm, GlobalTheory.HL.Places.bc]
      have htop : Submodule.span (A.loc p).Ep (A.bc p '' (Γ : Set (Fin (nV D) → D.host.E))) = ⊤ := by
        have hp := (hL p).2
        rw [← hΓp p] at hp
        change Submodule.span (A.loc p).Ep
          (↑(Submodule.span (A.L p).O (Set.image (A.bc p) (Γ : Set (Fin (nV D) → D.host.E)))) :
            Set (Fin (nV D) → (A.loc p).Ep)) = ⊤ at hp
        rwa [Submodule.span_span_of_tower] at hp
      have hle : Submodule.span (A.loc p).Ep (A.bc p '' (Γ : Set (Fin (nV D) → D.host.E))) ≤
          LinearMap.ker ψ := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨x, hx, rfl⟩
        change ψ (A.bc p x) = 0
        rw [hψ, LinearMap.mem_ker.mp (hker (Submodule.subset_span hx)), map_zero]
      rw [htop] at hle
      apply hφ
      apply LinearMap.ext
      intro x
      have hz : A.bc p x ∈ LinearMap.ker ψ := hle Submodule.mem_top
      apply (A.loc p).ιE.injective
      simpa only [LinearMap.mem_ker, hψ, LinearMap.zero_apply, map_zero] using hz
    refine ⟨Γ.map (((cE D).symm : (Fin (nV D) → D.host.E) →ₗ[D.host.E] _).restrictScalars (𝓞 D.host.E)),
      isFullLattice_map _ _ hΓfull, fun p => ?_⟩
    rw [localLattice_eq, ← hΓp p]
    congr 1
    unfold cL
    rw [← Submodule.map_comp]
    convert Submodule.map_id Γ
    ext x
    simp

end GlobalTheory.Unfold.LatLoc
