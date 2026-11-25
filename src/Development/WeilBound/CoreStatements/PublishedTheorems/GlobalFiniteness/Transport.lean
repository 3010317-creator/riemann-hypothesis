module

import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeModules
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsGsEquiv
public import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
public import GroundTheory.ProfiniteCohomology.RestrictedRamification.MaxUnramifiedOutside
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import ReciprocityTheory.GaloisValuations.Global
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideCohomology
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixing
public import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohCmp
public import Mathlib.FieldTheory.Galois.Profinite
public import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Mathlib.Tactic.Linter.Style
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TransportA
import GroundTheory.GlobalFields.HerbrandQuotients.RationalForm

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.GFTransport

theorem finite_cohomology_transport {k G H : Type} [CommRing k] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H)
    (A : Rep.{0} k G) [IsDiscreteRep A] (n : ℕ)
    (h : haveI := IsDiscreteRep.res θ.symm.continuous (φ := (θ.symm : H ≃* G).toMonoidHom) A;
      Finite (cohomology (Rep.res (θ.symm : H ≃* G).toMonoidHom A) n)) :
    Finite (cohomology A n) := by
  have := IsDiscreteRep.res θ.symm.continuous (φ := (θ.symm : H ≃* G).toMonoidHom) A
  let i := cohomologyIsoOfContinuousMulEquiv θ.symm
    (Iso.refl (Rep.res (θ.symm : H ≃* G).toMonoidHom A)) n
  refine Finite.of_surjective i.inv.hom fun x => ⟨i.hom.hom x, ?_⟩
  rw [← ModuleCat.comp_apply, i.hom_inv_id]
  rfl

theorem cohDict {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] {r : ℕ} {M : Type} [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M]
    [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (rhoS : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M)
    (hc : ContAction rhoS) :
    ∃ (A : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))))
      (_ : IsDiscreteRep A), Finite A.V ∧ (∀ a : A.V, (l ^ r) • a = 0) ∧
      Nonempty (H1 rhoS ≃+ cohomology A 1) ∧ Nonempty (H2 rhoS ≃+ cohomology A 2) ∧
      ∀ n : ℕ, Nonempty (Hn rhoS n ≃+ cohomology A n) := by
  let e := (PositivityTheory.Lit1.GEN.W_dictfwd_b.gsIso (Ω := Ω) (S : Set (HeightOneSpectrum (𝓞 F)))).symm
  have hc' := ReciprocityTheory.Neutral.Bridge.contAction_comp e hc
  let rho' : Representation (ZMod (l ^ r)) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M :=
    rhoS.comp (e : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) →*
      GS Ω (S : Set (HeightOneSpectrum (𝓞 F))))
  obtain ⟨A, hA, eA, he⟩ := CompanionTheory.LocalTateOrthogonality.Gcoh.gcRep _ (ZMod (l ^ r)) M rho' hc'
  have hAf : Finite A.V := Finite.of_equiv _ eA.toEquiv
  have hn : ∀ a : A.V, (l ^ r) • a = 0 := by
    intro a
    obtain ⟨m, rfl⟩ := eA.surjective a
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self, zero_smul, map_zero]
  obtain ⟨e1, -⟩ := CompanionTheory.LocalTateOrthogonality.Gcoh.gc1 _ (ZMod (l ^ r)) M rho' A eA he
  obtain ⟨e2, -⟩ := CompanionTheory.LocalTateOrthogonality.Gcoh.gc2 _ (ZMod (l ^ r)) M rho' A eA he
  have t1 := ReciprocityTheory.Neutral.Bridge.equivH1OfIso e rhoS rho' (fun _ _ => rfl)
  have t2 := ReciprocityTheory.Neutral.Bridge.equivH2OfIso e rhoS rho' (fun _ _ => rfl)
  refine ⟨A, hA, hAf, hn, ⟨t1.toAddEquiv.trans e1⟩, ⟨t2.toAddEquiv.trans e2⟩, fun n => ?_⟩
  obtain ⟨en⟩ := CompanionTheory.LocalTateOrthogonality.Gcoh.gcn _ (ZMod (l ^ r)) M rho' A eA he n
  exact ⟨(ReciprocityTheory.Neutral.Bridge.isoHn e rhoS rho' (fun _ _ => rfl) n).toAddEquiv.trans en⟩

end PositivityTheory.Lit1.GFTransport
