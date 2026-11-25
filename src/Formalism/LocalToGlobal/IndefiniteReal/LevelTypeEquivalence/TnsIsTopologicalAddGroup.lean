module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

noncomputable section

namespace Formalism.IndefR.Eqv.G5

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tns_isModuleTopology : IsModuleTopology (AF F) (AF F ⊗[F] E) := by
  first
    | exact ⟨rfl⟩

attribute [local instance] tns_isModuleTopology

theorem tns_isTopologicalAddGroup : IsTopologicalAddGroup (AF F ⊗[F] E) := by
  first
    | exact IsModuleTopology.topologicalAddGroup (AF F) (AF F ⊗[F] E)

section Basis

variable {d : ℕ} (b : Module.Basis (Fin d) F E)

def tnsCoord : (AF F ⊗[F] E) ≃ₗ[AF F] (Fin d → AF F) :=
  (Algebra.TensorProduct.basis (AF F) b).equivFun

theorem tnsCoord_continuous : Continuous (tnsCoord b) := by
  first
    | exact IsModuleTopology.continuous_of_linearMap (R := AF F) (tnsCoord b).toLinearMap

theorem tnsCoord_inclR (e : E) (k : Fin d) :
    tnsCoord b (inclR (AF F) e) k = algebraMap F (AF F) (b.repr e k) := by
  first
    | simp [tnsCoord, inclR, Algebra.TensorProduct.basis_repr_tmul]

end Basis

-- Private copy of `GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero` from
-- `Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero`.
private theorem exists_nhds_zero_principal_eq_zero (F : Type) [Field F] [NumberField F] :
    ∃ U ∈ nhds (0 : AdeleRing (𝓞 F) F),
      ∀ x : F, algebraMap F (AdeleRing (𝓞 F) F) x ∈ U → x = 0 := by
  have hU : IsOpen (X := InfiniteAdeleRing F)
      (Set.pi Set.univ fun v : InfinitePlace F => Metric.ball (0 : v.Completion) 1) :=
    isOpen_set_pi Set.finite_univ fun v _ => Metric.isOpen_ball
  have hV : IsOpen {a : FiniteAdeleRing (𝓞 F) F | ∀ v, a v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  refine ⟨_, (hU.prod hV).mem_nhds ⟨fun v _ => Metric.mem_ball_self one_pos,
    fun v => zero_mem _⟩, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hx
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F x fun v => by
    have h := h2 v
    rw [AdeleRing.algebraMap_snd_apply, HeightOneSpectrum.mem_adicCompletionIntegers,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
    exact h
  have hlt : ∀ w : InfinitePlace F, w (algebraMap (𝓞 F) F a) < 1 := fun w => by
    have h := h1 w trivial
    rw [mem_ball_zero_iff, AdeleRing.algebraMap_fst_apply, InfinitePlace.Completion.norm_coe] at h
    exact h
  by_contra h0
  have ha : a ≠ 0 := fun h => h0 (by rw [h, map_zero])
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact absurd (InfinitePlace.one_le_of_lt_one (w := w) ha fun z _ => hlt z) (not_le.2 (hlt w))

theorem tns_disc :∃ V : Set (AF F ⊗[F] E), IsOpen V ∧ (0 : AF F ⊗[F] E) ∈ V ∧
    ∀ e : E, inclR (AF F) e ∈ V → e = 0 := by
  obtain ⟨U, hU, hV⟩ := exists_nhds_zero_principal_eq_zero F
  obtain ⟨V0, hVU, hV0, h0⟩ := mem_nhds_iff.mp hU
  haveI : Module.Finite F E := inferInstance
  have b := Module.finBasis F E
  refine ⟨(tnsCoord b) ⁻¹' Set.univ.pi (fun _ => V0), ?_, ?_, ?_⟩
  · exact (isOpen_set_pi Set.finite_univ fun _ _ => hV0).preimage (tnsCoord_continuous b)
  · rw [Set.mem_preimage, map_zero, Set.mem_univ_pi]
    intro _
    exact h0
  · intro e he
    rw [Set.mem_preimage, Set.mem_univ_pi] at he
    rw [← b.repr.map_eq_zero_iff]
    ext k
    rw [Finsupp.coe_zero, Pi.zero_apply]
    apply hV
    apply hVU
    rw [← tnsCoord_inclR b e k]
    exact he k

theorem tup_disc (M n : ℕ) :
    DiscreteTopology (Set.range (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _)) := by
  obtain ⟨V, hV, h0, hVe⟩ := tns_disc (F := F) (E := E)
  haveI : IsTopologicalAddGroup (AF F ⊗[F] E) := tns_isTopologicalAddGroup
  have key : ∀ p : Set.range (ratTup (F := F) (AF F) : (Fin n → Fin M → E) → _),
      IsOpen ({p} : Set _) := by
    rintro ⟨_, X, rfl⟩
    refine isOpen_induced_iff.mpr
      ⟨{y | ∀ a i, y a i - inclR (F := F) (AF F) (X a i) ∈ V}, ?_, ?_⟩
    · have hc : Continuous fun y : Fin n → Fin M → AF F ⊗[F] E => y - ratTup (F := F) (AF F) X :=
        continuous_id.sub continuous_const
      have ho : IsOpen (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin M => V) :=
        isOpen_set_pi Set.finite_univ fun _ _ => isOpen_set_pi Set.finite_univ fun _ _ => hV
      convert ho.preimage hc using 1
      ext y
      simp [ratTup]
    · ext ⟨_, Y, rfl⟩
      rw [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
      show (∀ a i, ratTup (F := F) (AF F) Y a i - inclR (F := F) (AF F) (X a i) ∈ V) ↔
        ratTup (F := F) (AF F) Y = ratTup (F := F) (AF F) X
      constructor
      · intro h
        have hXY : Y = X := funext fun a => funext fun i =>
          sub_eq_zero.mp (hVe (Y a i - X a i) (by rw [map_sub]; exact h a i))
        rw [hXY]
      · intro h a i
        have h' : inclR (F := F) (AF F) (Y a i) = inclR (F := F) (AF F) (X a i) :=
          congrFun (congrFun h a) i
        show inclR (F := F) (AF F) (Y a i) - inclR (F := F) (AF F) (X a i) ∈ V
        rw [h', sub_self]
        exact h0
  first
    | exact discreteTopology_iff_isOpen_singleton.mpr key

end Formalism.IndefR.Eqv.G5
