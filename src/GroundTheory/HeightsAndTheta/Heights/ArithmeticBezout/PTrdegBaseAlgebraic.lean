module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsTrdegBaseAlgebraic
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.Algebraic.Basic
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Cardinal

theorem TrdegBaseAlgebraic.proof : TrdegBaseAlgebraic.Statement := by
  intro F K Ω _ _ _ _ _ _ _ hKF ι z
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra F Ω, A = Algebra.adjoin F (Set.range z) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Subalgebra K Ω, B = Algebra.adjoin K (Set.range z) := ⟨_, rfl⟩
  rw [← hA, ← hB]
  have hAB : A ≤ B.restrictScalars F :=
    hA ▸ Algebra.adjoin_le
      (by rw [Subalgebra.coe_restrictScalars, hB]; exact Algebra.subset_adjoin)
  let i : A →+* B := A.val.toRingHom.codRestrict B fun x => hAB x.2
  have : FaithfulSMul F A :=
    (faithfulSMul_iff_algebraMap_injective F A).mpr (algebraMap F A).injective
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis F A
  let x : t → B := fun a => i a
  set C : Subalgebra K B := Algebra.adjoin K (Set.range x) with hC

  have hFC : Algebra.adjoin F (Set.range ((↑) : t → A)) ≤
      { C.toSubsemiring.comap i with
        algebraMap_mem' := fun c => by
          change i (algebraMap F A c) ∈ C
          rw [show i (algebraMap F A c) = algebraMap K B (algebraMap F K c)
            from Subtype.ext (IsScalarTower.algebraMap_apply F K Ω c)]
          exact C.algebraMap_mem _ } :=
    Algebra.adjoin_le fun _ ⟨a, ha⟩ => by
      subst ha
      exact show i a ∈ C from hC ▸ Algebra.subset_adjoin ⟨a, rfl⟩
  let f : Algebra.adjoin F (Set.range ((↑) : t → A)) →+* C :=
    (i.comp (Subalgebra.val _).toRingHom).codRestrict C fun r => hFC r.2
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun c : C => ((c : B) : Ω)) hab
  have key : ∀ (w : Ω), w ∈ Algebra.adjoin K (Set.range z) →
      ∀ (hw : w ∈ B), IsAlgebraic C (⟨w, hw⟩ : B) := by
    intro w hw'
    induction hw' using Algebra.adjoin_induction with
    | mem w hw' =>
      intro hw
      obtain ⟨m, rfl⟩ := hw'
      have hzA : z m ∈ A := hA ▸ Algebra.subset_adjoin ⟨m, rfl⟩
      have h1 : IsAlgebraic (Algebra.adjoin F (Set.range ((↑) : t → A))) (⟨z m, hzA⟩ : A) :=
        ht.isAlgebraic.isAlgebraic _
      exact h1.ringHom_of_comp_eq f i hf (RingHom.ext fun _ => rfl)
    | algebraMap k =>
      intro hw
      exact (hKF.isAlgebraic k).ringHom_of_comp_eq ((algebraMap K C).comp (algebraMap F K))
        (algebraMap K B) (RingHom.injective _) (RingHom.ext fun _ => rfl)
    | add u v hu' hv' hu hv =>
      intro hw
      exact (hu (hB ▸ hu')).add (hv (hB ▸ hv'))
    | mul u v hu' hv' hu hv =>
      intro hw
      exact (hu (hB ▸ hu')).mul (hv (hB ▸ hv'))
  have alg : Algebra.IsAlgebraic C B := ⟨fun b => key b.1 (hB ▸ b.2) b.2⟩
  calc Algebra.trdeg K B ≤ #(Set.range x) := Algebra.IsAlgebraic.trdeg_le_cardinalMk K (Set.range x)
    _ ≤ #t := Cardinal.mk_range_le
    _ = Algebra.trdeg F A := ht.cardinalMk_eq_trdeg

end GroundTheory.Heights₂.Heights
