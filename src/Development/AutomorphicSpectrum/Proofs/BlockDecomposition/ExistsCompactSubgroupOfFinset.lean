module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.LeviEmbMemNormalizerLower
public import Mathlib.NumberTheory.LocalField.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUnipotentInCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.UnipExhaust

theorem exists_compact_subgroup_of_finset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ)
      (s : Finset (GL (Fin N) k)), (↑s : Set (GL (Fin N) k)) ⊆ unipB k (Fin N) →
      ∃ L : Subgroup (GL (Fin N) k), L ≤ unipB k (Fin N) ∧ (↑s : Set (GL (Fin N) k)) ⊆ L ∧
        IsCompact (L : Set (GL (Fin N) k)) := by
  intro k _ _ _ _ N s hs
  obtain ⟨U, hU, hsU⟩ :=
    GlobalTheory.UnipCptSub.exists_compact_subgroup_of_isCompact _ s.finite_toSet.isCompact hs
  refine ⟨U ⊓ unipB k (Fin N), inf_le_right, fun g hg => ⟨hsU hg, hs hg⟩, ?_⟩
  rw [Subgroup.coe_inf, GlobalTheory.UnipCptSub.unipB_eq_unipOf]
  exact hU.inter_right (GlobalTheory.UnipCompact.isClosed_unipOf _)

end GlobalTheory.CompanionTheory.UnipExhaust
