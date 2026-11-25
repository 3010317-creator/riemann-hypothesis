module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.Tactic.Linter.HaveILetI
public import Formalism.SharedLemmas.PrecompleteFinite

@[expose] public section

open IsLocalRing

private theorem isPrecomplete_finite {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Finite R M] (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I M := by
  first
  | exact _root_.Formalism.SharedLemmas.isPrecomplete_of_moduleFinite
  | (apply _root_.Formalism.SharedLemmas.isPrecomplete_of_moduleFinite <;> assumption)

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.finCompl :
    ∀ (Λ M : Type) [CommRing Λ] [IsNoetherianRing Λ] (I : Ideal Λ) [IsAdicComplete I Λ] [AddCommGroup M] [Module Λ M] [Module.Finite Λ M], IsAdicComplete I M := by
  intro Λ M _ _ I _ _ _ _
  exact
    { toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson I)
      toIsPrecomplete := isPrecomplete_finite I }
