module

public import Mathlib.Data.Set.Card
import Mathlib.Tactic.Linter.HaveILetI
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.Algebra.Group.Action.Defs

@[expose] public section

open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.card_dvd_of_partition_equal_size :
    ∀ (ι Q : Type) [Finite ι] (T : Q → Set ι) (d : ℕ), (∀ q, (T q).ncard = d) → (∀ i, ∃! q, i ∈ T q) →
      Nat.card Q ∣ Nat.card ι := by
  intro ι Q _ T d hT hu
  classical
  choose f hf unique using hu
  have fiber (q : Q) : {i | f i = q} = T q := by
    ext i
    exact ⟨fun h => (show f i = q from h) ▸ hf i, fun h => (unique i q h).symm⟩
  let e (q : Q) : {i // f i = q} ≃ Fin d :=
    Finite.equivFinOfCardEq (by
      change ({i | f i = q} : Set ι).ncard = d
      rw [fiber, hT])
  let partition : ι ≃ Q × Fin d := (Equiv.sigmaFiberEquiv f).symm.trans
    ((Equiv.sigmaCongrRight e).trans (Equiv.sigmaEquivProd Q (Fin d)))
  refine ⟨d, ?_⟩
  rw [Nat.card_congr partition, Nat.card_prod, Nat.card_fin]
