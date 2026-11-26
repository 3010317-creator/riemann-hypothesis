module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs

@[expose] public section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def InjectiveHolomorphicOpen.Statement : Prop :=
  ∀ (k : ℕ) (U : Set (Fin k → ℂ)) (f : (Fin k → ℂ) → Fin k → ℂ),
    IsOpen U → DifferentiableOn ℂ f U → Set.InjOn f U → IsOpen (f '' U)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
