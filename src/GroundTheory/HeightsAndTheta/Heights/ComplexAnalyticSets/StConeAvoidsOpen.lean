module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsConeAvoid

@[expose] public section

namespace GroundTheory.Heights₂.Heights.ComplexSets

open MvPolynomial

noncomputable section

def ConeAvoidsOpen.Statement : Prop :=
  ∀ (n d N : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)),
    IsZariskiOpen {A : Matrix (Fin d) (Fin n) ℂ | ConeAvoids J A N}

end

end GroundTheory.Heights₂.Heights.ComplexSets
