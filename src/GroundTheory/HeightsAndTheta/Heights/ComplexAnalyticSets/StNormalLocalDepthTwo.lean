module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSerreConditions

@[expose] public section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def NormalLocalDepthTwo.Statement : Prop :=
  ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B],
    SerreSAt B 2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
