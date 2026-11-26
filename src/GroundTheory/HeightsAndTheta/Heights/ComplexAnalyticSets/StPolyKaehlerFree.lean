module

public import Mathlib.RingTheory.Kaehler.Basic

@[expose] public section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

def PolyKaehlerFree.Statement : Prop :=
  ∀ (R k : Type) [Field R] [Field k] [Algebra R k] (n : ℕ),
    Module.Free (MvPolynomial (Fin n) k) Ω[MvPolynomial (Fin n) k⁄R]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
