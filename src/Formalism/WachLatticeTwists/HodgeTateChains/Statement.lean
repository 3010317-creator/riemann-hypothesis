module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.NumberTheory.Padics.PadicIntegers

@[expose] public section

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Polynomial

def c0 (ℓ m : ℕ) (U : Finset ℤ) : ℕ := 2 + ∑ u ∈ U, (m + padicValInt ℓ u)

def HTpoly (ℓ : ℕ) [Fact ℓ.Prime] (w : ℤ_[ℓ]ˣ) (U : Finset ℤ) (i : ℤ) : Polynomial ℤ_[ℓ] :=
  ∏ a ∈ U, (X - C (((w ^ (i - a) : ℤ_[ℓ]ˣ) : ℤ_[ℓ])))

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
