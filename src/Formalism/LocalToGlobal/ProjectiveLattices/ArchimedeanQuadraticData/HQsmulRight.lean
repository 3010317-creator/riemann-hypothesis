module

public import ReciprocityTheory.SemistableReduction.TorsionNonvanishStatement
import Mathlib.RingTheory.PiTensorProduct

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.FundamentalDomainD5

open NumberField Matrix ComplexConjugate ReciprocityTheory.MultiplicativeHeights

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {r : ℕ}

def Theta (p : ℕ) (w : ι → Fin r → ℂ) : ι → Fin r → ℂ := fun i a => sgn p a * w i a

section Herm

variable (S : HermForm K r)

end Herm

end Formalism.L2.Pj.FundamentalDomainD5
