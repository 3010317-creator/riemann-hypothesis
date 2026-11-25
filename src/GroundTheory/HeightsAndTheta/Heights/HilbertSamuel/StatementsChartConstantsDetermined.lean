module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.PenHost
import Mathlib.Tactic.TypeStar
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ArithModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjDefs

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry NumberField

def intsIn (F Ω : Type*) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] : Subalgebra ℤ Ω :=
  ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).toIntAlgHom.range

section Inhabitants

open ProjLine

end Inhabitants

end GroundTheory.Heights₂.Heights.HilbertSamuel
