module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
public import Formalism.DropLevelBounds.ConstantCoeffVanishing.UbintConstantCoeffEqZero
public import Formalism.LocalToGlobal.CharacterGerms.IntSProd
public import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin
public import Formalism.LocalToGlobal.CharacterGerms.RowTieJet
public import Formalism.LocalToGlobal.CharacterGerms.SubstSubst
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

theorem cc_smul {σ : Type} (c : C) {F : MvPowerSeries σ C} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (c • F) = 0 := by
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, hF, mul_zero]

end VP

end Formalism.L2.FormalSeriesBounds
