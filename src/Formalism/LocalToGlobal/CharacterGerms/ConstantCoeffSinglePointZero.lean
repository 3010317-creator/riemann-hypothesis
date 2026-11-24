module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieValCut
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Formalism.LocalToGlobal.CharacterGerms.RowTieJet
public import Formalism.LocalToGlobal.CharacterGerms.SubstSubst

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

section Pull

variable (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o))

theorem cc_X {σ : Type} (s : σ) : MvPowerSeries.constantCoeff (MvPowerSeries.X s : MvPowerSeries σ C) = 0 := MvPowerSeries.constantCoeff_X s

end Pull

section Emb

variable {n : ℕ}

end Emb

end VP

end Formalism.L2.FormalSeriesBounds
