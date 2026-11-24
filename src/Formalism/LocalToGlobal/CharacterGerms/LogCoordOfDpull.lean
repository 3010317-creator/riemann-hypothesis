module

public import Formalism.IncomingBounds.StatementThmP
public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Formalism.IncomingBounds.FlowDegreeBounds.ThmPJet
public import Formalism.LocalToGlobal.CharacterGerms.ConstMemTypeSetOfNonneg
public import Formalism.LocalToGlobal.CharacterGerms.LemmaMJet
import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

namespace VP

theorem cc_subst_eq {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) (f : MvPowerSeries σ C) :
    MvPowerSeries.constantCoeff (MvPowerSeries.subst a f) = MvPowerSeries.constantCoeff f := by
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  set c := MvPowerSeries.constantCoeff f with hc
  have hg : MvPowerSeries.constantCoeff (f - algebraMap C (MvPowerSeries σ C) c) = 0 := by
    simp [hc, MvPowerSeries.algebraMap_apply]
  have hf : f = algebraMap C (MvPowerSeries σ C) c + (f - algebraMap C (MvPowerSeries σ C) c) := by
    ring
  have h1 : MvPowerSeries.subst a (algebraMap C (MvPowerSeries σ C) c) =
      algebraMap C (MvPowerSeries τ C) c := by
    rw [← MvPowerSeries.coe_substAlgHom hs]
    exact (MvPowerSeries.substAlgHom hs).commutes c
  rw [hf, MvPowerSeries.subst_add hs, map_add (f := _), h1, constantCoeff_subst_zero ha hg]
  simp [MvPowerSeries.algebraMap_apply]

variable {Y : FBChart C V O dd} {p : ∀ o, PairData Y d (I o)}

end VP

end Formalism.L2.FormalSeriesBounds
