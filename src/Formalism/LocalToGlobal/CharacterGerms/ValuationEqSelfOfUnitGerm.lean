module

public import Formalism.LocalToGlobal.CharacterGerms.RowTieValCut
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Formalism.LocalToGlobal.CharacterGerms.RowTieJet
public import Formalism.LocalToGlobal.CharacterGerms.GermLiftSelfSt
public import Formalism.LocalToGlobal.CharacterGerms.IntSProd
public import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd
public import Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfLogUnitGerm
import Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffSinglePointZero
import Formalism.LocalToGlobal.CharacterGerms.SubstSubst
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ChartValuesBoundProductsOnPlanes

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.CharacterGerms.ValuationEqSelfOfUnitGerm

-- ===== clump member: Formalism.LocalToGlobal.CharacterGerms.ValuationEqSelfOfUnitGerm =====
-- clump-header: {"m": "Formalism.LocalToGlobal.CharacterGerms.ValuationEqSelfOfUnitGerm", "h": "module\n\npublic import Formalism.LocalToGlobal.CharacterGerms.GermLiftSelfSt\nimport Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffSinglePointZero\npublic import Formalism.LocalToGlobal.CharacterGerms.IntSProd\npublic import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd\nimport Formalism.LocalToGlobal.CharacterGerms.SubstSubst\npublic import Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfLogUnitGerm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

namespace VP

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

theorem pullback_two_var_prod {ι : Type} (s : Finset ι) (F : ι → PS C 2 dd) :
    pull2 Y p (∏ i ∈ s, F i) = ∏ i ∈ s, pull2 Y p (F i) := by
  unfold pull2
  exact linPull_prod _ _ s F

end VP

theorem valuation_eq_self_of_unit_germ (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) (H : ∀ o, (Y.rawSelf (p o)).Hyps V)
    (Ls : LetSys C dd) (n : ℕ) (_h2 : UnitSelfSt Y p) (_h3 : GermLiftSelfSt Y p H) : ValEqSelfSt Y p H Ls n :=
  by apply GlobalTheory.ValSelf.valEqSelf

end Formalism.L2.FormalSeriesBounds
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.CharacterGerms.ValuationEqSelfOfUnitGerm =====
