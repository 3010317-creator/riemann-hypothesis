module

public import Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfUnitGerm
public import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.IncomingBounds.FlowDegreeBounds.ThmPJet
public import Formalism.LocalToGlobal.CharacterGerms.LogCoordOfDpull
public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
public import Formalism.LocalToGlobal.CharacterGerms.RowTieValCut
public import Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffSinglePointZero
import Formalism.LocalToGlobal.CharacterGerms.LemmaMJet
import Formalism.LocalToGlobal.CharacterGerms.SubstSubst

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Formalism.LocalToGlobal.CharacterGerms.RowTieValG, Formalism.LocalToGlobal.CharacterGerms.GermLiftSelfSt

-- ===== clump member: Formalism.LocalToGlobal.CharacterGerms.RowTieValG =====
-- clump-header: {"m": "Formalism.LocalToGlobal.CharacterGerms.RowTieValG", "h": "module\n\npublic import Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfUnitGerm\npublic import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin\npublic import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow\npublic import Formalism.IncomingBounds.FlowDegreeBounds.ThmPJet\nimport Formalism.LocalToGlobal.CharacterGerms.LemmaMJet\npublic import Formalism.LocalToGlobal.CharacterGerms.LogCoordOfDpull\nimport Formalism.LocalToGlobal.CharacterGerms.SubstSubst\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  {Var : Type} [Fintype Var] {n : ℕ}

def colLin (M : Var → Fin n × Fin dd → C) (b : Fin n) : Var → Fin dd → C := fun x i => M x (b, i)

variable (Y : FBChart C V O dd) (M : Var → Fin n × Fin dd → C)

def linPt (q : Fin n × Fin dd) : MvPowerSeries Var C := MvPowerSeries.subst (linS (colLin M q.1)) (e Y q.2)

def linPull (F : PS C n dd) : MvPowerSeries Var C := MvPowerSeries.subst (linPt Y M) F

theorem cc_linPt (q : Fin n × Fin dd) : MvPowerSeries.constantCoeff (linPt Y M q) = 0 := by
  unfold linPt
  exact VP.cc_subst (fun s => by simp [linS, MvPowerSeries.smul_eq_C_mul]) (cc_e Y q.2)

theorem linPull_prod {ι : Type} (s : Finset ι) (F : ι → PS C n dd) :
    linPull Y M (∏ i ∈ s, F i) = ∏ i ∈ s, linPull Y M (F i) := by
  unfold linPull
  exact VP.subst_prod (cc_linPt Y M) s F

end VP

end Formalism.L2.FormalSeriesBounds
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.CharacterGerms.RowTieValG =====

-- ===== clump member: Formalism.LocalToGlobal.CharacterGerms.GermLiftSelfSt =====
-- clump-header: {"m": "Formalism.LocalToGlobal.CharacterGerms.GermLiftSelfSt", "h": "module\n\npublic import Formalism.LocalToGlobal.CharacterGerms.RowTieValG\npublic import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf\npublic import Formalism.LocalToGlobal.CharacterGerms.RowTieValCut\npublic import Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffSinglePointZero\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I0 : Orb → Type} [∀ o, Fintype (I0 o)]

abbrev IS (I0 : Orb → Type) : Orb → Fin 2 → Type := fun o _ => I0 o

section Defs

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o))

def uS (w : WVO (IS I0)) : Fin 2 × Fin dd → C := (Y.rawSelf (p w.1)).u w.2.1 w.2.2

def pull2 (F : PS C 2 dd) : MvPowerSeries (WVO (IS I0)) C := VP.linPull Y (uS Y p) F

def UnitSelfSt : Prop :=
  SelfSep Y p → ∃ U : PS C 2 dd, IntS V U ∧ V.v (MvPowerSeries.constantCoeff U) = 0 ∧
    pull2 Y p (∏ col : Fin 2, ev (n := 2) ![pt C dd col] (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0))) =
      pull2 Y p U * ∏ o, toAllS (I := IS I0) o (mvExp (Y.rawSelf (p o)).hRow)

def GermLiftSelfSt (H : ∀ o, (Y.rawSelf (p o)).Hyps V) : Prop :=
  SelfSep Y p → ∀ (o : Orb) (S : ∀ g, Sys (((Y.rawSelf (p o)).rowData (H o)).G g))
    (t : ∀ _ : Fin 2, I0 o → MvPowerSeries (I0 o) C), (∀ g, (S g).IsT (t g)) →
    ∀ F ∈ IntGerm V t, ∃ G : PS C 2 dd, IntS V G ∧ pull2 Y p G = toAllS (I := IS I0) o F

end Defs

namespace VP

variable (Y : FBChart C V O dd) (p : ∀ o, SelfData Y d (I0 o)) {N n : ℕ} (pl : Fin N × Fin 2 ↪ Fin n)

end VP

end Formalism.L2.FormalSeriesBounds
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Formalism.LocalToGlobal.CharacterGerms.GermLiftSelfSt =====
