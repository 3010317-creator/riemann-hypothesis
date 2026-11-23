module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SignAtBasePlaceEqEmbedding
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameData
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwInputs.Move

variable {D : D7} (r : Rest D)

theorem twistUp_good {A : Type} [CommGroup A] {t : Twist D A} (g : t.Good) : (twistUp r t).Good :=
  ⟨g.1, g.2, g.3, g.4, g.5, g.6⟩

theorem twistDn_good {A : Type} [CommGroup A] {t : Twist (overD D r) A} (g : t.Good) : (twistDn r t).Good :=
  ⟨g.1, g.2, g.3, g.4, g.5, g.6⟩

theorem baseUp_good {S T : HSp D} {B : Base S T} (g : B.Good) : (baseUp r B).Good := by
  have gd := twistUp_good r g.de
  have v := g.frame.vac.2
  refine ⟨g.even, g.odd, ⟨g.frame.1, g.frame.2, g.frame.3, g.frame.4, g.frame.5, g.frame.6, g.frame.7, g.frame.8, g.frame.vac.1, ?_⟩,
    gd, ⟨g.places.1, g.places.2, g.places.3⟩, ⟨g.wt.1, g.wt.2⟩, g.sig, g.sigOK, g.eta, g.hecke, g.real, g.unram, g.tame, g.inf⟩
  exact ⟨v.1, ⟨v.2.1, v.2.2, v.2.3, v.2.4⟩, v.3, v.4, v.5⟩

theorem baseUp_isWeil {S T : HSp D} {B : Base S T} {ν : (AE D)ˣ →* Circle} {ω : PairRep S T}
    (g : B.IsWeil ν ω) : (baseUp r B).IsWeil (D := overD D r) ν ω := by
  refine ⟨g.1, g.2, g.3, g.4, g.5, fun p f a => ?_, fun x y w f a => g.7 x y w f ⟨a.1, a.2, a.3, a.4⟩,
    fun x hx y hy f a => g.8 x hx y hy f ⟨a.1, a.2, a.3, a.4⟩, fun f a => g.9 f ⟨a.1, a.2, a.3, a.4⟩,
    fun μ F h1 h2 p f a => g.10 μ F h1 h2 p f ⟨a.1, a.2, a.3, a.4⟩, fun e he x y h1 h2 z w h3 h4 => ?_⟩
  · have b := g.6 p f ⟨a.1, a.2, a.3, a.4⟩
    exact ⟨b.1, b.2, b.3, b.4⟩
  · obtain ⟨r0, hr, h5⟩ := g.11 e he x y h1 h2 z w h3 h4
    exact ⟨r0, hr, fun l h6 f a => h5 l (fun u hu f a => h6 u hu f ⟨a.1, a.2, a.3, a.4⟩) f ⟨a.1, a.2, a.3, a.4⟩⟩

theorem baseUp_adm {S T : HSp D} {B : Base S T} {Q : Finset (Pl D.host.E)}
    (g : (baseUp r B).admitted Q) : B.admitted Q :=
  ⟨⟨g.1.1, g.1.2, g.1.3⟩, g.2⟩

theorem baseUp_isClassSystem {S T : HSp D} {B : Base S T} {t : Twist (overD D r) Circle} {I : Type}
    {y : I → GA D S} (g : IsClassSystem S (B.levJ (twistDn r t)) y) :
    IsClassSystem (D := overD D r) S ((baseUp r B).levJ t) y :=
  ⟨g.1, g.2, g.3⟩

theorem baseUp_isBaseFrame {S T : HSp D} (B : Base S T) :
    (Lev.IsBaseFrame S B.F.βS B.F.ΛS 1 → Lev.IsBaseFrame (D := overD D r) S (baseUp r B).F.βS (baseUp r B).F.ΛS 1) ∧
    (Lev.IsBaseFrame T B.F.βT B.F.ΛT 1 → Lev.IsBaseFrame (D := overD D r) T (baseUp r B).F.βT (baseUp r B).F.ΛT 1) ∧
    ((∀ P ∈ B.G.Pg, ∃ k, P ∈ placesOver D.host.E (D.host.g k)) →
      ∀ P ∈ (baseUp r B).G.Pg, ∃ k, P ∈ placesOver (overD D r).host.E ((overD D r).host.g k)) :=
  ⟨id, id, id⟩

theorem cart_onb_over {V : HSp D} {P : D.what₂.Tau → SPar} {P' : (overD D r).what₂.Tau → SPar}
    {M : Mult.DSModel V P} {M' : Mult.DSModel (D := overD D r) V P'} (hm : SameModel M M') :
    HEq (cart M) (cart M') ∧ HEq (onb M) (onb M') := by
  have h1 := hm.ε
  have h2 := hm.fr
  cases M; cases M'
  dsimp only at h1 h2
  subst h1; subst h2
  exact ⟨HEq.rfl, HEq.rfl⟩

theorem chrEq_over {c : (AE D)ˣ →* Circle} {c' : (AE (overD D r))ˣ →* Circle} (hc : HEq c c')
    {χ : Formalism.L2.Host.HChar D.host.E} {χ' : Formalism.L2.Host.HChar (overD D r).host.E} (hχ : HEq χ χ')
    (g : ChrEq (D := D) c χ) : ChrEq (D := overD D r) c' χ' := by
  cases hc; cases hχ
  exact g

end GlobalTheory.TwInputs.Move

end
