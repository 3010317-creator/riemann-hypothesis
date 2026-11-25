module

public import Formalism.SharpRestriction.GrowthBounds.FormalGroupSystem
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Monotonicity.Lemmas
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
import Mathlib.Topology.Sheaves.Presheaf

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.BasicNotions Finset

variable {D : Formalism.BasicNotions.D7} {L : SizeData₂ D}

def nc_ya (_X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D)
    (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) : ℝ :=
  Formalism.MainNotions.G.al L (Formalism.MainNotions.G.aL L) (t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w))

def nc_zc (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ)
    (s : Fin ((D.gat u w hg).P.n' (Y.vOf u w hg t0))) : ℝ :=
  Formalism.MainNotions.G.fillG X (Formalism.MainNotions.G.bL L) j (false, t0 + s.val • Formalism.MainNotions.G.hP D (D.what₂.places.resChar w)) + Formalism.MainNotions.G.cG L


open Classical in
def nc_Loc (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts)
    (_hT : GatTies D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ) : Prop :=
  let p := D.what₂.places.resChar w
  let v := Y.vOf u w hg t0
  let Fl := Y.Fl u w hg
  Formalism.MainNotions.G.gU X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) p j t0 =
            Formalism.MainNotions.FormalGroupSystem.gam p * ∑ s ∈ Fl.TT v, nc_ya X Y u w hg t0 s -
              ∑ s ∈ (Fl.TT v).filter IsOddPos, ∑' e : ℕ,
                min (nc_ya X Y u w hg t0 s / ((p : ℝ)) ^ (2 * e + 1)) (nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1))) -
              Formalism.MainNotions.G.dl X K p t0 ∧
  Formalism.MainNotions.G.g0 X K (Formalism.MainNotions.G.aL L) (Formalism.MainNotions.G.bL L) p j t0 =
            ∑ s ∈ Fl.TT v, ∑' e : ℕ, (if Formalism.MainNotions.G.Excl D p (t0 + s.val • Formalism.MainNotions.G.hP D p) (2 * e + 1) then 0 else
              max 0 (nc_ya X Y u w hg t0 s / ((p : ℝ)) ^ (2 * e + 1) - nc_zc X Y u w hg t0 j (Formalism.MainNotions.G.posAdd s (2 * e + 1)))) -
              Formalism.MainNotions.G.dl X K p t0 ∧
  (∀ s ∈ Fl.TT v, nc_ya X Y u w hg t0 s ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
  (∀ s, 0 ≤ al (Fl.TT v) ((D.gat u w hg).P.lam0 v) s) ∧
  (∀ s, (cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s : ℝ) ≤ nc_zc X Y u w hg t0 j s) ∧
  (∀ s, 0 ≤ cap Fl.t (Fl.TT v) ((D.gat u w hg).P.lam0 v) (Fl.w v) j s) ∧
  (∀ s ∈ Fl.TT v, ∀ e, 2 * e + 1 ∈ dSet (Fl.TT v) s → Formalism.MainNotions.G.Excl D p (t0 + s.val • Formalism.MainNotions.G.hP D p) (2 * e + 1))

def nc_De (D : Formalism.BasicNotions.D7) (L : SizeData₂ D) (X : Formalism.MainNotions.G.Inst D L) (Y : Formalism.MainNotions.G.LatInst D) (K : Formalism.MainNotions.G.Consts)
    (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : Formalism.MainNotions.G.HH D) (j : ℕ) : Prop :=
  de (D.what₂.places.resChar w) (Y.Fl u w hg).t ((Y.Fl u w hg).TT (Y.vOf u w hg t0))
      ((D.gat u w hg).P.lam0 (Y.vOf u w hg t0)) ((Y.Fl u w hg).w (Y.vOf u w hg t0)) j ≤
    Formalism.MainNotions.G.dl X K (D.what₂.places.resChar w) t0

end Formalism.MainNotions.FormalGroupSystem.Pf
