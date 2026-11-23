module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsClassSystem
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

theorem val_move {T T' : Type} {n n' : ℕ} (hT : T = T') (hn : n = n') {a : T → GL (Fin n) ℂ} {a' : T' → GL (Fin n') ℂ}
    {c : T → Matrix (Fin n) (Fin n) ℂ} {c' : T' → Matrix (Fin n') (Fin n') ℂ} (ha : HEq a a') (hc : HEq c c')
    (g : ∀ τ, (a τ).val = c τ) (τ : T') : (a' τ).val = c' τ := by
  subst hT hn ha hc
  exact g τ

theorem grp_move {R R' : Ranks} {H : Host R} {H' : Host R'} {L L' : Fin 2 → Type} (hR : R = R') (hH : HEq H H') (hL : L = L')
    {r r' : ℕ} (e : r = R.r) (e' : r' = R'.r) {A B : Finset (Pl H.E)} {A' B' : Finset (Pl H'.E)} (hA : HEq A A') (hB : HEq B B')
    {u : (∀ kv : (Σ k : Fin 2, L k), GL (Fin R.r) (ZMod (H.g kv.1))) ≃* G0 A r}
    {u' : (∀ kv : (Σ k : Fin 2, L' k), GL (Fin R'.r) (ZMod (H'.g kv.1))) ≃* G0 A' r'} (hu : HEq u u')
    {c : G0 B R.r ≃* ∀ kv : (Σ k : Fin 2, L k), GL (Fin R.r) (ZMod (H.g kv.1))}
    {c' : G0 B' R'.r ≃* ∀ kv : (Σ k : Fin 2, L' k), GL (Fin R'.r) (ZMod (H'.g kv.1))} (hc : HEq c c')
    (g : ∀ x P (h : P ∈ A) (h' : P ∈ B) (a b : Fin r), (u x ⟨P, h⟩).val a b = (c.symm x ⟨P, h'⟩).val (Fin.cast e a) (Fin.cast e b)) :
    ∀ x P (h : P ∈ A') (h' : P ∈ B') (a b : Fin r'),
      (u' x ⟨P, h⟩).val a b = (c'.symm x ⟨P, h'⟩).val (Fin.cast e' a) (Fin.cast e' b) := by
  subst hR; subst hH; subst hL e e' hA hB hu hc
  exact g

theorem setupUp_good {D : D7} (r : Rest D) {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0}
    (h : CopyTw D (overD D r) ι e) {ρ : Setup D.ntw} (g : ρ.Good) : (setupUp r ρ).Good := by
  have grc : (setupUp r ρ).rc.Good := ⟨g.rc.1, g.rc.2, g.rc.3, g.rc.4⟩
  refine ⟨grc, fun i => ⟨(g.ch i).1, (g.ch i).2⟩, g.bad_ne, g.goodSetup_bad_mem_badPlaces,
    g.goodSetup_badPlaces_conj, g.goodSetup_placesOverTwo_subset, g.goodSetup_count_eq_zero_off_badPlaces,
    fun i b x' => ?_, g.ek_e,
    fun i j b => baseUp_good r (g.base i j b),
    fun i j b => (baseUp_isBaseFrame r (ρ.B i j b)).1 (g.latS i j b),
    fun i j b => (baseUp_isBaseFrame r (ρ.B i j b)).2.1 (g.latT i j b),
    fun i j b => (baseUp_isBaseFrame r (ρ.B i j b)).2.2 (g.Pg i j b),
    fun i j b => ?_, fun i j b t ht => ?_, fun i j b t ht ha => ?_⟩
  · have h3 := eq_of_heq (h.sideEmb_heq (i := i) (i' := i) .rfl b x')
    have h4 := h.embLL0_eq x'
    exact (congrArg (ρ.e i b) h3.symm).trans ((g.e_LL0 i b (e x')).trans h4)
  · apply SameTwist.eq
    dsimp only [setupUp, baseUp]
    rw [g.delta i j b]
    exact ⟨.rfl, .rfl, .rfl⟩
  · exact baseUp_isWeil r (g.weil i j b (twistDn r t) (twistDn_good r ht))
  · exact baseUp_isClassSystem r (g.classes i j b (twistDn r t) (twistDn_good r ht) (baseUp_adm r ha))

theorem setupUp_realPin {D : D7} (r : Rest D) {ι : D.what₂.LL →+* (overD D r).what₂.LL} {e : ↥(overD D r).LL0 ≃+* ↥D.LL0}
    (_h : CopyTw D (overD D r) ι e) {X : RealSide D} {X' : RealSide (overD D r)} (m : RealMove X X' ι)
    {ρ : Setup D.ntw} (p : RealPin X.R X.cG ρ) : RealPin X'.R X'.cG (setupUp r ρ) := by
  have chain : ∀ {A A' : Type} {a c : A} {a' c' : A'}, HEq a a' → a = c → HEq c c' → a' = c' :=
    fun h1 h2 h3 => eq_of_heq (h1.symm.trans ((heq_of_eq h2).trans h3))
  constructor
  case deltaPl =>
    intro i t' P' h1 h2
    obtain ⟨t, P, h3, h4⟩ := m.Q i t' P' h1 h2
    cases h4
    exact p.deltaPl i t _ h3 h2
  all_goals
    intro i j b
    have q := sameBase_up r (ρ.B i j b)
    have hMW := cart_onb_over r (m.MW j j rfl)
  · exact chain q.ψ (p.psi i j b) m.ψ
  · exact chain q.θ (p.inf i j b) m.θ
  · exact chain q.sT (p.cartT i j b) hMW.1
  · exact val_move rfl rfl q.BS (m.BV j j rfl) (p.onbS i j b)
  · exact chain q.BT (p.onbT i j b) hMW.2
  · exact chain q.ΛS (p.latS i j b) (m.ΛV j j rfl)
  · exact chain q.ΛT (p.latT i j b) (m.ΛW j j rfl)
  · exact chain q.βS (p.frS i j b) (m.βV j j rfl)
  · exact chain q.βT (p.frT i j b) (m.βW j j rfl)
  · exact chain q.f₀ (p.vac i j b) (m.vacP j j rfl)
  · exact chain q.Pg (p.Pg i j b) m.Pg
  · exact grp_move rfl .rfl rfl (FWT.rank_Wc j) (FWT.rank_Wc (D := overD D r) j) q.Pg m.Pg .rfl m.cG (p.grp i j b)
  · exact chain q.mu0 (p.mu0 i j b) (m.mu0 j)
  · exact chain q.eta (p.eta i j b) m.eta
  · exact chrEq_over r q.de.chi (m.delAt _) (p.delta i j b)
  · exact congrFun (chain q.ap (funext (p.ap i j b)) .rfl)
  · exact congrFun (chain q.am (funext (p.am i j b)) .rfl)

theorem setup_move_data : ∀ {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}, CopyTw D D' ι e → ∀ {X : RealSide D} {X' : RealSide D'}, RealMove X X' ι → ∀ (ρ : Setup D.ntw), ρ.Good → RealPin X.R X.cG ρ →
    ∃ ρ' : Setup D'.ntw, SameData ρ ρ' ∧ ρ'.Good ∧ RealPin X'.R X'.cG ρ' := by
  intro D D' ι e h X X' m ρ g p
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact ⟨setupUp r ρ, sameData_up r ρ, setupUp_good r h g, setupUp_realPin r h m p⟩

end GlobalTheory.TwInputs.Move

end
