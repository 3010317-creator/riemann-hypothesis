module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqZeroOfCobOneEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveModPrimeEqQuasiLogarithmDefect
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Dual.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualEqSmulOfForallDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLieExistsAdditiveEvalModPrimePow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueIsLie
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem lie_surj_mod_p : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E],
    IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
    ∀ l : G.dual.Lie, ∃ (f : MvPowerSeries (Fin d) E) (l' l'' : G.dual.Lie),
      QL c.μ ⊤ f ∧ c.IsLie f l' ∧ l = l' + (p : O) • l'' := by
  intro p _ O E _ _ _ hF G d c l
  obtain ⟨b, z, hbz, hl⟩ := _root_.GlobalTheory.PDivGroup.dual_lie_exists_eval_mod_pow p O G l 1
  rw [pow_one] at hbz
  obtain ⟨f, s, y, hf, hs, hy⟩ := _root_.GlobalTheory.QLog.additive_mod_p_is_defect p O E hF G d c b z hbz
  obtain ⟨l', hl', -⟩ := _root_.GlobalTheory.QLog.Chart.existsUnique_isLie p O E hF G d c f hf
  have hdiv : ∀ w : G.dual.omega, (p : O) ∣ (l - l') w := by
    intro w
    obtain ⟨φ, hφ⟩ := AugCot.d_surjective _ (w.1 1)
    have h1 := hl w φ hφ
    have h2 := hl'.2 1 w φ s hφ (by rw [pow_one]; exact hs)
    rw [pow_one] at h1 h2
    rw [hy, map_add (f := _), map_smul, smul_eq_mul] at h2
    have h3 : (p : O) ∣ l' w - φ b := by
      have := dvd_add h2 (dvd_mul_right (p : O) (φ y))
      rwa [show l' w - (φ b + (p : O) * φ y) + (p : O) * φ y = l' w - φ b by ring] at this
    have := dvd_sub h1 h3
    rwa [show l w - φ b - (l' w - φ b) = (l - l') w by simp] at this
  obtain ⟨l'', hl''⟩ := _root_.GlobalTheory.dual_eq_smul_of_forall_dvd O G.dual.omega (p : O) (fun x hx => hF.sat x hx) (l - l') hdiv
  exact ⟨f, l', l'', hf, hl', by rw [← hl'']; abel⟩

end GlobalTheory.QLog
