module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EquivariantPhiModuleMatrixMemOE
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAinfLiftPeriodPowSmulIntertwiner
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrobeniusPeriod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowerSeriesLiftOfPeriodPowSmulIntegralMatr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratPeriodMatrixExistsFixedFrobeniusSolution
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

theorem GlobalTheory.BSP.equivariant_matrix_over_bk : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ) (S : Strat bk d) (S' : Strat bk d') (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (ρ' : ↥(GK K) → Matrix (Fin d') (Fin d') ℤ_[l]) (T : Matrix (Fin d) (Fin d) (WCb l)) (T' : Matrix (Fin d') (Fin d') (WCb l)), MReal S ρ T → MReal S' ρ' T' → ∀ f : Matrix (Fin d') (Fin d) ℤ_[l], (∀ g, f * ρ g = ρ' g * f) → ∃ Y : Matrix (Fin d') (Fin d) bk.S, T' * Y.map bk.evW = zW f * T := by
  intro l _ K bk d d' S S' ρ ρ' T T' hT hT' f hf
  obtain ⟨X, hX, hfix, hphi⟩ := _root_.GlobalTheory.BSP.MReal.exists_fixed_frob l K bk d d' S S' ρ ρ' T T' hT hT' f hf
  have hOE := _root_.GlobalTheory.BSP.EquivOE.main l K bk d d' S S' X hfix hphi
  obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.BSP.exists_isPer l K bk
  obtain ⟨M, x, hx⟩ := _root_.GlobalTheory.BSP.PoleBound.exists_pow_smul l K bk τ hτ d d' S S' ρ ρ' T T' hT hT' f X hX
  obtain ⟨Y, hY⟩ := _root_.GlobalTheory.BSP.KisinFF.main l K bk τ hτ d d' M X x hOE hx
  exact ⟨Y, by rw [hY]; exact hX⟩
