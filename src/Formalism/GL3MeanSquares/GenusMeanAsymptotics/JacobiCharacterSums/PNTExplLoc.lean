module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Formalism.ZeroFreeRegion.FinalZFR
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.ExistsLocalZeroExpansionOfBound

@[expose] public section

noncomputable section

namespace Formalism.HermitianLattices.Ext.PrimesInProgressions

open Formalism.ZeroFreeDirichlet

theorem ex_landau_ord_core (f : ℂ → ℂ) (z₀ : ℂ) (r B : ℝ) (hr : 0 < r) (hB : 1 ≤ B)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ r)) (hfz₀ : f z₀ ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ B * ‖f z₀‖) :
    ∃ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ m ρ) ∧
      (∀ ρ ∈ Z, analyticOrderNatAt f ρ = m ρ) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ Real.log B / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log B / r := by
  obtain ⟨Z, m, hZ, hm, horder, hsum, hest⟩ :=
    exists_localZeroExpansion_with_order f z₀ r B hr hB hf hfz₀ hbound
  exact ⟨Z, m, hZ, hm, fun ρ hρ => by simp [analyticOrderNatAt, horder ρ hρ], hsum, hest⟩

theorem ex_landau_ord (f : ℂ → ℂ) (z₀ : ℂ) (r B : ℝ) (hr : 0 < r) (hB : 1 ≤ B)
    (hf : DifferentiableOn ℂ f (Metric.closedBall z₀ r)) (hfz₀ : f z₀ ≠ 0)
    (hbound : ∀ z ∈ Metric.closedBall z₀ r, ‖f z‖ ≤ B * ‖f z₀‖) :
    ∃ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ Metric.closedBall z₀ (r / 3) ∧ f ρ = 0)) ∧
      (∀ ρ ∈ Z, 1 ≤ analyticOrderNatAt f ρ) ∧
      ((∑ ρ ∈ Z, analyticOrderNatAt f ρ : ℕ) : ℝ) ≤ Real.log B / Real.log 2 ∧
      ∀ z ∈ Metric.closedBall z₀ (r / 6), f z ≠ 0 →
        ‖deriv f z / f z - ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ)‖ ≤ 72 * Real.log B / r := by
  obtain ⟨Z, m, hZ, hm1, hmo, hcnt, hest⟩ := ex_landau_ord_core f z₀ r B hr hB hf hfz₀ hbound
  have hsum : ∀ z : ℂ, ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (z - ρ) =
      ∑ ρ ∈ Z, (m ρ : ℂ) / (z - ρ) :=
    fun z => Finset.sum_congr rfl (fun ρ hρ => by rw [hmo ρ hρ])
  refine ⟨Z, hZ, fun ρ hρ => by rw [hmo ρ hρ]; exact hm1 ρ hρ, ?_, ?_⟩
  · rw [Finset.sum_congr rfl hmo]
    exact hcnt
  · intro z hz hfz
    rw [hsum z]
    exact hest z hz hfz

end Formalism.HermitianLattices.Ext.PrimesInProgressions
