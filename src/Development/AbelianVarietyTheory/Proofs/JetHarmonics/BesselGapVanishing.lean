module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GrowthUnitaryGroupRpowNegIntegrable
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UhMeasurableSet
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PolynomialProperness.ZhatNormLinearBound
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.HaarCompactGrowth.GrowthSphericalBound
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNonneg
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.ReproducingFormulaReduction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SigmaContOn
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.BesselGapVanishing
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselNeZeroOfCyclicOrbit
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.HpkMulMulHpkApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselConv

open Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity

section

variable {k r : ℕ} {H Wp : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem ae_mem_prod {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z ∧ Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Nset k r := by
  have := hW.1; have := hN.1
  have hWae : ∀ᵐ p1 ∂μW, Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z := ae_iff.mpr hW.2.2.1
  have hNae : ∀ᵐ p2 ∂μN, Matrix.of p2 ∈ Formalism.QuantumDeterminants.Nset k r := ae_iff.mpr hN.2.2.1
  exact (Measure.quasiMeasurePreserving_fst.ae hWae).and (Measure.quasiMeasurePreserving_snd.ae hNae)

theorem pi_inv_contOn [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π) :
    ContinuousOn (fun p1 : Formalism.QuantumDeterminants.Mt k r => π (Matrix.of p1)⁻¹)
      {p1 : Formalism.QuantumDeterminants.Mt k r | Matrix.of p1 ∈ Formalism.QuantumDeterminants.UWset k r z} := by
  apply Gp91.GlobalTheory.BesselConv.pi_inv_contOn <;> assumption

theorem beInt_aesm [FiniteDimensional ℂ Wp] {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ}
    {σ : Mx k r → (H →L[ℂ] H)} (hσ : PI.UpqRep.IsDSHpk k r ε lam σ)
    {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (w v : H) :
    AEStronglyMeasurable (beInt z c π σ w v) (μW.prod μN) := by
  apply Gp91.GlobalTheory.BesselConv.beInt_aesm <;> assumption

theorem norm_beInt_le (σ : Mx k r → (H →L[ℂ] H)) {z : Fin (2 * r + k + 1) → ℂ} (c : ℂ) {u : Fin k → ℝ}
    {π : Mx k r → (Wp →L[ℂ] Wp)} (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hπ : PI.UpqRep.IsHCTypeW k r z u π)
    (w v : H) (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (hp : Matrix.of p.1 ∈ Formalism.QuantumDeterminants.UWset k r z) :
    ‖beInt z c π σ w v p‖ ≤ ‖⟪v, σ (Matrix.of p.1 * Matrix.of p.2) w⟫_ℂ‖ := by
  have h1 : ‖π (Matrix.of p.1)⁻¹‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ξ => by
      rw [piW_unitary hT hπ _ (uw_inv hp).1 ξ, one_mul]
  unfold beInt
  rw [norm_smul, norm_mul, norm_star, psi_norm, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) h1

end

end GlobalTheory.BesselConv
