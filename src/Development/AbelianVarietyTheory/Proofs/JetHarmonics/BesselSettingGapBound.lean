module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreservingStatement
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayThresholdsOfSpectralGapCondition
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsHaarOnIffGroupsUnitaryUnipotentStatement
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
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
import Mathlib.Tactic.Linter.HaveILetI
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

noncomputable section

namespace GlobalTheory.BesselFirstLeft

theorem sigmaFinite_of_haar {k r : ℕ} {U : Set (B.Mat k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (h : B.IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun {K} hK => h.finite_compact K hK⟩
  infer_instance

theorem left_integral {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp))
    (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (l : R.H → Wp) (hk : 1 ≤ k) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) (hW : B.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW)
    (hN : B.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) (hl : IsBeL R z π μW μN l)
    {Y x : R.H} (hY : Y ∈ R.sm) (hx : x ∈ R.TK) :
    Integrable (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1)) (μW.prod μN) ∧
    ∫ p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r,
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1) ∂(μW.prod μN) =
      (innerSL ℂ (l x)).smulRight (l Y) := by
  obtain ⟨-, -, -, -, hinv, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r z μW μN hk hz hT
    (((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μW).2.2 z hz hT hk).2 hW) ((GlobalTheory.T.isHaarOn_iff_groups_unitary_unipotent k r μN).2.1.2 hN)
  obtain ⟨-, -, hψ, -, hU, -⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r z Formalism.QuantumDeterminants.cStd hz
  obtain ⟨hint, hbe⟩ := hl.2 Y hY x hx
  set φ := (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (((fun i j => ((Matrix.of p.1)⁻¹ : Mx k r) i j), (fun i j => ((Matrix.of p.2)⁻¹ : Mx k r) i j)) : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r)) with hφ
  have heq : (fun p => beInt z Formalism.QuantumDeterminants.cStd π R.σ Y x (φ p)) =ᵐ[μW.prod μN]
      (fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r =>
      (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2) *
        ⟪x, R.σ ((Matrix.of p.1)⁻¹ * (Matrix.of p.2)⁻¹) Y⟫_ℂ) • π (Matrix.of p.1)) := by
    filter_upwards [hae] with p hp
    have h1 : ((Matrix.of p.1 : Mx k r)⁻¹)⁻¹ = Matrix.of p.1 :=
      Matrix.nonsing_inv_nonsing_inv _ (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit (hU _ hp.1 _ hp.1).2.2)
    have h2 := (hψ _ hp.2).2
    change (⟪x, R.σ ((Matrix.of p.1 : Mx k r)⁻¹ * (Matrix.of p.2 : Mx k r)⁻¹) Y⟫_ℂ *
      star (Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (Matrix.of p.2 : Mx k r)⁻¹)) • π ((Matrix.of p.1 : Mx k r)⁻¹)⁻¹ = _
    rw [h1, h2, star_star, mul_comm]
  refine ⟨((hinv.integrable_comp hint.aestronglyMeasurable).2 hint).congr heq, ?_⟩
  rw [← integral_congr_ae heq, ← hbe, be]
  have := integral_map hinv.aemeasurable (f := beInt z Formalism.QuantumDeterminants.cStd π R.σ Y x)
    (by rw [hinv.map_eq]; exact hint.aestronglyMeasurable)
  rw [hinv.map_eq] at this
  exact this.symm

end GlobalTheory.BesselFirstLeft
