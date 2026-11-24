module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselCharacterUnipotentRadicalPropertiesStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselPeriodAdjointPair
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupParameterMeasurePreservingStatement
public import Formalism.HermitianCurvature.BesselNonvanishingReduction
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecayThresholdsOfSpectralGapCondition
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.LUFactorOrbitBounds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DiscreteSeriesUnitarySmoothBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
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

namespace GlobalTheory

theorem besselInner_haar {k r : ℕ} {U : Set (Mx k r)} {μ : Measure (Formalism.QuantumDeterminants.Mt k r)} (h : B.IsHaarOn U μ) :
    PI.BesselPeriodGGP.IsHaarOn U μ :=
  ⟨Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite h, h.ne_zero, h.conc, h.left⟩

theorem besselInner_integral {k r : ℕ} (R : Rep k r) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [CompleteSpace Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
    (D : B.RealPlaceData k r Wp Wq)
    (hmul : ∀ g ∈ GG k r, ∀ h ∈ GG k r, ∀ v, R.σ (g * h) v = R.σ g (R.σ h v))
    (huni : ∀ g ∈ GG k r, ∀ v w, ⟪R.σ g v, R.σ g w⟫_ℂ = ⟪v, w⟫_ℂ)
    {γ : Mx k r} (hγ : γ ∈ GG k r) (x y : R.H) (X : Wq →L[ℂ] Wp)
    (a : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) (ha1 : Matrix.of a.1 ∈ GG k r) (ha2 : Matrix.of a.2 ∈ GG k r)
    (hint : Integrable (beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x))
      (D.μW'.prod D.μN)) :
    ∫ b, JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ (a, b) ∂(D.μW'.prod D.μN) =
      Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) • (D.π (Matrix.of a.1)).comp (X.comp
        (be D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ D.μW' D.μN y (R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x))) := by
  obtain ⟨-, -, -, hT, -, hae⟩ := GlobalTheory.T.besselSubgroup_parameter_measurePreserving k r D.z' D.μW' D.μN D.k_pos D.z'_mem D.T'_pos
    (besselInner_haar D.haarW') (besselInner_haar D.haarN)
  obtain ⟨-, -, -, hconj, hW, hN⟩ := GlobalTheory.T.besselCharacter_unipotentRadical_properties k r D.z' Formalism.QuantumDeterminants.cStd D.z'_mem
  set v := R.σ (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) x with hv
  set G := beInt D.z' Formalism.QuantumDeterminants.cStd D.π' R.σ y v with hG
  set T : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r → Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r := fun p =>
    ((fun i j => (Matrix.of p.1 : Mx k r) i j),
      (fun i j => ((Matrix.of p.1)⁻¹ * Matrix.of p.2 * Matrix.of p.1 : Mx k r) i j)) with hTdef
  let L : (Wq →L[ℂ] Wq) →L[ℂ] (Wq →L[ℂ] Wp) :=
    Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) •
      ContinuousLinearMap.compL ℂ Wq Wq Wp ((D.π (Matrix.of a.1)).comp X)
  have hL : ∀ A, L A = Formalism.QuantumDeterminants.psi k r D.z Formalism.QuantumDeterminants.cStd (Matrix.of a.2) •
      (D.π (Matrix.of a.1)).comp (X.comp A) := fun A => rfl
  have key : (fun b => JF.integrand D (fun g => ⟪x, R.σ g y⟫_ℂ • X) γ (a, b)) =ᵐ[D.μW'.prod D.μN]
      fun b => L (G (T b)) := by
    filter_upwards [hae] with b hb
    obtain ⟨hb1, hb2⟩ := hb
    have hb1G : Matrix.of b.1 ∈ GG k r := (hW _ hb1 _ hb1).2.2
    have hb2G : Matrix.of b.2 ∈ GG k r := hN _ hb2
    have u1 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh ha1
    have u2 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh ha2
    have u3 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hγ
    have u4 := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hb1G
    have hg0 : γ⁻¹ * Matrix.of a.2 * Matrix.of a.1 ∈ GG k r :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv hγ) ha2) ha1
    have hs : B.sgs (a, b) γ ∈ GG k r :=
      Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul (Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul
        (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha1) (Formalism.QuantumDeterminants.WeylGroupFacts.uh_inv ha2)) hγ) hb2G) hb1G
    have e1 : (γ⁻¹ * Matrix.of a.2 * Matrix.of a.1) * B.sgs (a, b) γ =
        Matrix.of b.1 * ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1) := by
      simp only [B.sgs, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ u1,
        Matrix.mul_nonsing_inv_cancel_left _ _ u2, Matrix.mul_nonsing_inv_cancel_left _ _ u4,
        Matrix.nonsing_inv_mul_cancel_left _ _ u3]
    have e2 : ⟪x, R.σ (B.sgs (a, b) γ) y⟫_ℂ =
        ⟪v, R.σ (Matrix.of b.1 * ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1)) y⟫_ℂ := by
      rw [← e1, hmul _ hg0 _ hs, hv, huni _ hg0]
    have e3 := (hconj _ hb1 _ hb2).2.2.2
    have e4 : G (T b) = (⟪v, R.σ (Matrix.of b.1 * ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1)) y⟫_ℂ *
        star (Formalism.QuantumDeterminants.psi k r D.z' Formalism.QuantumDeterminants.cStd ((Matrix.of b.1)⁻¹ * Matrix.of b.2 * Matrix.of b.1))) •
        D.π' (Matrix.of b.1)⁻¹ := rfl
    rw [hL, e4, e3, ← e2]
    ext w
    simp only [JF.integrand, JF.xiP, B.rho, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      map_smul, smul_smul]
    congr 1
    ring
  have hGT : Integrable (fun b => G (T b)) (D.μW'.prod D.μN) := hT.integrable_comp_of_integrable hint
  rw [integral_congr_ae key, L.integral_comp_comm hGT, ← hL]
  congr 1
  have h2 := integral_map hT.aemeasurable (f := G) (by rw [hT.map_eq]; exact hint.aestronglyMeasurable)
  rw [hT.map_eq] at h2
  exact h2.symm

end GlobalTheory
