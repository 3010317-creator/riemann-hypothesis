module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFrameEntryRelationStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselLieTriangularVanishingStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalueStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DualTensorCayleyCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameWConjMatrixUnitsStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProjectorEntryValueUnderLinearFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmoothVectorsDiscreteSeriesGlModuleStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SplitCasimirEigenvalueOnDualTensorSummandStatement
import Formalism.FormalDegreeBessel.FormalDegreeRatio.GBasic
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

namespace BesselProjectorValue

lemma star_Hpk (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    star (Formalism.QuantumDeterminants.Hpk k r i j) = Formalism.QuantumDeterminants.Hpk k r i j := by
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> simp

lemma ev_flat {k r : ℕ} (R : Rep k r) (f : Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1) → R.H) :
    ev (Formalism.QuantumDeterminants.Hpk k r) R (flat k r f) x = ∑ j, f j • x j := by
  unfold ev
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have h1 : ∀ i, star (flat k r f i) = ∑ p, f p * Formalism.QuantumDeterminants.Hpk k r p i := by
    intro i
    simp [flat, Formalism.QuantumDeterminants.herm, dotProduct, Matrix.mulVec_single_one, Matrix.col, star_Hpk]
  simp only [h1, Finset.sum_mul]
  rw [Finset.sum_comm]
  have h2 : ∀ p, ∑ i, f p * Formalism.QuantumDeterminants.Hpk k r p i * Formalism.QuantumDeterminants.Hpk k r i j = f p * (1 : Mx k r) p j := by
    intro p
    rw [← Formalism.QuantumDeterminants.GBasic.Hpk_sq k r, Matrix.mul_apply, Finset.mul_sum]
    simp only [mul_assoc]
  simp only [h2, Matrix.one_apply]
  simp

lemma sum_frame {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g)
    (f : Fin n → ℂ) (x : Fin n → V) :
    ∑ j, f j • x j = ∑ d, (g⁻¹ *ᵥ f) d • ∑ c, g c d • x c := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  have : (g *ᵥ (g⁻¹ *ᵥ f)) j = f j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd, Matrix.one_mulVec]
  rw [← this]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun d _ => mul_comm _ _

lemma sum_coframe {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (g : Matrix (Fin n) (Fin n) ℂ) (hg : IsUnit g)
    (ω : Fin n → ℂ) (v : V) (c : Fin n) :
    ∑ d, g⁻¹ d c • ((gᵀ *ᵥ ω) d • v) = ω c • v := by
  have hd : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det g).1 hg
  simp only [smul_smul]
  rw [← Finset.sum_smul]
  congr 1
  have : ((g⁻¹)ᵀ *ᵥ (gᵀ *ᵥ ω)) c = ω c := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.transpose_one,
      Matrix.one_mulVec]
  rw [← this]
  rfl

end BesselProjectorValue

end GlobalTheory
