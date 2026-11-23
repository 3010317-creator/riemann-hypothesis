module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompact
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerate
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtension
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Mathlib.Probability.Kernel.Defs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureOrthogonalSum
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DetAdmA
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
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF

theorem lintegral_fibSF_of_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∀ S ∈ (BsetF R σ B₀ : Set (HermR R σ (n + 1))), ∫⁻ v, φ v ∂(fibSF σ J t m₁ m' s B₀ a κ₁ cm S) = (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) * (cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : ℝ≥0∞) ^ n * Pint σ J t m₁ m' s φ ((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) : R) (cvec R t a (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) (schur R σ t a S) := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D φ hφ S hS
  obtain ⟨hTR, hLC, hSC, hT2, -⟩ := D.hR
  have := hTR
  have := hLC
  have := hSC
  have := hT2
  have hJ' := _root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.isHermND_blockOne_algebraMap F E σ M J D.hJ t D.ht
  obtain ⟨hKR, hKLC, hKSC, hKT2, -, -, -, hKB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ D.hCM R
  have := hKR
  have := hKLC
  have := hKSC
  have := hKT2
  obtain ⟨-, -, hHSC, -, hHB, hact⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ D.hCM (M + 1) _ hJ' R
  have := hHSC
  have := hHB
  have := hKB (n + 1) (M + 1)
  have k₁ := (_root_.GlobalTheory.CompanionTheory.SW.PiLocalization₂.gramFib_basic F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁).2.1
  have k' := (_root_.GlobalTheory.CompanionTheory.SW.StageF.gramFibFree_basic F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm').1
  have hact' := (hact (n + 1)).1
  have := k₁ (hermScal R σ (algebraMap F R t))
  have := k' (schur R σ t a S)
  have hvec : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E),
      Measurable (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X) := by
    intro A c
    refine Measurable.of_eval (fun i => ?_)
    induction i using Fin.cases with
    | zero =>
      have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X 0) =
          fun _ => Fin.cons A (fun _ => 0) := rfl
      rw [h0]
      exact measurable_const
    | succ j =>
      refine Measurable.of_eval (fun k => ?_)
      induction k using Fin.cases with
      | zero =>
        have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X j.succ 0) = fun _ => c j := rfl
        rw [h0]
        exact measurable_const
      | succ l =>
        have h0 : (fun X : Fin n → Fin M → R ⊗[F] E => vec A c X j.succ l.succ) =
            fun X => X j l := rfl
        rw [h0]
        exact (measurable_pi_apply l).comp (measurable_pi_apply j)
  have hf : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E), Measurable (fun p :
      (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec A c p.2)) := fun A c =>
    hact'.measurable.comp ((D.hs.comp measurable_fst).prodMk ((hvec A c).comp measurable_snd))
  have hg : ∀ (A : R ⊗[F] E) (c : Fin n → R ⊗[F] E), Measurable (fun p :
      (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
        φ (actW R σ (blockOne (algebraMap F E t) J) (s p.1) (vec A c p.2))) := fun A c =>
    hφ.comp (hf A c)
  have hfib := Set.indicator_of_mem hS (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2)))
  have hfib' : fibSF σ J t m₁ m' s B₀ a κ₁ cm S = _ := hfib
  rw [hfib', lintegral_smul_measure, lintegral_map hφ (hf _ _),
    lintegral_prod _ (hg _ _).aemeasurable, ENNReal.smul_def, smul_eq_mul]
  push_cast
  rfl

end GlobalTheory.CompanionTheory.SW.StageF
