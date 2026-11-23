module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSupportCompactInvarianceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartitionOfUnitySupportStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.ArchPure

open Matrix

variable {F : Type} [Field F] [NumberField F]

def mk (a : Ainf F) (b : Af F) : AF F := (a, b)

theorem evI_fin (b : Af F) : evI F (((0 : Ainf F), b) : AF F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F 0 = 0
  exact map_zero _

theorem snd_of_at {z : AF F} (hz : At (evI F) z) : z.2 = 0 := by
  have h := hz (((0 : Ainf F), (1 : Af F)) : AF F) (evI_fin 1)
  have h2 : (1 : Af F) * z.2 = 0 := congrArg Prod.snd h
  rwa [one_mul] at h2

theorem slice {κ : Type} [Fintype κ] (c : κ → Af F) :
    ∀ Ψ ∈ schA F κ, ∃ f' : SInf F κ, ∀ s : κ → mixedEmbedding.mixedSpace F,
      Ψ (fun i => mk ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (s i)) (c i)) = f' s := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, -, rfl⟩ := hx
    refine ⟨g c • f, fun s => ?_⟩
    simp only [pureA, mk, RingEquiv.apply_symm_apply, SchwartzMap.smul_apply, smul_eq_mul,
      mul_comm]
  | zero => exact ⟨0, fun s => rfl⟩
  | add x y _ _ hx hy =>
    obtain ⟨f1, h1⟩ := hx
    obtain ⟨f2, h2⟩ := hy
    exact ⟨f1 + f2, fun s => by rw [Pi.add_apply, h1, h2, SchwartzMap.add_apply]⟩
  | smul a x _ hx =>
    obtain ⟨f1, h1⟩ := hx
    exact ⟨a • f1, fun s => by rw [Pi.smul_apply, h1, SchwartzMap.smul_apply]⟩

theorem locA : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ GlobalTheory.WeilM.schA F κ,
    ∃ (C K : Set (κ → Af F)), IsCompact C ∧ IsOpen K ∧ (0 : κ → Af F) ∈ K ∧
      (∀ x : κ → AF F, Φ x ≠ 0 → (fun i => (x i).2) ∈ C) ∧
      ∀ x x' : κ → AF F, (∀ i, (x i).1 = (x' i).1) → (fun i => (x' i).2 - (x i).2) ∈ K → Φ x' = Φ x := GlobalTheory.T.adelic_schwartz_support_compact_invariance

theorem locB : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ (C K : Set (κ → Af F)), IsCompact C → IsOpen K → (0 : κ → Af F) ∈ K →
    ∀ y : κ → AF F, ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ b ∈ s, ∀ i, (b i).1 = 0) ∧
      ∑ b ∈ s, c b * ψ (y ⬝ᵥ b) = 1 ∧
      ∀ x : κ → AF F, (fun i => (x i).2) ∈ C → (∀ k ∈ K, (fun i => (x i).2) ≠ (fun i => (y i).2) + k) →
        ∑ b ∈ s, c b * ψ (x ⬝ᵥ b) = 0 := GlobalTheory.T.character_partition_of_unity_support

theorem fibre : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (T : Module.End ℂ ((κ → AF F) → ℂ)), IsStd ψ → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) →
    (∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) → T Φ y = 0 := by
  intro F _ _ κ _ ψ T hψ hkeep hcomm Φ hΦ y hy
  obtain ⟨C, K, hC, hK, hK0, hsupp, hinv⟩ := locA Φ hΦ
  obtain ⟨s, c, hs, hy1, hm⟩ := locB ψ hψ C K hC hK hK0 y
  have hu0 : evI F (mk 0 1) = 0 := evI_fin 1
  have hub : ∀ b ∈ s, (mk 0 1 : AF F) • b = b := fun b hb => funext fun i =>
    Prod.ext (show (0 : Ainf F) * (b i).1 = (b i).1 by rw [zero_mul, hs b hb i])
      (show (1 : Af F) * (b i).2 = (b i).2 from one_mul _)
  have hsch : ∀ (b : κ → AF F) (Ψ : (κ → AF F) → ℂ), schr ψ (0, b) Ψ = fun x => ψ (x ⬝ᵥ b) * Ψ x :=
    fun b Ψ => funext fun x => by simp [schr]
  have hfac : ∀ (Ψ : (κ → AF F) → ℂ) x, (∑ b ∈ s, c b • schr ψ (0, b) Ψ) x = (∑ b ∈ s, c b * ψ (x ⬝ᵥ b)) * Ψ x := by
    intro Ψ x
    rw [Finset.sum_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Pi.smul_apply, hsch, smul_eq_mul]
    ring
  have hzero : (∑ b ∈ s, c b • schr ψ (0, b) Φ) = 0 := by
    funext x
    rw [hfac, Pi.zero_apply]
    by_cases hx : Φ x = 0
    · rw [hx, mul_zero]
    · refine mul_eq_zero_of_left (hm x (hsupp x hx) fun k hk he => hx ?_) _
      have hk' : (fun i => (x i).2 - (y i).2) = k := funext fun i => by
        rw [congrFun he i, Pi.add_apply]
        abel
      have e1 : Φ x = Φ (fun i => mk (x i).1 (y i).2) := hinv _ _ (fun i => rfl) (by rw [← hk'] at hk; exact hk)
      rw [e1]
      have hz : At (evI F) (fun i => mk ((x i).1 - (y i).1) (0 : Af F)) := by
        intro u' hu'
        have h1 : u'.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp hu'
        funext i
        exact Prod.ext (show u'.1 * ((x i).1 - (y i).1) = 0 by rw [h1, zero_mul])
          (show u'.2 * (0 : Af F) = 0 from mul_zero _)
      have e2 := hy _ hz
      have e3 : y + (fun i => mk ((x i).1 - (y i).1) (0 : Af F)) = fun i => mk (x i).1 (y i).2 := by
        funext i
        exact Prod.ext (show (y i).1 + ((x i).1 - (y i).1) = (x i).1 by abel)
          (show (y i).2 + 0 = (y i).2 from add_zero _)
      rwa [e3] at e2
  have hT : T (∑ b ∈ s, c b • schr ψ (0, b) Φ) = ∑ b ∈ s, c b • schr ψ (0, b) (T Φ) := by

    rw [map_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [map_smul]
    congr 1
    have := hcomm (mk 0 1) hu0 0 b Φ hΦ
    rwa [smul_zero, hub b hb] at this
  have e := congrFun hT y
  rw [hzero, map_zero, Pi.zero_apply, hfac, hy1, one_mul] at e
  exact e.symm

end GlobalTheory.ArchPure
