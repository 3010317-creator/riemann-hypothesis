module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLUDecompositionOfLeadingMinorsNeZero
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteShiftsVanishingLeadingMinor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTransvectionMulVecMemSpanWeightVectorsDomin
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerTriangularGLComplexInduction
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyRepMulVecMemOfCofiniteScalarShift
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

open Matrix Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP NumberField GlobalTheory.AlgWtHW

namespace GlobalTheory.AlgWtHW

theorem mulVec_mem_sle_of_isBEig : ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (Φ : GL (Fin n) ℂ → Matrix ι ι ℂ), IsPolyRep Φ → ∀ (v : ι → ℂ) (lam : Fin n → ℤ), IsBEig Φ v lam → ∀ B : GL (Fin n) ℂ, Φ B *ᵥ v ∈ Sle Φ lam := by
  intro n ι _ _ Φ hΦ v lam hv B
  have hdom : DomLE lam lam := ⟨rfl, fun _ => le_rfl⟩
  have hvS : v ∈ Sle Φ lam := by
    refine Submodule.subset_span ⟨lam, hdom, fun D hD => hv.2 D ?_⟩
    intro a b hab
    exact hD (ne_of_gt hab)

  have hstab : ∀ L : GL (Fin n) ℂ, L.val.BlockTriangular OrderDual.toDual →
      ∀ w ∈ Sle Φ lam, Φ L *ᵥ w ∈ Sle Φ lam := by
    refine _root_.GlobalTheory.lowerTriangular_GL_induction _ ?_ ?_ ?_ ?_
    · intro w hw; rw [hΦ.one, one_mulVec]; exact hw
    · intro A C hA hC w hw
      rw [hΦ.mul, ← mulVec_mulVec]
      exact hA _ (hC w hw)
    · intro D hD w hw
      refine Submodule.span_induction (p := fun w _ => Φ D *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        rw [hu D hD]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨ν, hν, hu⟩)
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx
    · intro i j s T hji hT w hw
      refine Submodule.span_induction (p := fun w _ => Φ T *ᵥ w ∈ Sle Φ lam) ?_ ?_ ?_ ?_ hw
      · rintro u ⟨ν, hν, hu⟩
        exact _root_.GlobalTheory.AlgWtHW.lowerTransvection_mulVec_mem_Sle Φ hΦ lam ν hν u hu i j hji s T hT
      · simp
      · intro x y _ _ hx hy; rw [mulVec_add]; exact Submodule.add_mem _ hx hy
      · intro c x _ hx; rw [mulVec_smul]; exact Submodule.smul_mem _ _ hx

  have hbig : ∀ C : GL (Fin n) ℂ,
      (∀ (k : ℕ) (hk : k ≤ n), (C.val.submatrix (Fin.castLE hk) (Fin.castLE hk)).det ≠ 0) →
      Φ C *ᵥ v ∈ Sle Φ lam := by
    intro C hC
    obtain ⟨L, U, hL, hU, rfl⟩ := _root_.GlobalTheory.LUDecomp.lu C hC
    rw [hΦ.mul, ← mulVec_mulVec, hv.2 U hU, mulVec_smul]
    exact Submodule.smul_mem _ _ (hstab L hL v hvS)

  refine _root_.GlobalTheory.AlgWtHW.mulVec_mem_of_cofinite_shift Φ hΦ _ v B _ (_root_.GlobalTheory.shift_minors_vanish_finite B.val) ?_
  intro s hs C hC
  apply hbig
  rw [hC]
  simpa using hs

end GlobalTheory.AlgWtHW
