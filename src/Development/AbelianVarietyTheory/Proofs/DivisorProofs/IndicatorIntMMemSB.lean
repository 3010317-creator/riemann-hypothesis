module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory ValuativeRel Matrix Filter Topology
open GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model GlobalTheory.SplitFlip

namespace GlobalTheory.KSplit

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsSmU (χ : kˣ →* ℂˣ) : Prop := IsOpen (χ.ker : Set kˣ) ∧ ∀ x, ‖(χ x : ℂ)‖ = 1


variable (k) in
def intM (m n : Type) : Set (Matrix m n k) := {X | ∀ i j, X i j ∈ 𝒪[k]}

def IsEqv {n : ℕ} (ν : kˣ →* ℂˣ) (z : ℂ) (l : (Matrix (Fin n) (Fin n) k → ℂ) → ℂ) : Prop :=
  (∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), ∀ φ' ∈ SB (Matrix (Fin n) (Fin n) k), l (φ + φ') = l φ + l φ') ∧
  (∀ c : ℂ, ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k), l (c • φ) = c * l φ) ∧
  ∀ g₁ g₂ : GL (Fin n) k, ∀ φ ∈ SB (Matrix (Fin n) (Fin n) k),
    (ν (gdet g₁ * gdet g₂) : ℂ) * apow (gdet g₁ * gdet g₂) z * l (fun X => φ (g₁.val * X * g₂.val)) = l φ

def mapA {a : ℕ} (a' : ℕ) (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ) (ν β : kˣ →* ℂˣ)
    (Φ : Matrix (Fin a) (Fin (a + a')) k → ℂ) (h : GL (Fin (a + a')) k) : ℂ :=
  l fun g => omA ν β 1 h Φ (g * X0 k (finSumFinEquiv : Fin a ⊕ Fin a' ≃ Fin (a + a')))

section Frames

variable {R S D : Type} [Fintype R] [DecidableEq R] [Fintype S] [DecidableEq S] [Fintype D] [DecidableEq D]



end Frames

variable {a a' : ℕ} {z : ℂ} {ν α β : kˣ →* ℂˣ}

end Local

section Adelic

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end Adelic

end GlobalTheory.KSplit

end
