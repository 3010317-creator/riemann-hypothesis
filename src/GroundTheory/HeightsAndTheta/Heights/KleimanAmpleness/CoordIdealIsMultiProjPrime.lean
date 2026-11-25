module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman

open MvPolynomial

noncomputable section

section Cech

structure CechSystem (ι : Type) (k : Type) [CommRing k] where

  V : Finset ι → Type
  [grp : ∀ I, AddCommGroup (V I)]
  [mod : ∀ I, Module k (V I)]

  res : ∀ {I J : Finset ι}, I ⊆ J → V I →ₗ[k] V J

  piece : ∀ I, Submodule k (V I)

  good : Finset ι → Prop

attribute [instance] CechSystem.grp CechSystem.mod

end Cech

section Graded

variable (S : Type) [CommRing S] (N : ℕ)

abbrev Poly : Type := MvPolynomial (Fin (N + 1)) S

def polyPiece (d : ℤ) : Submodule S (Poly S N) :=
  weightedHomogeneousSubmodule S (fun _ => (1 : ℤ)) d

structure GradedMod (M : Type) [AddCommGroup M] [Module (Poly S N) M] [Module S M]
    [IsScalarTower S (Poly S N) M] where

  piece : ℤ → Submodule S M
  internal : DirectSum.IsInternal piece
  smul_mem : ∀ (d c : ℤ) (f : Poly S N), f ∈ polyPiece S N d → ∀ m ∈ piece c, f • m ∈ piece (d + c)

end Graded

section Cl

open ReciprocityTheory.ChartRestriction.G.Geo

variable (S : Type) [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]

def chartRingI (x : Fin (N + 1) → Ω) (I : Finset (Fin (N + 1))) : Subalgebra S Ω :=
  Algebra.adjoin S {y | ∃ i ∈ I, ∃ j, y = x j / x i}

theorem chartRingI_singleton (x : Fin (N + 1) → Ω) (i : Fin (N + 1)) :
    chartRingI S x {i} = chartRing S x i := by
  unfold chartRingI chartRing
  congr 1
  ext y
  simp [eq_comm]

variable (E : Type) [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

variable {S E}

variable (S)

variable {S}

abbrev LineBundle (x : Fin (N + 1) → Ω) : Type := ChartBundle S x 1 Ω

variable (S)

end Cl

section Filtration

open ReciprocityTheory.ChartRestriction.G.Geo

variable (S : Type) [CommRing S] (N : ℕ)
variable {M : Type} [AddCommGroup M] [Module (Poly S N) M] [Module S M] [IsScalarTower S (Poly S N) M]


variable {S N}
variable {Ω : Type} [Field Ω] [Algebra S Ω]

variable (S)

end Filtration

section Comparison₂

open ReciprocityTheory.ChartRestriction.G.Geo

variable {S : Type} [CommRing S] {σ : Type} {Ω : Type} [Field Ω] [Algebra S Ω]


end Comparison₂

section Inhabitants

open ReciprocityTheory.ChartRestriction.G.Geo

variable (S : Type) [CommRing S] (N : ℕ)

variable {S} {Ω : Type} [Field Ω] [Algebra S Ω]

end Inhabitants

section Inhabitants2

open ReciprocityTheory.ChartRestriction.G.Geo

variable {S : Type} [CommRing S] {N : ℕ} {Ω : Type} [Field Ω] [Algebra S Ω]


variable (S N)

end Inhabitants2

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman
