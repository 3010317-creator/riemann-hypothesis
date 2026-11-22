module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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

namespace UpperTheory.Reformulated.B.H71

noncomputable def wt1 : Fin 3 → ℤ :=
  fun i ↦ 1 - ((i : ℕ) : ℤ)

theorem aux2.{u_1} {R : Type u_1} [CommRing R] (t : Rˣ) :
    ((Matrix.diagonal fun i : Fin 3 ↦ ((t ^ wt1 i : Rˣ) : R)) *
        Matrix.diagonal fun i : Fin 3 ↦ (((t ^ wt1 i)⁻¹ : Rˣ) : R)) =
      (1 : Matrix (Fin 3) (Fin 3) R) := by
  rw [Matrix.diagonal_mul_diagonal]
  simp only [Units.mul_inv, Matrix.diagonal_one]

theorem aux3.{u_1} {R : Type u_1} [CommRing R] (t : Rˣ) :
    ((Matrix.diagonal fun i : Fin 3 ↦ (((t ^ wt1 i)⁻¹ : Rˣ) : R)) *
        Matrix.diagonal fun i : Fin 3 ↦ ((t ^ wt1 i : Rˣ) : R)) =
      (1 : Matrix (Fin 3) (Fin 3) R) := by
  rw [Matrix.diagonal_mul_diagonal]
  simp only [Units.inv_mul, Matrix.diagonal_one]

noncomputable def torGL.{u_1} {R : Type u_1} [CommRing R] (t : Rˣ) : GL (Fin 3) R :=
  { val := Matrix.diagonal fun i : Fin 3 ↦ ((t ^ wt1 i : Rˣ) : R),
    inv := Matrix.diagonal fun i : Fin 3 ↦ (((t ^ wt1 i)⁻¹ : Rˣ) : R),
    val_inv := aux2 t, inv_val := aux3 t : (Matrix (Fin 3) (Fin 3) R)ˣ }

theorem aux5.{u_1} (R : Type u_1) [CommRing R] : torGL (1 : Rˣ) = (1 : GL (Fin 3) R) := by
  apply Units.ext
  change Matrix.diagonal (fun i : Fin 3 ↦ (↑((1 : Rˣ) ^ wt1 i) : R)) = 1
  simp only [one_zpow, Units.val_one, Matrix.diagonal_one]

theorem aux6.{u_1} (R : Type u_1) [CommRing R] (s t : Rˣ) :
    torGL (s * t) = torGL s * torGL t := by
  apply Units.ext
  change Matrix.diagonal (fun i : Fin 3 ↦ (↑((s * t) ^ wt1 i) : R)) =
    Matrix.diagonal (fun i : Fin 3 ↦ (↑(s ^ wt1 i) : R)) *
      Matrix.diagonal (fun i : Fin 3 ↦ (↑(t ^ wt1 i) : R))
  rw [Matrix.diagonal_mul_diagonal]
  simp only [mul_zpow, Units.val_mul]

noncomputable def tor.{u_1} (R : Type u_1) [CommRing R] : Rˣ →* GL (Fin 3) R :=
  { toFun := torGL, map_one' := aux5 R, map_mul' := aux6 R : Rˣ →* GL (Fin 3) R }

theorem map_tor {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (t : Aˣ) :
    Matrix.GeneralLinearGroup.map f (tor A t) = tor B (Units.map (f : A →* B) t) := by
  apply Units.ext
  change (Matrix.diagonal (fun i : Fin 3 ↦ (↑(t ^ wt1 i) : A))).map f =
    Matrix.diagonal (fun i : Fin 3 ↦ (↑((Units.map (f : A →* B) t) ^ wt1 i) : B))
  rw [Matrix.diagonal_map (map_zero f)]
  congr 1
  funext i
  rw [← map_zpow, Units.coe_map]
  rfl

end UpperTheory.Reformulated.B.H71
