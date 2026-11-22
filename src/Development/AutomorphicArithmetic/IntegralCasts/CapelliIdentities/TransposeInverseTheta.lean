module

public import Mathlib.GroupTheory.SemidirectProduct
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace UpperTheory.Reformulated.B.TransposeInverseTheta

noncomputable def Jmat.{u_1} (R : Type u_1) [CommRing R] (m : ℕ) : Matrix (Fin m) (Fin m) R :=
  fun i j ↦ if j = i.rev then 1 else 0

theorem aux2.{u_1} {R : Type u_1} [CommRing R] (m : ℕ) :
    Jmat R m * Jmat R m = (1 : Matrix (Fin m) (Fin m) R) := by
  ext i j
  simp only [Matrix.mul_apply, Jmat, Matrix.one_apply]
  simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fin.rev_rev]
  simp only [eq_comm]

noncomputable def Jgl.{u_1} (R : Type u_1) [CommRing R] (m : ℕ) : GL (Fin m) R :=
  { val := Jmat R m, inv := Jmat R m, val_inv := aux2 m,
    inv_val := aux2 m : (Matrix (Fin m) (Fin m) R)ˣ }

theorem aux4.{u_1} {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) :
    (↑g⁻¹ : Matrix n n R).transpose * (↑g : Matrix n n R).transpose = (1 : Matrix n n R) := by
  rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]

theorem aux5.{u_1} {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R] (g : GL n R) :
    (↑g : Matrix n n R).transpose * (↑g⁻¹ : Matrix n n R).transpose = (1 : Matrix n n R) := by
  rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

noncomputable def trInv.{u_1} {n : Type} [Fintype n] [DecidableEq n] {R : Type u_1} [CommRing R]
    (g : GL n R) : GL n R :=
  { val := (↑g⁻¹ : Matrix n n R).transpose, inv := (↑g : Matrix n n R).transpose,
    val_inv := aux4 g, inv_val := aux5 g : (Matrix n n R)ˣ }

noncomputable def theta.{u_1} {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) :
    GL (Fin m) R :=
  Jgl R m * trInv g * Jgl R m

private theorem trInv_mul {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g h : GL n R) : trInv (g * h) = trInv g * trInv h := by
  apply Units.ext
  change (↑(g * h)⁻¹ : Matrix n n R).transpose = (↑g⁻¹ : Matrix n n R).transpose * (↑h⁻¹ : Matrix n n R).transpose
  rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul]

private theorem trInv_trInv {n : Type} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]
    (g : GL n R) : trInv (trInv g) = g := by
  apply Units.ext
  change (↑g : Matrix n n R).transpose.transpose = ↑g
  rw [Matrix.transpose_transpose]

private theorem Jgl_mul_self {m : ℕ} {R : Type*} [CommRing R] : Jgl R m * Jgl R m = 1 :=
  Units.ext (aux2 m)

private theorem trInv_Jgl {m : ℕ} {R : Type*} [CommRing R] : trInv (Jgl R m) = Jgl R m := by
  apply Units.ext
  change (Jmat R m).transpose = Jmat R m
  ext i j
  simp only [Matrix.transpose_apply, Jmat]
  by_cases h : j = i.rev
  · have h' : i = j.rev := by rw [h, Fin.rev_rev]
    simp [h]
  · have h' : ¬ i = j.rev := fun e => h (by rw [e, Fin.rev_rev])
    simp [h, h']

theorem aux8.{u_1} {m : ℕ} {R : Type u_1} [CommRing R] (g : GL (Fin m) R) :
    theta (theta g) = g := by
  have hJ := Jgl_mul_self (m := m) (R := R)
  simp only [theta, trInv_mul, trInv_trInv, trInv_Jgl]
  calc _ = (Jgl R m * Jgl R m) * g * (Jgl R m * Jgl R m) := by simp only [mul_assoc]
    _ = g := by rw [hJ, one_mul, mul_one]

theorem aux9.{u_1} {m : ℕ} {R : Type u_1} [CommRing R] (g h : GL (Fin m) R) :
    theta (g * h) = theta g * theta h := by
  have hJ := Jgl_mul_self (m := m) (R := R)
  simp only [theta, trInv_mul]
  calc _ = Jgl R m * trInv g * 1 * trInv h * Jgl R m := by simp only [mul_assoc, one_mul]
    _ = _ := by rw [← hJ]; simp only [mul_assoc]

noncomputable def thetaAut.{u_1} (m : ℕ) (R : Type u_1) [CommRing R] : MulAut (GL (Fin m) R) :=
  { toFun := theta, invFun := theta, left_inv := aux8, right_inv := aux8, map_mul' := aux9 :
    GL (Fin m) R ≃* GL (Fin m) R }

theorem aux11.{u_1} (m : ℕ) (R : Type u_1) [CommRing R] :
    (if (1 : ℤˣ) = 1 then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) = 1 :=
  ite_eq_left rfl

private theorem thetaAut_mul_self (m : ℕ) (R : Type*) [CommRing R] :
    thetaAut m R * thetaAut m R = 1 := by
  ext1 g
  exact aux8 g

theorem aux12.{u_1} (m : ℕ) (R : Type u_1) [CommRing R] (s t : ℤˣ) :
    (if s * t = 1 then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) =
      (if s = 1 then (1 : MulAut (GL (Fin m) R)) else thetaAut m R) *
        if t = 1 then (1 : MulAut (GL (Fin m) R)) else thetaAut m R := by
  have hne : (-1 : ℤˣ) ≠ 1 := by decide
  rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
  · simp
  · simp [hne]
  · simp [hne]
  · simp [hne, thetaAut_mul_self]

noncomputable def sgnAct.{u_1} (m : ℕ) (R : Type u_1) [CommRing R] : ℤˣ →* MulAut (GL (Fin m) R) :=
  { toFun := fun s ↦ if s = 1 then 1 else thetaAut m R,
    map_one' := aux11 m R, map_mul' := aux12 m R : ℤˣ →* MulAut (GL (Fin m) R) }

@[reducible] noncomputable def GG.{u_1} (m : ℕ) (R : Type u_1) [CommRing R] : Type u_1 :=
  GL (Fin m) R ⋊[sgnAct m R] ℤˣ

@[reducible] noncomputable def ofGL.{u_1} {m : ℕ} {R : Type u_1} [CommRing R] :
    GL (Fin m) R →* GG m R :=
  SemidirectProduct.inl

noncomputable def conjBy.{u_1, u_3} {m : ℕ} {R : Type u_1} [CommRing R] {G : Type u_3} [Group G]
    (h : GL (Fin m) R) (r : G →* GG m R) : G →* GG m R :=
  (MulAut.conj (ofGL h)).toMonoidHom.comp r

theorem conj_left {G R : Type} [Group G] [CommRing R] {m : ℕ} (h : GL (Fin m) R) (r : G →* GG m R)
    (g : G) : (conjBy h r g).left = h * (r g).left * sgnAct m R (r g).right h⁻¹ := by
  have e : (conjBy h r) g =
      SemidirectProduct.inl h * r g * (SemidirectProduct.inl h)⁻¹ := rfl
  rw [e, ← map_inv, SemidirectProduct.mul_left, SemidirectProduct.mul_left]
  simp [mul_assoc]

end UpperTheory.Reformulated.B.TransposeInverseTheta
