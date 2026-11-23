module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AbsInvOf
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.VInduction
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct

private theorem UpperTheory.Ru.crystallineComparison.eq_zero_of_coord {F V C : Type*} [Field F] [AddCommGroup V] [Module F V]
    [AddCommGroup C] [Module F C] (w : V ⊗[F] C)
    (h : ∀ f : Module.Dual F V, TensorProduct.lid F C (LinearMap.rTensor C f w) = 0) : w = 0 := by
  classical
  let b := Module.Basis.ofVectorSpace F V
  apply (TensorProduct.equivFinsuppOfBasisLeft b).injective
  rw [map_zero]
  ext i
  have key : ∀ w : V ⊗[F] C, (TensorProduct.equivFinsuppOfBasisLeft b w) i =
      TensorProduct.lid F C (LinearMap.rTensor C (b.coord i) w) := by
    intro w
    induction w with
    | tmul x y => simp
    | add x y hx hy => simp [hx, hy]
  rw [key, h]
  rfl

private theorem UpperTheory.Ru.crystallineComparison.submodule_pi_smul_sum_eq_zero {R : Type*} [CommRing R]
    {N : ℕ → Type*} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)] {S : Submodule R (∀ n, N n)}
    {κ : Type*} [Fintype κ] (t : R) (c : κ → R) (x : κ → S) (y : ∀ n, κ → N n)
    (hxy : ∀ k n, (x k).1 n = y n k) (hy : ∀ n, t • ∑ k, c k • y n k = 0) :
    t • ∑ k, c k • x k = 0 := by
  refine Subtype.ext (funext fun n => ?_)
  have hev : (∑ k, c k • x k).1 n = ∑ k, c k • y n k := by
    let ev : S →+ N n := { toFun := fun s => s.1 n, map_zero' := rfl, map_add' := fun _ _ => rfl }
    exact (map_sum ev _ _).trans <| Finset.sum_congr rfl fun k _ => congrArg (c k • ·) (hxy k n)
  exact (congrArg (t • ·) hev).trans (hy n)

private theorem UpperTheory.Ru.crystallineComparison.lid_rTensor_sum_eq_zero {F V A C B : Type*}
    [Field F] [AddCommGroup V] [Module F V] [CommRing C] [Algebra F C] [CommRing B]
    (ι : C →+* B) (hι : Function.Injective ι) (c0 : A → C) (i : A → B) (hc : ∀ a, ι (c0 a) = i a)
    (q : F → B) (hq : ∀ z, ι (algebraMap F C z) = q z) {κ : Type*} [Fintype κ]
    (x : κ → V) (c : κ → A) (r : C) (f : Module.Dual F V)
    (h : ∑ k, q (f (x k)) * i (c k) = 0) :
    TensorProduct.lid F C (LinearMap.rTensor C f (∑ k, x k ⊗ₜ[F] (c0 (c k) * r ^ 0))) = 0 := by
  apply hι
  simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, pow_zero, mul_one,
    map_zero, Algebra.smul_def, map_mul, hq, hc]
  exact h

theorem UpperTheory.Ru.crystallineComparison.injOf :
    UpperTheory.Ru.crystallineComparison.InjOf := by
  intro l _ K B₀ ι hι hc hq G Amp hF hE hL e e' hB hP hcomp M hM j κ _ v c u hu
  refine (hL.ch M hM).elim fun a => ?_
  set_option synthInstance.maxHeartbeats 2000000 in
  have h0 : (per l K).t ^ u • ∑ k, (show (per l K).A from c k) • e'.e a j (v k) = 0 :=
    UpperTheory.Ru.crystallineComparison.submodule_pi_smul_sum_eq_zero (S := (M.MS j).lim)
      (UpperTheory.Ru.crystallineComparison.tA l ^ u) c (fun k => e'.e a j (v k))
      (fun n k => e M n j ((v k).lev n)) (fun k n => hcomp M a j (v k) n) hu
  have h1 := UpperTheory.Ru.crystallineComparison.injAbs l K (per l K) G (dat Amp) hF hE hL e' hB hP M hM a j κ v c u h0
  apply UpperTheory.Ru.crystallineComparison.eq_zero_of_coord
  intro f
  set_option synthInstance.maxHeartbeats 100000 in
    exact UpperTheory.Ru.crystallineComparison.lid_rTensor_sum_eq_zero ι hι B₀.c (per l K).i hc
      (per l K).q hq (fun k => M.toV j (v k)) c
      (Ring.inverse (B₀.c (UpperTheory.Ru.crystallineComparison.tA l))) f (h1 f)
