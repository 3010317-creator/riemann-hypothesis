module

public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveMulEqVonMangoldtConvolution
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEndomorphismDensityGLRecursion
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEqFinsumPsi
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEqui
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MonicFactorizationConvolutionCancelOfOne
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassEqOfLinearEquivInvariant
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EndomorphismMassMulParabolicInductionTrivial
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
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem mass_comp_charpoly_eq_mul (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ) (P : F[X]) :
    mass (fun g : Module.End F V => s (LinearMap.charpoly g)) P =
      s P * mass (fun _ : Module.End F V => (1 : ℂ)) P := by
  have : Finite (Module.End F V) := Module.finite_of_finite F
  unfold mass
  have hfin : ({g : Module.End F V | LinearMap.charpoly g = P}).Finite := Set.toFinite _
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
  refine Finset.sum_congr rfl fun g hg => ?_
  have : LinearMap.charpoly g = P := by simpa using hg
  simp [this]

theorem mass_psi_eq_glCard_mul_mangoldt_div :
    ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
      (s : F[X] → ℂ), IsAdditive s → ∀ P : F[X], P.Monic → P.natDegree = Module.finrank F V →
      mass (psi s V) P = glCard F P.natDegree * mangoldt s P / ((Nat.card F : ℂ) ^ P.natDegree - 1) := by
  intro F _ _ V _ _ _ s hs P hP hdeg
  have hiso := _root_.GlobalTheory.CuspGL.psi_conj F s
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hmu1 : mu (1 : F[X]) = 1 := (_root_.GlobalTheory.CuspGL.mu_rec F 1 monic_one).2
  have hlog := _root_.GlobalTheory.CuspGL.LogDeriv.additive_mul_eq_conv F (Nat.card F) hq s mu hs hmu1 (fun Q hQ => (_root_.GlobalTheory.CuspGL.mu_rec F Q hQ).1)
  have hmul : ∀ Q : F[X], Q.Monic → s Q * mu Q =
      conv (fun D => mass (psi s (Fin D.natDegree → F)) D / glCard F D.natDegree) mu Q := by
    intro Q hQ
    have h := _root_.GlobalTheory.CuspGL.MassMult.mass_mult F (Fin Q.natDegree → F) (fun V _ _ _ => psi s V) hiso Q hQ (by simp)
    have h2 : (fun g : Module.End F (Fin Q.natDegree → F) =>
        ∑ᶠ W : {W : Submodule F (Fin Q.natDegree → F) // ∀ x ∈ W, g x ∈ W}, psi s W.1 (g.restrict W.2)) =
        fun g => s (LinearMap.charpoly g) := by
      funext g
      exact (_root_.GlobalTheory.CuspGL.charpoly_eq_finsum_psi F _ s g).symm
    rw [← h]
    rw [h2, mass_comp_charpoly_eq_mul, mu, mul_div_assoc]
  have hc := _root_.GlobalTheory.CuspGL.ConvCancel.conv_cancel F _ _ mu hmu1 (fun Q hQ => (hmul Q hQ).symm.trans (hlog Q hQ)) P hP
  have hV := _root_.GlobalTheory.CuspGL.mass_eq_mass_pi_of_invariant F V (fun V _ _ _ => psi s V) hiso P hdeg
  have hg : glCard F P.natDegree ≠ 0 := by
    unfold glCard
    exact_mod_cast (Nat.card_pos (α := GL (Fin P.natDegree) F)).ne'
  rw [hV, mul_div_assoc, ← hc, mul_div_cancel₀ _ hg]

end GlobalTheory.CuspGL
