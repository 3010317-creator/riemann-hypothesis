module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToSpanSingletonConstGenInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppOneEqZeroOfKernelIdealOfCompEqPrimeSmul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusDualAddFinrankKerVerschiebung
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFrobeniusKernelHopfLePowCotangent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusKernelIdealEqKernelRelativeFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
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
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    G.height ≤ Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) := by
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdimD : Module.finrank K (G.dual.A 1) = p ^ G.dual.height := by
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum K) := inferInstance
    have e := G.dual.rank_eq 1 q
    rw [Module.rankAtStalk_eq_finrank_of_free] at e
    simpa using e
  have hhD : G.dual.height = G.height := by simp
  have hord := finrank_eq_ker_mul_range K (G.dual.A 1) _ ((relFrob h G.dual).app 1)
  have hD : Module.finrank K (G.dual.A 1 ⧸ kerIdeal ((relFrob h G.dual).app 1)) ≤
      p ^ Module.finrank K (Cot K (G.dual.A 1)) := by
    rw [← _root_.GlobalTheory.PDiv.frobKerIdeal_eq_kerIdeal_relFrob p K h G.dual 1]
    exact _root_.GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot p K (G.dual.A 1)
  have hA : Module.finrank K (G.A 1 ⧸ kerIdeal ((relFrob h G).app 1)) ≤
      p ^ Module.finrank K (Cot K (G.A 1)) := by
    rw [← _root_.GlobalTheory.PDiv.frobKerIdeal_eq_kerIdeal_relFrob p K h G 1]
    exact _root_.GlobalTheory.PDiv.FrobKerOrder.finrank_le_pow_finrank_cot p K (G.A 1)
  have hker : (kerIdeal ((relFrob h G).app 1)).restrictScalars K ≤
      LinearMap.ker ((verschiebung h G).app 1 :
        G.A 1 →ₐ[K] (frobTwist h G).A 1).toLinearMap := fun a ha =>
    _root_.GlobalTheory.PDivGroup.app_one_eq_zero_of_mem_kerIdeal_of_comp_eq_prime_smul p K G (frobTwist h G) (relFrob h G) (verschiebung h G)
      (verschiebung_comp_relFrob h G) a ha
  have hV := _root_.GlobalTheory.PDivGroup.finrank_range_relFrob_dual_add_finrank_ker_verschiebung p K h G
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((relFrob h G).app 1)).restrictScalars K)
  rw [(Submodule.Quotient.restrictScalarsEquiv K (kerIdeal ((relFrob h G).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have hr : Module.finrank K (LinearMap.range ((relFrob h G.dual).app 1 :
        (frobTwist h G.dual).A 1 →ₐ[K] G.dual.A 1).toLinearMap) ≤
      p ^ Module.finrank K (Cot K (G.A 1)) := by omega
  have key : p ^ G.height ≤
      p ^ (Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1))) := by
    rw [pow_add, mul_comm, ← hhD, ← hdimD, hord]
    exact Nat.mul_le_mul hD hr
  exact (Nat.pow_le_pow_iff_right hp2).1 key
