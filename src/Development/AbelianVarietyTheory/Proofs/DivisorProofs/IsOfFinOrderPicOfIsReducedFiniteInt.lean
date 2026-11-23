module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulMemRangePiQuotientMinimalPrimes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOfFinOrderOfIsOfFinOrderMapRingHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicIsOfFinOrderOfFiniteInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicPiIsOfFinOrder
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GlobalTheory.PicReducedTors

theorem pic_isOfFinOrder : ∀ (B : Type) [CommRing B] [IsReduced B] [Module.Finite ℤ B] (M : CommRing.Pic B),
    IsOfFinOrder M := by
  intro B _ _ _ M
  haveI : IsNoetherian ℤ B := inferInstance
  haveI : IsNoetherianRing B := isNoetherian_of_tower ℤ inferInstance
  haveI : Finite (minimalPrimes B) := (minimalPrimes.finite_of_isNoetherianRing B).to_subtype
  let φ := Pi.ringHom fun P : minimalPrimes B => Ideal.Quotient.mk (P : Ideal B)
  haveI : Module.Finite ℤ ((P : minimalPrimes B) → B ⧸ (P : Ideal B)) := inferInstance
  obtain ⟨n, hn, hmul⟩ := _root_.GlobalTheory.CokerMinimalPrimes.exists_nat_mul_mem_range_pi_quotient_minimalPrimes B
  have hinj : Function.Injective φ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro b hb
    have hrad : b ∈ (⊥ : Ideal B).radical := by
      rw [← Ideal.sInf_minimalPrimes, Submodule.mem_sInf]
      intro P hP
      have := congrFun hb ⟨P, hP⟩
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact this
    obtain ⟨k, hk⟩ := hrad
    exact IsReduced.eq_zero b ⟨k, by simpa using hk⟩
  refine _root_.GlobalTheory.isOfFinOrder_of_isOfFinOrder_mapRingHom B _ φ n hinj hn hmul M ?_
  refine _root_.GlobalTheory.pic_pi_isOfFinOrder _ _ (fun P N => ?_) _
  haveI : (P : Ideal B).IsPrime := P.2.1.1
  exact _root_.GlobalTheory.pic_isOfFinOrder_of_finite_int _ N

end GlobalTheory.PicReducedTors
