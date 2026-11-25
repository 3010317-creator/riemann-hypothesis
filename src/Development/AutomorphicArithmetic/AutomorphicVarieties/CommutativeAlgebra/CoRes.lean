module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
public import Mathlib.Algebra.DualNumber
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
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

theorem UpperTheory.V.Alg.co_res :
    ∀ (O : Type) [CommRing O] [IsLocalRing O], IsCO O (ResidueField O) ∧ IsCO O (DualNumber (ResidueField O)) := by
  intro O _ _
  constructor
  · refine IsCO.mk ?_ ?_ ?_
    · infer_instance
    · show IsLocalHom (residue O)
      infer_instance
    · intro x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x
      refine ⟨a, ?_⟩
      have h : x - algebraMap O (ResidueField O) a = 0 := sub_eq_zero.mpr ha.symm
      rw [h]
      exact zero_mem _
  · have hm : ∀ x : DualNumber (ResidueField O), x ∈ maximalIdeal _ ↔ x.fst = 0 := by
      intro x
      rw [mem_maximalIdeal, mem_nonunits_iff, TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero,
        not_not]
    have hfst : ∀ a : O, (algebraMap O (DualNumber (ResidueField O)) a).fst =
        algebraMap O (ResidueField O) a :=
      fun a => (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes a
    refine IsCO.mk ?_ ?_ ?_
    · have : Module.Finite (ResidueField O) (DualNumber (ResidueField O)) :=
        Module.Finite.of_surjective
          ((TrivSqZeroExt.inlAlgHom (ResidueField O) _ _).toLinearMap.coprod
            (TrivSqZeroExt.inrHom _ _))
          fun x => ⟨(x.fst, x.snd), TrivSqZeroExt.ext (by simp) (by simp)⟩
      have : IsArtinianRing (DualNumber (ResidueField O)) :=
        IsArtinianRing.of_finite (ResidueField O) _
      infer_instance
    · refine ⟨fun a ha => ?_⟩
      have h1 := ha.map (TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O))
      rw [(TrivSqZeroExt.fstHom O (ResidueField O) (ResidueField O)).commutes] at h1
      exact isUnit_of_map_unit (residue O) a h1
    · intro x
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective x.fst
      refine ⟨a, ?_⟩
      rw [hm, TrivSqZeroExt.fst_sub, hfst]
      exact sub_eq_zero.mpr ha.symm
