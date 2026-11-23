module

public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.EchEqOneIff
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FinsumQuotientOfLe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
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

open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real

namespace GlobalTheory.SW.FourierJ

open Matrix Complex in
open scoped ComplexConjugate Real in
private theorem mem_perSub_iff_exists_eq_smul_zm {κ ι : Type} [Fintype κ] [Fintype ι] (R : ℕ)
    (y : Matrix κ ι ℚ) : y ∈ _root_.GlobalTheory.SW.perSub ℚ κ ι R ↔
      ∃ m : κ → ι → ℤ, y = R • _root_.GlobalTheory.SW.FourierJ.zm m := by
  rw [_root_.GlobalTheory.SW.HaarLevel.mem_perSub]
  constructor
  · rintro ⟨y', rfl⟩
    obtain ⟨m, hm⟩ := (_root_.GlobalTheory.SW.FourierJ.intM_iff _).mp
      ((_root_.GlobalTheory.SW.HaarLevel.intM_iff _).mpr ⟨y', rfl⟩)
    exact ⟨m, by rw [hm]⟩
  · rintro ⟨m, rfl⟩
    obtain ⟨y', hy'⟩ := (_root_.GlobalTheory.SW.HaarLevel.intM_iff _).mp
      ((_root_.GlobalTheory.SW.FourierJ.intM_iff _).mpr ⟨m, rfl⟩)
    exact ⟨y', by rw [hy']⟩

open Matrix Complex in
open scoped ComplexConjugate Real in
theorem _root_.GlobalTheory.SW.FourierJ.haar_eq_sum_rep : ∀ (κ ι : Type) [Fintype κ]
    [Fintype ι] [DecidableEq κ] [DecidableEq ι] (R : ℕ) (φ : Matrix κ ι ℚ → ℂ), 0 < R →
    _root_.GlobalTheory.SW.HasLevel R φ → _root_.GlobalTheory.SW.haar φ =
      ((R : ℂ) ^ (Fintype.card κ * Fintype.card ι))⁻¹ *
        ∑ n : κ → ι → Fin (R * R), φ (_root_.GlobalTheory.SW.FourierJ.rep R n) := by
  intro κ ι _ _ _ _ R φ hR hφ
  classical
  obtain ⟨h1, -⟩ := _root_.GlobalTheory.SW.haar_eq_haarAt ℚ κ ι R φ hR hφ
  rw [h1]
  unfold _root_.GlobalTheory.SW.haarAt
  rw [Module.finrank_self, one_mul]
  congr 1
  have hper : ∀ x : Matrix κ ι ℚ, φ (Quotient.out
      (QuotientAddGroup.mk x : Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R)) = φ x := by
    intro x
    have hmem : -x + Quotient.out
        (QuotientAddGroup.mk x : Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R) ∈
        _root_.GlobalTheory.SW.perSub ℚ κ ι R :=
      QuotientAddGroup.eq.mp (QuotientAddGroup.out_eq' _).symm
    have h := _root_.GlobalTheory.SW.HaarLevel.periodic hφ x _ hmem
    rwa [add_neg_cancel_left] at h
  have hsupp : (Function.support fun q : Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R =>
      φ (Quotient.out q)) ⊆ ↑(Finset.univ.image fun n : κ → ι → Fin (R * R) =>
        (QuotientAddGroup.mk (_root_.GlobalTheory.SW.FourierJ.rep R n) :
          Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R)) := by
    intro q hq
    obtain ⟨n, m, hnm⟩ := exists_rep_add_smul_zm_of_intM_smul hR _ (hφ.1 _ (Function.mem_support.mp hq))
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range]
    refine ⟨n, ?_⟩
    rw [← QuotientAddGroup.out_eq' q, hnm, QuotientAddGroup.eq, neg_add_cancel_left]
    exact (mem_perSub_iff_exists_eq_smul_zm R _).mpr ⟨m, rfl⟩
  have hinj : Function.Injective fun n : κ → ι → Fin (R * R) =>
      (QuotientAddGroup.mk (_root_.GlobalTheory.SW.FourierJ.rep R n) :
        Matrix κ ι ℚ ⧸ _root_.GlobalTheory.SW.perSub ℚ κ ι R) := by
    intro n n' h
    obtain ⟨m, hm⟩ := (mem_perSub_iff_exists_eq_smul_zm R _).mp (QuotientAddGroup.eq.mp h)
    exact rep_eq_of_neg_add_eq_smul_zm hR m hm
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_image (fun n _ n' _ h => hinj h)]
  exact Finset.sum_congr rfl fun n _ => hper _

end GlobalTheory.SW.FourierJ
