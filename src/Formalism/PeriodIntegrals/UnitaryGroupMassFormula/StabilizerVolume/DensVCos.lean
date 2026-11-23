module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVGen
import Aesop.Main
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensVCos

@[expose] public section

noncomputable section

namespace PI.VolStabS

open MeasureTheory Topology Set Filter

export PI.VolStabSW (hasDens_zero hasDens_sum DensCosB IsCOBasis isCompact_cos integrable_cos)

namespace HasDens
export PI.VolStabSW.HasDens (add)
end HasDens

section Cos

variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}

theorem densLC_of_cosB [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] (U : Set V)
    (B : AddSubgroup V → Prop) (hB : IsCOBasis B) (h : DensCosB B μ f ι ν U) :
    DensOn (IsLCcOn U) μ f ι ν := by
  classical
  rintro φ ⟨hlc, hs, hsU⟩
  have hloc : ∀ x : tsupport φ, ∃ Λx : AddSubgroup V, IsOpen (Λx : Set V) ∧
      IsCompact (Λx : Set V) ∧
      (∀ y, y - (x : V) ∈ Λx → ∀ Λ : AddSubgroup V, B Λ → IsOpen (Λ : Set V) →
        IsCompact (Λ : Set V) → Λ ≤ Λx →
          ∃ g, HasDens μ f ι ν ({z | z - y ∈ Λ}.indicator fun _ => (1 : ℝ)) g) ∧
      ∀ z ∈ Λx, φ ((x : V) + z) = φ x := by
    intro x
    obtain ⟨N, hN, hd⟩ := h x (hsU x.2)
    have hfib : {z : V | φ ((x : V) + z) = φ x} ∈ 𝓝 (0 : V) := by
      have ho : IsOpen {z : V | (φ ∘ fun z => (x : V) + z) z = φ x} :=
        (hlc.comp_continuous (continuous_const.add continuous_id)).isClopen_fiber _ |>.isOpen
      exact ho.mem_nhds (by simp)
    obtain ⟨Λx, -, ho, hc, hsub⟩ := hB _ (inter_mem hN hfib)
    refine ⟨Λx, ho, hc, fun y hy Λ hBΛ hΛo hΛc hle => ?_, fun z hz => (hsub hz).2⟩
    obtain ⟨g, hg, hS⟩ := hd y (hsub hy).1 Λ hBΛ hΛo hΛc fun z hz => (hsub (hle hz)).1
    exact ⟨g, integrable_cos Λ hΛo hΛc y, hg, hS⟩
  choose Λx hΛxo hΛxc hΛxd hΛxφ using hloc
  obtain ⟨t, ht⟩ := hs.isCompact.elim_finite_subcover
    (fun x : tsupport φ => {y : V | y - (x : V) ∈ Λx x})
    (fun x => (hΛxo x).preimage (continuous_id.sub continuous_const))
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, by simp [(Λx _).zero_mem]⟩)
  obtain ⟨Λs, -, hso, -, -⟩ := hB univ univ_mem
  set Λi : AddSubgroup V := Λs ⊓ ⨅ x ∈ t, Λx x with hΛi
  have hΛio : IsOpen (Λi : Set V) := isOpen_inf_iInf Λs hso t Λx hΛxo
  obtain ⟨Λ', hBΛ', hΛ'o, hΛ'c, hΛ'sub⟩ := hB _ (hΛio.mem_nhds Λi.zero_mem)
  have hΛ'le : ∀ x ∈ t, Λ' ≤ Λx x := fun x hx z hz =>
    AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 (inf_le_right (a := Λs) (hΛ'sub hz)) x) hx
  have hK : ∀ y ∈ tsupport φ, ∃ x ∈ t, y - (x : V) ∈ Λx x := fun y hy => by
    obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (ht hy)
    exact ⟨x, hx, hyx⟩
  have hconst : ∀ y ∈ tsupport φ, ∀ z ∈ Λ', φ (y + z) = φ y := by
    intro y hy z hz
    obtain ⟨x, hx, hyx⟩ := hK y hy
    have h1 := hΛxφ x (y - x) hyx
    have h2 := hΛxφ x (y + z - x) (by
      have := (Λx x).add_mem hyx (hΛ'le x hx hz)
      rwa [show y - (x : V) + z = y + z - x by abel] at this)
    rw [add_sub_cancel] at h1 h2
    rw [h2, h1]
  obtain ⟨t2, ht2⟩ := hs.isCompact.elim_finite_subcover
    (fun y : tsupport φ => {z : V | z - (y : V) ∈ Λ'})
    (fun y => hΛ'o.preimage (continuous_id.sub continuous_const))
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, by simp [Λ'.zero_mem]⟩)
  set T : Finset (V ⧸ Λ') :=
    t2.image fun y : tsupport φ => (QuotientAddGroup.mk (y : V) : V ⧸ Λ') with hT
  have hrep : ∀ q ∈ T, ∃ y ∈ tsupport φ, q.out - y ∈ Λ' := by
    intro q hq
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.1 hq
    refine ⟨y, y.2, ?_⟩
    have := Λ'.neg_mem (QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (y : V) : V ⧸ Λ')))
    rwa [neg_add_rev, neg_neg, neg_add_eq_sub] at this
  have hTd : ∀ q ∈ T, ∃ g, HasDens μ f ι ν ({z | z - q.out ∈ Λ'}.indicator fun _ => (1 : ℝ)) g := by
    intro q hq
    obtain ⟨y, hy, hqy⟩ := hrep q hq
    obtain ⟨x, hx, hyx⟩ := hK y hy
    exact hΛxd x q.out (by
      have := (Λx x).add_mem hyx (hΛ'le x hx hqy)
      rwa [show y - (x : V) + (q.out - y) = q.out - x by abel] at this) Λ' hBΛ' hΛ'o hΛ'c
      (hΛ'le x hx)
  choose! gq hgq using hTd
  have hsum := hasDens_sum
    (fun q v => φ (q : V ⧸ Λ').out * {z | z - q.out ∈ Λ'}.indicator (fun _ => (1 : ℝ)) v)
    (fun q b => φ (q : V ⧸ Λ').out * gq q b) T (fun q hq => (hgq q hq).const_mul _)
  have heq : (fun v => ∑ q ∈ T,
      φ (q : V ⧸ Λ').out * {z | z - q.out ∈ Λ'}.indicator (fun _ => (1 : ℝ)) v) = φ := by
    funext x
    have hind : ∀ q : V ⧸ Λ', {z | z - q.out ∈ Λ'}.indicator (fun _ => (1 : ℝ)) x =
        if (x : V ⧸ Λ') = q then 1 else 0 := by
      intro q
      have : x - q.out ∈ Λ' ↔ (x : V ⧸ Λ') = q := by
        conv_rhs => rw [← QuotientAddGroup.out_eq' q]
        rw [eq_comm, QuotientAddGroup.eq, neg_add_eq_sub]
      by_cases hq : (x : V ⧸ Λ') = q
      · rw [if_pos hq, Set.indicator_of_mem (show x ∈ {z | z - q.out ∈ Λ'} from this.2 hq)]
      · rw [if_neg hq, Set.indicator_of_notMem (show x ∉ {z | z - q.out ∈ Λ'} from
          fun h' => hq (this.1 h'))]
    simp only [hind, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
    split_ifs with hxT
    · obtain ⟨y, hy, hqy⟩ := hrep _ hxT
      have e1 := hconst y hy _ hqy
      rw [add_sub_cancel] at e1
      have hxo : x - (x : V ⧸ Λ').out ∈ Λ' := by
        have := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (x : V ⧸ Λ'))
        rwa [neg_add_eq_sub] at this
      have e2 := hconst y hy _ (Λ'.add_mem hxo hqy)
      rw [show y + (x - (x : V ⧸ Λ').out + ((x : V ⧸ Λ').out - y)) = x by abel] at e2
      rw [e1, e2]
    · by_contra hne
      have hxK : x ∈ tsupport φ := subset_tsupport φ (Ne.symm hne)
      obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht2 hxK)
      apply hxT
      refine Finset.mem_image.2 ⟨y, hy, ?_⟩
      exact QuotientAddGroup.eq.2 (by rw [neg_add_eq_sub]; exact hxy)
  rw [heq] at hsum
  exact ⟨_, hsum.2.1, hsum.2.2⟩

end Cos

end PI.VolStabS
