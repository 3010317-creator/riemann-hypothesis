module

public import Mathlib.GroupTheory.Index
public import Mathlib.MeasureTheory.Group.Defs
import Mathlib.Tactic.Linter.HaveILetI
public import Mathlib.MeasureTheory.Group.Measure

@[expose] public section

open Matrix
open scoped Topology Pointwise

namespace GlobalTheory.CompanionTheory.HaarIndex

theorem measure_eq_relIndex_mul : ∀ (G : Type) [AddGroup G] [MeasurableSpace G] [MeasurableAdd G]
    (μ : MeasureTheory.Measure G) [μ.IsAddLeftInvariant] (H K : AddSubgroup G), H ≤ K →
    MeasurableSet (H : Set G) → H.relIndex K ≠ 0 →
    μ (K : Set G) = (H.relIndex K : ENNReal) * μ (H : Set G) := by
  intro G _ _ _ μ _ H K hHK hH hn
  classical
  set H' := H.addSubgroupOf K
  have : H'.FiniteIndex := ⟨hn⟩
  obtain ⟨s, hs, -⟩ := H'.exists_isComplement_left 0
  have hs' : Finite s := hs.finite_left_iff.mpr inferInstance
  have hcover : (K : Set G) = ⋃ a : s, (a.1 : G) +ᵥ (H : Set G) := by
    ext x
    refine ⟨fun hx => ?_, fun hx => ?_⟩
    · obtain ⟨⟨a, y⟩, hxy⟩ := hs.2 ⟨x, hx⟩
      exact Set.mem_iUnion.2 ⟨a, y.1.1, y.2, congrArg Subtype.val hxy⟩
    · rcases Set.mem_iUnion.1 hx with ⟨a, y, hy, hxy⟩
      exact hxy ▸ K.add_mem a.1.2 (hHK hy)
  have hdisj : Pairwise fun a b : s =>
      Disjoint ((a.1 : G) +ᵥ (H : Set G)) ((b.1 : G) +ᵥ (H : Set G)) :=
    fun a b hab => Set.disjoint_left.2 fun _ ⟨y, hy, h1⟩ ⟨z, hz, h2⟩ =>
      hab (Prod.ext_iff.1 (hs.1 (a₁ := (a, ⟨⟨y, hHK hy⟩, hy⟩))
        (a₂ := (b, ⟨⟨z, hHK hz⟩, hz⟩)) (Subtype.ext (h1.trans h2.symm)))).1
  rw [hcover, MeasureTheory.measure_iUnion hdisj fun _ => hH.const_vadd _]
  simp [MeasureTheory.measure_vadd, hs.encard_left, AddSubgroup.relIndex, H']

end GlobalTheory.CompanionTheory.HaarIndex
