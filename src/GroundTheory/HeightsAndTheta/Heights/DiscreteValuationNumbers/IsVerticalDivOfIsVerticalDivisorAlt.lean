module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace Objects

section Ring

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R]

theorem weight_blockWeight_apply (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype m (fun i c => c • blockWeight ι i) (fun i => zero_smul ℕ _),
    Finset.sum_apply, Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

theorem isMultiHomog_iff (f : MRing ι R) (b : K → ℕ) :
    IsMultiHomog f b ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b := by
  constructor
  · intro h m hm k
    rw [← weight_blockWeight_apply, h (mem_support_iff.mp hm)]
  · intro h m hm
    funext k
    rw [weight_blockWeight_apply, h m (mem_support_iff.mpr hm) k]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_iff (I : Ideal (MRing ι R)) :
    IsMultiHomogIdeal I ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal I := by
  classical
  constructor
  · intro h
    refine ⟨{x | x ∈ I ∧ ∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog x a}, fun f hf => hf.2, ?_⟩
    refine le_antisymm (fun f hf => ?_) (Ideal.span_le.mpr fun x hx => hx.1)
    rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    refine Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨h f hf b, b, ?_⟩
    exact (isMultiHomog_iff _ b).mp (weightedHomogeneousComponent_isWeightedHomogeneous b f)
  · rintro ⟨S, hS, rfl⟩ f hf b
    have hI : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by
      refine Ideal.homogeneous_span _ _ fun x hx => ?_
      obtain ⟨a, ha⟩ := hS x hx
      exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((isMultiHomog_iff x a).mpr ha)⟩
    exact weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) hI hf b

theorem isMultiProjPrime_iff (P : Ideal (MRing ι R)) :
    IsMultiProjPrime P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P :=
  ⟨fun h => ⟨h.isPrime, (isMultiHomogIdeal_iff P).mp h.multiHomog, h.relevant⟩,
    fun h => ⟨h.1, (isMultiHomogIdeal_iff P).mpr h.2.1, h.2.2⟩⟩

end Ring

section Rename

variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {ι : K → Type*} {ι' : K' → Type*}
  {R : Type*} [CommRing R]

theorem isMultiHomog_rename_of_weight {v : (Σ k, ι k) → (Σ k', ι' k')} {E : (K → ℕ) → (K' → ℕ)}
    (hw : ∀ d : (Σ k, ι k) →₀ ℕ,
      Finsupp.weight (blockWeight ι') (Finsupp.mapDomain v d) = E (Finsupp.weight (blockWeight ι) d))
    {f : MRing ι R} {a : K → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (rename v f) (E a) := by
  unfold IsMultiHomog at hf ⊢
  induction hf using IsWeightedHomogeneous.induction_on with
  | zero => simpa using isWeightedHomogeneous_zero R _ _
  | add p q _ _ ihp ihq => simpa [map_add (f := _)] using ihp.add ihq
  | monomial d r hr =>
    rw [rename_monomial]
    exact isWeightedHomogeneous_monomial _ _ _ (by rw [hw, hr])

theorem rename_weightedHomogeneousComponent_of_isMultiHomog {v : (Σ k, ι k) → (Σ k', ι' k')}
    {E : (K → ℕ) → (K' → ℕ)} (hE : Function.Injective E)
    (hm : ∀ (f : MRing ι R) (a : K → ℕ), IsMultiHomog f a → IsMultiHomog (rename v f) (E a))
    (b : K → ℕ) (h : MRing ι R) :
    rename v (weightedHomogeneousComponent (blockWeight ι) b h) =
      weightedHomogeneousComponent (blockWeight ι') (E b) (rename v h) := by
  induction h using MvPolynomial.induction_on' with
  | monomial d r =>
    have h1 : IsMultiHomog (monomial d r : MRing ι R) (Finsupp.weight (blockWeight ι) d) :=
      isWeightedHomogeneous_monomial _ _ _ rfl
    have h2 := hm _ _ h1
    by_cases hb : b = Finsupp.weight (blockWeight ι) d
    · subst hb
      rw [IsWeightedHomogeneous.weightedHomogeneousComponent_same h1,
        IsWeightedHomogeneous.weightedHomogeneousComponent_same h2]
    · rw [IsWeightedHomogeneous.weightedHomogeneousComponent_ne b h1 hb,
        IsWeightedHomogeneous.weightedHomogeneousComponent_ne _ h2 (fun e => hb (hE e)), map_zero]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]

theorem comap_isMultiProjPrime_of_rename [Fintype K] [Fintype K'] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
    {v : (Σ k, ι k) → (Σ k', ι' k')} {E : (K → ℕ) → (K' → ℕ)} (hE : Function.Injective E)
    (hm : ∀ (f : MRing ι R) (a : K → ℕ), IsMultiHomog f a → IsMultiHomog (rename v f) (E a))
    {Q : Ideal (MRing ι' R)} (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q)
    (hrel : ∀ k, ∃ i : ι k, (X (v ⟨k, i⟩) : MRing ι' R) ∉ Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename v)) := by
  rw [← isMultiProjPrime_iff] at hQ ⊢
  have := hQ.isPrime
  refine ⟨Ideal.comap_isPrime _ Q, fun h hh b => ?_, fun k => ?_⟩
  · rw [Ideal.mem_comap] at hh ⊢
    rw [rename_weightedHomogeneousComponent_of_isMultiHomog hE hm]
    exact hQ.multiHomog _ hh _
  · obtain ⟨i, hi⟩ := hrel k
    exact ⟨i, by rw [Ideal.mem_comap, rename_X]; exact hi⟩

end Rename

end Objects

end

end GroundTheory.Heights₂.Heights.NumbersDVR
