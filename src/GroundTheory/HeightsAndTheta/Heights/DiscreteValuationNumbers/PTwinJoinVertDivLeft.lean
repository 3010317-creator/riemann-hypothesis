module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerLast
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.IsVerticalDivOfIsVerticalDivisorAlt

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (joinCoord mcIdeal mcMap assocDeg assocVar joinCoord_assocVar IsVertDiv)

noncomputable section

namespace JoinVerticalDivisorLeft

variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type} {ι₂ : K₂ → Type}

theorem assocVar_fst (p : Σ k : K ⊕ K', Sum.elim ι ι' k) :
    (assocVar ι₂ p).1 = Sum.map id Sum.inl p.1 := by
  obtain ⟨k | k, i⟩ := p <;> rfl

theorem assocBlock_injective :
    Function.Injective (Sum.map id Sum.inl : K ⊕ K' → K ⊕ (K' ⊕ K₂)) :=
  Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩

variable [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)]


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem mcMap_rename_assocVar (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    mcMap R (joinCoord x (joinCoord z w)) (rename (assocVar ι₂) h) =
      rename (Sum.map id Sum.inl) (mcMap R (joinCoord x z) h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [mcMap, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, rename_X, hp]
    congr 1
    simp [mcMap, joinCoord_assocVar, assocVar_fst]


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem rename_assocVar_mem_mcIdeal_iff (R : Type) [CommRing R] {Ω : Type} [Field Ω] [Algebra R Ω]
    (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) (w : (Σ k, ι₂ k) → Ω)
    (h : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R) :
    rename (assocVar ι₂) h ∈ mcIdeal R (joinCoord x (joinCoord z w)) ↔ h ∈ mcIdeal R (joinCoord x z) := by
  simp only [mcIdeal, RingHom.mem_ker]
  rw [mcMap_rename_assocVar]
  exact map_eq_zero_iff _ (rename_injective _ assocBlock_injective)


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem blockWeight_assocVar [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (p : Σ k : K ⊕ K', Sum.elim ι ι' k) (s : K ⊕ (K' ⊕ K₂)) :
    blockWeight (Sum.elim ι (Sum.elim ι' ι₂)) (assocVar ι₂ p) s =
      Sum.elim (fun k => blockWeight (Sum.elim ι ι') p (.inl k))
        (Sum.elim (fun k => blockWeight (Sum.elim ι ι') p (.inr k)) 0) s := by
  obtain ⟨k | k, i⟩ := p <;> rcases s with l | l | l <;> simp [blockWeight, assocVar, Pi.single_apply]


omit [Fintype K] [Fintype K'] [Fintype K₂] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  [∀ k, Fintype (ι₂ k)] in
theorem weight_mapDomain_assocVar [DecidableEq K] [DecidableEq K'] [DecidableEq K₂]
    (d : (Σ k : K ⊕ K', Sum.elim ι ι' k) →₀ ℕ) :
    Finsupp.weight (blockWeight (Sum.elim ι (Sum.elim ι' ι₂))) (Finsupp.mapDomain (assocVar ι₂) d) =
      Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inl k))
        (Sum.elim (fun k => Finsupp.weight (blockWeight (Sum.elim ι ι')) d (.inr k)) 0) := by
  rw [Finsupp.weight_apply, Finsupp.sum_mapDomain_index (by simp) (by intros; simp [add_smul]),
    Finsupp.weight_apply]
  funext s
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, blockWeight_assocVar]
  rcases s with l | l | l <;> simp


theorem isMultiHomog_rename_assocVar {R : Type} [CommRing R]
    {f : MvPolynomial (Σ k : K ⊕ K', Sum.elim ι ι' k) R} {a : K ⊕ K' → ℕ}
    (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (assocVar ι₂) f)
      (Sum.elim (fun k => a (.inl k)) (Sum.elim (fun k => a (.inr k)) 0)) := by
  classical
  rw [← Objects.isMultiHomog_iff] at hf ⊢
  exact Objects.isMultiHomog_rename_of_weight
    (E := fun b => Sum.elim (fun k => b (.inl k)) (Sum.elim (fun k => b (.inr k)) 0))
    (weight_mapDomain_assocVar (ι₂ := ι₂)) hf

theorem comap_isMultiProjPrime {R : Type} [CommRing R]
    {Q : Ideal (MvPolynomial (Σ k : K ⊕ (K' ⊕ K₂), Sum.elim ι (Sum.elim ι' ι₂) k) R)}
    (hQ : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime Q) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂))) := by
  classical
  refine Objects.comap_isMultiProjPrime_of_rename
    (E := fun a => Sum.elim (fun k => a (.inl k)) (Sum.elim (fun k => a (.inr k)) 0))
    (fun a b e => funext fun k => by rcases k with k | k; exact congrFun e (.inl k); exact congrFun e (.inr (.inl k)))
    (fun _ _ hf => Objects.isMultiHomog_rename_of_weight
      (E := fun b => Sum.elim (fun k => b (.inl k)) (Sum.elim (fun k => b (.inr k)) 0))
      (weight_mapDomain_assocVar (ι₂ := ι₂)) hf) hQ ?_
  rintro (k | k)
  · exact hQ.2.2 (.inl k)
  · exact hQ.2.2 (.inr (.inl k))

end JoinVerticalDivisorLeft


open JoinVerticalDivisorLeft in
theorem JoinVerticalDivisorLeft.proof : JoinVerticalDivisorLeft.Statement := by
  intro O _ _ _ Ω _ _ K _ ι _ x K' _ ι' _ z K₂ _ ι₂ _ w b f g hD
  obtain ⟨⟨α, β, hf, hg, hb⟩, hfP, hgP, hU⟩ := hD
  refine ⟨⟨_, _, isMultiHomog_rename_assocVar (ι₂ := ι₂) hf, isMultiHomog_rename_assocVar (ι₂ := ι₂) hg, ?_⟩,
    ?_, ?_, ?_⟩
  · rintro (k | k | k)
    · simpa [assocDeg] using hb (.inl k)
    · simpa [assocDeg] using hb (.inr k)
    · simp [assocDeg]
  · rwa [rename_assocVar_mem_mcIdeal_iff]
  · rwa [rename_assocVar_mem_mcIdeal_iff]
  · intro Q hQ hPQ hQO
    have hle : mcIdeal O (joinCoord x z) ≤ Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂)) :=
      fun h hh => Ideal.mem_comap.mpr (hPQ ((rename_assocVar_mem_mcIdeal_iff O x z w h).mpr hh))
    have hO : (Q.comap (rename (assocVar (ι := ι) (ι' := ι') ι₂))).comap
        (C : O →+* ReciprocityTheory.ChartRestriction.G.Geo.MRingOver O (Sum.elim ι ι')) = ⊥ := by
      rw [eq_bot_iff] at hQO ⊢
      intro c hc
      apply hQO
      simpa [Ideal.mem_comap, rename_C] using hc
    obtain ⟨u, v, ⟨γ, hu⟩, ⟨δ, hv⟩, huQ, hvQ, huv⟩ := hU _ (comap_isMultiProjPrime hQ) hle hO
    refine ⟨rename (assocVar ι₂) u, rename (assocVar ι₂) v, ⟨_, isMultiHomog_rename_assocVar hu⟩,
      ⟨_, isMultiHomog_rename_assocVar hv⟩, huQ, hvQ, ?_⟩
    have := (rename_assocVar_mem_mcIdeal_iff O x z w _).mpr huv
    simpa only [map_sub, map_mul] using this

end

end GroundTheory.Heights₂.Heights.NumbersDVR
