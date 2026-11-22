module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FormRightMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardEqRelIndex

@[expose] public section

open NumberField Module Filter

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LIOrb

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem card_quot_inf_ne_zero {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₂ : Submodule.IsFullLattice K M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) ≠ 0 := by
  have card_eq (M N : Submodule (𝓞 K) V) (hM : Submodule.IsLattice K M)
      (hN : Submodule.IsFullLattice K N) :
      Nat.card (↥(locF 𝔭 M) ⧸ (locF 𝔭 M ⊓ locF 𝔭 N).submoduleOf (locF 𝔭 M)) =
        (M ⊓ locF 𝔭 N).toAddSubgroup.relIndex M.toAddSubgroup := by
    have hex : ∃ r : ℕ, ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, (algebraMap (𝓞 F) (𝓞 K)) a • y ∈ locF 𝔭 N := by
      have hp := h𝔭.isPrime
      obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM hN
      have hn' : (n : 𝓞 F) ≠ 0 := by exact_mod_cast hn
      obtain ⟨r, u, hu, hdvd⟩ := D2.exists_mul_dvd h𝔭 hn'
      refine ⟨r, fun a ha y hy => ?_⟩
      rw [LocF.mem_locF_iff hp]
      refine ⟨u, hu, ?_⟩
      obtain ⟨d, hd⟩ := hdvd a ha
      rw [smul_smul, ← map_mul, hd, map_mul, mul_comm, mul_smul, LocF.algebraMap_intCast_smul]
      exact N.smul_mem _ (hnx y hy)
    obtain ⟨r, hr⟩ := hex
    have hpow {a : 𝓞 F} (ha : a ∈ 𝔭 ^ r) {x : V} (hx : x ∈ locF 𝔭 M) :
        (algebraMap (𝓞 F) (𝓞 K)) a • x ∈ locF 𝔭 N := by
      obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime M x).1 hx
      have htx' : (algebraMap (𝓞 F) (𝓞 K)) t • ((algebraMap (𝓞 F) (𝓞 K)) a • x) ∈ locF 𝔭 N := by
        rw [smul_comm]
        exact hr a ha _ htx
      obtain ⟨u, hu, hux⟩ := (LocF.mem_locF_iff h𝔭.isPrime N _).1 htx'
      refine (LocF.mem_locF_iff h𝔭.isPrime N _).2 ⟨u * t, ?_, ?_⟩
      · exact fun hm => (h𝔭.isPrime.mem_or_mem hm).elim hu ht
      · rwa [map_mul, mul_smul]
    set B' := (locF 𝔭 M ⊓ locF 𝔭 N).submoduleOf (locF 𝔭 M) with hB'
    let φ : ↥M →ₗ[𝓞 K] ↥(locF 𝔭 M) ⧸ B' := B'.mkQ ∘ₗ Submodule.inclusion (LocF.le_locF 𝔭 M)
    have hsurj : Function.Surjective φ := by
      intro z
      induction z using Submodule.Quotient.induction_on with
      | H x =>
      obtain ⟨c, hc, hcx⟩ := localizedQuotients.exists_approx h𝔭 M r x.2
      refine ⟨⟨_, hcx⟩, ?_⟩
      simp only [φ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      change ((algebraMap (𝓞 F) (𝓞 K)) c • (x : V) - (x : V)) ∈ locF 𝔭 M ⊓ locF 𝔭 N
      have e : (algebraMap (𝓞 F) (𝓞 K)) c • (x : V) - (x : V) = (algebraMap (𝓞 F) (𝓞 K)) (c - 1) • (x : V) := by
        rw [map_sub, map_one, sub_smul, one_smul]
      rw [e]
      exact Submodule.mem_inf.2 ⟨(locF 𝔭 M).smul_mem _ x.2, hpow hc x.2⟩
    have hker : (LinearMap.ker φ).toAddSubgroup =
        (M ⊓ locF 𝔭 N).toAddSubgroup.addSubgroupOf M.toAddSubgroup := by
      ext y
      rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
      simp only [φ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      change ((y : V) ∈ locF 𝔭 M ⊓ locF 𝔭 N) ↔ (y : V) ∈ M ⊓ locF 𝔭 N
      rw [Submodule.mem_inf, Submodule.mem_inf]
      exact ⟨fun h => ⟨y.2, h.2⟩, fun h => ⟨LocF.le_locF 𝔭 M y.2, h.2⟩⟩
    rw [AddSubgroup.relIndex, AddSubgroup.index, ← hker]
    exact (Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv).symm
  rw [card_eq M₁ M₂ hM₁ hM₂]
  exact IA.relIndex_ne_zero hM₁ hM₂ 𝔭

private theorem isLattice_inf_locF_of_isLattice {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {M N : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M) (hN : Submodule.IsLattice K N) :
    Submodule.IsLattice K (M ⊓ locF 𝔭 N) := by
  refine ⟨?_, ?_⟩
  · have : Module.Finite (𝓞 K) M := Module.Finite.iff_fg.mpr hM.fg
    have : IsNoetherian (𝓞 K) ↥(M ⊓ locF 𝔭 N) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli

private theorem isFullLattice_inf_locF_of_isFullLattice {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {M N : Submodule (𝓞 K) V} (hM : Submodule.IsFullLattice K M) (hN : Submodule.IsFullLattice K N) :
    Submodule.IsFullLattice K (M ⊓ locF 𝔭 N) := by
  obtain ⟨r, hr⟩ := IA.exists_pow_smul h𝔭 hM.toIsLattice hN
  have h0 : 𝔭 ≠ ⊥ := fun h0 =>
    NumberField.RingOfIntegers.not_isField F (Ring.isField_iff_maximal_bot.2 (h0 ▸ h𝔭))
  have hne : 𝔭 ^ r ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot] at h0 ⊢
    exact pow_ne_zero r h0
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  set c : K := algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) a) with hc_def
  have hc : c ≠ 0 := by
    intro hc0
    apply ha0
    apply NumberField.RingOfIntegers.algebraMap.injective F K
    apply NumberField.RingOfIntegers.coe_injective (K := K)
    simpa [hc_def] using hc0
  refine { toIsLattice := isLattice_inf_locF_of_isLattice h𝔭 hM.toIsLattice hN.toIsLattice
           span_eq_top := ?_ }
  rw [eq_top_iff, ← hM.span_eq_top, Submodule.span_le]
  intro y hy
  have hmem : algebraMap (𝓞 F) (𝓞 K) a • y ∈ M ⊓ locF 𝔭 N := ⟨M.smul_mem _ hy, hr a ha y hy⟩
  have ey : y = c⁻¹ • (algebraMap (𝓞 F) (𝓞 K) a • y) := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) a) y, ← hc_def, smul_smul, inv_mul_cancel₀ hc,
      one_smul]
  rw [SetLike.mem_coe, ey]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)


theorem card_quot_inf_mul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsFullLattice K M₁)
    (hM₁i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₁) (hM₂ : Submodule.IsFullLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₁) 𝔭 =
      Nat.card (↥(locF 𝔭 M₂) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₂)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₂) 𝔭 := by
  have card_eq (M N : Submodule (𝓞 K) V) (hM : Submodule.IsLattice K M)
      (hN : Submodule.IsFullLattice K N) :
      Nat.card (↥(locF 𝔭 M) ⧸ (locF 𝔭 M ⊓ locF 𝔭 N).submoduleOf (locF 𝔭 M)) =
        (M ⊓ locF 𝔭 N).toAddSubgroup.relIndex M.toAddSubgroup := by
    have hex : ∃ r : ℕ, ∀ a ∈ 𝔭 ^ r, ∀ y ∈ M, (algebraMap (𝓞 F) (𝓞 K)) a • y ∈ locF 𝔭 N := by
      have hp := h𝔭.isPrime
      obtain ⟨n, hn, hnx⟩ := LocF.exists_zsmul_le hM hN
      have hn' : (n : 𝓞 F) ≠ 0 := by exact_mod_cast hn
      obtain ⟨r, u, hu, hdvd⟩ := D2.exists_mul_dvd h𝔭 hn'
      refine ⟨r, fun a ha y hy => ?_⟩
      rw [LocF.mem_locF_iff hp]
      refine ⟨u, hu, ?_⟩
      obtain ⟨d, hd⟩ := hdvd a ha
      rw [smul_smul, ← map_mul, hd, map_mul, mul_comm, mul_smul, LocF.algebraMap_intCast_smul]
      exact N.smul_mem _ (hnx y hy)
    obtain ⟨r, hr⟩ := hex
    have hpow {a : 𝓞 F} (ha : a ∈ 𝔭 ^ r) {x : V} (hx : x ∈ locF 𝔭 M) :
        (algebraMap (𝓞 F) (𝓞 K)) a • x ∈ locF 𝔭 N := by
      obtain ⟨t, ht, htx⟩ := (LocF.mem_locF_iff h𝔭.isPrime M x).1 hx
      have htx' : (algebraMap (𝓞 F) (𝓞 K)) t • ((algebraMap (𝓞 F) (𝓞 K)) a • x) ∈ locF 𝔭 N := by
        rw [smul_comm]
        exact hr a ha _ htx
      obtain ⟨u, hu, hux⟩ := (LocF.mem_locF_iff h𝔭.isPrime N _).1 htx'
      refine (LocF.mem_locF_iff h𝔭.isPrime N _).2 ⟨u * t, ?_, ?_⟩
      · exact fun hm => (h𝔭.isPrime.mem_or_mem hm).elim hu ht
      · rwa [map_mul, mul_smul]
    set B' := (locF 𝔭 M ⊓ locF 𝔭 N).submoduleOf (locF 𝔭 M) with hB'
    let φ : ↥M →ₗ[𝓞 K] ↥(locF 𝔭 M) ⧸ B' := B'.mkQ ∘ₗ Submodule.inclusion (LocF.le_locF 𝔭 M)
    have hsurj : Function.Surjective φ := by
      intro z
      induction z using Submodule.Quotient.induction_on with
      | H x =>
      obtain ⟨c, hc, hcx⟩ := localizedQuotients.exists_approx h𝔭 M r x.2
      refine ⟨⟨_, hcx⟩, ?_⟩
      simp only [φ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      change ((algebraMap (𝓞 F) (𝓞 K)) c • (x : V) - (x : V)) ∈ locF 𝔭 M ⊓ locF 𝔭 N
      have e : (algebraMap (𝓞 F) (𝓞 K)) c • (x : V) - (x : V) = (algebraMap (𝓞 F) (𝓞 K)) (c - 1) • (x : V) := by
        rw [map_sub, map_one, sub_smul, one_smul]
      rw [e]
      exact Submodule.mem_inf.2 ⟨(locF 𝔭 M).smul_mem _ x.2, hpow hc x.2⟩
    have hker : (LinearMap.ker φ).toAddSubgroup =
        (M ⊓ locF 𝔭 N).toAddSubgroup.addSubgroupOf M.toAddSubgroup := by
      ext y
      rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup, LinearMap.mem_ker]
      simp only [φ, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
        Submodule.Quotient.mk_eq_zero]
      change ((y : V) ∈ locF 𝔭 M ⊓ locF 𝔭 N) ↔ (y : V) ∈ M ⊓ locF 𝔭 N
      rw [Submodule.mem_inf, Submodule.mem_inf]
      exact ⟨fun h => ⟨y.2, h.2⟩, fun h => ⟨LocF.le_locF 𝔭 M y.2, h.2⟩⟩
    rw [AddSubgroup.relIndex, AddSubgroup.index, ← hker]
    exact (Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv).symm
  have e₁ := card_eq M₁ M₂ hM₁.toIsLattice hM₂
  have e₂ := card_eq M₂ M₁ hM₂.toIsLattice hM₁
  rw [inf_comm (locF 𝔭 M₂) (locF 𝔭 M₁)] at e₂

  have hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h (M₁ ⊓ locF 𝔭 M₂) := fun x hx y hy => hM₁i x hx.1 y hy.1
  have hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h (M₂ ⊓ locF 𝔭 M₁) := fun x hx y hy => hM₂i x hx.1 y hy.1
  have hvA := vd_locF hK hF hs hd (isFullLattice_inf_locF_of_isFullLattice h𝔭 hM₁ hM₂) hAi h𝔭
  have hvB := vd_locF hK hF hs hd (isFullLattice_inf_locF_of_isFullLattice h𝔭 hM₂ hM₁) hBi h𝔭
  rw [IA.locF_inf 𝔭 h𝔭.isPrime] at hvA hvB
  have hAB : vd h (M₁ ⊓ locF 𝔭 M₂) 𝔭 = vd h (M₂ ⊓ locF 𝔭 M₁) 𝔭 := by
    rw [← hvA, ← hvB, inf_comm]
  rw [e₁, e₂, vd_locF hK hF hs hd hM₁ hM₁i h𝔭, vd_locF hK hF hs hd hM₂ hM₂i h𝔭,
    IA.vd_mul hF hK hs hd hM₁ hM₁i hM₂ h𝔭, IA.vd_mul hF hK hs hd hM₂ hM₂i hM₁ h𝔭, hAB]

end Formalism.HermitianLattices.Ext.L3.LIOrb
