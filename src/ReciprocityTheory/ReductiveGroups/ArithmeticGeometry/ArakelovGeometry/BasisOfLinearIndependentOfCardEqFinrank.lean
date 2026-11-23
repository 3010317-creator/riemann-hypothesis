module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ProjectiveFrameCoordNeZero

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Polynomial Module

variable {Ω : Type*} [Field Ω] [CharZero Ω] {κ : Type*} {D : ℕ}

theorem closure_mem (x : κ → Ω) (e : Fin (D + 1) → κ) (m : Ω)
    (hm : m ∈ Submonoid.closure (Set.range fun i => x i / x (e 0))) :
    ∃ d, ∃ s ∈ sec ℤ x d, m = s / x (e 0) ^ d := by
  induction hm using Submonoid.closure_induction with
  | mem _ hy =>
    obtain ⟨i, rfl⟩ := hy
    exact ⟨1, x i, (mem_sec_iff x 1 _).2 ⟨MvPolynomial.X i, MvPolynomial.isHomogeneous_X ℤ i, by simp⟩,
      by rw [pow_one]⟩
  | one =>
    exact ⟨0, 1, (mem_sec_iff x 0 _).2 ⟨1, MvPolynomial.isHomogeneous_one κ ℤ, by simp⟩, by simp⟩
  | mul _ _ _ _ ha hb =>
    obtain ⟨d1, s1, hs1, rfl⟩ := ha
    obtain ⟨d2, s2, hs2, rfl⟩ := hb
    exact ⟨d1 + d2, s1 * s2, mul_mem_sec x hs1 hs2, by rw [div_mul_div_comm, pow_add]⟩

theorem exists_indep_sections' [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ)
    (h : IsRatProjFrame x e) :
    ∃ (k : ℕ) (ε : Fin (projDeg x e) → Ω), (∀ l, ε l ∈ sec ℤ x k) ∧
      LinearIndependent (fnField (x ∘ e)) ε := by
  classical
  have := finiteDimensional_ext x e h
  have hne : x (e 0) ≠ 0 := projective_frame_coord_ne_zero x e h
  let T : Set Ω := Submonoid.closure (Set.range fun i => x i / x (e 0))
  have hTL : ∀ z ∈ T, z ∈ IntermediateField.extendScalars (fnField_comp_le' x e) := fun z hz => by
    obtain ⟨d, σ, hσ, rfl⟩ := closure_mem x e z hz
    exact sec_div_mem x (e 0) hσ
  let s : Set (IntermediateField.extendScalars (fnField_comp_le' x e)) := {z | (z : Ω) ∈ T}
  have hspan : Submodule.span (fnField (x ∘ e)) s = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    have hz : (z : Ω) ∈ (IntermediateField.adjoin (fnField (x ∘ e))
        (Set.range fun i => x i / x (e 0))).toSubalgebra := by
      rw [← fnField_eq_adjoin x e hne]; exact z.2
    rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic
      (by rintro _ ⟨i, rfl⟩; exact (div_isIntegral x e h i).isAlgebraic)] at hz
    have hz' : (z : Ω) ∈ Subalgebra.toSubmodule (Algebra.adjoin (fnField (x ∘ e))
        (Set.range fun i => x i / x (e 0))) := hz
    rw [Algebra.adjoin_eq_span] at hz'
    have hmap : Submodule.span (fnField (x ∘ e)) T = (Submodule.span (fnField (x ∘ e)) s).map
        (IntermediateField.val (IntermediateField.extendScalars (fnField_comp_le' x e))).toLinearMap := by
      rw [Submodule.map_span]
      exact congrArg _ (Set.ext fun w => ⟨fun hw => ⟨⟨w, hTL w hw⟩, hw, rfl⟩,
        by rintro ⟨w', hw', rfl⟩; exact hw'⟩)
    obtain ⟨w, hw, hwz⟩ := hmap ▸ hz'
    rwa [← Subtype.ext hwz]
  obtain ⟨b, hbs, hbspan, hbli⟩ := exists_linearIndependent (fnField (x ∘ e)) s
  let B := Basis.mk hbli (by rw [Subtype.range_coe, hbspan, hspan])
  have : Finite b := Module.Finite.finite_basis B
  let : Fintype b := Fintype.ofFinite b
  let eqv : Fin (projDeg x e) ≃ b :=
    (Fintype.equivFinOfCardEq (by rw [projDeg_eq, Module.finrank_eq_card_basis B])).symm
  choose d σ hσ hdeq using fun j => closure_mem x e _ (hbs (eqv j).2)
  let k := Finset.univ.sup d
  have hdk : ∀ j, d j ≤ k := fun j => Finset.le_sup (Finset.mem_univ j)
  refine ⟨k, fun j => σ j * x (e 0) ^ (k - d j), fun j => ?_, ?_⟩
  · simpa [Nat.add_sub_of_le (hdk j)] using mul_mem_sec x (hσ j) ((mem_sec_iff x (k - d j) _).2
      ⟨MvPolynomial.X (e 0) ^ (k - d j),
        by simpa using (MvPolynomial.isHomogeneous_X ℤ (e 0)).pow (k - d j), by simp⟩)
  · have hli1 : LinearIndependent (fnField (x ∘ e))
        (fun j => (((eqv j : b) : IntermediateField.extendScalars (fnField_comp_le' x e)) : Ω)) :=
      (hbli.comp eqv eqv.injective).map'
        (IntermediateField.val (IntermediateField.extendScalars (fnField_comp_le' x e))).toLinearMap
        (LinearMap.ker_eq_bot.2 Subtype.val_injective)
    have hli2 := hli1.map' (LinearMap.mulRight (fnField (x ∘ e)) (x (e 0) ^ k))
      (LinearMap.ker_eq_bot.2 (mul_left_injective₀ (pow_ne_zero k hne)))
    convert hli2 using 1
    funext j
    simp only [Function.comp_apply, LinearMap.mulRight_apply, hdeq j]
    have hc := pow_ne_zero (d j) hne
    rw [show x (e 0) ^ k = x (e 0) ^ d j * x (e 0) ^ (k - d j) by
      rw [← pow_add, Nat.add_sub_of_le (hdk j)]]
    field_simp

theorem eq_zero_of_trace [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsRatProjFrame x e)
    {k : ℕ} (ε : Fin (projDeg x e) → Ω) (hε : ∀ l, ε l ∈ sec ℤ x k)
    (hli : LinearIndependent (fnField (x ∘ e)) ε)
    (t : IntermediateField.extendScalars (fnField_comp_le' x e))
    (h0 : ∀ l, Algebra.trace (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))
      (t * ⟨ε l / x (e 0) ^ k, sec_div_mem x (e 0) (hε l)⟩) = 0) : t = 0 := by
  classical
  have := finiteDimensional_ext x e h
  have hne : x (e 0) ≠ 0 := projective_frame_coord_ne_zero x e h
  let b : Fin (projDeg x e) → IntermediateField.extendScalars (fnField_comp_le' x e) :=
    fun j => ⟨ε j / x (e 0) ^ k, sec_div_mem x (e 0) (hε j)⟩
  have hb : LinearIndependent (fnField (x ∘ e)) b := by
    apply LinearIndependent.of_comp (IntermediateField.val _).toLinearMap
    convert hli.map' (LinearMap.mulRight (fnField (x ∘ e)) ((x (e 0) ^ k)⁻¹))
      (LinearMap.ker_eq_bot.2 (mul_left_injective₀ (inv_ne_zero (pow_ne_zero k hne)))) using 1
    funext j; exact div_eq_mul_inv _ _
  have hrank : Fintype.card (Fin (projDeg x e)) =
      Module.finrank (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e)) := by
    rw [Fintype.card_fin, projDeg_eq]
  have : Nonempty (Fin (projDeg x e)) := ⟨⟨0, projDeg_pos' x e h⟩⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hb hrank
  refine (traceForm_nondegenerate (fnField (x ∘ e))
    (IntermediateField.extendScalars (fnField_comp_le' x e))).1 t fun n => ?_
  rw [Algebra.traceForm_apply, ← B.sum_repr n, Finset.mul_sum, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [mul_smul_comm, map_smul, coe_basisOfLinearIndependentOfCardEqFinrank, h0 j, smul_zero]

def chartGen (x : κ → Ω) (e : Fin (D + 1) → κ) (l : Fin (D + 1)) (k : {k // k ≠ l}) :
    fnField (x ∘ e) :=
  ⟨x (e k) / x (e l), div_mem_fnField (x ∘ e) k l⟩

def chartRing (x : κ → Ω) (e : Fin (D + 1) → κ) (l : Fin (D + 1)) : Subalgebra ℤ (fnField (x ∘ e)) :=
  Algebra.adjoin ℤ (Set.range (chartGen x e l))

theorem chartGen_indep (x : κ → Ω) (e : Fin (D + 1) → κ) (hfree : coordIdeal ℤ (x ∘ e) = ⊥)
    (l : Fin (D + 1)) : AlgebraicIndependent ℤ (chartGen x e l) := by
  classical
  have hne : x (e l) ≠ 0 := coord_ne_zero (x ∘ e) hfree l
  have hform : ∀ (F : MvPolynomial (Fin (D + 1)) ℤ) (n : ℕ), F.IsHomogeneous n →
      coneMap ℤ (x ∘ e) F = Polynomial.C (MvPolynomial.aeval (x ∘ e) F) * Polynomial.X ^ n := by
    intro F n hF
    unfold coneMap
    rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq',
      MvPolynomial.eval₂_eq', map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdeg : ∑ i, d i = n := by
      rw [← hF (MvPolynomial.mem_support_iff.1 hd), Finsupp.weight_apply,
        Finsupp.sum_fintype _ _ (by simp)]
      simp
    rw [← hdeg]
    simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, eq_intCast, map_mul,
      map_prod, map_pow, map_intCast]
    ring
  rw [algebraicIndependent_iff_injective_aeval, injective_iff_map_eq_zero]
  intro P hP
  have hPΩ : MvPolynomial.aeval (fun k : {k // k ≠ l} => x (e k) / x (e l)) P = 0 := by
    have h1 := congrArg ((fnField (x ∘ e)).val.restrictScalars ℤ) hP
    rwa [map_zero, ← AlgHom.comp_apply, MvPolynomial.comp_aeval] at h1
  set Q := MvPolynomial.rename (Subtype.val : {k // k ≠ l} → Fin (D + 1)) P with hQ
  set H : MvPolynomial (Fin (D + 1)) ℤ := ∑ n ∈ Finset.range (Q.totalDegree + 1),
      MvPolynomial.homogeneousComponent n Q * MvPolynomial.X l ^ (Q.totalDegree - n) with hH
  have hHhom : H.IsHomogeneous Q.totalDegree :=
    MvPolynomial.IsHomogeneous.sum _ _ _ fun n hn => by
      simpa [Nat.add_sub_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))] using
        (MvPolynomial.homogeneousComponent_isHomogeneous n Q).mul
          ((MvPolynomial.isHomogeneous_X ℤ l).pow (Q.totalDegree - n))
  have hterm : ∀ n ∈ Finset.range (Q.totalDegree + 1),
      MvPolynomial.aeval (x ∘ e) (MvPolynomial.homogeneousComponent n Q *
        MvPolynomial.X l ^ (Q.totalDegree - n)) =
      x (e l) ^ Q.totalDegree *
        MvPolynomial.aeval (fun i => (x ∘ e) i / x (e l)) (MvPolynomial.homogeneousComponent n Q) := by
    intro n hn
    have hn' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
    have hdeh : MvPolynomial.aeval (fun i => (x ∘ e) i / x (e l)) (MvPolynomial.homogeneousComponent n Q) =
        MvPolynomial.aeval (x ∘ e) (MvPolynomial.homogeneousComponent n Q) / x (e l) ^ n := by
      simpa [div_eq_inv_mul, inv_pow, div_eq_mul_inv, mul_comm] using
        aeval_smul_homog (MvPolynomial.homogeneousComponent_isHomogeneous n Q) (x (e l))⁻¹ (x ∘ e)
    rw [map_mul, map_pow, MvPolynomial.aeval_X, hdeh]
    conv_rhs => rw [← Nat.add_sub_of_le hn', pow_add]
    have hc := pow_ne_zero n hne
    simp only [Function.comp_apply]
    field_simp
  have hHy : MvPolynomial.aeval (x ∘ e) H = 0 := by
    rw [hH, map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← map_sum,
      MvPolynomial.sum_homogeneousComponent, hQ, MvPolynomial.aeval_rename]
    exact mul_eq_zero_of_right _ hPΩ
  have hH0 : H = 0 := by
    have hk : H ∈ coordIdeal ℤ (x ∘ e) := by
      rw [coordIdeal, RingHom.mem_ker, hform H _ hHhom, hHy, map_zero, zero_mul]
    rwa [hfree, Ideal.mem_bot] at hk
  have hψ : (MvPolynomial.aeval fun k => if k = l then (1 : MvPolynomial (Fin (D + 1)) ℤ)
      else MvPolynomial.X k).comp (MvPolynomial.rename Subtype.val) =
      MvPolynomial.rename (R := ℤ) (Subtype.val : {k // k ≠ l} → Fin (D + 1)) :=
    MvPolynomial.algHom_ext fun k => by simp [k.2]
  have h4 := congrArg (MvPolynomial.aeval fun k => if k = l then (1 : MvPolynomial (Fin (D + 1)) ℤ)
      else MvPolynomial.X k) hH0
  rw [hH, map_sum, map_zero] at h4
  simp only [map_mul, map_pow, MvPolynomial.aeval_X, ↓reduceIte, one_pow, mul_one] at h4
  rw [← map_sum, MvPolynomial.sum_homogeneousComponent, hQ, ← AlgHom.comp_apply, hψ] at h4
  exact MvPolynomial.rename_injective _ Subtype.val_injective (h4.trans (map_zero _).symm)

theorem chartRing_closed (x : κ → Ω) (e : Fin (D + 1) → κ) (hfree : coordIdeal ℤ (x ∘ e) = ⊥)
    (l : Fin (D + 1)) : IsIntegrallyClosed (chartRing x e l) := by
  unfold chartRing
  have : UniqueFactorizationMonoid (Algebra.adjoin ℤ (Set.range (chartGen x e l))) :=
    (chartGen_indep x e hfree l).aevalEquiv.toMulEquiv.uniqueFactorizationMonoid inferInstance
  exact UniqueFactorizationMonoid.instIsIntegrallyClosed

theorem chartRing_frac (x : κ → Ω) (e : Fin (D + 1) → κ) (hfree : coordIdeal ℤ (x ∘ e) = ⊥)
    (l : Fin (D + 1)) : IsFractionRing (chartRing x e l) (fnField (x ∘ e)) := by
  classical
  have hne : ∀ i, x (e i) ≠ 0 := coord_ne_zero (x ∘ e) hfree
  let R : Subring Ω := ((chartRing x e l).toSubring).map (fnField (x ∘ e)).val.toRingHom
  let T : Set Ω := Set.range fun k : {k // k ≠ l} => x (e k) / x (e l)
  have hTR : Subring.closure T ≤ R := by
    rw [Subring.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨chartGen x e l k, Algebra.subset_adjoin ⟨k, rfl⟩, rfl⟩
  let F : IntermediateField ℚ Ω := (Subfield.closure T).toIntermediateField fun q => by
    rw [eq_ratCast]; exact SubfieldClass.ratCast_mem _ q
  have hgen : ∀ i, x (e i) / x (e l) ∈ Subfield.closure T := fun i =>
    if h : i = l then h ▸ (div_self (hne i)).symm ▸ one_mem _
    else Subfield.subset_closure ⟨⟨i, h⟩, rfl⟩
  have hle : fnField (x ∘ e) ≤ F := by
    unfold fnField
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, j, rfl⟩
    simp only [Function.comp_apply]
    rw [show x (e i) / x (e j) = x (e i) / x (e l) / (x (e j) / x (e l)) from
      (div_div_div_cancel_right₀ (hne l) _ _).symm]
    exact div_mem (hgen i) (hgen j)
  have hinj : Function.Injective (algebraMap (chartRing x e l) (fnField (x ∘ e))) :=
    Subtype.val_injective
  refine ⟨fun ⟨b, hb⟩ => IsUnit.mk0 _ ((map_ne_zero_iff _ hinj).2 (nonZeroDivisors.ne_zero hb)),
    fun z => ?_, fun h => ⟨1, by simp [hinj h]⟩⟩
  obtain ⟨p, hp, q, hq, hpq⟩ := Subfield.mem_closure_iff.1 (hle z.2)
  obtain ⟨a, ha, hap⟩ := hTR hp
  obtain ⟨b, hb, hbq⟩ := hTR hq
  by_cases hq0 : q = 0
  · refine ⟨⟨0, ⟨1, mem_nonZeroDivisors_of_ne_zero one_ne_zero⟩⟩, Subtype.ext ?_⟩
    simp [← hpq, hq0]
  · refine ⟨⟨⟨a, ha⟩, ⟨⟨b, hb⟩, mem_nonZeroDivisors_of_ne_zero fun hb0 =>
        hq0 (hbq.symm.trans (by have hb' : b = 0 := congrArg Subtype.val hb0; rw [hb', map_zero]))⟩⟩,
      Subtype.ext ?_⟩
    show (z : Ω) * (b : Ω) = (a : Ω)
    have ha' : (a : Ω) = p := hap
    have hb' : (b : Ω) = q := hbq
    rw [ha', hb', ← hpq, div_mul_cancel₀ _ hq0]

theorem coord_div_isIntegral (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e)
    (l : Fin (D + 1)) (i : κ) : IsIntegral (chartRing x e l) (x i / x (e l)) := by
  classical
  have hne : x (e l) ≠ 0 := coord_ne_zero (x ∘ e) h.free l
  let R : Subring Ω := ((chartRing x e l).toSubring).map (fnField (x ∘ e)).val.toRingHom
  let ψ : Polynomial Ω →+* Ω := Polynomial.evalRingHom (x (e l))⁻¹
  have hev : ∀ q : MvPolynomial (Fin (D + 1)) ℤ,
      ψ (coneMap ℤ (x ∘ e) q) = MvPolynomial.aeval (fun k => x (e k) / x (e l)) q := by
    intro q
    induction q using MvPolynomial.induction_on with
    | C a => simp [coneMap, ψ]
    | add p1 p2 h1 h2 => rw [map_add (f := _), map_add (f := _), map_add (f := _), h1, h2]
    | mul_X p1 k h1 => rw [map_mul, map_mul, map_mul, h1]; simp [coneMap, ψ, div_eq_mul_inv]
  have hmem : ∀ v : coneRing ℤ (x ∘ e), ψ v ∈ R := by
    rintro ⟨_, q, rfl⟩
    change ψ (coneMap ℤ (x ∘ e) q) ∈ R
    rw [hev]
    refine aeval_mem_subring R (fun a => by simp [intCast_mem]) _ (fun k => ?_) q
    by_cases hk : k = l
    · subst hk; rw [div_self hne]; exact one_mem _
    · exact ⟨chartGen x e l ⟨k, hk⟩, Algebra.subset_adjoin ⟨⟨k, hk⟩, rfl⟩, rfl⟩
  let φ : coneRing ℤ (x ∘ e) →+* R := (ψ.comp (coneRing ℤ (x ∘ e)).val.toRingHom).codRestrict R hmem
  let eqv : (chartRing x e l).toSubring ≃+* R :=
    Subring.equivMapOfInjective _ _ fun _ _ hab => Subtype.ext hab
  let ψ' : R →+* chartRing x e l := eqv.symm.toRingHom
  have := IsIntegral.map_of_comp_eq (ψ'.comp φ) ψ
    (RingHom.ext fun v => congrArg Subtype.val (eqv.apply_symm_apply (φ v))) (h.integral i)
  simpa [ψ, div_eq_mul_inv] using this

theorem sec_div_isIntegral (x : κ → Ω) (e : Fin (D + 1) → κ) [Fintype κ] (h : IsProjFrame x e)
    (l : Fin (D + 1)) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n) :
    IsIntegral (chartRing x e l) (⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ :
      IntermediateField.extendScalars (fnField_comp_le' x e)) := by
  classical
  obtain ⟨p, hp, rfl⟩ := (mem_sec_iff x n s).1 hs
  let S := (integralClosure (chartRing x e l) Ω).restrictScalars ℤ
  let y' : κ → S := fun i => ⟨x i / x (e l), coord_div_isIntegral x e h l i⟩
  have hΩ : IsIntegral (chartRing x e l) (MvPolynomial.aeval x p / x (e l) ^ n) := by
    have hhom : MvPolynomial.aeval x p / x (e l) ^ n = S.val (MvPolynomial.aeval y' p) := by
      calc MvPolynomial.aeval x p / x (e l) ^ n
          = MvPolynomial.aeval (fun i => (x (e l))⁻¹ * x i) p := by
              rw [aeval_smul_homog hp, inv_pow, div_eq_mul_inv, mul_comm]
        _ = MvPolynomial.aeval (fun i => x i / x (e l)) p := by simp [div_eq_inv_mul]
        _ = S.val (MvPolynomial.aeval y' p) := by rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]; rfl
    rw [hhom]
    exact (MvPolynomial.aeval y' p).2
  exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom (chartRing x e l)
    (IntermediateField.extendScalars (fnField_comp_le' x e)) Ω)
    fun _ _ hab => Subtype.ext hab).1 hΩ

theorem trace_mem_chart [Fintype κ] (x : κ → Ω) (e : Fin (D + 1) → κ) (h : IsProjFrame x e)
    (l : Fin (D + 1)) (n : ℕ) {s : Ω} (hs : s ∈ sec ℤ x n) :
    Algebra.trace (fnField (x ∘ e)) (IntermediateField.extendScalars (fnField_comp_le' x e))
      ⟨s / x (e l) ^ n, sec_div_mem x (e l) hs⟩ ∈ chartRing x e l := by
  have hi := sec_div_isIntegral x e h l n hs
  have := chartRing_frac x e h.free l
  have := chartRing_closed x e h.free l
  by_cases hfd : FiniteDimensional (fnField (x ∘ e))
      (IntermediateField.extendScalars (fnField_comp_le' x e))
  · have := hfd
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (K := fnField (x ∘ e))).1
      (Algebra.isIntegral_trace (L := fnField (x ∘ e)) hi)
    exact hy ▸ y.2
  · rw [Algebra.trace_eq_zero_of_not_exists_basis _
      (by rintro ⟨_, ⟨b⟩⟩; exact hfd (Module.Finite.of_basis b)), LinearMap.zero_apply]
    exact zero_mem _

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.TraceNormBounds
