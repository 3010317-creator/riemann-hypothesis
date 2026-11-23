module

public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Mathlib.RingTheory.Polynomial.Vieta

@[expose] public section

open Finset MvPolynomial in
private theorem exF {B S : Type} [CommRing B] [CommRing S] [Algebra B S] {m : ℕ} (Q : Polynomial B)
    (θ : Fin m → S) (hQ : Q.map (algebraMap B S) = ∏ i, (Polynomial.X - Polynomial.C (θ i))) (r : ℕ) :
    ∃ F : Polynomial B, F.map (algebraMap B S) = ∏ I ∈ powersetCard r univ, (Polynomial.X - Polynomial.C (∏ i ∈ I, θ i)) := by
  let P : Polynomial (MvPolynomial (Fin m) B) := ∏ I ∈ powersetCard r univ, (Polynomial.X - Polynomial.C (∏ i ∈ I, X i))
  have hsym (j : ℕ) : (P.coeff j).IsSymmetric := fun e => by
    simpa [Polynomial.coeff_map] using congrArg (fun p => p.coeff j) <| show P.map (rename e).toRingHom = P by
      simp_rw [P, Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
      conv_rhs => rw [← map_univ_equiv e, powersetCard_map]
      simp [-map_univ_equiv, map_prod]
  rw [show (∏ I ∈ powersetCard r univ, (Polynomial.X - Polynomial.C (∏ i ∈ I, θ i))) = P.map (aeval θ).toRingHom by simp [P, Polynomial.map_prod, map_prod]]
  change _ ∈ Polynomial.lifts (algebraMap B S); rw [Polynomial.lifts_iff_coeff_lifts]; intro j
  obtain ⟨E, hE⟩ := esymmAlgHom_fin_surjective B le_rfl ⟨P.coeff j, hsym j⟩
  let b (k : Fin m) : B := (-1) ^ ((k : ℕ) + 1) * Q.coeff (m - ((k : ℕ) + 1))
  refine ⟨aeval b E, ?_⟩
  suffices hhom : (Algebra.ofId B S).comp (aeval b) = (aeval θ).comp (aeval fun k : Fin m => esymm (Fin m) B (k + 1)) by
    simpa [Polynomial.coeff_map, ← esymmAlgHom_apply, congrArg Subtype.val hE] using DFunLike.congr_fun hhom E
  refine algHom_ext fun k => ?_
  have h1 : (Q.map (algebraMap B S)).coeff (m - ((k : ℕ) + 1)) = (-1) ^ ((k : ℕ) + 1) * (univ.val.map θ).esymm ((k : ℕ) + 1) := by
    rw [show Q.map (algebraMap B S) = ((univ.val.map θ).map (Polynomial.X - Polynomial.C ·)).prod by rw [hQ, Multiset.map_map]; rfl, Multiset.prod_X_sub_C_coeff _ (by simp)]
    simp [Nat.sub_sub_self k.2]
  simp only [b, AlgHom.comp_apply, Algebra.ofId_apply, aeval_X, aeval_esymm_eq_multiset_esymm, map_mul, map_pow, map_neg, map_one]
  rw [← Polynomial.coeff_map, h1, ← mul_assoc, ← mul_pow]; simp

open Polynomial Finset in
private theorem isLocalRing_integralClosure {B : Type} [CommRing B] [IsDomain B] [HenselianLocalRing B] :
    IsLocalRing (integralClosure B (AlgebraicClosure (FractionRing B))) := by
  classical
  let Ω := AlgebraicClosure (FractionRing B); let S := integralClosure B Ω
  have hinj : Function.Injective (algebraMap B S) := fun a b h =>
    IsFractionRing.injective B (FractionRing B) ((algebraMap (FractionRing B) Ω).injective (congrArg Subtype.val h))
  obtain ⟨n2, hn2⟩ := Ideal.exists_maximal S
  refine IsLocalRing.of_unique_max_ideal ⟨n2, hn2, fun n1 hn1 => hn1.eq_of_le hn2.ne_top fun θ0 h1 => ?_⟩
  by_contra h2; obtain ⟨Q, hQm, hQ0⟩ := Algebra.IsIntegral.isIntegral (R := B) θ0
  let s : Multiset Ω := (Q.map (algebraMap B Ω)).roots; let L := s.toList
  let θ (i : Fin L.length) : S := ⟨L[i], Q, hQm, by simpa [eval_map] using (mem_roots'.mp (Multiset.mem_toList.mp (L.getElem_mem i.2))).2⟩
  have hQ : Q.map (algebraMap B S) = ∏ i, (X - C (θ i)) := by
    apply map_injective (algebraMap S Ω) Subtype.val_injective
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq, (IsAlgClosed.splits _).eq_prod_roots_of_monic (hQm.map _),
      show (Q.map (algebraMap B Ω)).roots = (L : Multiset Ω) from (Multiset.coe_toList s).symm, Multiset.map_coe, Multiset.prod_coe, Fin.prod_univ_def, Polynomial.map_list_prod]
    exact congrArg List.prod (List.ext_getElem (by simp) fun i _ _ => by simp [θ])
  obtain ⟨i0, -, hi0'⟩ := prod_eq_zero_iff.mp (by rw [← eval_prod (x := θ0), ← hQ, eval_map]; exact hQ0)
  obtain rfl : θ0 = θ i0 := by simpa [sub_eq_zero] using hi0'
  have hker (n : Ideal S) (hn : n.IsMaximal) (b : B) : algebraMap B S b ∈ n ↔ b ∈ IsLocalRing.maximalIdeal B := by
    rw [← Ideal.mem_under, IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := B) n)]
  let a := (Q.map (IsLocalRing.residue B)).rootMultiplicity 0; let r := L.length - a
  have hmapn (n : Ideal S) : Q.map ((Ideal.Quotient.mk n).comp (algebraMap B S)) = ∏ i, (X - C (Ideal.Quotient.mk n (θ i))) := by rw [← Polynomial.map_map, hQ, Polynomial.map_prod]; simp
  have hcard (n : Ideal S) (hn : n.IsMaximal) : (univ.filter (θ · ∈ n)).card = a := by
    let _ := Ideal.Quotient.field n
    let ι : IsLocalRing.ResidueField B →+* S ⧸ n := Ideal.Quotient.lift _ ((Ideal.Quotient.mk n).comp (algebraMap B S)) fun b hb => Ideal.Quotient.eq_zero_iff_mem.mpr ((hker n hn b).mpr hb)
    have hq : (Q.map (IsLocalRing.residue B)).map ι = ((univ.val.map fun i => Ideal.Quotient.mk n (θ i)).map (X - C ·)).prod := by
      rw [Polynomial.map_map, show ι.comp (IsLocalRing.residue B) = (Ideal.Quotient.mk n).comp (algebraMap B S) from RingHom.ext fun _ => rfl, hmapn n, Multiset.map_map]; rfl
    rw [show a = ((Q.map (IsLocalRing.residue B)).map ι).rootMultiplicity (ι 0) from eq_rootMultiplicity_map ι.injective 0, map_zero, ← count_roots, hq, roots_multiset_prod_X_sub_C, Multiset.count_map, card_def, filter_val]
    exact congrArg Multiset.card (Multiset.filter_congr fun _ _ => (eq_comm.trans Ideal.Quotient.eq_zero_iff_mem).symm)
  have hcard' (n : Ideal S) (hn : n.IsMaximal) : (univ.filter (θ · ∉ n)).card = r := by
    have := card_filter_add_card_filter_not (s := univ) (θ · ∈ n); rw [hcard n hn, card_univ, Fintype.card_fin] at this; omega
  obtain ⟨F, hFS⟩ := exF Q θ hQ r
  have hmonic : F.Monic := monic_of_injective hinj (hFS ▸ monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _)
  let _ := Ideal.Quotient.field n2; let ψ : B →+* S ⧸ n2 := (Ideal.Quotient.mk n2).comp (algebraMap B S); let θb (i : Fin L.length) : S ⧸ n2 := Ideal.Quotient.mk n2 (θ i)
  have hψ (b : B) : ψ b = 0 ↔ b ∈ IsLocalRing.maximalIdeal B := Ideal.Quotient.eq_zero_iff_mem.trans (hker n2 hn2 b)
  let I0 := univ.filter (θ · ∉ n2); let c : S ⧸ n2 := ∏ i ∈ I0, θb i; let A : B := (-1) ^ r * Q.coeff a
  have hc0 : c ≠ 0 := prod_ne_zero_iff.mpr fun i hi => mt Ideal.Quotient.eq_zero_iff_mem.mp (mem_filter.mp hi).2
  have hI0mem : I0 ∈ powersetCard r univ := mem_powersetCard.mpr ⟨subset_univ _, hcard' n2 hn2⟩
  have hI0zero (I : Finset (Fin L.length)) (hIm : I ∈ powersetCard r univ) (hne : I ≠ I0) : ∏ i ∈ I, θb i = 0 := by
    obtain ⟨i, hiI, hiI0⟩ := not_subset.mp fun hs => hne (eq_of_subset_of_card_le hs (by rw [(mem_powersetCard.mp hIm).2, hcard' n2 hn2]))
    exact prod_eq_zero hiI (Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa [I0] using hiI0))
  have hψA : ψ A = c := by
    have hv := Multiset.prod_X_sub_C_coeff (univ.val.map θb) (by simpa using hcard n2 hn2 ▸ (card_le_univ _).trans_eq (Fintype.card_fin _))
    rw [show ((univ.val.map θb).map (X - C ·)).prod = Q.map ψ by rw [hmapn n2, Multiset.map_map]; rfl, coeff_map, Multiset.card_map, card_val, card_univ, Fintype.card_fin, esymm_map_val, sum_eq_single I0 hI0zero fun h => absurd hI0mem h] at hv
    rw [show A = (-1) ^ r * Q.coeff a from rfl, map_mul, map_pow, map_neg, map_one, hv, ← mul_assoc, ← mul_pow]; simp [c]
  have hFψ : F.map ψ = (X - C c) * ∏ I ∈ (powersetCard r univ).erase I0, (X - C (∏ i ∈ I, θb i)) := by
    rw [← Polynomial.map_map, hFS, Polynomial.map_prod, ← mul_prod_erase _ _ hI0mem]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]; simp only [c, θb, I0, _root_.map_prod]
  have hder : (F.map ψ).derivative.eval c ≠ 0 := by
    rw [hFψ, derivative_mul]
    simp only [derivative_sub, derivative_X, derivative_C, sub_zero, one_mul, eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero, eval_prod]
    exact prod_ne_zero_iff.mpr fun I hI => by rw [hI0zero I (mem_erase.mp hI).2 (mem_erase.mp hI).1, sub_zero]; exact hc0
  have hev : F.eval A ∈ IsLocalRing.maximalIdeal B := by rw [← hψ, ← eval₂_at_apply, ← eval_map, hψA, hFψ]; simp
  have hunit : IsUnit (F.derivative.eval A) := by rw [← IsLocalRing.notMem_maximalIdeal]; rwa [← hψ, ← eval₂_at_apply, ← eval_map, hψA, ← derivative_map]
  obtain ⟨τ, hτ0, hτA⟩ := HenselianLocalRing.is_henselian F hmonic A hev hunit
  have hτm : τ ∉ IsLocalRing.maximalIdeal B := fun hm => hc0 (hψA ▸ (hψ A).mpr (by simpa using Ideal.sub_mem _ hm hτA))
  obtain ⟨I, hI, hIτ⟩ := prod_eq_zero_iff.mp (by rw [← eval_prod (x := algebraMap B S τ), ← hFS, eval_map, eval₂_at_apply, hτ0.eq_zero, map_zero])
  have hτI : algebraMap B S τ = ∏ i ∈ I, θ i := by rwa [eval_sub, eval_X, eval_C, sub_eq_zero] at hIτ
  have hIeq (n : Ideal S) (hn : n.IsMaximal) : I = univ.filter (θ · ∉ n) :=
    eq_of_subset_of_card_le (fun i hi => mem_filter.mpr ⟨mem_univ _, fun hin => hτm ((hker n hn τ).mp (hτI ▸ Ideal.mem_of_dvd n (dvd_prod_of_mem θ hi) hin))⟩) (by rw [(mem_powersetCard.mp hI).2, hcard' n hn])
  have hi0 : i0 ∈ I := by rw [hIeq n2 hn2]; exact mem_filter.mpr ⟨mem_univ _, h2⟩
  rw [hIeq n1 hn1] at hi0; exact (mem_filter.mp hi0).2 h1

private theorem ext_hom {B S C : Type} [CommRing B] [CommRing S] [IsDomain S] [Algebra B S] [Algebra.IsIntegral B S]
    (hinj : Function.Injective (algebraMap B S)) [Field C] [IsAlgClosed C] (f : B →+* C) : ∃ g : S →+* C, g.comp (algebraMap B S) = f := by
  let q := RingHom.ker f; have : q.IsPrime := RingHom.ker_isPrime f
  obtain ⟨P, hP, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain (S := S) q (by rw [(RingHom.injective_iff_ker_eq_bot _).mp hinj]; exact bot_le)
  have : P.LiesOver q := ⟨hc.symm⟩; let _ : Algebra (B ⧸ q) C := (RingHom.kerLift f).toAlgebra
  have : IsDomain (B ⧸ q) := Ideal.Quotient.isDomain q; have : IsDomain (S ⧸ P) := Ideal.Quotient.isDomain P
  have : Module.IsTorsionFree (B ⧸ q) (S ⧸ P) := inferInstance
  have : Module.IsTorsionFree (B ⧸ q) C := Module.isTorsionFree_iff_algebraMap_injective.mpr f.kerLift_injective
  have : Algebra.IsIntegral (B ⧸ q) (S ⧸ P) := .tower_top B; have : Algebra.IsAlgebraic (B ⧸ q) (S ⧸ P) := Algebra.IsIntegral.isAlgebraic
  let L : (S ⧸ P) →ₐ[B ⧸ q] C := IsAlgClosed.lift
  exact ⟨(L : (S ⧸ P) →+* C).comp (Ideal.Quotient.mk P), RingHom.ext fun b => L.commutes (Ideal.Quotient.mk q b)⟩

open Polynomial in
private theorem loc_hom {l : ℕ} [Fact (Nat.Prime l)] (κ : PadicAlgCl l) (hκ : 1 ≤ ‖κ‖) :
    ∃ h : ℤ_[l][X], h.eval₂ ((algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l])) κ = 0 ∧ h.coeff 0 = 1 := by
  have hκ0 : κ ≠ 0 := by rintro rfl; norm_num at hκ
  have hm : (minpoly ℚ_[l] κ⁻¹).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
  have hc : ∀ n, ‖(minpoly ℚ_[l] κ⁻¹).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).mp (show ‖κ⁻¹‖ ≤ 1 by rw [norm_inv]; exact inv_le_one_of_one_le₀ hκ)
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic (show minpoly ℚ_[l] κ⁻¹ ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) by rw [lifts_iff_coeff_lifts]; exact fun n => ⟨⟨_, hc n⟩, rfl⟩) hm
  refine ⟨q.reverse, ?_, q.coeff_zero_reverse.trans hqm⟩
  let _ : Invertible κ⁻¹ := invertibleOfNonzero (inv_ne_zero hκ0)
  let ψ := (algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l])
  have h1 := q.eval₂_reverse_mul_pow ψ κ⁻¹
  rw [invOf_eq_inv, inv_inv, show q.eval₂ ψ κ⁻¹ = 0 by rw [← eval₂_map, hq]; exact minpoly.aeval _ _] at h1
  exact (mul_eq_zero.mp h1).resolve_right (pow_ne_zero _ (inv_ne_zero hκ0))

set_option linter.unusedVariables false in set_option linter.overlappingInstances false in
theorem UpperTheory.Reformulated.B.MajorantSquareBound.spl_near :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {O B : Type}
    [inst_1 : CommRing O] [inst_2 : Algebra ℤ_[l] O] [inst_3 : Algebra O (PadicAlgCl l)]
    [IsScalarTower ℤ_[l] O (PadicAlgCl l)] [inst_5 : CommRing B] [IsDomain B] [HenselianLocalRing B]
    [inst_8 : Algebra O B] (x y : B →ₐ[O] PadicAlgCl l) (d : O),
    (Algebra.algebraMap O (PadicAlgCl l) : O → PadicAlgCl l) d ≠ (0 : PadicAlgCl l) →
      ∀ (t : B),
        (x : B → PadicAlgCl l) t = (0 : PadicAlgCl l) →
          ∀ (v : FractionRing B),
            IsIntegral B v →
              (Algebra.algebraMap B (FractionRing B) : B → FractionRing B) ((Algebra.algebraMap O B : O → B) d) * v =
                  (Algebra.algebraMap B (FractionRing B) : B → FractionRing B) t →
                ∀ (κ : PadicAlgCl l),
                  (Algebra.algebraMap O (PadicAlgCl l) : O → PadicAlgCl l) d * κ = (y : B → PadicAlgCl l) t →
                    ‖κ‖ < (1 : ℝ) := by
  intro l _ O B _ _ _ _ _ _ _ _ x y d hd t hxt v hv hdv κ hκ
  by_contra! hκ1
  let K := FractionRing B; let S := integralClosure B (AlgebraicClosure K)
  have : IsLocalRing S := isLocalRing_integralClosure
  have hinj : Function.Injective (algebraMap B S) := fun a b h =>
    IsFractionRing.injective B K ((algebraMap K (AlgebraicClosure K)).injective (congrArg Subtype.val h))
  obtain ⟨gx, hgx⟩ := ext_hom hinj (x : B →+* PadicAlgCl l); obtain ⟨gy, hgy⟩ := ext_hom hinj (y : B →+* PadicAlgCl l)
  have ex (b : B) : gx (algebraMap B S b) = x b := DFunLike.congr_fun hgx b
  have ey (b : B) : gy (algebraMap B S b) = y b := DFunLike.congr_fun hgy b
  let vS : S := ⟨algebraMap K _ v, hv.algebraMap⟩
  have hS : algebraMap B S (algebraMap O B d) * vS = algebraMap B S t := Subtype.ext <| by
    have := congrArg (algebraMap K (AlgebraicClosure K)) hdv
    rwa [map_mul, ← IsScalarTower.algebraMap_apply B K, ← IsScalarTower.algebraMap_apply B K] at this
  have h1 : gx vS = 0 := (mul_eq_zero.mp (by simpa [ex, x.commutes, hxt] using congrArg gx hS)).resolve_left hd
  have h2 : gy vS = κ := mul_left_cancel₀ hd (by simpa [ey, y.commutes, ← hκ] using congrArg gy hS)
  obtain ⟨h, hh0, hh1⟩ := loc_hom κ hκ1
  let φ : ℤ_[l] →+* S := (algebraMap B S).comp ((algebraMap O B).comp (algebraMap ℤ_[l] O))
  have hφ : gy.comp φ = (algebraMap ℚ_[l] (PadicAlgCl l)).comp (algebraMap ℤ_[l] ℚ_[l]) := by
    ext a; simp only [φ, RingHom.comp_apply, ey, y.commutes]
    rw [← IsScalarTower.algebraMap_apply ℤ_[l] O (PadicAlgCl l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  have mem_max (z : S) (g : S →+* PadicAlgCl l) (hz : g z = 0) : z ∈ IsLocalRing.maximalIdeal S :=
    (IsLocalRing.mem_maximalIdeal _).mpr fun hu => not_isUnit_zero (hz ▸ hu.map g)
  have hmem := Ideal.sub_mem _ (mem_max (h.eval₂ φ vS) gy (by rw [Polynomial.hom_eval₂, hφ, h2, hh0])) (Ideal.mul_mem_left _ (h.divX.eval₂ φ vS) (mem_max vS gx h1))
  rw [show h.eval₂ φ vS = h.divX.eval₂ φ vS * vS + 1 by
    conv_lhs => rw [← h.divX_mul_X_add, hh1]; simp [Polynomial.eval₂_add, Polynomial.eval₂_mul], add_sub_cancel_left] at hmem
  exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal S).ne_top hmem
