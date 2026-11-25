module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Base
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsSchur
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AddGapLe
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.TypeStar

@[expose] public section

noncomputable section

namespace GroundTheory.Heights₂.Heights.RestTerms

section
open MvPolynomial Finset

noncomputable section

theorem SchAltPartitionExpansion.alt_partition_add_stair_eq {r : ℕ} (lam : Fin r → ℕ) :
    Comb.alt (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) =
      vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam := by
  unfold Comb.alt
  rw [← Matrix.det_transpose, mul_comm]
  exact Schur.det_pow_add_staircase_eq lam

theorem SchAltPartitionExpansion.strictAnti_partition_add_stair {r n : ℕ} {lam : Fin r → ℕ} (hlam : lam ∈ partitionsOf r n) :
    StrictAnti (fun i : Fin r => lam i + (r - 1 - (i : ℕ))) := by
  unfold partitionsOf at hlam
  rw [Finset.mem_filter] at hlam
  intro i j hij
  have h1 := hlam.2 i j hij.le
  have hj := j.isLt
  have hij' : (i : ℕ) < j := hij
  simp only
  omega

theorem SchAltPartitionExpansion.proof (h1 : SchStrictAntiSplit.Statement) :
    SchAltPartitionExpansion.Statement := by
  intro r n P hP hhom
  set e : (Fin r → ℕ) → (Fin r →₀ ℕ) := fun lam =>
    Finsupp.equivFunOnFinite.symm fun i : Fin r => lam i + (r - 1 - (i : ℕ)) with he
  have e_inj : Set.InjOn e (partitionsOf r n : Set (Fin r → ℕ)) := by
    intro a _ b _ hab
    funext i
    have := congrArg (fun f : Fin r →₀ ℕ => f i) hab
    simp only [he, Finsupp.coe_equivFunOnFinite_symm] at this
    omega

  have hR : ∑ lam ∈ partitionsOf r n,
      C (AddMonoidAlgebra.coeff P (e lam)) *
        (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ)) * schur (Fin r) lam) =
      ∑ d ∈ (partitionsOf r n).image e, AddMonoidAlgebra.coeff P d • Comb.alt (⇑d) := by
    rw [Finset.sum_image e_inj]
    refine Finset.sum_congr rfl fun lam _ => ?_
    rw [C_mul', ← SchAltPartitionExpansion.alt_partition_add_stair_eq]
    simp [he]
  rw [hR]
  conv_lhs => rw [Comb.IsAlt.eq_sum_alt hP]
  refine Finset.sum_subset ?_ ?_
  · intro d hd
    rw [Finset.mem_filter] at hd
    have hsum : ∑ i, d i = r * (r - 1) / 2 + n := by
      have := hhom (mem_support_iff.mp hd.1)
      rw [← Finsupp.degree_eq_sum, Finsupp.degree_eq_weight_one]
      exact this
    obtain ⟨hge, hmem⟩ := h1 r n (⇑d) hd.2 hsum
    refine Finset.mem_image.mpr ⟨_, hmem, ?_⟩
    ext i
    simp only [he, Finsupp.coe_equivFunOnFinite_symm]
    have := hge i
    omega
  · intro d hd hnot
    obtain ⟨lam, hlam, rfl⟩ := Finset.mem_image.mp hd
    have hz : AddMonoidAlgebra.coeff P (e lam) = 0 := by
      by_contra hne
      apply hnot
      rw [Finset.mem_filter]
      refine ⟨mem_support_iff.mpr hne, ?_⟩
      simpa [he] using SchAltPartitionExpansion.strictAnti_partition_add_stair hlam
    rw [hz, zero_smul]

end
end

section
open MvPolynomial

noncomputable section

theorem rename_alternant_equiv {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] (e : ι ≃ κ) (v : ι → ℕ) :
    rename e (alternant v) = alternant (v ∘ e.symm) := by
  unfold alternant
  rw [AlgHom.map_det, ← Matrix.det_submatrix_equiv_self e
    (Matrix.of fun p p' : κ => (X p : MvPolynomial κ ℚ) ^ (v ∘ e.symm) p')]
  congr 1
  ext i i'
  simp [Matrix.map_apply, Matrix.submatrix_apply]

def smallBlockEquiv (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a ≃ Fin (r + a) where
  toFun x := (smallBlockPlace r a c x).2
  invFun := smallBlockOf r a c
  left_inv := by
    intro x
    cases c <;> rcases x with i | j <;> simp [smallBlockPlace, smallBlockOf, yIndex, zIndex]
  right_inv := by
    intro p
    cases c <;> simp only [smallBlockOf] <;> split_ifs with h <;>
      apply Fin.ext <;> simp [smallBlockPlace, yIndex, zIndex] <;> omega

theorem SchAlternantRenamePlace.proof : SchAlternantRenamePlace.Statement := by
  intro r a c v
  have hg : smallBlockPlace r a c =
      (fun p : Fin (r + a) => ((0 : Fin 1), p)) ∘ smallBlockEquiv r a c := by
    funext x
    exact Prod.ext (Subsingleton.elim _ _) rfl
  have hs : (smallBlockEquiv r a c).symm = smallBlockOf r a c := rfl
  rw [hg, ← rename_rename]
  congr 1
  rw [rename_alternant_equiv, hs]

end
end

section
open MvPolynomial Finset

noncomputable section

def smallBlockPlaceEquiv (r a : ℕ) (c : SmallBlock) : Fin r ⊕ Fin a ≃ Fin (r + a) where
  toFun x := (smallBlockPlace r a c x).2
  invFun := smallBlockOf r a c
  left_inv x := by
    cases c <;> rcases x with i | j <;>
      simp [smallBlockPlace, smallBlockOf, yIndex, zIndex]
  right_inv p := by
    cases c
    · by_cases h : (p : ℕ) < a
      · simp [smallBlockPlace, smallBlockOf, zIndex, h]
      · simp only [smallBlockOf, h, dite_false, smallBlockPlace, Sum.elim_inl, yIndex]
        ext; simp; omega
    · by_cases h : (p : ℕ) < r
      · simp [smallBlockPlace, smallBlockOf, yIndex, h]
      · simp only [smallBlockOf, h, dite_false, smallBlockPlace, Sum.elim_inr, zIndex]
        ext; simp; omega

theorem smallBlockPlace_eq (r a : ℕ) (c : SmallBlock) (x : Fin r ⊕ Fin a) :
    smallBlockPlace r a c x = (0, smallBlockPlaceEquiv r a c x) := by
  exact Prod.ext (Subsingleton.elim _ _) rfl

theorem SchAntisymmetrizePlace.proof : SchAntisymmetrizePlace.Statement := by
  intro r a c Q
  set e := smallBlockPlaceEquiv r a c with he
  unfold antisymmetrize antisym

  rw [map_sum]
  refine Fintype.sum_equiv ((Equiv.funUnique (Fin 1) _).trans e.symm.permCongr) _ _ ?_
  intro w
  simp only [Equiv.trans_apply, Equiv.funUnique_apply]
  rw [AlgHom.map_smul_of_tower, blockPermute, rename_rename, rename_rename]
  have hs : blockSign 1 (r + a) w = ((Equiv.Perm.sign (e.symm.permCongr (w 0)) : ℤ) : ℚ) := by
    rw [Equiv.Perm.sign_permCongr, blockSign, Fintype.prod_unique]
    rfl
  rw [hs]
  congr 3
  funext x
  simp [smallBlockPlace_eq, ← he]

end

theorem prod_one_sub_rootOfUnityPoint (h1 : SchProdOneSubRootsOfUnity.Statement) {N k : ℕ}
    (hk : 1 ≤ k) (hkN : k ≤ N) :
    ∏ i : Fin N, (1 - Polynomial.C (rootOfUnityPoint N k i) * Polynomial.X) =
      (1 - Polynomial.X ^ k : Polynomial ℂ) := by
  let f : ℕ → Polynomial ℂ := fun i =>
    1 - Polynomial.C (if i < k then rootOfUnity k ^ i else 0) * Polynomial.X
  calc ∏ i : Fin N, (1 - Polynomial.C (rootOfUnityPoint N k i) * Polynomial.X)
      = ∏ i ∈ range N, f i := Fin.prod_univ_eq_prod_range f N
    _ = ∏ i ∈ range k, f i := by
        refine (prod_subset (range_subset_range.2 hkN) fun i _ hik => ?_).symm
        have : ¬ i < k := fun h => hik (mem_range.2 h)
        simp [f, this]
    _ = ∏ i ∈ range k, (1 - Polynomial.C (rootOfUnity k ^ i) * Polynomial.X) :=
        prod_congr rfl fun i hi => by simp [f, mem_range.1 hi]
    _ = 1 - Polynomial.X ^ k := h1 k hk

theorem SchCompleteAtRootsOfUnity.proof (h1 : SchProdOneSubRootsOfUnity.Statement)
    (h2 : SchCompleteGenerating.Statement) : SchCompleteAtRootsOfUnity.Statement := by
  intro N k d hk hkN
  let H : ℕ → ℂ := fun n => aeval (rootOfUnityPoint N k) (hsymm (Fin N) ℚ n)
  have hrec : ∀ n, H n - (if k ≤ n then H (n - k) else 0) = if n = 0 then 1 else 0 := by
    intro n
    have e := h2 N (rootOfUnityPoint N k) n
    rw [prod_one_sub_rootOfUnityPoint h1 hk hkN] at e
    rw [← e]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow, sub_mul,
      sum_sub_distrib, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_range]
    simp [H]
  show H d = _
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    have e := hrec d
    rcases Nat.eq_zero_or_pos d with rfl | hd
    · rw [ite_eq_right (by omega), sub_zero, ite_eq_left rfl] at e
      rw [e, ite_eq_left (dvd_zero k)]
    · by_cases hkd : k ≤ d
      · rw [ite_eq_left hkd, ite_eq_right (show d ≠ 0 by omega), sub_eq_zero, ih (d - k) (by omega)] at e
        have hdvd : k ∣ d - k ↔ k ∣ d := by
          conv_rhs => rw [show d = d - k + k by omega]
          exact (Nat.dvd_add_self_right).symm
        rw [e]
        exact if_congr hdvd rfl rfl
      · rw [ite_eq_right hkd, ite_eq_right (show d ≠ 0 by omega), sub_zero] at e
        rw [e, ite_eq_right]
        exact fun h => hkd (Nat.le_of_dvd hd h)

noncomputable section

namespace SchCompleteGenerating

theorem coeff_prod_geomSeries_eval {N : ℕ} (y : Fin N → ℂ) (n : ℕ) :
    PowerSeries.coeff n (∏ i : Fin N, Schur.geomSeries (y i)) =
      aeval y (hsymm (Fin N) ℚ n) := by

  rw [PowerSeries.coeff_prod, Schur.hsymm_eq_sum_finsuppAntidiag, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp [Schur.geomSeries, PowerSeries.coeff_mk, map_prod]

theorem coe_prod_one_sub {N : ℕ} (y : Fin N → ℂ) :
    ((∏ i : Fin N, (1 - Polynomial.C (y i) * Polynomial.X) : Polynomial ℂ) : PowerSeries ℂ) =
      ∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
  simp

theorem prod_one_sub_mul_prod_geomSeries {N : ℕ} (y : Fin N → ℂ) :
    (∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X)) *
      ∏ i : Fin N, Schur.geomSeries (y i) = 1 := by
  rw [← prod_mul_distrib]
  exact prod_eq_one fun i _ => by rw [mul_comm, Schur.geomSeries_mul]

theorem proof : Statement := by
  intro N y d
  have key := congrArg (PowerSeries.coeff d) (prod_one_sub_mul_prod_geomSeries y)
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a (∏ i : Fin N, (1 - PowerSeries.C (y i) * PowerSeries.X)) *
      PowerSeries.coeff b (∏ i : Fin N, Schur.geomSeries (y i))), PowerSeries.coeff_one] at key
  simp only [coeff_prod_geomSeries_eval, ← coe_prod_one_sub, Polynomial.coeff_coe] at key
  exact key

end SchCompleteGenerating

end

noncomputable section

theorem SchConcatAlternant.alternant_comp_perm {N : ℕ} (w : Fin N → ℕ) (τ : Equiv.Perm (Fin N)) :
    alternant (w ∘ τ) = C ((Equiv.Perm.sign τ : ℤ) : ℚ) * alternant w := by
  unfold alternant
  have hM : (Matrix.of fun i i' : Fin N =>
      (X i : MvPolynomial (Fin N) ℚ) ^ (w ∘ τ) i') =
      (Matrix.of fun i i' : Fin N => (X i : MvPolynomial (Fin N) ℚ) ^ w i').submatrix id τ := rfl
  rw [hM, Matrix.det_permute', map_intCast]

theorem SchConcatAlternant.alternant_add_staircase {N : ℕ} (mu : Fin N → ℕ) :
    alternant (fun p : Fin N => mu p + (N - 1 - (p : ℕ))) =
      vandermondeOf (fun p : Fin N => (X p : MvPolynomial (Fin N) ℚ)) * schur (Fin N) mu := by
  rw [mul_comm, ← Schur.det_pow_add_staircase_eq, ← Matrix.det_transpose]
  rfl

theorem SchConcatAlternant.proof (h1 : SchAlternantRenamePlace.Statement)
    (h2 : SchConcatExponent.Statement) : SchConcatAlternant.Statement := by
  intro r a c
  obtain ⟨τ, hτ⟩ := h2 r a c
  refine ⟨((Equiv.Perm.sign τ : ℤ) : ℚ), ?_, fun lam hlam => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with h | h <;> simp [h]
  · rw [h1, hτ lam hlam, SchConcatAlternant.alternant_comp_perm,
      SchConcatAlternant.alternant_add_staircase,
      Schur.schur_padPartition (Fin (r + a)) (fun i : Fin r => lam i - a) (r + a) (by omega), map_mul,
      rename_C]

end
end

noncomputable section

def SchConcatExponent.rotateFun (r a : ℕ) (p : Fin (r + a)) : Fin (r + a) :=
  if h : (p : ℕ) < a then ⟨r + p, by omega⟩ else ⟨p - a, by have := p.isLt; omega⟩

def SchConcatExponent.rotateInv (r a : ℕ) (q : Fin (r + a)) : Fin (r + a) :=
  if h : (q : ℕ) < r then ⟨q + a, by omega⟩ else ⟨q - r, by have := q.isLt; omega⟩

theorem SchConcatExponent.rotateFun_val (r a : ℕ) (p : Fin (r + a)) :
    (SchConcatExponent.rotateFun r a p : ℕ) = if (p : ℕ) < a then r + p else p - a := by
  unfold SchConcatExponent.rotateFun; split <;> rfl

theorem SchConcatExponent.rotateInv_val (r a : ℕ) (q : Fin (r + a)) :
    (SchConcatExponent.rotateInv r a q : ℕ) = if (q : ℕ) < r then q + a else q - r := by
  unfold SchConcatExponent.rotateInv; split <;> rfl

def SchConcatExponent.rotate (r a : ℕ) : Equiv.Perm (Fin (r + a)) where
  toFun := SchConcatExponent.rotateFun r a
  invFun := SchConcatExponent.rotateInv r a
  left_inv p := by
    have hp := p.isLt
    apply Fin.ext
    rw [SchConcatExponent.rotateInv_val, SchConcatExponent.rotateFun_val]
    split_ifs <;> omega
  right_inv q := by
    have hq := q.isLt
    apply Fin.ext
    rw [SchConcatExponent.rotateFun_val, SchConcatExponent.rotateInv_val]
    split_ifs <;> omega

theorem SchConcatExponent.proof : SchConcatExponent.Statement := by
  intro r a c
  cases c with
  | first =>
    refine ⟨Equiv.refl _, fun lam hlam => ?_⟩
    funext p
    have hp := p.isLt
    by_cases h : (p : ℕ) < r
    · have := hlam ⟨p, h⟩
      simp [smallBlockOf, Schur.padPartition, h]
      omega
    · simp [smallBlockOf, Schur.padPartition, h]
      omega
  | last =>
    refine ⟨SchConcatExponent.rotate r a, fun lam hlam => ?_⟩
    funext p
    have hp := p.isLt
    simp only [Function.comp_apply]
    generalize hq : SchConcatExponent.rotate r a p = q
    have hv : (q : ℕ) = if (p : ℕ) < a then r + p else p - a := by
      rw [← hq]; exact SchConcatExponent.rotateFun_val r a p
    simp only [Schur.padPartition, smallBlockOf]
    by_cases h : (p : ℕ) < a
    · have hn : ¬ ((q : ℕ) < r) := by rw [hv, ite_eq_left h]; omega
      rw [dite_eq_left h, dite_eq_right hn]
      simp only [Sum.elim_inr]
      rw [hv, ite_eq_left h]
      omega
    · have h' : (p : ℕ) - a < r := by omega
      have hn : (q : ℕ) < r := by rw [hv, ite_eq_right h]; exact h'
      rw [dite_eq_right h, dite_eq_left hn]
      simp only [Sum.elim_inl]
      have hqe : (⟨q, hn⟩ : Fin r) = ⟨(p : ℕ) - a, h'⟩ := Fin.ext (by rw [hv, ite_eq_right h])
      rw [hqe, hv, ite_eq_right h]
      have := hlam ⟨(p : ℕ) - a, h'⟩
      omega

end

section
open MvPolynomial Finset

theorem SchEvalPowerSumHom.eq_single_of_dvd {N k : ℕ} (hk1 : 1 ≤ k) (hkN : k ≤ N)
    (e : Fin N →₀ ℕ) (hw : Finsupp.weight (fun i : Fin N => (i : ℕ) + 1) e = k)
    (hd : ∀ i ∈ e.support, k ∣ (i : ℕ) + 1) :
    e = Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1 := by
  have hsum : ∑ i ∈ e.support, e i * ((i : ℕ) + 1) = k := by
    simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] at hw
    exact hw
  obtain ⟨j, hj⟩ : e.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    rw [h, Finset.sum_empty] at hsum
    omega
  have hej : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  have hjk : k ≤ (j : ℕ) + 1 := Nat.le_of_dvd (by omega) (hd j hj)
  rw [← Finset.add_sum_erase _ _ hj] at hsum
  have hmul : k ≤ e j * ((j : ℕ) + 1) := le_trans hjk (Nat.le_mul_of_pos_left _ hej)
  have hrest : ∑ i ∈ e.support.erase j, e i * ((i : ℕ) + 1) = 0 := by omega
  have hjm : e j * ((j : ℕ) + 1) = k := by omega
  have hej1 : e j = 1 := by nlinarith
  have hjv : j = (⟨k - 1, by omega⟩ : Fin N) := by
    rw [hej1, one_mul] at hjm
    exact Fin.ext (by simp; omega)
  have hother : ∀ i, i ≠ j → e i = 0 := by
    intro i hij
    by_contra hne
    have hi : i ∈ e.support.erase j :=
      Finset.mem_erase.mpr ⟨hij, Finsupp.mem_support_iff.mpr hne⟩
    have h0 := (Finset.sum_eq_zero_iff.mp hrest) i hi
    rw [Nat.mul_eq_zero] at h0
    omega
  ext i
  rw [Finsupp.single_apply]
  split_ifs with h
  · rw [← h, ← hjv, hej1]
  · exact hother i (fun hij => h (hjv.symm.trans hij.symm))

theorem SchEvalPowerSumHom.proof (h1 : SchPowerSumAtRootsOfUnity.Statement) :
    SchEvalPowerSumHom.Statement := by
  intro N k hk1 hkN S hS
  have hzv : ∀ i : Fin N, aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1)) =
      if k ∣ (i : ℕ) + 1 then (k : ℂ) else 0 := fun i =>
    h1 N k ((i : ℕ) + 1) hk1 hkN (by omega)
  have hcomp : aeval (rootOfUnityPoint N k) (powerSumHom N S) =
      aeval (fun i : Fin N => aeval (rootOfUnityPoint N k) (psum (Fin N) ℚ ((i : ℕ) + 1))) S := by
    rw [powerSumHom, ← AlgHom.comp_apply, comp_aeval]
  rw [hcomp]

  conv_lhs => rw [S.as_sum, map_sum]
  rw [Finset.sum_eq_single (Finsupp.single (⟨k - 1, by omega⟩ : Fin N) 1)]
  · have hdvd : k ∣ ((⟨k - 1, by omega⟩ : Fin N) : ℕ) + 1 := by
      simp only [Nat.sub_add_cancel hk1, dvd_refl]
    rw [aeval_monomial, Finsupp.prod_single_index (by simp), pow_one, hzv, ite_eq_left hdvd]
    simp [mul_comm]
  · intro e he hne
    rw [aeval_monomial]
    have hw := hS (MvPolynomial.mem_support_iff.mp he)
    obtain ⟨i, hi, hik⟩ : ∃ i ∈ e.support, ¬ k ∣ (i : ℕ) + 1 := by
      by_contra hcon
      push Not at hcon
      exact hne (SchEvalPowerSumHom.eq_single_of_dvd hk1 hkN e hw hcon)
    rw [Finsupp.prod, Finset.prod_eq_zero hi, mul_zero]
    rw [hzv, ite_eq_right hik, zero_pow (Finsupp.mem_support_iff.mp hi)]
  · intro h
    rw [MvPolynomial.notMem_support_iff.mp h, monomial_zero, map_zero]
end

section
open Finset

theorem SchHookResidues.proof : SchHookResidues.Statement := by
  intro k nu hk hanti hsum hhook
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  set s := univ.filter fun i : Fin (n + 1) => (i : ℕ) ≠ 0 ∧ nu i = 1 with hs
  set t := s.card with ht
  have down : ∀ i j : Fin (n + 1), (i : ℕ) ≠ 0 → i ≤ j → j ∈ s → i ∈ s := by
    intro i j hi hij hj
    simp only [hs, mem_filter, mem_univ, true_and] at hj ⊢
    have h1 := hanti hij
    have h2 := hhook i hi
    exact ⟨hi, by omega⟩
  have hA : ∀ j ∈ s, (j : ℕ) ≤ t := by
    intro j hj
    have hsub : Finset.Icc 1 (j : ℕ) ⊆ s.map Fin.valEmbedding := by
      intro m hm
      rw [Finset.mem_Icc] at hm
      rw [Finset.mem_map]
      refine ⟨⟨m, by omega⟩, down _ j (show m ≠ 0 by omega)
        (by rw [Fin.le_iff_val_le_val]; show m ≤ (j : ℕ); omega) hj, rfl⟩
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hB : ∀ i : Fin (n + 1), (i : ℕ) ≠ 0 → (i : ℕ) ≤ t → i ∈ s := by
    intro i hi hit
    by_contra hni
    have hsub : s.map Fin.valEmbedding ⊆ Finset.Ico 1 (i : ℕ) := by
      intro m hm
      rw [Finset.mem_map] at hm
      obtain ⟨j, hj, rfl⟩ := hm
      have hj' := hj
      simp only [hs, mem_filter, mem_univ, true_and] at hj'
      rw [Finset.mem_Ico]
      refine ⟨by simp only [Fin.valEmbedding_apply]; omega, ?_⟩
      by_contra hle
      exact hni (down i j hi (by rw [Fin.le_iff_val_le_val]; simp at hle; omega) hj)
    have := Finset.card_le_card hsub
    simp at this
    omega
  have hval : ∀ i : Fin (n + 1), (i : ℕ) ≠ 0 → nu i = if (i : ℕ) ≤ t then 1 else 0 := by
    intro i hi
    have h1 := hhook i hi
    split_ifs with h
    · have := hB i hi h
      simp only [hs, mem_filter, mem_univ, true_and] at this
      exact this.2
    · have : nu i ≠ 1 := by
        intro h1'
        have := hA i (by simp only [hs, mem_filter, mem_univ, true_and]; exact ⟨hi, h1'⟩)
        omega
      omega
  have htn : t ≤ n := by
    have hsub : s ⊆ univ.erase 0 := by
      intro i hi
      simp only [hs, mem_filter, mem_univ, true_and] at hi
      exact Finset.mem_erase.mpr ⟨fun h => hi.1 (by simp [h]), mem_univ _⟩
    have := card_le_card hsub
    simpa [card_erase_of_mem] using this
  have hnu0 : nu 0 + t = n + 1 := by
    have hpt : ∀ i, nu i = (if i = 0 then nu 0 else 0) +
        (if (i : ℕ) ≠ 0 ∧ nu i = 1 then 1 else 0) := by
      intro i
      by_cases h0 : i = 0
      · subst h0; simp
      · have hi : (i : ℕ) ≠ 0 := fun h => h0 (Fin.ext (by simp [h]))
        have := hhook i hi
        rw [ite_eq_right h0, zero_add]
        split_ifs with h <;> omega
    have hsum2 : ∑ i, nu i = nu 0 + t := by
      rw [Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_add_distrib, Finset.sum_boole]
      simp [t, s]
    omega
  refine ⟨(Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1)))⁻¹, ?_, ?_⟩
  · intro i
    obtain ⟨j, rfl⟩ := (Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1))).surjective i
    simp only [Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rcases lt_trichotomy (j : ℕ) t with h | h | h
    · have hlt : j < (⟨t, by omega⟩ : Fin (n + 1)) := Fin.lt_def.mpr h
      have hv : ((Fin.cycleRange (⟨t, by omega⟩ : Fin (n + 1)) j : Fin (n + 1)) : ℕ) = j + 1 :=
        Fin.coe_cycleRange_of_lt hlt
      rw [hval _ (by rw [hv]; omega), hv, ite_eq_left (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · rw [Fin.cycleRange_of_eq (Fin.ext h), Fin.val_zero]
      have h2 : nu 0 + (n + 1 - 1 - 0) = (n - t) + (n + 1) := by omega
      rw [h2, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      omega
    · have hgt : (⟨t, by omega⟩ : Fin (n + 1)) < j := Fin.lt_def.mpr h
      rw [Fin.cycleRange_of_gt hgt, hval j (by omega), ite_eq_right (by omega),
        Nat.mod_eq_of_lt (by omega)]
      omega
  · rw [Equiv.Perm.sign_inv, Fin.sign_cycleRange]
    simp [t, s]

theorem SchJTMatrixDetAtRoots.proof (h1 : SchRootOfUnityBialternant.Statement)
    (h2 : SchRootOfUnityRowsPerm.Statement) (h3 : SchRootOfUnityRowsEq.Statement)
    (h4 : SchHookResidues.Statement) (h5 : SchNonHookResidues.Statement)
    (h6 : SchRootOfUnityVandermondeNe.Statement) : SchJTMatrixDetAtRoots.Statement := by
  intro k nu hk hanti hsum
  have hV := h6 k hk
  have hB := h1 k nu hk

  have hstair : (Matrix.of fun i j : Fin k =>
      rootOfUnity k ^ ((j : ℕ) * (k - 1 - (i : ℕ)))).det =
      vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) := by
    rw [← Schur.det_pow_staircase_eq_vandermondeOf (fun j : Fin k => rootOfUnity k ^ (j : ℕ))]
    congr 1
    ext i j
    simp [Matrix.of_apply, pow_mul]
  split_ifs with hhook
  · obtain ⟨π, hres, hsign⟩ := h4 k nu hk hanti hsum hhook
    have hP := h2 k (fun i => nu i + (k - 1 - (i : ℕ))) π hk hres
    rw [hstair] at hP
    have hP' : (Matrix.of fun i j : Fin k =>
        rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det =
        (((Equiv.Perm.sign π : ℤ) : ℂ)) *
          vandermondeOf (fun i : Fin k => rootOfUnity k ^ (i : ℕ)) := hP
    rw [hB] at hP'
    have := mul_right_cancel₀ hV hP'
    rw [this, hsign]
    push_cast
    rfl
  · obtain ⟨i, i', hne, hres⟩ := h5 k nu hk hanti hsum hhook
    have hZ : (Matrix.of fun i j : Fin k =>
        rootOfUnity k ^ ((j : ℕ) * (nu i + (k - 1 - (i : ℕ))))).det = 0 :=
      h3 k (fun i => nu i + (k - 1 - (i : ℕ))) i i' hne hres
    rw [hB] at hZ
    exact (mul_eq_zero.mp hZ).resolve_right hV

theorem sum_fin_staircase (k : ℕ) : ∑ i : Fin k, (k - 1 - (i : ℕ)) = k * (k - 1) / 2 := by
  have h := Finset.sum_range_reflect (fun i : ℕ => i) k
  rw [Fin.sum_univ_eq_sum_range (fun i => k - 1 - i) k, h, Finset.sum_range_id]

theorem SchNonHookResidues.proof (h1 : SchResidueCount.Statement) :
    SchNonHookResidues.Statement := by
  intro k nu hk hanti hsum hnot
  push Not at hnot
  obtain ⟨j, hj0, hj2⟩ := hnot
  have hk2 : 2 ≤ k := by have := j.isLt; omega
  by_contra hcon
  push Not at hcon
  set l : Fin k → ℕ := fun i => nu i + (k - 1 - (i : ℕ)) with hl
  have hinj : Function.Injective (fun i => l i % k) := by
    intro a b hab
    by_contra hne
    exact hcon a b hne hab
  have hle : ∀ i, nu i ≤ k := fun i =>
    hsum ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hlt : ∀ i, l i < 2 * k := by
    intro i
    have := hle i
    have := i.isLt
    simp only [hl]
    omega
  have hcount := h1 k l hlt hinj
  have hsumL : ∑ i, l i = k + k * (k - 1) / 2 := by
    simp only [hl, Finset.sum_add_distrib, hsum, sum_fin_staircase]
  let i0 : Fin k := ⟨0, by omega⟩
  let i1 : Fin k := ⟨1, by omega⟩
  have h1le : nu j ≤ nu i1 := hanti (show i1 ≤ j by rw [Fin.le_iff_val_le_val]; simp [i1]; omega)
  have h0le : nu i1 ≤ nu i0 := hanti (show i0 ≤ i1 by rw [Fin.le_iff_val_le_val]; simp [i0, i1])
  have hsub : ({i0, i1} : Finset (Fin k)) ⊆ univ.filter fun i => k ≤ l i := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    have hv0 : (i0 : ℕ) = 0 := rfl
    have hv1 : (i1 : ℕ) = 1 := rfl
    rcases hx with rfl | rfl <;>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hl, hv0, hv1] <;> omega
  have hcard : 2 ≤ (univ.filter fun i => k ≤ l i).card := by
    have := Finset.card_le_card hsub
    rwa [Finset.card_pair (by simp [i0, i1, Fin.ext_iff])] at this
  have hmul := Nat.mul_le_mul_left k hcard
  omega
end

section
open MvPolynomial Finset

noncomputable section

theorem SchPowerSumAtRootsOfUnity.rootOfUnity_isPrimitiveRoot {k : ℕ} (hk : 1 ≤ k) : IsPrimitiveRoot (rootOfUnity k) k := by
  simpa [rootOfUnity] using Complex.isPrimitiveRoot_exp k (by omega)

theorem SchPowerSumAtRootsOfUnity.proof : SchPowerSumAtRootsOfUnity.Statement := by
  intro N k j hk hkN hj
  have hprim := SchPowerSumAtRootsOfUnity.rootOfUnity_isPrimitiveRoot hk

  simp only [psum, map_sum, map_pow, aeval_X]
  have hsum : ∑ i : Fin N, rootOfUnityPoint N k i ^ j =
      ∑ i ∈ range k, (rootOfUnity k ^ j) ^ i := by
    unfold rootOfUnityPoint
    rw [Fin.sum_univ_eq_sum_range (fun i => (if i < k then rootOfUnity k ^ i else 0) ^ j) N,
      ← Finset.sum_range_add_sum_Ico _ hkN]
    rw [Finset.sum_eq_zero (s := Ico k N) (fun i hi => by
      simp only [Finset.mem_Ico] at hi
      simp [show ¬ i < k by omega, zero_pow (show j ≠ 0 by omega)]), add_zero]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp only [Finset.mem_range] at hi
    simp [hi, ← pow_mul, mul_comm]
  rw [hsum]
  split_ifs with hd
  · have h1 : rootOfUnity k ^ j = 1 := (hprim.pow_eq_one_iff_dvd j).2 hd
    simp [h1]
  · have h1 : rootOfUnity k ^ j ≠ 1 := fun h => hd ((hprim.pow_eq_one_iff_dvd j).1 h)
    have h2 : (rootOfUnity k ^ j) ^ k = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow]
    rw [geom_sum_eq h1, h2, sub_self, zero_div]

end
end

section
open Polynomial Finset

theorem SchProdOneSubRootsOfUnity.proof : SchProdOneSubRootsOfUnity.Statement := by
  intro k hk
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  have hζ : IsPrimitiveRoot (rootOfUnity k) k := Complex.isPrimitiveRoot_exp k (NeZero.ne k)
  refine eq_of_degree_sub_lt_of_eval_finset_eq (insert 0 (nthRootsFinset k 1)) ?_ fun x hx => ?_
  · rw [card_insert_of_notMem (by simp [mem_nthRootsFinset hk, zero_pow (NeZero.ne k)]),
      hζ.card_nthRootsFinset]
    refine (degree_le_of_natDegree_le (n := k) ?_).trans_lt (by exact_mod_cast Nat.lt_succ_self k)
    refine (natDegree_sub_le _ _).trans (max_le ?_ (by compute_degree))
    refine (natDegree_prod_le _ _).trans ?_
    exact (sum_le_sum (g := fun _ => 1) (fun i _ => by compute_degree)).trans (by simp)
  · rcases mem_insert.mp hx with rfl | hx
    · simp [eval_prod, zero_pow (NeZero.ne k)]
    · have hxk := (mem_nthRootsFinset hk _).mp hx
      obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one (show x⁻¹ ^ k = 1 by simp [inv_pow, hxk])
      simp only [eval_prod, eval_sub, eval_one, eval_pow, eval_X, hxk, sub_self]
      apply prod_eq_zero (mem_range.mpr hi)
      simp [hi', inv_mul_cancel₀ (ne_zero_of_mem_nthRootsFinset one_ne_zero hx)]
end

section
open MvPolynomial Finset

noncomputable section

theorem schurAtRoots_place_lt {r k : ℕ} (nu : Fin r → ℕ) (hanti : Antitone nu)
    (hsum : ∑ i, nu i = k) (i : Fin r) (hi : 1 ≤ nu i) : (i : ℕ) < k := by
  have h1 : (Iic i).card • 1 ≤ ∑ j ∈ Iic i, nu j :=
    Finset.card_nsmul_le_sum _ _ _ fun j hj => le_trans hi (hanti (Finset.mem_Iic.mp hj))
  have h2 : ∑ j ∈ Iic i, nu j ≤ ∑ j, nu j :=
    Finset.sum_le_sum_of_subset (Finset.subset_univ _)
  rw [Fin.card_Iic, smul_eq_mul, mul_one] at h1
  omega

theorem SchSchurAtRootsOfUnity.proof (h1 : SchSchurRowsToK.Statement)
    (h2 : SchSchurEvalMatrix.Statement) (h3 : SchJTMatrixDetAtRoots.Statement) :
    SchSchurAtRootsOfUnity.Statement := by
  intro N r k nu hk hkN hanti hsum
  set nu' : Fin k → ℕ := fun i => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0 with hnu'
  have hplace := schurAtRoots_place_lt nu hanti hsum

  have hanti' : Antitone nu' := by
    intro i j hij
    simp only [hnu']
    by_cases hj : (j : ℕ) < r
    · have hi : (i : ℕ) < r := lt_of_le_of_lt (Fin.le_def.mp hij) hj
      rw [dite_eq_left hi, dite_eq_left hj]
      exact hanti (Fin.le_def.mpr (Fin.le_def.mp hij))
    · rw [dite_eq_right hj]; exact Nat.zero_le _

  have hsum' : ∑ i, nu' i = k := by
    set g : ℕ → ℕ := fun i => if h : i < r then nu ⟨i, h⟩ else 0 with hg
    have e1 : ∑ i, nu' i = ∑ i ∈ range k, g i := by
      rw [← Fin.sum_univ_eq_sum_range]
    have e2 : ∑ i, nu i = ∑ i ∈ range r, g i := by
      rw [← Fin.sum_univ_eq_sum_range]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hg, dite_eq_left i.isLt]
    have hgk : ∀ i, k ≤ i → g i = 0 := by
      intro i hi
      simp only [hg]
      split_ifs with h
      · by_contra hne
        have := hplace ⟨i, h⟩ (Nat.one_le_iff_ne_zero.mpr hne)
        simp at this; omega
      · rfl
    have hgr : ∀ i, r ≤ i → g i = 0 := by
      intro i hi; simp only [hg]; rw [dite_eq_right (by omega)]
    have e3 : ∑ i ∈ range k, g i = ∑ i ∈ range (r + k), g i :=
      Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hni =>
         hgk i (not_lt.mp (fun h => hni (Finset.mem_range.mpr h)))
    have e4 : ∑ i ∈ range r, g i = ∑ i ∈ range (r + k), g i :=
      Finset.sum_subset (Finset.range_mono (by omega)) fun i _ hni =>
         hgr i (not_lt.mp (fun h => hni (Finset.mem_range.mpr h)))
    rw [e1, e3, ← e4, ← e2, hsum]
  rw [h1 (Fin N) r k nu hanti hsum, h2 N k k _ hk hkN, h3 k nu' hk hanti' hsum']

  have hcond : (∀ i : Fin k, (i : ℕ) ≠ 0 → nu' i ≤ 1) ↔ (∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1) := by
    constructor
    · intro H i hi0
      by_cases hz : nu i = 0
      · rw [hz]; exact Nat.zero_le _
      · have hik := hplace i (Nat.one_le_iff_ne_zero.mpr hz)
        have := H ⟨i, hik⟩ hi0
        simp only [hnu', dite_eq_left i.isLt] at this
        exact this
    · intro H i hi0
      simp only [hnu']
      split_ifs with h
      · exact H ⟨i, h⟩ hi0
      · exact Nat.zero_le _

  have hcard : (univ.filter fun i : Fin k => (i : ℕ) ≠ 0 ∧ nu' i = 1).card =
      (univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card := by
    refine Finset.card_bij'
      (fun i hi => ⟨i, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi
        by_contra h; rw [dite_eq_right h] at hi; omega⟩)
      (fun i hi => ⟨i, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact hplace i (by omega)⟩) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi ⊢
      obtain ⟨h0, h1⟩ := hi
      split_ifs at h1 with h
      exact ⟨h0, h1⟩
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hnu'] at hi ⊢
      refine ⟨hi.1, ?_⟩
      rw [dite_eq_left i.isLt]; exact hi.2
    · intro i hi; rfl
    · intro i hi; rfl
  simp only [hcond, hcard]

end

noncomputable section

theorem SchSchurEvalMatrix.aeval_completeSymmetric (h1 : SchCompleteAtRootsOfUnity.Statement)
    (N k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N) (d : ℤ) :
    aeval (rootOfUnityPoint N k) (completeSymmetric (Fin N) d) =
      if 0 ≤ d ∧ (k : ℤ) ∣ d then 1 else 0 := by
  unfold completeSymmetric
  by_cases h0 : 0 ≤ d
  · rw [ite_eq_left h0, h1 N k d.toNat hk hkN]
    have hdiv : (k ∣ d.toNat) ↔ ((k : ℤ) ∣ d) := by
      rw [← Int.natCast_dvd_natCast, Int.toNat_of_nonneg h0]
    by_cases hd : (k : ℤ) ∣ d
    · rw [ite_eq_left (hdiv.mpr hd), ite_eq_left ⟨h0, hd⟩]
    · rw [ite_eq_right (fun h => hd (hdiv.mp h)), ite_eq_right (fun h => hd h.2)]
  · rw [ite_eq_right h0, map_zero, ite_eq_right (fun h => h0 h.1)]

theorem SchSchurEvalMatrix.proof (h1 : SchCompleteAtRootsOfUnity.Statement) :
    SchSchurEvalMatrix.Statement := by
  intro N k r nu hk hkN
  unfold schur
  rw [AlgHom.map_det]
  congr 1
  ext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
    SchSchurEvalMatrix.aeval_completeSymmetric h1 N k hk hkN]
  rfl

end

theorem SchSchurRowsToK.proof : SchSchurRowsToK.Statement := by
  intro σ _ _ r k nu hanti hsum
  by_cases hrk : r ≤ k
  · exact (Schur.schur_padPartition σ nu k hrk).symm
  · replace hrk : k < r := Nat.lt_of_not_le hrk
    have hzero : ∀ i : Fin r, k ≤ (i : ℕ) → nu i = 0 := by
      intro i hi
      by_contra hne
      have hpos : 1 ≤ nu i := Nat.one_le_iff_ne_zero.mpr hne
      have h1 : ∑ j ∈ Finset.Iic i, 1 ≤ ∑ j ∈ Finset.Iic i, nu j :=
        Finset.sum_le_sum fun j hj => le_trans hpos (hanti (Finset.mem_Iic.mp hj))
      have h2 : ∑ j ∈ Finset.Iic i, nu j ≤ ∑ j, nu j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun _ _ _ => Nat.zero_le _)
      simp only [Finset.sum_const, smul_eq_mul, mul_one, Fin.card_Iic] at h1
      omega
    have heq : nu = Schur.padPartition r
        (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0) := by
      funext i
      simp only [Schur.padPartition]
      by_cases hik : (i : ℕ) < k
      · simp [hik, i.isLt]
      · simp only [hik, dite_false]
        exact hzero i (by omega)
    calc schur σ nu
        = schur σ (Schur.padPartition r
            (fun i : Fin k => if h : (i : ℕ) < r then nu ⟨i, h⟩ else 0)) :=
          congrArg (schur σ) heq
      _ = _ := Schur.schur_padPartition σ _ r hrk.le

noncomputable section

theorem SchSmallBlockProduct.sum_fin_staircase (r : ℕ) : ∑ i : Fin r, (r - 1 - (i : ℕ)) = r * (r - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r,
    Finset.sum_range_reflect (fun i => i) r, Finset.sum_range_id]

theorem SchSmallBlockProduct.vandermondeOf_X_comp {m : ℕ} {κ : Type*} (g : Fin m → κ) :
    vandermondeOf (fun i => (X (g i) : MvPolynomial κ ℚ)) =
      rename g (vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ))) := by
  simp [vandermondeOf, map_prod, map_sub, rename_X]

theorem SchSmallBlockProduct.vandermondeOf_X_eq_alternant (m : ℕ) :
    vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) =
      alternant (fun j : Fin m => m - 1 - (j : ℕ)) := by
  rw [← Schur.det_pow_staircase_eq_vandermondeOf, alternant, ← Matrix.det_transpose]
  rfl

theorem SchSmallBlockProduct.schur_mul_vandermondeOf_eq_alternant {m : ℕ} (lam : Fin m → ℕ) :
    schur (Fin m) lam * vandermondeOf (fun i : Fin m => (X i : MvPolynomial (Fin m) ℚ)) =
      alternant (fun i : Fin m => lam i + (m - 1 - (i : ℕ))) := by
  rw [← Schur.det_pow_add_staircase_eq, alternant, ← Matrix.det_transpose]
  rfl

theorem SchSmallBlockProduct.proof (h1 : SchAevalSignedRename.Statement)
    (h2 : SchAlternantHomogeneous.Statement) : SchSmallBlockProduct.Statement := by
  intro r a c lam
  set e : Fin r → ℕ := fun i => lam i + (r - 1 - (i : ℕ)) with he
  have hy : yRoot 1 r a c 0 = fun i => C c.sign * (X (yIndex 1 r a c 0 i) : RootRing 1 (r + a)) :=
    rfl
  have hz : zRoot 1 r a c 0 = fun i => (X (zIndex 1 r a c 0 i) : RootRing 1 (r + a)) := rfl

  have hVy : vandermondeOf (yRoot 1 r a c 0) =
      aeval (yRoot 1 r a c 0) (vandermondeOf (fun i : Fin r => (X i : MvPolynomial (Fin r) ℚ))) := by
    simp [vandermondeOf, map_prod, map_sub]

  have hdeg : ∑ i, e i = ∑ i, lam i + r * (r - 1) / 2 := by
    rw [he, Finset.sum_add_distrib, SchSmallBlockProduct.sum_fin_staircase]
  have hA : aeval (yRoot 1 r a c 0) (alternant e) =
      C (c.sign ^ (∑ i, lam i + r * (r - 1) / 2)) * rename (yIndex 1 r a c 0) (alternant e) := by
    rw [hy, ← hdeg]
    exact h1 (Fin r) (Fin 1 × Fin (r + a)) c.sign (yIndex 1 r a c 0) _ (alternant e) (h2 (Fin r) e)
  have hVz : vandermondeOf (zRoot 1 r a c 0) =
      rename (zIndex 1 r a c 0) (alternant fun j : Fin a => a - 1 - (j : ℕ)) := by
    rw [hz, SchSmallBlockProduct.vandermondeOf_X_comp, SchSmallBlockProduct.vandermondeOf_X_eq_alternant]
  have hplace_l : smallBlockPlace r a c ∘ Sum.inl = yIndex 1 r a c 0 := rfl
  have hplace_r : smallBlockPlace r a c ∘ Sum.inr = zIndex 1 r a c 0 := rfl
  rw [hVy, ← map_mul, SchSmallBlockProduct.schur_mul_vandermondeOf_eq_alternant, hA, hVz, map_mul, rename_rename,
    rename_rename, hplace_l, hplace_r, mul_assoc]

end
end

section
open Finset

theorem SchStrictAntiSplit.sum_staircase (r : ℕ) :
    ∑ i : Fin r, (r - 1 - (i : ℕ)) = r * (r - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => r - 1 - i) r, Finset.sum_range_reflect (fun i => i) r,
    Finset.sum_range_id]

theorem SchStrictAntiSplit.proof : SchStrictAntiSplit.Statement := by
  intro r n d hd hsum
  have hlow : ∀ i : Fin r, r - 1 - (i : ℕ) ≤ d i := by
    intro i
    have hr : 0 < r := Fin.pos i
    have h := _root_.UpperTheory.Reformulated.B.Yoa4.add_gap_le hd (r - 1 - (i : ℕ)) i ⟨r - 1, by omega⟩
      (by simp; omega)
    omega
  refine ⟨hlow, ?_⟩
  rw [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
  refine ⟨?_, ?_⟩
  · have hadd : ∑ i : Fin r, (d i - (r - 1 - (i : ℕ))) + ∑ i : Fin r, (r - 1 - (i : ℕ)) =
        ∑ i : Fin r, d i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hlow i)
    rw [SchStrictAntiSplit.sum_staircase] at hadd
    omega
  · intro i j hij
    have h := _root_.UpperTheory.Reformulated.B.Yoa4.add_gap_le hd ((j : ℕ) - i) i j (by omega)
    have := hlow i
    have := hlow j
    have : (i : ℕ) ≤ j := hij
    have : (j : ℕ) < r := j.isLt
    show d j - (r - 1 - (j : ℕ)) ≤ d i - (r - 1 - (i : ℕ))
    omega
end

section
open MvPolynomial Finset

theorem SchWeightedPreimage.proof (h1 : SchPowerSumHomWeighted.Statement) :
    SchWeightedPreimage.Statement := by
  classical
  intro N k P hsym hhom
  obtain ⟨S₀, hS₀⟩ := Flag.exists_powerSumHom_eq hsym
  let w : Fin N → ℕ := fun i => (i : ℕ) + 1
  refine ⟨weightedHomogeneousComponent w k S₀, ?_,
    weightedHomogeneousComponent_isWeightedHomogeneous k S₀⟩
  have hfin := weightedHomogeneousComponent_finsupp (w := w) S₀
  have hsum := sum_weightedHomogeneousComponent w S₀
  rw [finsum_eq_sum _ hfin] at hsum
  have hterm : ∀ m : ℕ, homogeneousComponent k (powerSumHom N (weightedHomogeneousComponent w m S₀))
      = if k = m then powerSumHom N (weightedHomogeneousComponent w m S₀) else 0 :=
    fun m => homogeneousComponent_of_mem
      (h1 N m _ (weightedHomogeneousComponent_isWeightedHomogeneous m S₀))
  have key : homogeneousComponent k (powerSumHom N S₀) =
      powerSumHom N (weightedHomogeneousComponent w k S₀) := by
    conv_lhs => rw [← hsum]

    rw [map_sum, map_sum]
    simp only [hterm, Finset.sum_ite_eq]
    split_ifs with hk
    · rfl
    · have hk0 : weightedHomogeneousComponent w k S₀ = 0 := by
        by_contra hne
        exact hk (Set.Finite.mem_toFinset (hs := hfin) |>.mpr hne)
      rw [hk0, map_zero]
  rw [← key, hS₀, homogeneousComponent_eq_self hhom]

noncomputable section

theorem SchurPowerSumCoefficient.proof (h1 : SchWeightedPreimage.Statement)
    (h2 : SchEvalPowerSumHom.Statement) (h3 : SchSchurHomogeneous.Statement)
    (h4 : SchSchurAtRootsOfUnity.Statement) : SchurPowerSumCoefficient.Statement := by
  intro N r k hk1 hkN nu hanti hsum
  have hhom := h3 (Fin N) r nu
  rw [hsum] at hhom
  obtain ⟨S, hS, hw⟩ := h1 N k (schur (Fin N) nu) (Schur.schur_isSymmetric (σ := Fin N) nu) hhom
  refine ⟨S, hS, ?_⟩
  have e1 := h2 N k hk1 hkN S hw
  rw [hS, h4 N r k nu hk1 hkN hanti hsum] at e1
  have hk : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  apply Rat.cast_injective (α := ℂ)
  split_ifs with h
  · rw [ite_eq_left h] at e1
    push_cast
    rw [eq_div_iff hk]
    linear_combination -e1
  · rw [ite_eq_right h] at e1
    push_cast
    rcases mul_eq_zero.mp e1.symm with h0 | h0
    · exact absurd h0 hk
    · exact h0

end
end

end GroundTheory.Heights₂.Heights.RestTerms

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem SchurSignCoefficient.coeff_aeval_diagonal {N : ℕ} (c : Fin N → ℚ)
    (P : MvPolynomial (Fin N) ℚ) (e : Fin N →₀ ℕ) :
    AddMonoidAlgebra.coeff (aeval (fun i : Fin N => C (c i) * X i) P) e = (∏ i, c i ^ e i) * AddMonoidAlgebra.coeff P e := by
  induction P using MvPolynomial.induction_on' with
  | monomial u a =>
    have hmon : aeval (fun i : Fin N => C (c i) * X i) (monomial u a) =
        monomial u (a * ∏ i, c i ^ u i) := by
      rw [aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (by simp),
        Finsupp.prod_fintype _ _ (by simp)]
      simp only [mul_pow, Finset.prod_mul_distrib, algebraMap_eq, C_mul, ← C_pow, ← map_prod]
      ring
    rw [hmon, coeff_monomial, coeff_monomial]
    split_ifs with hue
    · subst hue; ring
    · simp
  | add p q hp hq => rw [map_add (f := _), MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem SchurSignCoefficient.aeval_smul_powerSumHom (N : ℕ) (s : ℚ)
    (S : MvPolynomial (Fin N) ℚ) :
    aeval (fun i : Fin N => C s * X i) (powerSumHom N S) =
      powerSumHom N (aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i) S) := by
  have key : (aeval (fun i : Fin N => C s * X i)).comp (powerSumHom N) =
      (powerSumHom N).comp (aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i)) := by
    apply MvPolynomial.algHom_ext
    intro i

    simp only [AlgHom.comp_apply, powerSumHom, aeval_X, map_mul, aeval_C, algebraMap_eq, psum,
    map_sum, map_pow, mul_pow, Finset.mul_sum]
  exact DFunLike.congr_fun key S

theorem SchurSignCoefficient.proof (h : SchurPowerSumCoefficient.Statement) :
    SchurSignCoefficient.Statement := by
  intro N r k hk1 hkN nu s _ hnu hsum
  obtain ⟨S₀, hS₀, hc₀⟩ := h N r k hk1 hkN nu hnu hsum
  refine ⟨aeval (fun i : Fin N => C (s ^ ((i : ℕ) + 1)) * X i) S₀, ?_, ?_⟩
  · rw [← SchurSignCoefficient.aeval_smul_powerSumHom, hS₀]
  · rw [SchurSignCoefficient.coeff_aeval_diagonal, hc₀]
    congr 1
    rw [Finset.prod_eq_single (⟨k - 1, by omega⟩ : Fin N)]
    · rw [Finsupp.single_eq_same, pow_one]
      congr 1
      simp only
      omega
    · intro b _ hb
      rw [Finsupp.single_apply, ite_eq_right (Ne.symm hb), pow_zero]
    · intro hn
      exact absurd (Finset.mem_univ _) hn

end

end RestTerms

end GroundTheory.Heights₂.Heights
