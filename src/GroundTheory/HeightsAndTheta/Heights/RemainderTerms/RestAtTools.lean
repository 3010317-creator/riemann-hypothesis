module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PHomogeneousComponentMul
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Statements
public import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace GroundTheory.Heights₂.Heights.RestTerms

section
open MvPolynomial Finset

noncomputable section

namespace FlagEq

variable {f N : ℕ}

def permSign (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : ℤ :=
  ∏ τ, ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)

def stairExp (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : Fin f × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => N - 1 - ((w v.1).symm v.2 : ℕ)

def rho (f N : ℕ) : Fin f × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => N - 1 - (v.2 : ℕ)

def stairConst (f N : ℕ) : ℝ := (∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ)) ^ f

theorem stairExp_one : stairExp f N 1 = rho f N := by
  ext v; simp [stairExp, rho, Equiv.Perm.one_def]

theorem permSign_one : permSign f N 1 = 1 := by simp [permSign]

theorem permSign_inv (w : Fin f → Equiv.Perm (Fin N)) : permSign f N w⁻¹ = permSign f N w := by
  simp [permSign, Equiv.Perm.sign_inv]

theorem permSign_mul (u w : Fin f → Equiv.Perm (Fin N)) :
    permSign f N (u * w) = permSign f N u * permSign f N w := by
  simp [permSign, Equiv.Perm.sign_mul, prod_mul_distrib]

theorem permSign_mul_self (u : Fin f → Equiv.Perm (Fin N)) :
    permSign f N u * permSign f N u = 1 := by
  rw [permSign, ← prod_mul_distrib]
  exact prod_eq_one fun τ _ => by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

theorem stairConst_pos : 0 < stairConst f N :=
  pow_pos (prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _) _

theorem coeff_rename_prodCongrRight {R : Type*} [CommSemiring R] (w : Fin f → Equiv.Perm (Fin N))
    (P : MvPolynomial (Fin f × Fin N) R) (d : Fin f × Fin N →₀ ℕ) :
    AddMonoidAlgebra.coeff (rename (Equiv.prodCongrRight w) P) d =
      AddMonoidAlgebra.coeff P (Finsupp.equivFunOnFinite.symm fun v => d (Equiv.prodCongrRight w v)) := by
  rw [← coeff_rename_mapDomain (Equiv.prodCongrRight w) (Equiv.injective _) P]
  congr 1
  ext v
  obtain ⟨u, rfl⟩ := (Equiv.prodCongrRight w).surjective v
  rw [Finsupp.mapDomain_apply_of_injective (Equiv.injective _)]
  simp

theorem coeff_rho_antisym {R : Type*} [CommRing R] (P : MvPolynomial (Fin f × Fin N) R) :
    AddMonoidAlgebra.coeff (∑ w : Fin f → Equiv.Perm (Fin N),
        ((permSign f N w : ℤ) : R) • rename (Equiv.prodCongrRight w) P) (rho f N) =
      ∑ w, ((permSign f N w : ℤ) : R) * AddMonoidAlgebra.coeff P (stairExp f N w) := by
  rw [coeff_sum]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ (fun w => ?_)
  rw [MvPolynomial.coeff_smul, smul_eq_mul, coeff_rename_prodCongrRight, Equiv.inv_apply, permSign_inv]
  congr 2

theorem blockVandermonde_eq_sum (f N : ℕ) :
    blockVandermonde f N = ∑ w : Fin f → Equiv.Perm (Fin N),
      ((permSign f N w : ℤ) : ℚ) • monomial (stairExp f N w) (1 : ℚ) := by
  simp only [blockVandermonde, Comb.vandermondeOf_eq_det, Matrix.det_apply', Matrix.of_apply]
  rw [prod_univ_sum, Fintype.piFinset_univ]
  refine sum_congr rfl fun w _ => ?_
  rw [prod_mul_distrib, smul_eq_C_mul, monomial_eq, C_1, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  congr 1
  · simp [permSign]
  · refine prod_congr rfl fun τ _ => ?_
    symm
    rw [← Equiv.prod_comp (w τ)]
    simp [stairExp]

theorem coeff_blockVandermonde (α : Fin f × Fin N →₀ ℕ) :
    AddMonoidAlgebra.coeff (blockVandermonde f N) α =
      ∑ w, ((permSign f N w : ℤ) : ℚ) * if stairExp f N w = α then 1 else 0 := by
  rw [blockVandermonde_eq_sum, coeff_sum]
  simp only [MvPolynomial.coeff_smul, coeff_monomial, smul_eq_mul]

theorem eq_one_of_stairExp_eq (w : Fin f → Equiv.Perm (Fin N)) (h : stairExp f N w = rho f N) :
    w = 1 := by
  funext τ
  ext i
  have h1 := DFunLike.congr_fun h (τ, w τ i)
  simp [stairExp, rho] at h1
  have := (w τ i).isLt
  have := i.isLt
  simp only [Pi.one_apply, Equiv.Perm.coe_one, id_eq]
  omega

theorem prod_factorial_stairExp (w : Fin f → Equiv.Perm (Fin N)) :
    (stairExp f N w).prod (fun _ e => (e.factorial : ℝ)) = stairConst f N := by
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Fintype.prod_prod_type]
  have h : ∀ τ, ∏ i : Fin N, ((stairExp f N w (τ, i)).factorial : ℝ) =
      ∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ) := by
    intro τ
    simp only [stairExp, Finsupp.coe_equivFunOnFinite_symm]
    exact Equiv.prod_comp (w τ).symm (fun i : Fin N => ((N - 1 - (i : ℕ)).factorial : ℝ))
  rw [prod_congr rfl (fun τ _ => h τ), prod_const, card_univ, Fintype.card_fin, stairConst]

theorem rho_degree (f N : ℕ) : (rho f N).degree = f * (N * (N - 1) / 2) := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [rho, Finsupp.coe_equivFunOnFinite_symm, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]
  have h := sum_range_reflect (fun i => i) N
  rw [h, sum_range_id]

end FlagEq

end
end

section
open MvPolynomial Finset

noncomputable section

def flagIntegralReal (f N : ℕ) : MvPolynomial (Fin f × Fin N) ℝ →ₗ[ℝ] ℝ where
  toFun G := ∑ α ∈ (blockVandermonde f N).support,
    AddMonoidAlgebra.coeff G α * ((AddMonoidAlgebra.coeff (blockVandermonde f N) α : ℚ) : ℝ) * α.prod (fun _ e => (e.factorial : ℝ))
  map_add' G H := by simp only [MvPolynomial.coeff_add, add_mul, sum_add_distrib]
  map_smul' c G := by simp only [MvPolynomial.coeff_smul, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc]

theorem flagIntegralReal_map (f N : ℕ) (Φ : RootRing f N) :
    flagIntegralReal f N (map (algebraMap ℚ ℝ) Φ) = (flagIntegral f N Φ : ℝ) := by
  simp [flagIntegralReal, flagIntegral, coeff_map, Finsupp.prod]

namespace FlagEq

theorem flagIntegralReal_eq {f N : ℕ} (G : MvPolynomial (Fin f × Fin N) ℝ) :
    flagIntegralReal f N G =
      stairConst f N * ∑ w, ((permSign f N w : ℤ) : ℝ) * AddMonoidAlgebra.coeff G (stairExp f N w) := by
  classical
  have hsub : (blockVandermonde f N).support ⊆
      (blockVandermonde f N).support ∪ univ.image (stairExp f N) := subset_union_left
  show ∑ α ∈ _, _ = _
  rw [sum_subset hsub (fun α _ hα => by rw [notMem_support_iff.mp hα]; simp)]
  have hc : ∀ α : Fin f × Fin N →₀ ℕ, ((AddMonoidAlgebra.coeff (blockVandermonde f N) α : ℚ) : ℝ) =
      ∑ w, ((permSign f N w : ℤ) : ℝ) * if stairExp f N w = α then 1 else 0 := by
    intro α
    rw [coeff_blockVandermonde, Rat.cast_sum]
    refine sum_congr rfl fun w _ => ?_
    split_ifs <;> simp
  simp only [hc, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  rw [sum_ite_eq, ite_eq_left (mem_union_right _ (mem_image_of_mem _ (mem_univ w))),
    prod_factorial_stairExp]
  ring

theorem ddConst_apply (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      AddMonoidAlgebra.coeff (∑ w : Fin f → Equiv.Perm (Fin (j + k)),
        ((permSign f (j + k) w : ℤ) : ℝ) • rename (Equiv.prodCongrRight w) G) (rho f (j + k)) := by
  simp [IndefiniteRowSideFullHecke.RestTerms.ddConst, IndefiniteRowSideFullHecke.RestTerms.blockAntisym, permSign, rho,
    IndefiniteRowSideFullHecke.RestTerms.rhoMon, smul_eq_mul]

theorem ddConst_eq (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      ∑ w, ((permSign f (j + k) w : ℤ) : ℝ) * AddMonoidAlgebra.coeff G (stairExp f (j + k) w) := by
  rw [ddConst_apply, coeff_rho_antisym]

theorem rename_psumAt (f j k m : ℕ) (τ : Fin f) (w : Fin f → Equiv.Perm (Fin (j + k))) :
    rename (Equiv.prodCongrRight w) (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ) =
      IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ := by

  simp only [IndefiniteRowSideFullHecke.RestTerms.psumAt, map_sum, map_pow, rename_X, Equiv.prodCongrRight_apply]
  exact Equiv.sum_comp (w τ) (fun i => (X (τ, i) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) ^ m)

def antisym (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k :=
  ∑ w : Fin f → Equiv.Perm (Fin (j + k)),
    ((permSign f (j + k) w : ℤ) : ℝ) • rename (Equiv.prodCongrRight w) G

theorem antisym_psumAt_mul (f j k m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    antisym f j k (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) =
      IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * antisym f j k G := by
  simp only [antisym, map_mul, rename_psumAt, mul_sum, mul_smul_comm]

theorem rename_antisym (f j k : ℕ) (u : Fin f → Equiv.Perm (Fin (j + k)))
    (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    rename (Equiv.prodCongrRight u) (antisym f j k G) =
      ((permSign f (j + k) u : ℤ) : ℝ) • antisym f j k G := by
  have hcomp : ∀ w : Fin f → Equiv.Perm (Fin (j + k)),
      rename (Equiv.prodCongrRight u) (rename (Equiv.prodCongrRight w) G) =
        rename (Equiv.prodCongrRight (u * w)) G := by
    intro w
    rw [rename_rename]
    congr 1
  have hs : ((permSign f (j + k) u : ℤ) : ℝ) * ((permSign f (j + k) u : ℤ) : ℝ) = 1 := by
    exact_mod_cast permSign_mul_self u

  simp only [antisym, map_sum, map_smul, hcomp, smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun w => ?_)
  simp only [Equiv.coe_mulLeft, permSign_mul]
  push_cast
  rw [← mul_assoc, hs, one_mul]

theorem coeff_eq_zero_of_swap {f N : ℕ} (A : MvPolynomial (Fin f × Fin N) ℝ)
    (hA : ∀ u : Fin f → Equiv.Perm (Fin N),
      rename (Equiv.prodCongrRight u) A = ((permSign f N u : ℤ) : ℝ) • A)
    (β : Fin f × Fin N →₀ ℕ) (τ : Fin f) (i i' : Fin N) (hii : i ≠ i')
    (hβ : β (τ, i) = β (τ, i')) : AddMonoidAlgebra.coeff A β = 0 := by
  classical
  let u : Fin f → Equiv.Perm (Fin N) := Pi.mulSingle τ (Equiv.swap i i')
  have hu1 : u τ = Equiv.swap i i' := Pi.mulSingle_eq_same _ _
  have hu2 : ∀ τ', τ' ≠ τ → u τ' = 1 := fun τ' h => Pi.mulSingle_eq_of_ne h _
  have hs : permSign f N u = -1 := by
    rw [permSign, Fintype.prod_eq_single τ]
    · rw [hu1, Equiv.Perm.sign_swap hii]; rfl
    · intro τ' h; rw [hu2 τ' h]; simp
  have hfix : (Finsupp.equivFunOnFinite.symm fun v => β (Equiv.prodCongrRight u v)) = β := by
    ext ⟨τ', l⟩
    simp only [Finsupp.coe_equivFunOnFinite_symm, Equiv.prodCongrRight_apply]
    by_cases h : τ' = τ
    · subst h
      rw [hu1]
      rcases eq_or_ne l i with rfl | h1
      · rw [Equiv.swap_apply_left, hβ]
      · rcases eq_or_ne l i' with rfl | h2
        · rw [Equiv.swap_apply_right, hβ]
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · rw [hu2 τ' h]; rfl
  have h := congrArg (AddMonoidAlgebra.coeff · β) (hA u)
  rw [coeff_rename_prodCongrRight, hfix, hs, MvPolynomial.coeff_smul, smul_eq_mul] at h
  push_cast at h
  linarith

theorem ddConst_psumAt_mul (f j k m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hm : 1 ≤ m) : IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) = 0 := by
  classical
  rw [ddConst_apply, ← antisym, antisym_psumAt_mul, IndefiniteRowSideFullHecke.RestTerms.psumAt, sum_mul, coeff_sum]
  refine sum_eq_zero fun i _ => ?_
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs with h
  · rw [Finsupp.single_le_iff] at h
    simp only [rho, Finsupp.coe_equivFunOnFinite_symm] at h
    have hi : (i : ℕ) + m < j + k := by have := i.isLt; omega
    have hii : i ≠ ⟨(i : ℕ) + m, hi⟩ := by
      intro h'; have := congrArg Fin.val h'; simp at this; omega
    rw [coeff_eq_zero_of_swap _ (fun u => rename_antisym f j k u G) _ τ i ⟨(i : ℕ) + m, hi⟩ hii, mul_zero]
    rw [Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by intro h'; simp at h'; exact hii h'.symm)]
    simp only [rho, Finsupp.coe_equivFunOnFinite_symm]
    omega
  · rfl

theorem ddConst_monomial_rho (f j k : ℕ) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (monomial (rho f (j + k)) (1 : ℝ)) = 1 := by
  rw [ddConst_eq, Fintype.sum_eq_single 1]
  · simp [stairExp_one, permSign_one]
  · intro w hw
    rw [coeff_monomial, ite_eq_right (fun h => hw (eq_one_of_stairExp_eq w h.symm)), mul_zero]

end FlagEq

open FlagEq in
theorem flagIntegralReal_eq_mul_ddConst (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    flagIntegralReal f (j + k) G = stairConst f (j + k) * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G := by
  rw [flagIntegralReal_eq, ddConst_eq]

end
end

end GroundTheory.Heights₂.Heights.RestTerms

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def rootRingToReal (f N j k : ℕ) (h : N = j + k) : RootRing f N →+* IndefiniteRowSideFullHecke.RestTerms.Roots f j k :=
  (rename (R := ℝ) (Prod.map id (finCongr h))).toRingHom.comp (MvPolynomial.map (algebraMap ℚ ℝ))

@[simp] theorem rootRingToReal_X (f N j k : ℕ) (h : N = j + k) (v : Fin f × Fin N) :
    rootRingToReal f N j k h (X v) = X (v.1, finCongr h v.2) := by
  simp only [rootRingToReal, RingHom.comp_apply, map_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    rename_X] <;> rfl

@[simp] theorem rootRingToReal_C (f N j k : ℕ) (h : N = j + k) (q : ℚ) :
    rootRingToReal f N j k h (C q) = C (q : ℝ) := by
  simp [rootRingToReal]

theorem rootRingToReal_isHomogeneous_iff (f N j k : ℕ) (h : N = j + k) (P : RootRing f N) (n : ℕ) :
    (rootRingToReal f N j k h P).IsHomogeneous n ↔ P.IsHomogeneous n := by
  rw [rootRingToReal, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    IsHomogeneous.rename_isHomogeneous_iff
      (Function.Injective.prodMap Function.injective_id (finCongr h).injective)]
  constructor
  · intro hP d hd
    apply hP
    rw [coeff_map]
    exact (map_ne_zero_iff _ (algebraMap ℚ ℝ).injective).mpr hd
  · intro hP
    exact hP.map _

theorem map_vandermondeOf {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {m : ℕ}
    (v : Fin m → R) : φ (vandermondeOf v) = vandermondeOf (fun i => φ (v i)) := by
  simp [vandermondeOf, map_prod, map_sub]

theorem vandermondeOf_eq_vandermonde {R : Type*} [CommRing R] {m : ℕ} (v : Fin m → R) :
    vandermondeOf v = GroundTheory.Heights₂.Heights.vandermonde v := by
  have hM : (Matrix.of fun a b : Fin m => v a ^ (m - 1 - (b : ℕ))) =
      (Matrix.vandermonde v).submatrix id Fin.revPerm := by
    ext a b
    simp only [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.vandermonde_apply,
      Fin.revPerm_apply, Fin.val_rev]
    congr 1
    omega
  have hW : Matrix.vandermonde (fun i => v (Fin.revPerm i)) =
      (Matrix.vandermonde v).submatrix Fin.revPerm id := by
    ext a b
    simp [Matrix.vandermonde_apply]
  rw [GroundTheory.Heights₂.Heights.vandermonde, hM, Matrix.det_permute', ← Matrix.det_permute, ← hW,
    Matrix.det_vandermonde]
  have key : ∀ g : Fin m → Fin m → R,
      ∏ i, ∏ l ∈ Ioi i, g i l = ∏ i, ∏ l, if i < l then g i l else 1 := by
    intro g
    refine prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_filter]
    congr 1
    ext l
    simp
  rw [vandermondeOf, key, key]
  conv_rhs => rw [Finset.prod_comm]
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun i => ?_)
  refine Fintype.prod_equiv Fin.revPerm _ _ (fun l => ?_)
  simp [Fin.revPerm_apply, Fin.rev_lt_rev]

theorem rootRingToReal_blockPowerSum (f N j k : ℕ) (h : N = j + k) (m : ℕ) (τ : Fin f) :
    rootRingToReal f N j k h (blockPowerSum f N m τ) = IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ := by
  subst h
  simp [blockPowerSum, IndefiniteRowSideFullHecke.RestTerms.psumAt]

theorem rootRingToReal_smallPowerSum_last (f r a m : ℕ) (τ : Fin f) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (smallPowerSum f r a .last m τ) =
      IndefiniteRowSideFullHecke.RestTerms.smallPsum f a r true m τ := by

  simp only [smallPowerSum, yRoot, SmallBlock.sign, yIndex, map_sum, map_pow, rootRingToReal_X, IndefiniteRowSideFullHecke.RestTerms.smallPsum, ite_true, C_1, one_mul]
  refine sum_congr rfl fun i _ => ?_
  rfl

theorem rootRingToReal_smallPowerSum_first (f r a m : ℕ) (τ : Fin f) :
    rootRingToReal f (r + a) r a rfl (smallPowerSum f r a .first m τ) =
      IndefiniteRowSideFullHecke.RestTerms.smallPsum f r a false m τ := by

  simp only [smallPowerSum, yRoot, SmallBlock.sign, yIndex, map_sum, map_pow, rootRingToReal_X, IndefiniteRowSideFullHecke.RestTerms.smallPsum, Bool.false_eq_true, ite_false,
  C_1, neg_one_mul, map_neg]
  refine sum_congr rfl fun i _ => ?_
  rfl

theorem rootRingToReal_smallBlockMu_last (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (smallBlockMu f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.muClass f a r true := by

  rw [IndefiniteRowSideFullHecke.RestTerms.muClass, smallBlockMu, map_sum]
  refine sum_congr rfl fun τ _ => ?_
  rw [← rootRingToReal_smallPowerSum_last]
  simp [smallPowerSum]

theorem rootRingToReal_smallBlockMu_first (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (smallBlockMu f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.muClass f r a false := by

  rw [IndefiniteRowSideFullHecke.RestTerms.muClass, smallBlockMu, map_sum]
  refine sum_congr rfl fun τ _ => ?_
  rw [← rootRingToReal_smallPowerSum_first]
  simp [smallPowerSum]

theorem rootRingToReal_fibreClass_last (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (fibreClass f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.fibClass f a r true := by
  simp only [fibreClass, IndefiniteRowSideFullHecke.RestTerms.fibClass, ite_true, map_prod, map_mul, map_vandermondeOf]
  refine prod_congr rfl fun τ _ => ?_
  rw [vandermondeOf_eq_vandermonde, vandermondeOf_eq_vandermonde]
  congr 2
  · funext i
    simp only [yRoot, SmallBlock.sign, yIndex, rootRingToReal_X, C_1, one_mul] <;> rfl
  · funext i
    simp only [zRoot, zIndex, rootRingToReal_X] <;> rfl

theorem rootRingToReal_fibreClass_first (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (fibreClass f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.fibClass f r a false := by
  simp only [fibreClass, IndefiniteRowSideFullHecke.RestTerms.fibClass, Bool.false_eq_true, ite_false, map_prod, map_mul,
    map_vandermondeOf]
  refine prod_congr rfl fun τ _ => ?_
  rw [vandermondeOf_eq_vandermonde, vandermondeOf_eq_vandermonde]
  congr 2
  · funext i
    simp only [yRoot, SmallBlock.sign, yIndex, rootRingToReal_X, C_1, neg_one_mul, map_neg] <;> rfl
  · funext i
    simp only [zRoot, zIndex, rootRingToReal_X] <;> rfl

theorem rootRingToReal_restPolynomial_last (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a) (restPolynomial f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.restPoly f a r true := by
  rw [restPolynomial, IndefiniteRowSideFullHecke.RestTerms.restPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_last,
    rootRingToReal_fibreClass_last, IndefiniteRowSideFullHecke.RestTerms.nDim, show f * a * r = f * (r * a) by ring]

theorem rootRingToReal_restPolynomial_first (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl (restPolynomial f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.restPoly f r a false := by
  rw [restPolynomial, IndefiniteRowSideFullHecke.RestTerms.restPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_first,
    rootRingToReal_fibreClass_first, IndefiniteRowSideFullHecke.RestTerms.nDim, Nat.mul_assoc]

theorem rootRingToReal_degreePolynomial_last (f r a : ℕ) :
    rootRingToReal f (r + a) a r (Nat.add_comm r a)
        (smallBlockMu f r a .last ^ (f * (r * a)) * fibreClass f r a .last) =
      IndefiniteRowSideFullHecke.RestTerms.degPoly f a r true := by
  rw [IndefiniteRowSideFullHecke.RestTerms.degPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_last,
    rootRingToReal_fibreClass_last, IndefiniteRowSideFullHecke.RestTerms.nDim, show f * a * r = f * (r * a) by ring]

theorem rootRingToReal_degreePolynomial_first (f r a : ℕ) :
    rootRingToReal f (r + a) r a rfl
        (smallBlockMu f r a .first ^ (f * (r * a)) * fibreClass f r a .first) =
      IndefiniteRowSideFullHecke.RestTerms.degPoly f r a false := by
  rw [IndefiniteRowSideFullHecke.RestTerms.degPoly, map_mul, map_pow, rootRingToReal_smallBlockMu_first,
    rootRingToReal_fibreClass_first, IndefiniteRowSideFullHecke.RestTerms.nDim, Nat.mul_assoc]

theorem blockPowerSum_isHomogeneous (f N m : ℕ) (τ : Fin f) :
    (blockPowerSum f N m τ).IsHomogeneous m :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_X_pow _ _

theorem isPowerSumDecomposition_homogeneousComponent (f N : ℕ) (F : RootRing f N)
    (Q : ℕ → Fin f → RootRing f N) (hF : F.IsHomogeneous (topDegree f N + 1))
    (hQ : IsPowerSumDecomposition f N F Q) :
    IsPowerSumDecomposition f N F
        (fun m τ => homogeneousComponent (topDegree f N + 1 - m) (Q m τ)) ∧
      ∀ m τ, (homogeneousComponent (topDegree f N + 1 - m) (Q m τ)).IsHomogeneous
        (topDegree f N + 1 - m) := by
  refine ⟨?_, fun m τ => homogeneousComponent_isHomogeneous _ _⟩
  have hle : ∀ m, m ≤ N → ∀ τ : Fin f, m ≤ topDegree f N + 1 := by
    intro m hm τ
    have hf : 0 < f := τ.pos
    have h1 : N - 1 ≤ N * (N - 1) / 2 := by
      rw [Nat.le_div_iff_mul_le (by norm_num)]
      rcases N with _ | n
      · simp
      · simp only [Nat.add_sub_cancel]
        rcases n with _ | n
        · simp
        · nlinarith
    have h2 : N * (N - 1) / 2 ≤ topDegree f N := Nat.le_mul_of_pos_left _ hf
    omega
  unfold IsPowerSumDecomposition at hQ ⊢
  have hcomp : homogeneousComponent (topDegree f N + 1) F = F := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2 hF), ite_eq_left rfl]
  conv_lhs => rw [← hcomp, hQ]

  simp only [map_sum]
  refine sum_congr rfl fun m hm => sum_congr rfl fun τ _ => ?_
  rw [HomogeneousComponentMul.proof _ _ _ _ _ _ (blockPowerSum_isHomogeneous f N m τ),
    ite_eq_left (hle m (Finset.mem_Icc.1 hm).2 τ)]

end

end GroundTheory.Heights₂.Heights.RestTerms
end

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace TermBoundEq

theorem flagIntegralReal_rootRingToReal (f N j k : ℕ) (h : N = j + k) (P : RootRing f N) :
    flagIntegralReal f (j + k) (rootRingToReal f N j k h P) = (flagIntegral f N P : ℝ) := by
  subst h
  have hid : (Prod.map id (finCongr (rfl : j + k = j + k)) : Fin f × Fin (j + k) → _) = id :=
    funext fun _ => rfl
  have : rootRingToReal f (j + k) j k rfl P = map (algebraMap ℚ ℝ) P := by
    simp only [rootRingToReal, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hid,
      rename_id_apply]
  rw [this, flagIntegralReal_map]

def coeffMap {σ : Type*} (φ : Module.Dual ℚ ℝ) (P : MvPolynomial σ ℝ) : MvPolynomial σ ℚ :=
  ∑ d ∈ P.support, monomial d (φ (AddMonoidAlgebra.coeff P d))

variable {σ : Type*} (φ : Module.Dual ℚ ℝ)

theorem coeff_coeffMap (P : MvPolynomial σ ℝ) (d : σ →₀ ℕ) :
    AddMonoidAlgebra.coeff (coeffMap φ P) d = φ (AddMonoidAlgebra.coeff P d) := by
  classical
  rw [coeffMap, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hd
  · rfl
  · rw [notMem_support_iff.1 hd, map_zero]

theorem coeffMap_sum {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial σ ℝ) :
    coeffMap φ (∑ i ∈ s, P i) = ∑ i ∈ s, coeffMap φ (P i) := by
  ext d

  simp only [coeff_coeffMap, coeff_sum, map_sum]

theorem coeffMap_map_mul (R : MvPolynomial σ ℚ) (P : MvPolynomial σ ℝ) :
    coeffMap φ (map (algebraMap ℚ ℝ) R * P) = R * coeffMap φ P := by
  classical
  ext d

  rw [coeff_coeffMap, coeff_mul, coeff_mul, map_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [coeff_map, coeff_coeffMap, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem coeffMap_map (R : MvPolynomial σ ℚ) :
    coeffMap φ (map (algebraMap ℚ ℝ) R) = φ 1 • R := by
  ext d
  rw [coeff_coeffMap, coeff_map, MvPolynomial.coeff_smul, smul_eq_mul, ← mul_one (algebraMap ℚ ℝ _),
    ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem dual_flagIntegralReal (f N : ℕ) (P : MvPolynomial (Fin f × Fin N) ℝ) :
    φ (flagIntegralReal f N P) = flagIntegral f N (coeffMap φ P) := by
  have hterm : ∀ α : Fin f × Fin N →₀ ℕ,
      AddMonoidAlgebra.coeff P α * ((AddMonoidAlgebra.coeff (blockVandermonde f N) α : ℚ) : ℝ) *
          α.prod (fun _ e => (e.factorial : ℝ)) =
        (AddMonoidAlgebra.coeff (blockVandermonde f N) α * α.prod (fun _ e => (e.factorial : ℚ))) • AddMonoidAlgebra.coeff P α := by
    intro α
    rw [Rat.smul_def]
    simp only [Finsupp.prod, Rat.cast_mul, Rat.cast_prod, Rat.cast_natCast]
    ring
  show φ (∑ α ∈ _, _) = _

  simp only [hterm, map_sum, map_smul, smul_eq_mul, flagIntegral, coeff_coeffMap]
  exact sum_congr rfl fun α _ => by ring

theorem flagIntegral_sub_smul (f N : ℕ) (A B : RootRing f N) (s : ℚ) :
    flagIntegral f N (A - s • B) = flagIntegral f N A - s * flagIntegral f N B := by
  rw [flagIntegral, flagIntegral, flagIntegral, mul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun α _ => ?_
  rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, smul_eq_mul]
  ring

end TermBoundEq

end

end GroundTheory.Heights₂.Heights.RestTerms
