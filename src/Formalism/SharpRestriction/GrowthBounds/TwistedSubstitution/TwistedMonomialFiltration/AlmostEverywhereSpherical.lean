module

import Formalism.SharpRestriction.GrowthBounds.RootWeights.DerivativeValuationBounds
public import Formalism.SharpRestriction.GrowthBounds.TwistedSubstitution.TwistedMonomialFiltration.TMemLaurentFiltration
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.TestSideWords.TwistedFiltration.G1

open Formalism.MainNotions.G

theorem flt_twistMat_mem (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k e t : ℤ) (h0 : t ≤ 0) (hk : t ≤ e * k)
    (b c : Fin n) : twistMat R n j k b c ∈ (flt_L (GLCoord R n) e).F t := by
  apply _root_.Formalism.MainNotions.G.GLWeightTheory.flt_twistMat_mem <;> assumption


open Classical in
def flt_cost {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (b : Bool) : (ι × Fin n →₀ ℕ) →+ ℤ :=
  Finsupp.liftAddHom fun v => if v.1 ∈ S ∧ LL.vec v.1 = b then Nat.castAddMonoidHom ℤ else 0

open Classical in
theorem flt_cost_single {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (b : Bool) (v : ι × Fin n) (k : ℕ) :
    flt_cost LL S b (Finsupp.single v k) = if v.1 ∈ S ∧ LL.vec v.1 = b then (k : ℤ) else 0 := by
  unfold flt_cost
  rw [Finsupp.liftAddHom_apply_single]
  split_ifs
  · rfl
  · rfl

def flt_compat (e : ℤ) (bm : Bool) : Prop := (e = 1 ∧ bm = false) ∨ (e = -1 ∧ bm = true)

theorem flt_twistX_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) (v : ι × Fin n) :
    twistSub LL S j (X v : MvPolynomial (ι × Fin n) R) ∈
      (laurentCoeffFiltration R n (ι × Fin n) e).F ((-flt_cost LL S bm) (Finsupp.single v 1)) := by
  apply _root_.Formalism.MainNotions.G.GLWeightTheory.flt_twistX_mem <;> assumption

theorem flt_twist_monomial_mem {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} (LL : Letters ι) (S : Set ι) (j : Fin n)
    {e : ℤ} {bm : Bool} (h : flt_compat e bm) (al : ι × Fin n →₀ ℕ) :
    twistSub LL S j (monomial al (1 : R)) ∈ (laurentCoeffFiltration R n (ι × Fin n) e).F (-flt_cost LL S bm al) :=
  flt_hom_monomial (laurentCoeffFiltration R n (ι × Fin n) e) (twistSub LL S j) (-flt_cost LL S bm)
    (fun w => flt_twistX_mem LL S j h w) al

theorem flt_gL_mul_gLinv (R : Type*) [CommRing R] (n : ℕ) : gL R n * gLinv R n = 1 := by
  ext i k
  have hu : algebraMap _ (GLCoord R n) (genMat R n).det *
      IsLocalization.Away.invSelf (genMat R n).det = 1 :=
    IsLocalization.Away.mul_invSelf _
  have e : ∑ j, algebraMap _ (GLCoord R n) (genMat R n i j) *
      (IsLocalization.Away.invSelf (genMat R n).det *
        algebraMap _ (GLCoord R n) ((genMat R n).adjugate j k)) =
      IsLocalization.Away.invSelf (genMat R n).det *
        algebraMap _ (GLCoord R n) ((genMat R n * (genMat R n).adjugate) i k) := by

    rw [Matrix.mul_apply, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  rw [Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul] at e

  simp only [Matrix.mul_apply, gL, gLinv, Matrix.map_apply, ← map_mul, ← map_sum, e,
  Matrix.one_apply]
  split_ifs
  · rw [mul_one, mul_comm, hu, map_one]
  · rw [mul_zero, map_zero, mul_zero, map_zero]

theorem flt_gLinv_mul_gL (R : Type*) [CommRing R] (n : ℕ) : gLinv R n * gL R n = 1 :=
  mul_eq_one_comm.1 (flt_gL_mul_gLinv R n)

theorem flt_twistMat_mul (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k : ℤ) :
    twistMat R n j k * twistMat R n j (-k) = 1 := by
  have hd : Matrix.diagonal (fun a => if a = j then (LaurentPolynomial.T k : GLLaurent R n) else 1) *
      Matrix.diagonal (fun a => if a = j then LaurentPolynomial.T (-k) else 1) = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs
    · rw [← LaurentPolynomial.T_add, add_neg_cancel, LaurentPolynomial.T_zero]
    · rw [one_mul]
  unfold twistMat
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (gLinv R n) (gL R n), flt_gLinv_mul_gL, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal _) (Matrix.diagonal _), hd, Matrix.one_mul, flt_gL_mul_gLinv]

end Formalism.MainNotions.TestSideWords.TwistedFiltration.G1
