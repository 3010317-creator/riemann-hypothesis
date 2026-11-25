module

public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Base
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Comb
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.Elementary
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.JacobiTrudi
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.PrimeWeightEqZeroOfLt
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsCoinv
public import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsElem
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public section

noncomputable section

namespace GroundTheory.Heights₂.Heights.RestTerms

open Finset Comb

noncomputable section

theorem CombTableEqWords.proof (h1 : CombCardYoungCells.Statement)
    (h2 : CombWordOfTableau.Statement) (h3 : CombTableauOfWord.Statement) :
    CombTableEqWords.Statement := by
  intro m lam hlam
  classical
  let toWord (T : {T : youngCells lam ≃ Fin (youngCells lam).card // IsStandard T}) :
      latticeWords (youngCells lam).card lam :=
    ⟨rowWord T.1, (h2 m lam hlam T.1 T.2).1⟩
  have hbij : Function.Bijective toWord := by
    refine ⟨?_, fun w => ?_⟩
    · intro T U hTU
      apply Subtype.ext
      have hsymm : T.1.symm = U.1.symm := by
        refine Equiv.ext fun t => Subtype.ext ?_
        rw [← (h2 m lam hlam T.1 T.2).2 t, ← (h2 m lam hlam U.1 U.2).2 t]
        exact congrArg (fun w => cellOfWord w.1 t) hTU
      simpa using congrArg Equiv.symm hsymm
    · obtain ⟨T, hT, hw⟩ := h3 m lam hlam w.1 w.2
      exact ⟨⟨T, hT⟩, Subtype.ext hw⟩
  let e := Equiv.ofBijective toWord hbij
  show Nat.card {T : youngCells lam ≃ Fin (youngCells lam).card // IsStandard T} = _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe, h1 m lam]

end

end GroundTheory.Heights₂.Heights.RestTerms

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

open MvPolynomial Finset

noncomputable section

theorem OtherFactorBound.add_le_mul_add_one {r a : ℕ} (hr : 1 ≤ r) (ha : 1 ≤ a) :
    r + a ≤ r * a + 1 := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  nlinarith [Nat.zero_le (r' * a')]

theorem OtherFactorBound.coeff_bound (hS : SchurSignCoefficient.Statement)
    (hH : HookSumBound.Statement) (r a k : ℕ) (c : SmallBlock) (hk1 : 1 ≤ k) (hkN : k ≤ r + a)
    (S : MvPolynomial (Fin (r + a)) ℚ)
    (hSeq : powerSumHom (r + a) S =
      ∑ nu ∈ partitionsOf r k,
        C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
          aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu)) :
    |S.coeff (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1)| ≤
      (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a) / k := by
  set e := Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1 with he
  have hs : c.sign = 1 ∨ c.sign = -1 := by cases c <;> simp [SmallBlock.sign]
  have hex : ∀ nu : Fin r → ℕ, ∃ T : MvPolynomial (Fin (r + a)) ℚ, nu ∈ partitionsOf r k →
      powerSumHom (r + a) T = aeval (fun i : Fin (r + a) => C c.sign * X i)
          (schur (Fin (r + a)) nu) ∧
        AddMonoidAlgebra.coeff T e = c.sign ^ k * if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          (-1 : ℚ) ^ ((Finset.univ.filter fun i : Fin r => (i : ℕ) ≠ 0 ∧ nu i = 1).card) / k
        else 0 := by
    intro nu
    by_cases hnu : nu ∈ partitionsOf r k
    · have hmem := hnu
      simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hmem
      obtain ⟨T, hT1, hT2⟩ := hS (r + a) r k hk1 hkN nu c.sign hs
        (fun i j hij => hmem.2 i j hij) hmem.1
      exact ⟨T, fun _ => ⟨hT1, hT2⟩⟩
    · exact ⟨0, fun h => absurd h hnu⟩
  choose T hT using hex
  have hSsum : S = ∑ nu ∈ partitionsOf r k,
      C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * T nu := by
    apply Flag.powerSumHom_injective

    rw [hSeq, map_sum]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [map_mul, (hT nu hnu).1]
    congr 1
    simp [powerSumHom]
  have hterm : ∀ nu ∈ partitionsOf r k,
      |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * (T nu).coeff e| =
        (if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then
          ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) else 0) / k := by
    intro nu hnu
    rw [(hT nu hnu).2, abs_mul, abs_mul, abs_pow]
    have habs : |c.sign| = 1 := by rcases hs with h | h <;> simp [h]
    rw [habs, one_pow, one_mul, Nat.abs_cast]
    split_ifs
    · rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]; ring
    · simp
  calc |S.coeff e|
      = |∑ nu ∈ partitionsOf r k,
          ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * (T nu).coeff e| := by
        rw [hSsum, coeff_sum]
        simp only [coeff_C_mul]
    _ ≤ ∑ nu ∈ partitionsOf r k,
          |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) * (T nu).coeff e| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = (∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
          |((numStandardTable (fun i => a + nu i) : ℕ) : ℚ)|) / k := by
        rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, Finset.sum_filter]
        simp only [Nat.abs_cast]
    _ ≤ (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) * numStandardTable (rectangle r a) / k := by
        gcongr
        exact hH r a k (fun nu => ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ)) hk1
          (fun nu _ => by simp)

theorem OtherFactorBound.proof (hO : OtherFactorFormula.Statement)
    (hF : SameFactorFormula.Statement) (hS : SchurSignCoefficient.Statement)
    (hB : CharacterBound.Statement) (hH : HookSumBound.Statement)
    (hR : RectangleTablePos.Statement) (hD : RestPolynomialDecomposes.Statement) :
    OtherFactorBound.Statement := by
  intro f r a c hf hr ha
  have hP : (0 : ℚ) < numStandardTable (rectangle r a) := by exact_mod_cast hR r a
  have hkey := OtherFactorBound.add_le_mul_add_one hr ha
  refine ⟨?_, hD f r a c, ?_⟩
  · obtain ⟨C₀, hC₀, hJ, -⟩ := hF f r a c hf hr ha
    rw [hJ]
    have h1 : ((f * (r * a)).factorial : ℚ) ≠ 0 := by positivity
    have h2 : ((r * a).factorial : ℚ) ≠ 0 := by positivity
    have := hP.ne'
    simp_all
  intro Q hQ k hk2 hkN τ τ' hne
  have hk1 : k - 1 ≤ r * a := by omega
  refine ⟨fun h => absurd h (by omega), ?_⟩
  have hf2 : 2 ≤ f := by
    by_contra h
    have : f = 1 := by omega
    subst this
    exact hne (Subsingleton.elim _ _)
  obtain ⟨C₀, hC₀, hJ, hT⟩ := hO f r a c hf2 hr ha
  obtain ⟨S, hSeq, hTk⟩ := hT Q hQ k hk2 hkN τ τ' hne
  have hcoef := OtherFactorBound.coeff_bound hS hH r a k c (by omega) hkN S hSeq
  have hchi := hB r (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
    (fun _ _ _ => le_rfl) (by
      intro q hq
      simp only [List.mem_cons, List.mem_replicate] at hq
      omega)
  rw [hTk, hJ]
  set y := AddMonoidAlgebra.coeff S (Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1)
  set z := symmetricGroupCharacter (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
  set P : ℚ := (numStandardTable (rectangle r a) : ℚ) with hPdef
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  have hg : g + 2 - 2 = g := by omega
  rw [hg]

  set n1 := r * a with hn1
  set n := (g + 2) * n1 with hn
  have hD1 : ((n1 + k).factorial : ℚ) =
      (Nat.choose (n1 + k) k : ℚ) * (k.factorial : ℚ) * (n1.factorial : ℚ) := by
    have := Nat.add_choose_mul_factorial_mul_factorial n1 k
    rw [← this]; push_cast; ring
  have hA : (n1.factorial : ℚ) =
      ((n1 - (k - 1)).factorial : ℚ) * (n1.descFactorial (k - 1) : ℚ) := by
    exact_mod_cast (Nat.factorial_mul_descFactorial hk1).symm
  have hM : ((n + 1).factorial : ℚ) = ((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hchoose : (0 : ℚ) < Nat.choose (n1 + k) k := by
    exact_mod_cast Nat.choose_pos (by omega)

  have hstep : |C₀ * k * ((n + 1).factorial : ℚ) /
        (((n1 + k).factorial : ℚ) * ((n1 - (k - 1)).factorial : ℚ) *
          ((n1).factorial : ℚ) ^ g) * P ^ g * z * y| ≤
      ((n + 1 : ℕ) : ℚ) * |C₀ * (n.factorial : ℚ) / ((n1).factorial : ℚ) ^ (g + 2) * P ^ (g + 2)| *
        ((n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1)) / (k.factorial : ℚ) := by
    rw [hD1, hM]
    simp only [abs_mul, abs_div, abs_pow, Nat.abs_cast, abs_of_pos hP]
    have hX1 : 0 ≤ |C₀| * (k : ℚ) * (((n + 1 : ℕ) : ℚ) * (n.factorial : ℚ)) /
        ((Nat.choose (n1 + k) k : ℚ) * (k.factorial : ℚ) * (n1.factorial : ℚ) *
          ((n1 - (k - 1)).factorial : ℚ) * (n1.factorial : ℚ) ^ g) * P ^ g := by positivity
    refine (mul_le_mul (mul_le_mul_of_nonneg_left hchi hX1) hcoef (abs_nonneg _)
      (by positivity)).trans (le_of_eq ?_)
    field_simp
    rw [hA]
    ring
  refine hstep.trans ?_

  have hX : (n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1) ≤ restX r a ^ (k - 1) := by
    have h1 : (n1.descFactorial (k - 1) : ℚ) ≤ (n1 : ℚ) ^ (k - 1) := by
      exact_mod_cast Nat.descFactorial_le_pow n1 (k - 1)
    have h2 : (2 * (n1 : ℚ)) ≤ restX r a := by
      simp only [restX, hn1]; push_cast; nlinarith [(Nat.cast_nonneg (r + a : ℕ) : (0 : ℚ) ≤ _)]
    calc (n1.descFactorial (k - 1) : ℚ) * 2 ^ (k - 1)
        ≤ (n1 : ℚ) ^ (k - 1) * 2 ^ (k - 1) := by gcongr
      _ = (2 * (n1 : ℚ)) ^ (k - 1) := by ring
      _ ≤ restX r a ^ (k - 1) := by gcongr
  gcongr

end

end RestTerms

end GroundTheory.Heights₂.Heights

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace RestTerms

namespace Top

open MvPolynomial Finset

noncomputable section

theorem tri_add (r a : ℕ) :
    (r + a) * (r + a - 1) / 2 = r * (r - 1) / 2 + a * (a - 1) / 2 + r * a := by
  have h1 : (r + a) * (r + a - 1) = r * (r - 1) + a * (a - 1) + 2 * (r * a) := by
    rcases Nat.eq_zero_or_pos r with hr | hr
    · subst hr; simp
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha; simp
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
    rw [show r' + 1 + (a' + 1) - 1 = r' + a' + 1 by omega, Nat.add_sub_cancel, Nat.add_sub_cancel]
    ring
  obtain ⟨x, hx⟩ := Nat.even_mul_pred_self r
  obtain ⟨y, hy⟩ := Nat.even_mul_pred_self a
  generalize r * (r - 1) = A at h1 hx ⊢
  generalize a * (a - 1) = B at h1 hy ⊢
  generalize r * a = P at h1 ⊢
  generalize (r + a) * (r + a - 1) = T at h1 ⊢
  omega

theorem isHomogeneous_yRoot (f r a : ℕ) (c : SmallBlock) (τ : Fin f) (i : Fin r) :
    (yRoot f r a c τ i).IsHomogeneous 1 := by
  have := (isHomogeneous_C (Fin f × Fin (r + a)) c.sign).mul (isHomogeneous_X ℚ (yIndex f r a c τ i))
  simpa [yRoot] using this

theorem isHomogeneous_zRoot (f r a : ℕ) (c : SmallBlock) (τ : Fin f) (i : Fin a) :
    (zRoot f r a c τ i).IsHomogeneous 1 :=
  isHomogeneous_X ℚ _

theorem isHomogeneous_smallBlockMu (f r a : ℕ) (c : SmallBlock) :
    (smallBlockMu f r a c).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun τ _ => IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_yRoot f r a c τ i

theorem isHomogeneous_smallPowerSum (f r a : ℕ) (c : SmallBlock) (k : ℕ) (τ : Fin f) :
    (smallPowerSum f r a c k τ).IsHomogeneous k := by
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  simpa using (isHomogeneous_yRoot f r a c τ i).pow k

theorem isHomogeneous_fibreClass (hV : VandermondeOfHomogeneous.Statement) (f r a : ℕ)
    (c : SmallBlock) :
    (fibreClass f r a c).IsHomogeneous (f * (r * (r - 1) / 2 + a * (a - 1) / 2)) := by
  have h := IsHomogeneous.prod (Finset.univ : Finset (Fin f))
    (fun τ => vandermondeOf (yRoot f r a c τ) * vandermondeOf (zRoot f r a c τ))
    (fun _ => r * (r - 1) / 2 + a * (a - 1) / 2)
    (fun τ _ => (hV _ ℚ r _ (isHomogeneous_yRoot f r a c τ)).mul
      (hV _ ℚ a _ (isHomogeneous_zRoot f r a c τ)))
  simpa [fibreClass, Finset.sum_const, Finset.card_univ, Fintype.card_fin] using h

theorem isHomogeneous_mu_pow_fib (hV : VandermondeOfHomogeneous.Statement) (f r a : ℕ)
    (c : SmallBlock) :
    (smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c).IsHomogeneous
      (topDegree f (r + a)) := by
  have h := ((isHomogeneous_smallBlockMu f r a c).pow (f * (r * a))).mul
    (isHomogeneous_fibreClass hV f r a c)
  convert h using 1
  rw [topDegree, tri_add]
  ring

theorem multinomial_const (f x : ℕ) :
    (Nat.multinomial Finset.univ (fun _ : Fin f => x) : ℚ) =
      ((f * x).factorial : ℚ) / (x.factorial : ℚ) ^ f := by
  have h := Nat.multinomial_spec (Finset.univ : Finset (Fin f)) (fun _ => x)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Finset.sum_const,
    smul_eq_mul] at h
  have hx : (x.factorial : ℚ) ^ f ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero x)
  rw [eq_div_iff hx, mul_comm]
  exact_mod_cast h

theorem blockCoeff_rect_eq (hCI : CharacterAtIdentity.Statement) (r a : ℕ) (hra : r * a ≠ 0) :
    blockCoeff 0 (r * a) (rectangle r a) = numStandardTable (rectangle r a) := by
  rw [blockCoeff, ite_eq_left rfl, ite_eq_right hra]
  have h := hCI r (rectangle r a) (fun _ _ _ => le_rfl)
  have hs : ∑ i, rectangle r a i = r * a := by
    simp [rectangle, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hs] at h
  exact h

theorem kappa_ne_zero {r a : ℕ} {κ : ℚ}
    (h : κ = (r.factorial : ℚ) * a.factorial ∨ κ = -((r.factorial : ℚ) * a.factorial)) : κ ≠ 0 := by
  have : ((r.factorial : ℚ) * a.factorial) ≠ 0 := by positivity
  rcases h with h | h <;> rw [h]
  · exact this
  · exact neg_ne_zero.mpr this

theorem fibreDegree_eq (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) (f r a : ℕ) (c : SmallBlock) (hr : 1 ≤ r)
    (ha : 1 ≤ a) (κ : ℚ)
    (hκ : ∀ lam : Fin r → ℕ, Antitone lam →
        HasDD 1 (r + a) (yEval r a c (schur (Fin r) lam) * fib1 r a c) (pushOut r a c κ lam))
    (c0 : ℚ)
    (hInt : ∀ H : RootRing f (r + a), H.IsHomogeneous (topDegree f (r + a)) →
      algebraMap ℚ (FractionRing (RootRing f (r + a))) (flagIntegral f (r + a) H) =
        algebraMap ℚ (FractionRing (RootRing f (r + a))) c0 * dividedDifference f (r + a) H) :
    fibreDegree f r a c =
      c0 * κ ^ f * (f * (r * a)).factorial / ((r * a).factorial : ℚ) ^ f *
        (numStandardTable (rectangle r a) : ℚ) ^ f := by
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hH : gmf f r a c 0 (f * (r * a)) =
      smallBlockMu f r a c ^ (f * (r * a)) * fibreClass f r a c := by
    simp [gmf, extraFactor]
  have hdd := dividedDifference_eq_of_hasDD (hasDD_gmf hF f r a c κ hκ 0 (f * (r * a)))
  rw [hH, gmfOut_zero] at hdd
  have h := hInt _ (isHomogeneous_mu_pow_fib hV f r a c)
  rw [hdd, ← MvPolynomial.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply ℚ (RootRing f (r + a)) (FractionRing (RootRing f (r + a))),
    ← map_mul] at h
  have h2 := (algebraMap ℚ (FractionRing (RootRing f (r + a)))).injective h
  rw [fibreDegree, h2, multinomial_const, blockCoeff_rect_eq hCI r a hra]
  have hx : ((r * a).factorial : ℚ) ^ f ≠ 0 := pow_ne_zero _ (by exact_mod_cast Nat.factorial_ne_zero _)
  field_simp
  ring

theorem extraFactor_zero (r : ℕ) : extraFactor r 0 = 1 := by simp [extraFactor]

theorem smallPowerSum_mul_restPolynomial (f r a : ℕ) (c : SmallBlock) (k : ℕ) (hk : 2 ≤ k)
    (τ : Fin f) :
    smallPowerSum f r a c (k - 1) τ * restPolynomial f r a c =
      gmf f r a c (fun σ => if σ = τ then k - 1 else 0) (f * (r * a) + 1) := by
  rw [gmf, restPolynomial]
  have : ∏ σ, blockEmb f (r + a) σ
      (yEval r a c (extraFactor r (if σ = τ then k - 1 else 0))) =
      smallPowerSum f r a c (k - 1) τ := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ)]
    rw [Finset.prod_eq_one (fun σ hσ => by
      rw [ite_eq_right (Finset.ne_of_mem_erase hσ), extraFactor_zero, map_one, map_one])]
    rw [ite_eq_left rfl, extraFactor, ite_eq_right (by omega), blockEmb_yEval_psum, mul_one]
  rw [this]
  ring

theorem sum_erase_const (f : ℕ) (τ : Fin f) (x : ℕ) :
    ∑ _σ ∈ Finset.univ.erase τ, x = (f - 1) * x := by
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

end

end Top

open Top MvPolynomial Finset

noncomputable section

theorem SameFactorFormula.proof (hA : LemmaA.Statement) (hB : LemmaB.Statement)
    (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) (hRP : RectangleTablePos.Statement) :
    SameFactorFormula.Statement := by
  intro f r a c hf hr ha
  obtain ⟨κ, hκpm, hκ⟩ := hasDD_schur hB r a c
  obtain ⟨c0, hc0, hInt, hMain⟩ := hA f (r + a)
  have hκ0 := kappa_ne_zero hκpm
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hfR : (numStandardTable (rectangle r a) : ℚ) ≠ 0 := by exact_mod_cast (hRP r a).ne'
  refine ⟨c0 * κ ^ f, mul_ne_zero hc0 (pow_ne_zero _ hκ0),
    fibreDegree_eq hF hCI hV f r a c hr ha κ hκ c0 hInt, ?_⟩
  intro Q hQ k hk2 hkN τ
  set q : Fin f → ℕ := fun σ => if σ = τ then k - 1 else 0 with hqdef
  have hGF := smallPowerSum_mul_restPolynomial f r a c k hk2 τ
  obtain ⟨P, hP, -, S', hS', hI⟩ := hMain _ Q hQ k (by omega) hkN τ _
    (by simpa using isHomogeneous_smallPowerSum f r a c (k - 1) τ)
  have hPeq : P = gmfOut f r a c κ q (f * (r * a) + 1) := by
    apply IsFractionRing.injective (RootRing f (r + a)) (FractionRing (RootRing f (r + a)))
    rw [hP, hGF, dividedDifference_eq_of_hasDD (hasDD_gmf hF f r a c κ hκ q _)]
  have hsum : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') = (f - 1) * (r * a) := by
    rw [← sum_erase_const f τ (r * a)]
    exact Finset.sum_congr rfl fun σ hσ => by simp [hqdef, Finset.ne_of_mem_erase hσ]
  have hle : (f - 1) * (r * a) ≤ f * (r * a) + 1 :=
    (Nat.mul_le_mul_right _ (Nat.sub_le f 1)).trans (Nat.le_succ _)
  have hres := restrict_gmfOut f r a c κ q (f * (r * a) + 1) τ
    (fun σ hσ => by simp [hqdef, hσ]) (by rw [hsum]; exact hle)
  have hmτ : mstar f r a q (f * (r * a) + 1) τ τ = r * a + 1 := by
    simp only [mstar, ite_true, hsum]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    rw [Nat.add_sub_cancel, add_mul, one_mul]
    omega
  have hms : mstar f r a q (f * (r * a) + 1) τ = fun σ => if σ = τ then r * a + 1 else r * a := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; rw [hmτ, ite_eq_left rfl]
    · simp [mstar, hσ, hqdef]
  have hqτ : q τ = k - 1 := by simp [hqdef]
  rw [hmτ, hqτ, toN_blockOut r a c κ (k - 1) (r * a + 1) k (by omega)] at hres
  have hprod : ∏ σ ∈ Finset.univ.erase τ,
      (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ) =
      ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 1) := by
    rw [Finset.prod_congr rfl fun σ hσ => by
      rw [show q σ = 0 by simp [hqdef, Finset.ne_of_mem_erase hσ], Nat.sub_zero,
        blockCoeff_rect_eq hCI r a hra]]
    rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ,
      Fintype.card_fin]
  have hmult : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) =
      ((f * (r * a) + 1).factorial : ℚ) /
        (((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f - 1)) := by
    have hp : ∏ σ, (mstar f r a q (f * (r * a) + 1) τ σ).factorial =
        (r * a + 1).factorial * (r * a).factorial ^ (f - 1) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), hmτ]
      congr 1
      rw [Finset.prod_congr rfl (fun σ hσ =>
        show (mstar f r a q (f * (r * a) + 1) τ σ).factorial = (r * a).factorial by
          simp only [hms, ite_eq_right (Finset.ne_of_mem_erase hσ)]), Finset.prod_const,
        Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ, Fintype.card_fin]
    have hs' := (Finset.mem_piAntidiag.mp
      (mstar_mem f r a q (f * (r * a) + 1) τ (by rw [hsum]; exact hle))).1
    have h := Nat.multinomial_spec (Finset.univ : Finset (Fin f))
      (mstar f r a q (f * (r * a) + 1) τ)
    rw [hp, hs'] at h
    have hden : ((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f - 1) ≠ 0 := by positivity
    rw [eq_div_iff hden, ← h]
    push_cast
    ring
  set K : ℚ := (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) *
    ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 1) * κ with hK
  have hmultpos : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  have hK0 : K ≠ 0 := by
    rw [hK]; exact mul_ne_zero (mul_ne_zero hmultpos (pow_ne_zero _ (mul_ne_zero hfR hκ0))) hκ0
  set T := ∑ nu ∈ partitionsOf r k,
      C (symmetricGroupCharacter (fun i => a + nu i) ((k - 1) :: List.replicate (r * a + 1) 1)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) with hT
  have hTeq : ∑ nu ∈ partitionsOf r k, C (blockCoeff (k - 1) (r * a + 1) (fun i => a + nu i)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) = T := by
    rw [hT]
    refine Finset.sum_congr rfl fun nu _ => ?_
    rw [blockCoeff, ite_eq_right (by omega)]
  rw [hTeq, hprod] at hres
  have hPS : powerSumHom (r + a) S' = K • T := by
    rw [hS', hPeq, hres, hK, smul_eq_C_mul, smul_eq_C_mul]
    simp only [map_mul, map_pow]
    ring
  refine ⟨K⁻¹ • S', ?_, ?_⟩
  · rw [map_smul, hPS, smul_smul, inv_mul_cancel₀ hK0, one_smul]
  · rw [restTerm, hI, MvPolynomial.coeff_smul, smul_eq_mul]
    rw [hK, hmult]
    have hden : ((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f - 1) ≠ 0 := by positivity
    have hnum : ((f * (r * a) + 1).factorial : ℚ) ≠ 0 := by positivity
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hden ⊢
    field_simp
    ring

end

end RestTerms

end GroundTheory.Heights₂.Heights
end

namespace GroundTheory.Heights₂.Heights

section
namespace RestTerms

namespace Top

open MvPolynomial Finset

noncomputable section

theorem isSymmetric_aeval_smul_X {N : ℕ} (s : ℚ) {p : MvPolynomial (Fin N) ℚ} (hp : p.IsSymmetric) :
    (aeval (fun i : Fin N => C s * X i) p).IsSymmetric := by
  intro e
  have key : (rename e).comp (aeval (fun i : Fin N => C s * X i)) =
      (aeval (fun i : Fin N => C s * X i)).comp (rename e) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp
  have := congrArg (fun φ : MvPolynomial (Fin N) ℚ →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ p) key
  simp only [AlgHom.comp_apply] at this
  rw [this, hp e]

theorem k_sub_one_le (r a k : ℕ) (hr : 1 ≤ r) (ha : 1 ≤ a) (hk : k ≤ r + a) : k - 1 ≤ r * a := by
  have : r + a ≤ r * a + 1 := by nlinarith
  omega

end

end Top

open _root_.GroundTheory.Heights₂.Heights.RestTerms.Top MvPolynomial Finset

noncomputable section

theorem OtherFactorFormula.proof (hA : LemmaA.Statement) (hB : LemmaB.Statement)
    (hF : FrobeniusCharacterFormula.Statement) (hCI : CharacterAtIdentity.Statement)
    (hV : VandermondeOfHomogeneous.Statement) (hRP : RectangleTablePos.Statement) :
    OtherFactorFormula.Statement := by
  intro f r a c hf hr ha
  obtain ⟨κ, hκpm, hκ⟩ := hasDD_schur hB r a c
  obtain ⟨c0, hc0, hInt, hMain⟩ := hA f (r + a)
  have hκ0 := kappa_ne_zero hκpm
  have hra : r * a ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hfR : (numStandardTable (rectangle r a) : ℚ) ≠ 0 := by exact_mod_cast (hRP r a).ne'
  refine ⟨c0 * κ ^ f, mul_ne_zero hc0 (pow_ne_zero _ hκ0),
    fibreDegree_eq hF hCI hV f r a c hr ha κ hκ c0 hInt, ?_⟩
  intro Q hQ k hk2 hkN τ τ' hττ'
  have hk1 := k_sub_one_le r a k hr ha hkN
  set q : Fin f → ℕ := fun σ => if σ = τ' then k - 1 else 0 with hqdef
  have hGF := smallPowerSum_mul_restPolynomial f r a c k hk2 τ'
  obtain ⟨P, hP, -, S', hS', hI⟩ := hMain _ Q hQ k (by omega) hkN τ _
    (by simpa using isHomogeneous_smallPowerSum f r a c (k - 1) τ')
  have hPeq : P = gmfOut f r a c κ q (f * (r * a) + 1) := by
    apply IsFractionRing.injective (RootRing f (r + a)) (FractionRing (RootRing f (r + a)))
    rw [hP, hGF, dividedDifference_eq_of_hasDD (hasDD_gmf hF f r a c κ hκ q _)]
  have hτ'mem : τ' ∈ Finset.univ.erase τ := Finset.mem_erase.mpr ⟨hττ', Finset.mem_univ τ'⟩
  have hsum : ∑ σ' ∈ Finset.univ.erase τ, (r * a - q σ') = (f - 1) * (r * a) - (k - 1) := by
    rw [← Finset.add_sum_erase _ _ hτ'mem]
    have h2 : ∑ σ' ∈ (Finset.univ.erase τ).erase τ', (r * a - q σ') = (f - 2) * (r * a) := by
      rw [Finset.sum_congr rfl (fun σ hσ => show r * a - q σ = r * a by
        simp [hqdef, Finset.ne_of_mem_erase hσ]), Finset.sum_const,
        Finset.card_erase_of_mem hτ'mem, Finset.card_erase_of_mem (Finset.mem_univ τ),
        Finset.card_univ, Fintype.card_fin, smul_eq_mul]
      congr 1
    rw [h2]
    simp only [hqdef, ite_true]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
    simp only [Nat.add_sub_cancel, show f' + 2 - 1 = f' + 1 by omega]
    rw [add_mul, one_mul]
    omega
  have hle : (f - 1) * (r * a) - (k - 1) ≤ f * (r * a) + 1 :=
    (Nat.sub_le _ _).trans ((Nat.mul_le_mul_right _ (Nat.sub_le f 1)).trans (Nat.le_succ _))
  have hres := restrict_gmfOut f r a c κ q (f * (r * a) + 1) τ
    (fun σ hσ => by simp only [hqdef]; split_ifs <;> omega) (by rw [hsum]; exact hle)
  have hmτ : mstar f r a q (f * (r * a) + 1) τ τ = r * a + k := by
    simp only [mstar, ite_true, hsum]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
    simp only [show f' + 2 - 1 = f' + 1 by omega]
    have h3 : r * a ≤ (f' + 1) * (r * a) := Nat.le_mul_of_pos_left _ (by omega)
    rw [show (f' + 2) * (r * a) = (f' + 1) * (r * a) + r * a by ring]
    omega
  have hms : mstar f r a q (f * (r * a) + 1) τ = fun σ =>
      if σ = τ then r * a + k else if σ = τ' then r * a - (k - 1) else r * a := by
    funext σ
    by_cases hσ : σ = τ
    · subst hσ; rw [hmτ, ite_eq_left rfl]
    · by_cases hσ' : σ = τ'
      · subst hσ'; simp [mstar, hσ, hqdef]
      · simp [mstar, hσ, hσ', hqdef]
  have hqτ : q τ = 0 := by simp [hqdef, Ne.symm hττ']
  rw [hmτ, hqτ, toN_blockOut r a c κ 0 (r * a + k) k (by omega)] at hres
  set χR := symmetricGroupCharacter (rectangle r a) ((k - 1) :: List.replicate (r * a - (k - 1)) 1)
    with hχR
  have hprod : ∏ σ ∈ Finset.univ.erase τ,
      (blockCoeff (q σ) (r * a - q σ) (rectangle r a) * κ) =
      (χR * κ) * ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 2) := by
    rw [← Finset.mul_prod_erase _ _ hτ'mem]
    congr 1
    · simp only [hqdef, ite_true]
      rw [blockCoeff, ite_eq_right (by omega)]
    · rw [Finset.prod_congr rfl fun σ hσ => by
        rw [show q σ = 0 by simp [hqdef, Finset.ne_of_mem_erase hσ], Nat.sub_zero,
          blockCoeff_rect_eq hCI r a hra]]
      rw [Finset.prod_const, Finset.card_erase_of_mem hτ'mem,
        Finset.card_erase_of_mem (Finset.mem_univ τ), Finset.card_univ, Fintype.card_fin]
      congr 1
  have hmult : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) =
      ((f * (r * a) + 1).factorial : ℚ) /
        (((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
          ((r * a).factorial : ℚ) ^ (f - 2)) := by
    have hp : ∏ σ, (mstar f r a q (f * (r * a) + 1) τ σ).factorial =
        (r * a + k).factorial * ((r * a - (k - 1)).factorial * (r * a).factorial ^ (f - 2)) := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), hmτ, ← Finset.mul_prod_erase _ _ hτ'mem]
      congr 2
      · simp only [hms, ite_eq_right hττ', ite_true]
      · rw [Finset.prod_congr rfl (fun σ hσ =>
          show (mstar f r a q (f * (r * a) + 1) τ σ).factorial = (r * a).factorial by
            simp only [hms, ite_eq_right (Finset.ne_of_mem_erase hσ),
              ite_eq_right (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hσ))]), Finset.prod_const,
          Finset.card_erase_of_mem hτ'mem, Finset.card_erase_of_mem (Finset.mem_univ τ),
          Finset.card_univ, Fintype.card_fin]
        congr 1
    have hs' := (Finset.mem_piAntidiag.mp
      (mstar_mem f r a q (f * (r * a) + 1) τ (by rw [hsum]; exact hle))).1
    have h := Nat.multinomial_spec (Finset.univ : Finset (Fin f))
      (mstar f r a q (f * (r * a) + 1) τ)
    rw [hp, hs'] at h
    have hden : ((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
        ((r * a).factorial : ℚ) ^ (f - 2) ≠ 0 := by positivity
    rw [eq_div_iff hden, ← h]
    push_cast
    ring
  set T := ∑ nu ∈ partitionsOf r k,
      C ((numStandardTable (fun i => a + nu i) : ℕ) : ℚ) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) with hT
  have hTeq : ∑ nu ∈ partitionsOf r k, C (blockCoeff 0 (r * a + k) (fun i => a + nu i)) *
        aeval (fun i : Fin (r + a) => C c.sign * X i) (schur (Fin (r + a)) nu) = T := by
    rw [hT]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [blockCoeff, ite_eq_left rfl, ite_eq_right (by omega)]
    have hs := sum_of_mem_partitionsOf hnu
    have hanti := antitone_of_mem_partitionsOf hnu
    have h := hCI r (fun i => a + nu i) (fun i j hij => Nat.add_le_add_left (hanti hij) a)
    have hs2 : ∑ i, (a + nu i) = r * a + k := by
      rw [Finset.sum_add_distrib, hs]
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [hs2] at h
    rw [h]
  rw [hTeq, hprod] at hres
  have hTsym : T.IsSymmetric := by
    intro e

    rw [hT, map_sum]
    refine Finset.sum_congr rfl fun nu _ => ?_
    rw [map_mul, rename_C, isSymmetric_aeval_smul_X _ (Schur.schur_isSymmetric _) e]
  set K : ℚ := (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) *
    ((χR * κ) * ((numStandardTable (rectangle r a) : ℚ) * κ) ^ (f - 2)) * κ with hK
  have hPS : powerSumHom (r + a) S' = K • T := by
    rw [hS', hPeq, hres, hK, smul_eq_C_mul, smul_eq_C_mul]
    simp only [map_mul, map_pow]
    ring
  have hmultpos : (Nat.multinomial Finset.univ (mstar f r a q (f * (r * a) + 1) τ) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  by_cases hχ : χR = 0
  · obtain ⟨S, hS⟩ := Flag.exists_powerSumHom_eq hTsym
    have hS'0 : S' = 0 := by
      apply Flag.powerSumHom_injective
      rw [hPS, hK, hχ, map_zero]
      simp
    refine ⟨S, hS, ?_⟩
    rw [restTerm, hI, hS'0, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, hχ]
    ring
  · have hK0 : K ≠ 0 := by
      rw [hK]
      exact mul_ne_zero (mul_ne_zero hmultpos (mul_ne_zero (mul_ne_zero hχ hκ0)
        (pow_ne_zero _ (mul_ne_zero hfR hκ0)))) hκ0
    refine ⟨K⁻¹ • S', ?_, ?_⟩
    · rw [map_smul, hPS, smul_smul, inv_mul_cancel₀ hK0, one_smul]
    · rw [restTerm, hI, MvPolynomial.coeff_smul, smul_eq_mul]
      rw [hK, hmult]
      have hden : ((r * a + k).factorial : ℚ) * ((r * a - (k - 1)).factorial : ℚ) *
          ((r * a).factorial : ℚ) ^ (f - 2) ≠ 0 := by positivity
      have hnum : ((f * (r * a) + 1).factorial : ℚ) ≠ 0 := by positivity
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 2 := ⟨f - 2, by omega⟩
      simp only [Nat.add_sub_cancel] at hden ⊢
      field_simp
      ring

end

end RestTerms
end

section
namespace RestTerms

open Finset Elem

noncomputable section

theorem RestBoundOfPrimeBound.proof : RestBoundOfPrimeBound.Statement := by
  classical
  intro f r a c B₀ hf hr ha hB Q s e hp P
  set R : ℕ → ℝ := fun p => restPrimeModel f r a c Q s e p with hR
  set C : ℝ := ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| with hC
  set X : ℝ := (restX r a : ℝ) with hXdef
  have hN2 : 2 ≤ r + a := by omega
  have hNR : (2 : ℝ) ≤ ((r + a : ℕ) : ℝ) := by exact_mod_cast hN2
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hB0 : 0 < B₀ := by nlinarith
  have hC0 : 0 ≤ C := by positivity
  have hX0 : 0 ≤ X := by
    simp only [hXdef, restX]; push_cast; positivity
  set K : ℝ := 1.5 * f * X * C with hK
  have hK0 : 0 ≤ K := by positivity
  set S : Set ℕ := {p | p ∈ P ∧ p.Prime ∧ B₀ < p} with hS
  set g : ℕ → ℝ := fun i => if i ∈ P ∧ i.Prime ∧ B₀ < i then |R i| else 0 with hg
  have hind : S.indicator (fun p => |R p|) = g := by
    funext i
    by_cases h : i ∈ P ∧ i.Prime ∧ B₀ < i
    · simp [hS, hg, Set.indicator_of_mem, h]
    · rw [Set.indicator_of_notMem (show i ∉ S from h)]
      simp [hg, h]
  have hg0 : ∀ i, 0 ≤ g i := fun i => by
    simp only [hg]; split_ifs <;> positivity
  have hgle : ∀ i, g i ≤ K * (primeWeight B₀ i / (i : ℝ) ^ 2) := fun i => by
    simp only [hg]
    split_ifs with h
    · have hw : primeWeight B₀ i = Real.log i := by simp [primeWeight, h.2.1, h.2.2]
      rw [hw]
      calc |R i| ≤ 1.5 * f * X * (Real.log i / (i : ℝ) ^ 2) * ((f * (r * a) + 1 : ℕ) : ℝ) *
            |(fibreDegree f r a c : ℝ)| := hp i h.2.1 h.2.2
        _ = K * (Real.log i / (i : ℝ) ^ 2) := by rw [hK, hC]; ring
    · exact mul_nonneg hK0 (div_nonneg (primeWeight_nonneg B₀ i) (by positivity))
  have hpart : ∀ n, ∑ i ∈ range n, g i ≤ K * (2 * Real.log 4 / B₀) := fun n => by
    calc ∑ i ∈ range n, g i ≤ ∑ i ∈ range n, K * (primeWeight B₀ i / (i : ℝ) ^ 2) :=
          Finset.sum_le_sum fun i _ => hgle i
      _ = K * ∑ i ∈ range n, primeWeight B₀ i / (i : ℝ) ^ 2 := by rw [Finset.mul_sum]
      _ ≤ K * (2 * Real.log 4 / B₀) :=
          mul_le_mul_of_nonneg_left (prime_partial_le B₀ hB0 n) hK0
  have hgs : Summable g := summable_of_sum_range_le hg0 hpart
  have hsub : Summable (fun p : S => |R p|) :=
    (summable_subtype_iff_indicator (f := fun p : ℕ => |R p|) (s := S)).mpr (by rw [hind]; exact hgs)
  refine ⟨hsub, ?_⟩
  have htsum : ∑' p : S, |R p| ≤ K * (2 * Real.log 4 / B₀) := by
    rw [tsum_subtype S (fun p : ℕ => |R p|), hind]
    exact Real.tsum_le_of_sum_range_le hg0 hpart
  have habs : |∑' p : S, R p| ≤ ∑' p : S, |R p| := by
    have := norm_tsum_le_tsum_norm (f := fun p : S => R p)
      (by simpa [Real.norm_eq_abs] using hsub)
    simpa [Real.norm_eq_abs] using this

  have hXle : X ≤ 3 / 2 * ((r + a : ℕ) : ℝ) ^ 2 := by
    have h := XBound.intersectionNumber_baseChange r a hN2
    simp only [hXdef] at h ⊢
    linarith [h.1, h.2]
  have hNpos : (0 : ℝ) < ((r + a : ℕ) : ℝ) := by linarith
  have hD : (0 : ℝ) < 4 * f * ((r + a : ℕ) : ℝ) ^ 2 := by positivity
  have hlog : 2 * Real.log 4 / B₀ ≤ 2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2) := by
    calc 2 * Real.log 4 / B₀ ≤ 2.78 / B₀ :=
          div_le_div_of_nonneg_right two_log_four_le hB0.le
      _ ≤ 2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2) :=
          div_le_div_of_nonneg_left (by norm_num) hD hB
  have hconst := RestConstants.intersectionNumber_baseChange.2 f (r + a) hf hN2
  have hfin : K * (2 * Real.log 4 / B₀) ≤ 1.6 * C := by
    have hl0 : 0 ≤ 2 * Real.log 4 / B₀ :=
      div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))) hB0.le
    calc K * (2 * Real.log 4 / B₀)
        = (1.5 * f * X) * (2 * Real.log 4 / B₀) * C := by rw [hK]; ring
      _ ≤ (1.5 * f * (3 / 2 * ((r + a : ℕ) : ℝ) ^ 2)) * (2.78 / (4 * f * ((r + a : ℕ) : ℝ) ^ 2)) * C := by
          apply mul_le_mul_of_nonneg_right _ hC0
          apply mul_le_mul _ hlog hl0 (by positivity)
          exact mul_le_mul_of_nonneg_left hXle (by positivity)
      _ ≤ 1.6 * C := mul_le_mul_of_nonneg_right hconst hC0
  calc |∑' p : S, R p| ≤ ∑' p : S, |R p| := habs
    _ ≤ K * (2 * Real.log 4 / B₀) := htsum
    _ ≤ 1.6 * C := hfin
    _ = 1.6 * ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| := by rw [hC]; ring

end

end RestTerms
end

section
namespace RestTerms

open Finset

noncomputable section

theorem RestKSumBound.proof : RestKSumBound.Statement := by
  intro p X N hp hX hXp
  obtain ⟨hsum, htsum, hexp⟩ := ExponentialTail.intersectionNumber_baseChange p X hp hX hXp
  set g : ℕ → ℝ := fun j => 2 * (p ^ (j + 2))⁻¹ * X ^ (j + 1) / ((j + 2).factorial : ℝ) with hg
  have hIcc : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := by
    ext k; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hre : ∑ k ∈ Finset.Icc 2 N, 2 * (p ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ) =
      ∑ j ∈ Finset.range (N + 1 - 2), g j := by
    rw [hIcc, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hg]
    simp only
    rw [show 2 + j = j + 2 from Nat.add_comm 2 j, show j + 2 - 1 = j + 1 by omega]
  have hnn : ∀ j, 0 ≤ g j := fun j => by rw [hg]; positivity
  rw [hre]
  calc ∑ j ∈ Finset.range (N + 1 - 2), g j ≤ ∑' j, g j :=
        hsum.sum_le_tsum _ fun j _ => hnn j
    _ ≤ Real.exp (3 / 8) * X / p ^ 2 := htsum
    _ ≤ 1.5 * X / p ^ 2 := hexp

end

end RestTerms
end

section
namespace RestTerms

open Finset

noncomputable section

theorem RestPrimeBoundOfFactor.proof (h₁ : RestInnerTsumBound.Statement)
    (h₂ : RestKSumBound.Statement) : RestPrimeBoundOfFactor.Statement := by
  intro f r a c B₀ hf hr ha hB Q hT s e he p hp hpB
  set Y : ℝ := ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| with hY
  set X : ℝ := (restX r a : ℝ) with hX
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hX0 : 0 ≤ X := by rw [hX]; unfold restX; positivity
  have hN : 2 ≤ r + a := by omega
  have hXp : X ≤ 3 / 8 * (p : ℝ) := by
    have := XOverPrime.intersectionNumber_baseChange f r a B₀ p hf hN hB hpB
    rw [div_le_iff₀ hp0] at this
    linarith
  have hY0 : 0 ≤ Y := by positivity

  have hterm : ∀ τ : Fin f, ∀ k ∈ Finset.Icc 2 (r + a),
      |∑' n : ℕ, ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
        ((e p (n + 1) τ k * restTerm f (r + a) Q k τ
          (smallPowerSum f r a c (k - 1) (s p (n + 1) τ)) : ℚ) : ℝ)| ≤
        (Y * X ^ (k - 1) / (k.factorial : ℝ)) * (2 * ((p : ℝ) ^ k)⁻¹) := by
    intro τ k hk
    rw [Finset.mem_Icc] at hk
    refine (h₁ (p : ℝ) k _ _ hp2 (by omega) ?_).2
    intro n
    have hb := hT k hk.1 hk.2 τ (s p (n + 1) τ)
    have habs : |e p (n + 1) τ k * restTerm f (r + a) Q k τ
        (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| =
        |restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| := by
      rw [abs_mul]
      rcases he p (n + 1) τ k with h | h <;> simp [h]
    rw [← Rat.cast_abs, habs]
    calc ((|restTerm f (r + a) Q k τ (smallPowerSum f r a c (k - 1) (s p (n + 1) τ))| : ℚ) : ℝ)
        ≤ ((((f * (r * a) + 1 : ℕ) : ℚ) * |fibreDegree f r a c| * restX r a ^ (k - 1) /
            (k.factorial : ℚ) : ℚ) : ℝ) := Rat.cast_le.mpr hb
      _ = Y * X ^ (k - 1) / (k.factorial : ℝ) := by
        rw [hY, hX]; push_cast; ring
  have hsumk := h₂ (p : ℝ) X (r + a) hp0 hX0 hXp
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  unfold restPrimeModel
  rw [abs_mul, abs_of_nonneg hlog]
  calc Real.log p * |∑ τ : Fin f, ∑ k ∈ Finset.Icc 2 (r + a), ∑' n : ℕ,
        ((p : ℝ) ^ ((n + 1) * k))⁻¹ *
          ((e p (n + 1) τ k * restTerm f (r + a) Q k τ
            (smallPowerSum f r a c (k - 1) (s p (n + 1) τ)) : ℚ) : ℝ)|
      ≤ Real.log p * ∑ τ : Fin f, ∑ k ∈ Finset.Icc 2 (r + a),
          (Y * X ^ (k - 1) / (k.factorial : ℝ)) * (2 * ((p : ℝ) ^ k)⁻¹) := by
        apply mul_le_mul_of_nonneg_left _ hlog
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        exact hterm τ k hk
    _ = Real.log p * ((f : ℝ) * (Y * ∑ k ∈ Finset.Icc 2 (r + a),
          2 * ((p : ℝ) ^ k)⁻¹ * X ^ (k - 1) / (k.factorial : ℝ))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        congr 1
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ Real.log p * ((f : ℝ) * (Y * (1.5 * X / (p : ℝ) ^ 2))) := by
        gcongr
    _ = 1.5 * (f : ℝ) * X * (Real.log p / (p : ℝ) ^ 2) * Y := by ring
    _ = 1.5 * f * (restX r a : ℝ) * (Real.log p / (p : ℝ) ^ 2) *
          ((f * (r * a) + 1 : ℕ) : ℝ) * |(fibreDegree f r a c : ℝ)| := by
        rw [hY, hX]; ring

end

end RestTerms
end

end GroundTheory.Heights₂.Heights

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

theorem sameFactor_descFactorial_le (n₁ N : ℕ) :
    ∀ k : ℕ, 1 ≤ k → k ≤ N →
      (n₁ + k).descFactorial k * 2 ^ (k - 1) ≤ (n₁ + 1) * (2 * (n₁ + N)) ^ (k - 1)
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, _ => by simp [Nat.descFactorial]
  | k + 2, _, hN => by
    have ih : (n₁ + (k + 1)).descFactorial (k + 1) * 2 ^ k ≤ (n₁ + 1) * (2 * (n₁ + N)) ^ k := by
      simpa only [Nat.add_sub_cancel] using
        sameFactor_descFactorial_le n₁ N (k + 1) (by omega) (by omega)
    have hd : (n₁ + (k + 2)).descFactorial (k + 2) =
        (n₁ + (k + 1) + 1) * (n₁ + (k + 1)).descFactorial (k + 1) :=
      Nat.succ_descFactorial_succ (n₁ + (k + 1)) (k + 1)
    rw [show k + 2 - 1 = k + 1 by omega, pow_succ 2 k, pow_succ (2 * (n₁ + N)) k, hd]
    have hleft :
        (n₁ + (k + 1) + 1) * (n₁ + (k + 1)).descFactorial (k + 1) * (2 ^ k * 2) =
          ((n₁ + (k + 1)).descFactorial (k + 1) * 2 ^ k) * (2 * (n₁ + (k + 1) + 1)) := by
      ring
    rw [hleft, ← mul_assoc (n₁ + 1)]
    exact Nat.mul_le_mul ih (by omega)

theorem sameFactor_choose_le (r a k : ℕ) (hk1 : 1 ≤ k) (hkN : k ≤ r + a) :
    (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) / ((r * a : ℕ) + 1 : ℚ) ≤
      restX r a ^ (k - 1) / (k.factorial : ℚ) := by
  have h := sameFactor_descFactorial_le (r * a) (r + a) k hk1 hkN
  rw [Nat.descFactorial_eq_factorial_mul_choose] at h
  have hq : ((k.factorial * Nat.choose (r * a + k) k * 2 ^ (k - 1) : ℕ) : ℚ) ≤
      ((((r * a) + 1) * (2 * ((r * a) + (r + a))) ^ (k - 1) : ℕ) : ℚ) := by exact_mod_cast h
  have hX : restX r a = ((2 * ((r * a) + (r + a)) : ℕ) : ℚ) := by
    simp only [restX]; push_cast; ring
  rw [div_le_div_iff₀ (by positivity) (by positivity), hX]
  push_cast at hq ⊢
  linarith

theorem SameFactorBound.proof (hF : SameFactorFormula.Statement) (hS : SchurSignCoefficient.Statement)
    (hB : CharacterBound.Statement) (hH : HookSumBound.Statement)
    (hR : RectangleTablePos.Statement) (hD : RestPolynomialDecomposes.Statement) :
    SameFactorBound.Statement := by
  intro f r a c hf hr ha
  obtain ⟨C₀, hC₀, hJ, hT⟩ := hF f r a c hf hr ha
  have hfR : (0 : ℚ) < numStandardTable (rectangle r a) := by exact_mod_cast hR r a
  obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hJabs : |fibreDegree (f' + 1) r a c| =
      |C₀| * (((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1)) := by
    have hJp : (0 : ℚ) ≤ ((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1) := by positivity
    rw [hJ, ← abs_of_nonneg hJp, ← abs_mul]
    congr 1
    ring
  refine ⟨?_, hD (f' + 1) r a c, ?_⟩
  · rw [hJ]
    exact mul_ne_zero (div_ne_zero (mul_ne_zero hC₀ (by positivity)) (by positivity))
      (pow_ne_zero _ hfR.ne')
  intro Q hQ k hk2 hkN τ
  obtain ⟨S, hSP, hTk⟩ := hT Q hQ k hk2 hkN τ
  have hk1 : 1 ≤ k := by omega
  set s : ℚ := c.sign with hs_def
  have hs : s = 1 ∨ s = -1 := by cases c <;> simp [hs_def, SmallBlock.sign]
  have hsk : |s ^ k| = 1 := by rcases hs with h | h <;> simp [h]
  have hmem : ∀ nu ∈ partitionsOf r k, Antitone nu ∧ ∑ i, nu i = k := by
    intro nu hnu
    simp only [partitionsOf, Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hnu
    exact ⟨fun i j hij => hnu.2 i j hij, hnu.1⟩
  set chi : (Fin r → ℕ) → ℚ := fun nu =>
    symmetricGroupCharacter (fun i => a + nu i) ((k - 1) :: List.replicate (r * a + 1) 1)
    with hchi
  have hex := fun nu (hnu : nu ∈ partitionsOf r k) =>
    hS (r + a) r k hk1 hkN nu s hs (hmem nu hnu).1 (hmem nu hnu).2
  choose! Sν hSν1 hSν2 using hex

  have hSeq : S = ∑ nu ∈ partitionsOf r k, C (chi nu) * Sν nu := by
    apply Flag.powerSumHom_injective

    rw [hSP, map_sum]
    refine Finset.sum_congr rfl fun nu hnu => ?_
    rw [map_mul, hSν1 nu hnu]
    congr 1
    simp [powerSumHom, hchi]
  set e : Fin (r + a) →₀ ℕ := Finsupp.single (⟨k - 1, by omega⟩ : Fin (r + a)) 1 with he
  have hcoef : |S.coeff e| ≤
      (∑ nu ∈ (partitionsOf r k).filter (fun nu => ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1),
        |chi nu|) / k := by
    rw [hSeq, coeff_sum]
    simp only [coeff_C_mul]
    calc |∑ nu ∈ partitionsOf r k, chi nu * (Sν nu).coeff e|
        ≤ ∑ nu ∈ partitionsOf r k, |chi nu * (Sν nu).coeff e| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ nu ∈ partitionsOf r k,
            if ∀ i : Fin r, (i : ℕ) ≠ 0 → nu i ≤ 1 then |chi nu| / k else 0 := by
          refine Finset.sum_congr rfl fun nu hnu => ?_
          rw [hSν2 nu hnu]
          split_ifs
          · rw [abs_mul, abs_mul, hsk, abs_div, abs_pow, abs_neg, abs_one, one_pow, Nat.abs_cast]
            ring
          · simp
      _ = _ := by rw [Finset.sum_div, Finset.sum_filter]
  have hhook := hH r a k chi hk1 (fun nu hnu => hB r _ _
    (fun i j hij => Nat.add_le_add_left ((hmem nu hnu).1 hij) a)
    (fun q hq => by
      simp only [List.mem_cons, List.mem_replicate] at hq
      omega))

  set K : ℚ := k * ((f' + 1) * (r * a) + 1).factorial /
      (((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f' + 1 - 1)) *
      (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1 - 1) with hK
  have hK0 : 0 ≤ K := by positivity
  have hTabs : |restTerm (f' + 1) (r + a) Q k τ (smallPowerSum (f' + 1) r a c (k - 1) τ)| =
      |C₀| * K * |S.coeff e| := by
    rw [hTk, show ∀ x : ℚ, C₀ * k * ((f' + 1) * (r * a) + 1).factorial /
        (((r * a + 1).factorial : ℚ) * ((r * a).factorial : ℚ) ^ (f' + 1 - 1)) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1 - 1) * x = C₀ * K * x from
        fun x => by rw [hK]; ring, abs_mul, abs_mul, abs_of_nonneg hK0]
  rw [hTabs, hJabs]
  set B : ℚ := (Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) *
    numStandardTable (rectangle r a) with hBdef
  have hk0 : (0 : ℚ) < k := by exact_mod_cast (show 0 < k by omega)
  have hcoefB : |S.coeff e| ≤ B / k := le_trans hcoef (div_le_div_of_nonneg_right hhook hk0.le)
  have hKB : K * (B / k) = ((f' + 1) * (r * a) + 1 : ℕ) *
      ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) *
      ((Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) / ((r * a : ℕ) + 1 : ℚ)) := by
    rw [hK, hBdef, Nat.add_sub_cancel, Nat.factorial_succ, Nat.factorial_succ (r * a)]
    have : ((r * a).factorial : ℚ) ≠ 0 := by positivity
    have : (((f' + 1) * (r * a)).factorial : ℚ) ≠ 0 := by positivity
    field_simp
    push_cast
    ring
  have hP : (0 : ℚ) ≤ ((f' + 1) * (r * a) + 1 : ℕ) *
      ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
        (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) := by positivity
  calc |C₀| * K * |S.coeff e| ≤ |C₀| * K * (B / k) :=
        mul_le_mul_of_nonneg_left hcoefB (by positivity)
    _ = |C₀| * (((f' + 1) * (r * a) + 1 : ℕ) *
          ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
            (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) *
          ((Nat.choose (r * a + k) k : ℚ) * 2 ^ (k - 1) / ((r * a : ℕ) + 1 : ℚ))) := by
        rw [mul_assoc, hKB]
    _ ≤ |C₀| * (((f' + 1) * (r * a) + 1 : ℕ) *
          ((((f' + 1) * (r * a)).factorial / ((r * a).factorial : ℚ) ^ (f' + 1) *
            (numStandardTable (rectangle r a) : ℚ) ^ (f' + 1))) *
          (restX r a ^ (k - 1) / (k.factorial : ℚ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (sameFactor_choose_le r a k hk1 hkN) hP) (abs_nonneg _)
    _ = _ := by ring

end

end GroundTheory.Heights₂.Heights.RestTerms
