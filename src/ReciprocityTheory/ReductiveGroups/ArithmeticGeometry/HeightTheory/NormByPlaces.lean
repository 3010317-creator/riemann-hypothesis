module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtDefs
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HeightIntegralEstimates
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.Tactic.Lemma
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HNormB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.KTFiniteDimensional
public import Mathlib.Algebra.MvPolynomial.Nilpotent

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open NumberField

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}

namespace Data

variable (d : Data K ι Ω WT A)

theorem gen_span {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) : p = Ideal.span {d.gen p} := by
  obtain ⟨hprime, hh⟩ := hp
  haveI := hprime
  have hne : p ≠ ⊥ := by
    rintro rfl
    rw [Ideal.height_bot] at hh
    exact zero_ne_one hh
  obtain ⟨q, hqp, hq⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hprime hne
  have hsq : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
  have hle : Ideal.span {q} ≤ p := (Ideal.span_singleton_le_iff_mem _).mpr hqp
  have heq : Ideal.span {q} = p := by
    by_contra hne2
    haveI := hsq
    have hqb : (⊥ : Ideal (KTp K d.D d.N)) < Ideal.span {q} := by
      rw [bot_lt_iff_ne_bot, Ne, Ideal.span_singleton_eq_bot]
      exact hq.ne_zero
    have h1 : (Ideal.span {q}).height < ((1 : ℕ) : ℕ∞) :=
      (Ideal.height_le_iff (n := 1)).mp (by rw [hh]; norm_num) _ hsq (lt_of_le_of_ne hle hne2)
    have h2 : ¬ (Ideal.span {q}).height ≤ ((0 : ℕ) : ℕ∞) := by
      rw [Ideal.height_le_iff]
      push Not
      exact ⟨⊥, Ideal.isPrime_bot, hqb, by simp⟩
    apply h2
    have h1' : (Ideal.span {q}).height < 1 := by simpa using h1
    simpa using ENat.lt_one_iff_eq_zero.mp h1'
  have hpr : p.IsPrincipal := ⟨⟨q, heq.symm⟩⟩
  unfold Data.gen
  rw [dite_eq_left hpr]
  exact (Ideal.span_singleton_generator p).symm

private lemma gen_notMem_of_ne {p q : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) (hq : q ∈ d.HtOne)
    (hne : q ≠ p) : d.gen q ∉ p := by
  intro hg
  have hle : q ≤ p := by
    rw [d.gen_span hq]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hg
  haveI := hp.1
  have h1 := (Ideal.height_le_iff (n := 1)).mp (by rw [hp.2]; norm_num) q hq.1 (lt_of_le_of_ne hle hne)
  rw [hq.2] at h1
  norm_num at h1

private lemma exists_const_of_locally_unit_at_htOne (u : KTf K d.D d.N) (hu : u ≠ 0)
    (hloc : ∀ p ∈ d.HtOne, ∃ a s : KTp K d.D d.N, a ∉ p ∧ s ∉ p ∧
      u * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a) :
    ∃ κ : K, κ ≠ 0 ∧ u = algebraMap K (KTf K d.D d.N) κ := by
  have hred := IsFractionRing.num_den_reduced (KTp K d.D d.N) u
  have heq := IsFractionRing.mk'_num_den' (KTp K d.D d.N) u
  set n := IsFractionRing.num (KTp K d.D d.N) u with hn_def
  set m := IsFractionRing.den (KTp K d.D d.N) u with hm_def
  have hm0 : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (m : KTp K d.D d.N) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors m.2
  have hnu : algebraMap (KTp K d.D d.N) (KTf K d.D d.N) n =
      u * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (m : KTp K d.D d.N) := by
    rw [← heq, div_mul_cancel₀ _ hm0]
  have hcross : ∀ a s : KTp K d.D d.N,
      u * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a →
      n * s = a * (m : KTp K d.D d.N) := by
    intro a s has
    apply IsFractionRing.injective (KTp K d.D d.N) (KTf K d.D d.N)
    rw [map_mul, map_mul, hnu, ← has]
    ring
  have hn0 : n ≠ 0 := by
    intro h0
    apply hu
    rw [← heq, h0, map_zero, zero_div]
  have hm0' : (m : KTp K d.D d.N) ≠ 0 := nonZeroDivisors.coe_ne_zero m
  have hunit : ∀ x : KTp K d.D d.N, x ≠ 0 → (x = n ∨ x = m) → IsUnit x := by
    intro x hx0 hx
    by_contra hxu
    obtain ⟨π, hirr, hπx⟩ := WfDvdMonoid.exists_irreducible_factor hxu hx0
    have hπ : Prime π := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
    obtain ⟨a, s, ha, hs, has⟩ := hloc _
      ⟨(Ideal.span_singleton_prime hπ.ne_zero).mpr hπ, ValUFD.height_span_prime hπ⟩
    have hR := hcross a s has
    have hπa : ¬ π ∣ a := fun h => ha (Ideal.mem_span_singleton.mpr h)
    have hπs : ¬ π ∣ s := fun h => hs (Ideal.mem_span_singleton.mpr h)
    rcases hx with rfl | rfl
    · have h1 : π ∣ a * m := hR ▸ dvd_mul_of_dvd_left hπx s
      rcases hπ.dvd_or_dvd h1 with h | h
      · exact hπa h
      · exact hπ.not_unit (hred hπx h)
    · have h1 : π ∣ n * s := hR.symm ▸ dvd_mul_of_dvd_right hπx a
      rcases hπ.dvd_or_dvd h1 with h | h
      · exact hπ.not_unit (hred h hπx)
      · exact hπs h
  obtain ⟨r1, hr1, hn⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp (hunit n hn0 (Or.inl rfl))
  obtain ⟨r2, hr2, hm⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp (hunit _ hm0' (Or.inr rfl))
  have hC : ∀ r : K, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (MvPolynomial.C r) =
      algebraMap K (KTf K d.D d.N) r := fun r => by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  refine ⟨r1 / r2, div_ne_zero hr1.ne_zero hr2.ne_zero, ?_⟩
  rw [← heq, hn, hm, hC, hC, map_div₀]

private lemma prod_gen_zpow_split_at {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne) (E : Ideal (KTp K d.D d.N) → ℤ)
    (T : Finset (Ideal (KTp K d.D d.N))) (hT : ∀ q ∈ T, q ∈ d.HtOne) :
    ∃ A B : KTp K d.D d.N, A ∉ p ∧ B ∉ p ∧
      (∏ q ∈ T, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q) *
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) B =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ (if p ∈ T then E p else 0) *
          algebraMap (KTp K d.D d.N) (KTf K d.D d.N) A := by
  classical
  haveI := hp.1
  let T' := T.erase p
  let φ := algebraMap (KTp K d.D d.N) (KTf K d.D d.N)
  have hmem : ∀ q ∈ T', d.gen q ∈ p.primeCompl := fun q hq =>
    gen_notMem_of_ne d hp (hT q (Finset.mem_of_mem_erase hq)) (Finset.ne_of_mem_erase hq)
  refine ⟨∏ q ∈ T'.filter (fun q => 0 ≤ E q), d.gen q ^ (E q).toNat,
    ∏ q ∈ T'.filter (fun q => ¬ 0 ≤ E q), d.gen q ^ (-E q).toNat,
    p.primeCompl.prod_mem fun q hq => pow_mem (hmem q (Finset.mem_filter.1 hq).1) _,
    p.primeCompl.prod_mem fun q hq => pow_mem (hmem q (Finset.mem_filter.1 hq).1) _, ?_⟩
  have hsplit : (∏ q ∈ T, φ (d.gen q) ^ E q) =
      φ (d.gen p) ^ (if p ∈ T then E p else 0) * ∏ q ∈ T', φ (d.gen q) ^ E q := by
    split_ifs with hpT
    · exact (Finset.mul_prod_erase T _ hpT).symm
    · dsimp [T']; rw [zpow_zero, one_mul, Finset.erase_eq_of_notMem hpT]
  have hpos : (∏ q ∈ T'.filter (fun q => 0 ≤ E q), φ (d.gen q) ^ E q) =
      φ (∏ q ∈ T'.filter (fun q => 0 ≤ E q), d.gen q ^ (E q).toNat) := by
    rw [map_prod]
    refine Finset.prod_congr rfl fun q hq => ?_
    rw [map_pow, ← zpow_natCast, Int.toNat_of_nonneg (Finset.mem_filter.1 hq).2]
  have hneg : (∏ q ∈ T'.filter (fun q => ¬ 0 ≤ E q), φ (d.gen q) ^ E q) *
      φ (∏ q ∈ T'.filter (fun q => ¬ 0 ≤ E q), d.gen q ^ (-E q).toNat) = 1 := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun q hq => ?_
    have hq' := Finset.mem_filter.1 hq
    have hq0 : φ (d.gen q) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff]
      exact fun h0 => hmem q hq'.1 (h0 ▸ p.zero_mem)
    rw [map_pow, ← zpow_natCast, ← zpow_add₀ hq0,
      show E q + ((-E q).toNat : ℤ) = 0 by omega, zpow_zero]
  change (∏ q ∈ T, φ (d.gen q) ^ E q) * φ _ = φ _ ^ _ * φ _
  rw [hsplit, ← Finset.prod_filter_mul_prod_filter_not T' (fun q => 0 ≤ E q), mul_assoc,
    mul_assoc, hneg, mul_one, hpos]

private lemma overP_finite (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N))
    (hp : p ∈ d.HtOne) : (d.OverP c p).Finite := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1
  have hmap : ∀ x : KTp K d.D d.N, algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) x) = d.sH c x := by
    intro x
    exact IsFractionRing.lift_algebraMap (h c) x
  have hOver : d.OverP c p = HNm.OverR (R := KTp K d.D d.N) (F := KTf K d.D d.N) (L := OmS (Ω c) d.D d.N) p := by
    ext w
    simp only [Data.OverP, HNm.OverR, Set.mem_setOf_eq, hmap]
  obtain ⟨hprime, hh⟩ := hp
  haveI := hprime
  rw [hOver]
  exact (HNm.local_norm (R := KTp K d.D d.N) (F := KTf K d.D d.N) (L := OmS (Ω c) d.D d.N) p hh
    (d.gen p) (d.gen_span ⟨hprime, hh⟩) 1 one_ne_zero).1

theorem norm_by_places (hd : d.AxH 𝒜) (h : d.S1) (c : ι) :
    (∀ p ∈ d.HtOne, (d.OverP c p).Finite) ∧
    ∀ y : OmS (Ω c) d.D d.N, y ≠ 0 →
      {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w y ≠ 0}.Finite ∧
      ∃ κ : K, κ ≠ 0 ∧
        letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
        Algebra.norm (KTf K d.D d.N) y =
          algebraMap K (KTf K d.D d.N) κ *
            ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
              algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^
                (∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
                  (d.fze h c w : ℤ) * WithTop.untopD 0 (w y)) := by
  letI : Algebra (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.KTtoS h c).toAlgebra
  haveI : FiniteDimensional (KTf K d.D d.N) (OmS (Ω c) d.D d.N) := (d.omS_finite hd h c).1
  have hmap : ∀ x : KTp K d.D d.N, algebraMap (KTf K d.D d.N) (OmS (Ω c) d.D d.N)
      (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) x) = d.sH c x := by
    intro x
    exact IsFractionRing.lift_algebraMap (h c) x
  have hOver : ∀ p, d.OverP c p =
      HNm.OverR (R := KTp K d.D d.N) (F := KTf K d.D d.N) (L := OmS (Ω c) d.D d.N) p := by
    intro p
    ext w
    simp only [Data.OverP, HNm.OverR, Set.mem_setOf_eq, hmap]
  refine ⟨fun p hp => overP_finite d hd h c p hp, fun y hy => ?_⟩
  have hset : {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w y ≠ 0} =
      {p : Ideal (KTp K d.D d.N) | p.IsPrime ∧ p.height = 1 ∧
        ∃ w ∈ HNm.OverR (R := KTp K d.D d.N) (F := KTf K d.D d.N) (L := OmS (Ω c) d.D d.N) p, w y ≠ 0} := by
    ext p
    simp only [Set.mem_setOf_eq, Data.HtOne, hOver, and_assoc]
  have hfin : {p | p ∈ d.HtOne ∧ ∃ w ∈ d.OverP c p, w y ≠ 0}.Finite := by
    rw [hset]
    exact HNm.fin_support (R := KTp K d.D d.N) (F := KTf K d.D d.N) (L := OmS (Ω c) d.D d.N) y hy
  refine ⟨hfin, ?_⟩
  classical
  set E : Ideal (KTp K d.D d.N) → ℤ := fun p =>
    ∑ᶠ (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (_ : w ∈ d.OverP c p),
      (d.fze h c w : ℤ) * WithTop.untopD 0 (w y) with hE_def
  set T := hfin.toFinset with hT_def
  have hTsub : ∀ q ∈ T, q ∈ d.HtOne := fun q hq => ((Set.Finite.mem_toFinset _).mp hq).1
  have hE0 : ∀ p ∈ d.HtOne, p ∉ T → E p = 0 := by
    intro p hp hpT
    have hz : ∀ w ∈ d.OverP c p, w y = 0 := by
      intro w hw
      by_contra hne
      exact hpT ((Set.Finite.mem_toFinset _).mpr ⟨hp, w, hw, hne⟩)
    rw [hE_def]
    apply finsum_eq_zero_of_forall_eq_zero
    intro w
    by_cases hw : w ∈ d.OverP c p
    · simp [hw, hz w hw]
    · simp [hw]
  set z := Algebra.norm (KTf K d.D d.N) y with hz_def
  have hz0 : z ≠ 0 := Algebra.norm_ne_zero_iff.mpr hy
  set P := ∏ q ∈ T, algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen q) ^ E q with hP_def
  have hP0 : P ≠ 0 := by
    rw [hP_def, Finset.prod_ne_zero_iff]
    intro q hq
    apply zpow_ne_zero
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    intro h0
    have hqH := hTsub q hq
    have hq' := d.gen_span hqH
    rw [h0, Ideal.span_singleton_eq_bot.mpr rfl] at hq'
    have h2 := hqH.2
    rw [hq', Ideal.height_bot] at h2
    exact zero_ne_one h2
  have hloc : ∀ p ∈ d.HtOne, ∃ a s : KTp K d.D d.N, a ∉ p ∧ s ∉ p ∧
      z / P * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a := by
    intro p hp
    haveI := hp.1
    obtain ⟨-, a, s, ha, hs, hzs⟩ := HNm.local_norm (R := KTp K d.D d.N) (F := KTf K d.D d.N)
      (L := OmS (Ω c) d.D d.N) p hp.2 (d.gen p) (d.gen_span hp) y hy
    rw [← hOver p] at hzs
    change z * _ = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p * _ at hzs
    obtain ⟨A, B, hA, hB, hAB⟩ := prod_gen_zpow_split_at d hp E T hTsub
    have hexp : (if p ∈ T then E p else 0) = E p := by
      split_ifs with hpT
      · rfl
      · exact (hE0 p hp hpT).symm
    rw [hexp] at hAB
    refine ⟨a * B, s * A, fun h' => (hp.1.mem_or_mem h').elim ha hB,
      fun h' => (hp.1.mem_or_mem h').elim hs hA, ?_⟩
    have key : z * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s *
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) A =
        algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) B * P := by
      rw [hzs]
      calc algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p *
            algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) A
          = algebraMap (KTp K d.D d.N) (KTf K d.D d.N) a *
            (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p *
              algebraMap (KTp K d.D d.N) (KTf K d.D d.N) A) := by ring
        _ = _ := by rw [← hAB]; ring
    rw [map_mul, map_mul]
    calc z / P * (algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) A)
        = z * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) s * algebraMap (KTp K d.D d.N) (KTf K d.D d.N) A / P := by
          ring
      _ = _ := by rw [key, mul_div_cancel_right₀ _ hP0]
  obtain ⟨κ, hκ, hu⟩ := exists_const_of_locally_unit_at_htOne d (z / P) (div_ne_zero hz0 hP0) hloc
  refine ⟨κ, hκ, ?_⟩
  have hfp : ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p = P := by
    rw [hP_def]
    apply finprod_mem_eq_prod_of_subset
    · rintro p ⟨hpH, hp1⟩
      by_contra hpT
      exact hp1 (by simp only []; rw [hE0 p hpH hpT, zpow_zero])
    · exact fun q hq => hTsub q hq
  change z = algebraMap K (KTf K d.D d.N) κ * ∏ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
      algebraMap (KTp K d.D d.N) (KTf K d.D d.N) (d.gen p) ^ E p
  rw [hfp, ← hu, div_mul_cancel₀ _ hP0]

end Data

end ReciprocityTheory.ChartRestriction.G.T0
