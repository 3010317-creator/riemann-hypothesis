module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.AdicCompletion.RingHom
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Order
public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.FieldTheory.Perfect
import Mathlib.RingTheory.Teichmuller

@[expose] public section

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.powerSeries_equiv_of_complete_dvr :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A]
      (p : ℕ) [Fact p.Prime] [CharP A p] [Finite (ResidueField A)] (t : A), Irreducible t →
      ∃ e : PowerSeries (ResidueField A) ≃+* A, e PowerSeries.X = t ∧
        ∀ c, residue A (e (PowerSeries.C c)) = c := by
  intro A _ _ _ _ p _ _ _ t ht
  classical
  have hH : ∀ x y : A, (∀ n : ℕ, x - y ∈ maximalIdeal A ^ n) → x = y := fun x y h =>
    (IsHausdorff.eq_iff_smodEq (I := maximalIdeal A)).mpr fun n =>
      SModEq.sub_mem.mpr (by simpa [Ideal.smul_eq_mul] using h n)
  have hm : maximalIdeal A = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
  have htm : t ∈ maximalIdeal A := hm ▸ Ideal.subset_span rfl
  have : CharP (A ⧸ maximalIdeal A) p := by
    rw [CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime),
      ← map_natCast (Ideal.Quotient.mk (maximalIdeal A)), CharP.cast_eq_zero, map_zero]
  have : ExpChar (A ⧸ maximalIdeal A) p := .prime Fact.out
  have : Finite (A ⧸ maximalIdeal A) := ‹Finite (ResidueField A)›
  let teichRing : Perfection (A ⧸ maximalIdeal A) p →+* A :=
    { toMonoidWithZeroHom := Perfection.teichmuller₀ p (maximalIdeal A)
      map_add' x y := Perfection.teichmuller₀_spec fun n => by
        refine ⟨(Perfection.coeff _ p n x).out + (Perfection.coeff _ p n y).out, by simp, ?_⟩
        rw [add_pow_char_pow]
        exact ((Perfection.teichmuller₀_sModEq (Ideal.Quotient.mk_out _)).add
          (Perfection.teichmuller₀_sModEq (Ideal.Quotient.mk_out _))).symm }
  let s : ResidueField A →+* A :=
    teichRing.comp (Perfection.lift p (A ⧸ maximalIdeal A) (A ⧸ maximalIdeal A) (RingHom.id _))
  have hsr : ∀ c, residue A (s c) = c := fun c =>
    (Perfection.mk_teichmuller₀ _).trans rfl
  have hev : ∀ n (f : PowerSeries (ResidueField A)),
      (PowerSeries.trunc n f).eval₂ s t =
        ∑ i ∈ Finset.range n, s (PowerSeries.coeff i f) * t ^ i := fun n f =>
    PowerSeries.eval₂_trunc_eq_sum_range t s n f
  have key : ∀ n (P Q : Polynomial (ResidueField A)), (∀ i < n, P.coeff i = Q.coeff i) →
      Ideal.Quotient.mk (maximalIdeal A ^ n) (P.eval₂ s t) =
        Ideal.Quotient.mk (maximalIdeal A ^ n) (Q.eval₂ s t) := by
    intro n P Q h
    rw [Ideal.Quotient.eq, ← Polynomial.eval₂_sub]
    obtain ⟨R, hR⟩ := (Polynomial.X_pow_dvd_iff (f := P - Q) (n := n)).mpr fun d hd => by
      rw [Polynomial.coeff_sub, h d hd, sub_self]
    rw [hR, Polynomial.eval₂_mul, Polynomial.eval₂_X_pow]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow htm n)
  let g : (n : ℕ) → PowerSeries (ResidueField A) →+* A ⧸ maximalIdeal A ^ n := fun n =>
    { toFun f := Ideal.Quotient.mk (maximalIdeal A ^ n) ((PowerSeries.trunc n f).eval₂ s t)
      map_one' := by
        rw [key n _ 1 fun i hi => by
          simp [PowerSeries.coeff_trunc, hi, PowerSeries.coeff_one, Polynomial.coeff_one],
          Polynomial.eval₂_one, map_one]
      map_mul' f g' := by
        rw [← map_mul, ← Polynomial.eval₂_mul]
        exact key n _ _ fun i hi => by
          rw [← PowerSeries.trunc_trunc_mul_trunc]
          simp [PowerSeries.coeff_trunc, hi, ← Polynomial.coe_mul, Polynomial.coeff_coe]
      map_zero' := by simp
      map_add' f g' := by simp [hev] }
  have hg : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (maximalIdeal A) hle).comp (g n) = g m := fun {m n} hle => by
    ext f
    rw [RingHom.comp_apply]
    show Ideal.Quotient.factorPow (maximalIdeal A) hle
        (Ideal.Quotient.mk _ ((PowerSeries.trunc n f).eval₂ s t)) = _
    rw [Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
    exact key m _ _ fun i hi => by simp [PowerSeries.coeff_trunc, hi, lt_of_lt_of_le hi hle]
  let e0 := IsAdicComplete.liftRingHom (maximalIdeal A) g hg
  have hEq : ∀ n f, e0 f - (PowerSeries.trunc n f).eval₂ s t ∈ maximalIdeal A ^ n := fun n f =>
    Ideal.Quotient.eq.mp (IsAdicComplete.mk_liftRingHom (maximalIdeal A) g hg n f)
  have hres : ∀ f, residue A (e0 f) = PowerSeries.constantCoeff f := fun f => by
    have h1 := hEq 1 f
    rw [pow_one, hev, Finset.sum_range_one, pow_zero, mul_one] at h1
    exact (Ideal.Quotient.eq.mpr h1).trans
      ((hsr _).trans (PowerSeries.coeff_zero_eq_constantCoeff_apply f))
  have hX : e0 PowerSeries.X = t := by
    refine hH _ _ fun n => Ideal.pow_le_pow_right (n := n + 2) (m := n) (by omega) ?_
    have h1 := hEq (n + 2) PowerSeries.X
    have h2 : (PowerSeries.trunc (n + 2) PowerSeries.X).eval₂ s t = t := by
      rw [hev, Finset.sum_range_succ', Finset.sum_range_succ']
      simp [PowerSeries.coeff_X]
    rwa [h2] at h1
  have hinj : Function.Injective e0 := by
    refine (injective_iff_map_eq_zero e0).mpr fun f hf => ?_
    by_contra hne
    have hu : residue A (e0 (PowerSeries.divXPowOrder f)) ≠ 0 := by
      rw [hres]
      exact PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hne
    have hu' : e0 (PowerSeries.divXPowOrder f) ≠ 0 := fun h => hu (by rw [h, map_zero])
    rw [← PowerSeries.X_pow_order_mul_divXPowOrder (f := f), map_mul, map_pow, hX] at hf
    exact mul_ne_zero (pow_ne_zero _ ht.ne_zero) hu' hf
  have hδ : ∀ x : A, ∃ y, y * t = x - s (residue A x) := fun x => by
    rw [← Ideal.mem_span_singleton', ← hm, ← Ideal.Quotient.eq_zero_iff_mem, map_sub]
    exact sub_eq_zero.mpr (hsr _).symm
  choose δ hδ using hδ
  have hsurj : Function.Surjective e0 := fun x => by
    let F : PowerSeries (ResidueField A) := PowerSeries.mk fun n => residue A (δ^[n] x)
    have hc : ∀ n, x = (PowerSeries.trunc n F).eval₂ s t + t ^ n * δ^[n] x := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [hev, Finset.sum_range_succ, ← hev, Function.iterate_succ_apply', PowerSeries.coeff_mk]
        linear_combination ih - t ^ n * hδ (δ^[n] x)
    refine ⟨F, hH _ _ fun n => ?_⟩
    have h2 : e0 F - x = (e0 F - (PowerSeries.trunc n F).eval₂ s t) - t ^ n * δ^[n] x := by
      linear_combination -(hc n)
    rw [h2]
    exact Ideal.sub_mem _ (hEq n F) (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow htm n))
  exact ⟨RingEquiv.ofBijective e0 ⟨hinj, hsurj⟩, hX, fun c => by
    show residue A (e0 (PowerSeries.C c)) = c
    rw [hres, PowerSeries.constantCoeff_C]⟩
