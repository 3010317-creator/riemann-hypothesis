module

public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.RingTheory.Ideal.BigOperators
public import Mathlib.RingTheory.Ideal.Operations

@[expose] public section

namespace FunctorialResolution.EmbeddedResolution

section

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]

def multiIndexDeriv {h : ℕ} (D : Fin h → Derivation k R R) (α : Fin h → ℕ) (x : R) : R :=
  Fin.foldr h (fun i y => (⇑(D i))^[α i] y) x

private theorem multiIndexDeriv_succ {h : ℕ} (D : Fin (h + 1) → Derivation k R R)
    (α : Fin (h + 1) → ℕ) (x : R) :
    multiIndexDeriv D α x =
      (⇑(D 0))^[α 0] (multiIndexDeriv (fun i => D i.succ) (fun i => α i.succ) x) :=
  Fin.foldr_succ _ x

@[simp]
theorem multiIndexDeriv_of_isEmpty (D : Fin 0 → Derivation k R R) (α : Fin 0 → ℕ) :
    multiIndexDeriv D α = id :=
  rfl

@[simp]
theorem multiIndexDeriv_zero {h : ℕ} (D : Fin h → Derivation k R R) (f : R) :
    multiIndexDeriv D (0 : Fin h → ℕ) f = f := by
  induction h with
  | zero => rfl
  | succ _ ih => exact (Fin.foldr_succ _ _).trans (ih fun i => D i.succ)

@[simp]
theorem multiIndexDeriv_fun_zero {h : ℕ} (D : Fin h → Derivation k R R) (f : R) :
    multiIndexDeriv D (fun _ => 0) f = f :=
  multiIndexDeriv_zero D f

private theorem derivation_mem_pow_sub_one (J : Ideal R) (D : Derivation k R R) {n : ℕ} :
    ∀ {f : R}, f ∈ J ^ n → D f ∈ J ^ (n - 1) := by
  induction n with
  | zero => simp
  | succ m ih =>
    intro f hf
    rw [pow_succ] at hf
    refine Submodule.mul_induction_on (C := fun x => D x ∈ J ^ m) hf (fun a ha b hb => ?_)
      fun _ _ hx hy => by rw [map_add]; exact add_mem hx hy
    rw [D.leibniz, smul_eq_mul, smul_eq_mul]
    refine add_mem (Ideal.mul_mem_right _ _ ha) ?_
    rcases m with _ | m
    · simp
    · exact pow_succ' J m ▸ Ideal.mul_mem_mul hb (ih ha)

theorem multiIndexDeriv_mem_pow_sub {h : ℕ} (D : Fin h → Derivation k R R) (J : Ideal R) (n : ℕ)
    {f : R} (hf : f ∈ J ^ n) (α : Fin h → ℕ) :
    multiIndexDeriv D α f ∈ J ^ (n - ∑ i, α i) := by
  have hiter : ∀ (D₀ : Derivation k R R) (m k : ℕ) {x : R},
      x ∈ J ^ k → (⇑D₀)^[m] x ∈ J ^ (k - m) := by
    intro D₀ m
    induction m with
    | zero => simp
    | succ m ih =>
      intro k x hx
      simpa only [Function.iterate_succ_apply, Nat.sub_sub, add_comm 1 m] using
        ih (k - 1) (derivation_mem_pow_sub_one J D₀ hx)
  induction h with
  | zero => simpa using hf
  | succ _ ih =>
    rw [multiIndexDeriv_succ, Fin.sum_univ_succ, add_comm (α 0), ← Nat.sub_sub]
    exact hiter (D 0) (α 0) _ (ih (fun i => D i.succ) (fun i => α i.succ))

private theorem iterate_derivation_mul (D : Derivation k R R) (n : ℕ) (x y : R) :
    (⇑D)^[n] (x * y) =
      ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : R) * ((⇑D)^[i] x * (⇑D)^[n - i] y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, map_sum]
    refine (Finset.sum_congr rfl fun i hi =>
      show _ = ((n.choose i : ℕ) : R) * ((⇑D)^[i + 1] x * (⇑D)^[n - i] y) +
          ((n.choose i : ℕ) : R) * ((⇑D)^[i] x * (⇑D)^[n + 1 - i] y) by
        have hni : (n - i).succ = n + 1 - i := by rw [Finset.mem_range] at hi; omega
        rw [← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, D.leibniz, smul_eq_mul, smul_eq_mul,
          ← Function.iterate_succ_apply' (⇑D) i x, ← Function.iterate_succ_apply' (⇑D) (n - i) y,
          hni]
        ring).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_range_succ _ n, Finset.sum_range_succ' _ n,
      Finset.sum_range_succ' _ (n + 1), Finset.sum_range_succ _ n]
    simp only [Nat.choose_succ_succ, Nat.choose_self, Nat.choose_zero_right, Nat.choose_succ_self,
      Nat.sub_self, Nat.sub_zero, Nat.succ_sub_succ_eq_sub, Nat.succ_eq_add_one, add_comm 1,
      Nat.cast_add, Nat.cast_one, Nat.cast_zero, one_mul, add_mul, Finset.sum_add_distrib]
    ring

theorem multiIndexDeriv_mul {h : ℕ} (D : Fin h → Derivation k R R) (α : Fin h → ℕ) (f g : R) :
    multiIndexDeriv D α (f * g) =
      ∑ β ∈ Fintype.piFinset fun i => Finset.range (α i + 1),
        ((∏ i, (α i).choose (β i) : ℕ) : R) * multiIndexDeriv D β f *
          multiIndexDeriv D (fun i => α i - β i) g := by
  induction h with
  | zero => rw [Fintype.piFinset_of_isEmpty, Finset.univ_unique]; simp
  | succ h ih =>
    have hlin (z : R) : (⇑(D 0))^[α 0] z = ((D 0).toLinearMap ^ α 0) z :=
      (pow_apply_eq_iterate (D 0).toLinearMap (α 0) z).symm
    rw [multiIndexDeriv_succ, ih (fun i => D i.succ) (fun i => α i.succ), hlin, map_sum,
      ← Finset.sum_equiv (Fin.consEquiv fun _ : Fin (h + 1) => ℕ)
        (s := Finset.range (α 0 + 1) ×ˢ Fintype.piFinset fun i => Finset.range (α i.succ + 1))
        (by simp [Fin.forall_fin_succ]) fun _ _ => rfl,
      Finset.sum_product_right]
    refine Finset.sum_congr rfl fun γ _ => ?_
    rw [mul_assoc, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ← hlin,
      iterate_derivation_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Fin.consEquiv_apply, multiIndexDeriv_succ, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, Nat.cast_mul]
    ring

theorem multiIndexDeriv_mul_sub_sum_mem {h : ℕ} (D : Fin h → Derivation k R R) (J : Ideal R)
    (r s : ℕ) (α : Fin h → ℕ) (hα : ∑ i, α i = r + s) {f g : R}
    (hf : f ∈ J ^ r) (hg : g ∈ J ^ s) :
    multiIndexDeriv D α (f * g) -
        ∑ β ∈ (Fintype.piFinset fun i => Finset.range (α i + 1)).filter
            (fun β => ∑ i, β i = r),
          ((∏ i, (α i).choose (β i) : ℕ) : R) * multiIndexDeriv D β f *
            multiIndexDeriv D (fun i => α i - β i) g ∈ J := by
  rw [multiIndexDeriv_mul, ← Finset.sum_filter_add_sum_filter_not _ (fun β => ∑ i, β i = r),
    add_sub_cancel_left]
  refine Ideal.sum_mem _ fun β hβ => ?_
  obtain ⟨hβmem, hβne⟩ := Finset.mem_filter.mp hβ
  have h1 : (∑ i, (α i - β i)) + ∑ i, β i = r + s := by
    rw [← hα, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel <|
      Nat.lt_succ_iff.mp (Finset.mem_range.mp (Fintype.mem_piFinset.mp hβmem i))
  rcases lt_or_gt_of_ne hβne with hlt | hgt
  · exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _
      (Ideal.pow_le_self (by omega) (multiIndexDeriv_mem_pow_sub D J r hf β)))
  · exact Ideal.mul_mem_left _ _
      (Ideal.pow_le_self (by omega) (multiIndexDeriv_mem_pow_sub D J s hg _))

private theorem commute_multiIndexDeriv {h : ℕ} (D : Fin h → Derivation k R R) (E : R → R)
    (hE : ∀ i, Function.Commute E (⇑(D i))) (γ : Fin h → ℕ) :
    Function.Commute E (multiIndexDeriv D γ) := by
  induction h with
  | zero => intro _; rfl
  | succ _ ih =>
    intro x
    rw [multiIndexDeriv_succ, multiIndexDeriv_succ, (hE 0).iterate_right (γ 0),
      ih (fun i => D i.succ) (fun i => hE i.succ) (fun i => γ i.succ) x]

theorem multiIndexDeriv_add {h : ℕ} (D : Fin h → Derivation k R R)
    (hD : ∀ i j : Fin h, ∀ x : R, D i (D j x) = D j (D i x)) (α β : Fin h → ℕ) (x : R) :
    multiIndexDeriv D (α + β) x = multiIndexDeriv D α (multiIndexDeriv D β x) := by
  induction h generalizing x with
  | zero => rfl
  | succ h ih =>
    rw [multiIndexDeriv_succ, Pi.add_apply, Function.iterate_add_apply,
      show (fun i : Fin h => (α + β) i.succ) = (fun i => α i.succ) + fun i => β i.succ from rfl,
      ih (fun i => D i.succ) (fun i j => hD i.succ j.succ) (fun i => α i.succ)
        (fun i => β i.succ) x,
      ((commute_multiIndexDeriv (fun i => D i.succ) (⇑(D 0)) (fun i => hD 0 i.succ)
        (fun i => α i.succ)).iterate_left (β 0)) _,
      ← multiIndexDeriv_succ, ← multiIndexDeriv_succ]

def unitMultiIndex {h : ℕ} (i : Fin h) : Fin h → ℕ := fun j => if j = i then 1 else 0

theorem sum_unitMultiIndex {h : ℕ} (i : Fin h) : ∑ j, unitMultiIndex i j = 1 := by
  simp [unitMultiIndex]

theorem multiIndexDeriv_unitMultiIndex {h : ℕ} (D : Fin h → Derivation k R R) (i : Fin h) (x : R) :
    multiIndexDeriv D (unitMultiIndex i) x = D i x := by
  induction h with
  | zero => exact i.elim0
  | succ h ih =>
    refine i.cases ?_ fun j => ?_
    · simp [multiIndexDeriv_succ, unitMultiIndex]
    · rw [multiIndexDeriv_succ,
        show unitMultiIndex j.succ 0 = 0 by simp [unitMultiIndex, (Fin.succ_ne_zero j).symm],
        Function.iterate_zero_apply,
        show (fun k : Fin h => unitMultiIndex j.succ k.succ) = unitMultiIndex j by
          ext; simp [unitMultiIndex]]
      exact ih (fun k => D k.succ) j

theorem multiIndexDeriv_add_unitMultiIndex_apply_first {h : ℕ} (D : Fin h → Derivation k R R)
    (hD : ∀ i j : Fin h, ∀ x : R, D i (D j x) = D j (D i x)) (α : Fin h → ℕ) (i : Fin h) (x : R) :
    multiIndexDeriv D (α + unitMultiIndex i) x = multiIndexDeriv D α (D i x) := by
  rw [multiIndexDeriv_add D hD α (unitMultiIndex i) x, multiIndexDeriv_unitMultiIndex D i x]

end

end FunctorialResolution.EmbeddedResolution
