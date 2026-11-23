module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.Idempotents

@[expose] public section

namespace GlobalTheory.AlgRing

private theorem isNilpotent_mul_comm {R : Type} [Ring R] {a b : R}
    (h : IsNilpotent (a * b)) : IsNilpotent (b * a) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + 1, ?_⟩
  rw [pow_succ, ← mul_assoc, ← (SemiconjBy.pow_right (mul_assoc b a b).symm n).eq, hn, mul_zero,
    zero_mul]

private theorem not_isNilpotent_mul_mul_of_mul_eq {R : Type} [Ring R] (f a y : R)
    (hl : f * a = a) (hy : ¬ IsNilpotent (y * a)) : ¬ IsNilpotent (a * y * f) := fun h =>
  hy <| isNilpotent_mul_comm <| by simpa [← mul_assoc, hl] using isNilpotent_mul_comm h

private theorem exists_idempotent_of_not_isNilpotent (k R : Type) [Field k] [Ring R] [Algebra k R]
    (x : R) (hx : IsIntegral k x) (hn : ¬ IsNilpotent x) :
    ∃ e : R, IsIdempotentElem e ∧ e ≠ 0 ∧ ∃ q : Polynomial k, e = x * Polynomial.aeval x q := by
  have hp0 : minpoly k x ≠ 0 := minpoly.ne_zero hx
  obtain ⟨g, hpg, hg⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly k x) hp0 0
  simp only [map_zero, sub_zero] at hpg hg
  set s := Polynomial.rootMultiplicity 0 (minpoly k x)
  obtain ⟨a, b, hab⟩ := (Polynomial.irreducible_X.coprime_iff_not_dvd.mpr hg).pow_left (m := s + 1)
  have hev : Polynomial.aeval x (Polynomial.X ^ s * g) = 0 := hpg ▸ minpoly.aeval k x
  have hE : ∀ P : Polynomial k, Polynomial.aeval x (P * (Polynomial.X ^ s * g)) = 0 := fun P => by
    rw [map_mul, hev, mul_zero]
  refine ⟨Polynomial.aeval x (a * Polynomial.X ^ (s + 1)), ?_, ?_, ⟨a * Polynomial.X ^ s, ?_⟩⟩
  · have hpoly : (a * Polynomial.X ^ (s + 1)) * (a * Polynomial.X ^ (s + 1)) =
        a * Polynomial.X ^ (s + 1) + -(a * b * Polynomial.X) * (Polynomial.X ^ s * g) := by
      linear_combination (a * Polynomial.X ^ (s + 1)) * hab
    unfold IsIdempotentElem
    rw [← map_mul, hpoly, map_add, hE, add_zero]
  · intro he
    apply hn
    refine ⟨s, ?_⟩
    have hpoly : (Polynomial.X : Polynomial k) ^ s =
        Polynomial.X ^ s * (a * Polynomial.X ^ (s + 1)) + b * (Polynomial.X ^ s * g) := by
      linear_combination Polynomial.X ^ s * hab.symm
    have := congrArg (Polynomial.aeval x) hpoly
    rwa [map_add, hE, add_zero, map_mul, he, mul_zero, map_pow, Polynomial.aeval_X] at this
  · rw [show a * Polynomial.X ^ (s + 1) = Polynomial.X * (a * Polynomial.X ^ s) by ring,
      map_mul, Polynomial.aeval_X]

private theorem exists_idempotent_mem_left_multiples (k R : Type) [Field k] [Ring R] [Algebra k R]
    (hint : ∀ x : R, IsIntegral k x) (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0)
    (x : R) (hx : x ≠ 0) : ∃ e r : R, IsIdempotentElem e ∧ e ≠ 0 ∧ e = r * x := by
  have : ¬ ∀ y : R, IsNilpotent (y * x) := fun h => hx (hnil x h)
  push Not at this
  obtain ⟨y, hy⟩ := this
  obtain ⟨e, he, he0, q, rfl⟩ := exists_idempotent_of_not_isNilpotent k R (y * x) (hint _) hy
  have hcomm : Commute (y * x) (Polynomial.aeval (y * x) q) := by
    simpa using (Polynomial.commute_X q).map (Polynomial.aeval (y * x))
  exact ⟨_, Polynomial.aeval (y * x) q * y, he, he0, by rw [hcomm.eq, mul_assoc]⟩

private theorem sum_eq_one_of_maximal_orthogonalIdempotents (k R : Type) [Field k] [Ring R]
    [Algebra k R] (hint : ∀ x : R, IsIntegral k x)
    (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False) :
    ∑ i, e i = 1 := by
  by_contra hsum
  set f := 1 - ∑ i, e i with hfdef
  have hf : IsIdempotentElem f := he.isIdempotentElem_sum.one_sub
  have hef : ∀ i, e i * f = 0 := fun i => by
    rw [hfdef, mul_sub, mul_one, he.mul_sum_of_mem (Finset.mem_univ i), sub_self]
  have hfe : ∀ i, f * e i = 0 := fun i => by
    rw [hfdef, sub_mul, one_mul, Finset.sum_mul,
      Finset.sum_eq_single i (fun j _ hj => he.ortho hj) (by simp), (he.idem i).eq, sub_self]
  obtain ⟨e', r, he', he'0, rfl⟩ :=
    exists_idempotent_mem_left_multiples k R hint hnil f (sub_ne_zero.mpr (Ne.symm hsum))
  have hg : IsIdempotentElem (f * (r * f)) := by
    change f * (r * f) * (f * (r * f)) = f * (r * f)
    rw [mul_assoc f, ← mul_assoc (r * f), mul_assoc r f f, hf.eq, he'.eq]
  have hg0 : f * (r * f) ≠ 0 := fun h0 =>
    he'0 (by rw [← he'.eq, mul_assoc, h0, mul_zero])
  refine hmax (Fin.cons (f * (r * f)) e) ⟨Fin.forall_fin_succ.2 ⟨hg, he.idem⟩, ?_⟩
    (Fin.forall_fin_succ.2 ⟨hg0, hne⟩)
  rw [Pairwise, Fin.forall_fin_succ]
  refine ⟨Fin.forall_fin_succ.2 ⟨fun h => absurd rfl h, fun j _ => by
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [mul_assoc, mul_assoc, hfe, mul_zero, mul_zero]⟩, fun i => Fin.forall_fin_succ.2 ⟨fun _ => by
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← mul_assoc, hef, zero_mul], fun j hij => by
        simp only [Fin.cons_succ]
        exact he.ortho (fun h => hij (congrArg Fin.succ h))⟩⟩

private theorem eq_of_idempotent_in_corner_of_maximal {R : Type} [Ring R] {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i : Fin m) (f : R) (hf : IsIdempotentElem f) (hf0 : f ≠ 0) (hl : e i * f = f)
    (hr : f * e i = f) : f = e i := by
  by_contra hfe
  have hg : IsIdempotentElem (e i - f) := by
    change (e i - f) * (e i - f) = e i - f
    rw [sub_mul, mul_sub, mul_sub, (he.idem i).eq, hl, hr, hf.eq]; abel
  have hg0 : e i - f ≠ 0 := sub_ne_zero.mpr (Ne.symm hfe)
  have hgf : (e i - f) * f = 0 := by rw [sub_mul, hl, hf.eq, sub_self]
  have hfg : f * (e i - f) = 0 := by rw [mul_sub, hr, hf.eq, sub_self]
  have hjf : ∀ j, j ≠ i → e j * f = 0 := fun j hj => by rw [← hl, ← mul_assoc, he.ortho hj, zero_mul]
  have hfj : ∀ j, j ≠ i → f * e j = 0 := fun j hj => by rw [← hr, mul_assoc, he.ortho hj.symm, mul_zero]
  have hjg : ∀ j, j ≠ i → e j * (e i - f) = 0 := fun j hj => by rw [mul_sub, he.ortho hj, hjf j hj, sub_self]
  have hgj : ∀ j, j ≠ i → (e i - f) * e j = 0 := fun j hj => by rw [sub_mul, he.ortho hj.symm, hfj j hj, sub_self]
  set u := Function.update e i f
  refine hmax (Fin.cons (e i - f) u) ⟨Fin.forall_fin_succ.2 ⟨hg, fun j => ?_⟩, ?_⟩
    (Fin.forall_fin_succ.2 ⟨hg0, fun j => ?_⟩)
  · by_cases h : j = i <;> simp [u, h, hf, he.idem]
  · rw [Pairwise, Fin.forall_fin_succ]
    refine ⟨Fin.forall_fin_succ.2 ⟨fun h => absurd rfl h, fun b _ => ?_⟩,
      fun a => Fin.forall_fin_succ.2 ⟨fun _ => ?_, fun b hab => ?_⟩⟩
    · simp only [Fin.cons_zero, Fin.cons_succ, u, Function.update_apply]
      split_ifs with hb
      · exact hgf
      · exact hgj b hb
    · simp only [Fin.cons_zero, Fin.cons_succ, u, Function.update_apply]
      split_ifs with ha
      · exact hfg
      · exact hjg a ha
    · have hab' : a ≠ b := fun h => hab (congrArg Fin.succ h)
      simp only [Fin.cons_succ, u, Function.update_apply]
      split_ifs with ha hb hb
      · exact absurd (ha.trans hb.symm) hab'
      · exact hfj b hb
      · exact hjf a ha
      · exact he.ortho hab'
  · by_cases h : j = i <;> simp [u, h, hf0, hne]

private theorem exists_right_inverse_in_corner_of_not_isNilpotent (k R : Type) [Field k] [Ring R]
    [Algebra k R] (hint : ∀ x : R, IsIntegral k x) {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i : Fin m) (z : R) (hl : e i * z = z) (hr : z * e i = z) (hz : ¬ IsNilpotent z) :
    ∃ t, e i * t = t ∧ z * t = e i := by
  obtain ⟨f, hf, hf0, q, rfl⟩ := exists_idempotent_of_not_isNilpotent k R z (hint z) hz
  have hcomm : Commute z (Polynomial.aeval z q) := by
    simpa using (Polynomial.commute_X q).map (Polynomial.aeval z)
  have hfe := eq_of_idempotent_in_corner_of_maximal e he hne hmax i _ hf hf0
    (by rw [← mul_assoc, hl]) (by rw [hcomm.eq, mul_assoc, hr])
  exact ⟨e i * Polynomial.aeval z q, by rw [← mul_assoc, (he.idem i).eq],
    by rw [← mul_assoc, hr, hfe]⟩

private theorem exists_right_inverse_in_corner_of_ne_zero (k R : Type) [Field k] [Ring R]
    [Algebra k R] (hint : ∀ x : R, IsIntegral k x)
    (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i : Fin m) (w : R) (hl : e i * w = w) (hr : w * e i = w) (hw0 : w ≠ 0) :
    ∃ t, e i * t = t ∧ w * t = e i := by
  refine exists_right_inverse_in_corner_of_not_isNilpotent k R hint e he hne hmax i w hl hr fun hw => ?_
  have : ¬ ∀ y : R, IsNilpotent (y * w) := fun h => hw0 (hnil w h)
  push Not at this
  obtain ⟨y, hy⟩ := this
  have hu := not_isNilpotent_mul_mul_of_mul_eq (e i) w y hl hy
  obtain ⟨t, _, hut⟩ := exists_right_inverse_in_corner_of_not_isNilpotent k R hint e he hne hmax i
    (w * y * e i) (by rw [← mul_assoc, ← mul_assoc, hl]) (by rw [mul_assoc, (he.idem i).eq]) hu
  set s := y * e i * t
  have hws : w * s = e i := by simpa only [s, mul_assoc] using hut
  obtain ⟨N, hN⟩ := hw
  induction N with
  | zero => exact hne i (by rw [← mul_one (e i), ← pow_zero w, hN, mul_zero])
  | succ n ih =>
    rcases n with _ | n
    · exact hne i (by rw [← hws, ← pow_one w, hN, zero_mul])
    · refine ih ?_
      have h1 : w ^ (n + 1) * e i = w ^ (n + 1) := by rw [pow_succ, mul_assoc, hr]
      rw [← h1, ← hws, ← mul_assoc, ← pow_succ, hN, zero_mul]

private theorem exists_eq_smul_idempotent_of_mem_corner (k R : Type) [Field k] [IsAlgClosed k] [Ring R]
    [Algebra k R] (hint : ∀ x : R, IsIntegral k x)
    (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i : Fin m) (z : R) (hl : e i * z = z) (hr : z * e i = z) : ∃ c : k, z = c • e i := by
  have hei : e i * e i = e i := (he.idem i).eq
  have hdom : ∀ a b : R, e i * a = a → a * e i = a → e i * b = b → b * e i = b →
      a * b = 0 → a = 0 ∨ b = 0 := by
    intro a b _ har hbl hbr hab
    by_cases hb : b = 0
    · exact Or.inr hb
    · obtain ⟨t, _, hbt⟩ := exists_right_inverse_in_corner_of_ne_zero k R hint hnil e he hne hmax
        i b hbl hbr hb
      exact Or.inl (by rw [← har, ← hbt, ← mul_assoc, hab, zero_mul])
  obtain ⟨p, hpm, hpz⟩ := hint z
  have hprod : e i * Polynomial.aeval z (p.roots.map fun c => Polynomial.X - Polynomial.C c).prod = 0 := by
    rw [← (IsAlgClosed.splits p).eq_prod_roots_of_monic hpm, Polynomial.aeval_def, hpz, mul_zero]
  have hcomm : ∀ q : Polynomial k, e i * Polynomial.aeval z q = Polynomial.aeval z q * e i := fun q => by
    induction q using Polynomial.induction_on' with
    | add p₁ p₂ hp₁ hp₂ => simp only [map_add, mul_add, add_mul, hp₁, hp₂]
    | monomial n a =>
      simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
        mul_smul_comm, one_mul]
      congr 1
      exact (SemiconjBy.pow_right (hl.trans hr.symm) n).eq
  suffices ∀ s : Multiset k,
      e i * Polynomial.aeval z (s.map fun c => Polynomial.X - Polynomial.C c).prod = 0 →
      ∃ c : k, z = c • e i from this p.roots hprod
  intro s
  induction s using Multiset.induction_on with
  | empty => intro h; simp only [Multiset.map_zero, Multiset.prod_zero, map_one, mul_one] at h; exact absurd h (hne i)
  | cons c s ih =>
    intro h
    set q := (s.map fun c => Polynomial.X - Polynomial.C c).prod
    have hfactor : e i * Polynomial.aeval z ((Polynomial.X - Polynomial.C c) * q) =
        (z - c • e i) * (e i * Polynomial.aeval z q) := by
      rw [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one,
        ← mul_assoc, mul_sub, hl, mul_smul_comm, mul_one, ← mul_assoc (z - c • e i),
        sub_mul z (c • e i) (e i), hr, smul_mul_assoc, hei]
    simp only [Multiset.map_cons, Multiset.prod_cons] at h
    rw [hfactor] at h
    rcases hdom (z - c • e i) (e i * Polynomial.aeval z q)
        (by rw [mul_sub, hl, mul_smul_comm, hei]) (by rw [sub_mul, hr, smul_mul_assoc, hei])
        (by rw [← mul_assoc, hei]) (by rw [mul_assoc, ← hcomm q, ← mul_assoc, hei]) h with h0 | h0
    · exact ⟨c, sub_eq_zero.mp h0⟩
    · exact ih h0

private theorem exists_smul_eq_corner_of_maximal_orthogonalIdempotents (k R : Type) [Field k]
    [IsAlgClosed k] [Ring R] [Algebra k R] (hint : ∀ x : R, IsIntegral k x)
    (hnil : ∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) {m : ℕ} (e : Fin m → R)
    (he : OrthogonalIdempotents e) (hne : ∀ i, e i ≠ 0)
    (hmax : ∀ e' : Fin (m + 1) → R, OrthogonalIdempotents e' → (∀ i, e' i ≠ 0) → False)
    (i j : Fin m) : ∃ a : R, ∀ r : R, ∃ c : k, e i * r * e j = c • a := by
  by_cases h : ∀ r, e i * r * e j = 0
  · exact ⟨0, fun r => ⟨0, by rw [h r, smul_zero]⟩⟩
  push Not at h
  obtain ⟨r0, ha0⟩ := h
  set a := e i * r0 * e j
  have hii : e i * e i = e i := (he.idem i).eq
  have hjj : e j * e j = e j := (he.idem j).eq
  have hal : e i * a = a := by simp only [a, ← mul_assoc, hii]
  have har : a * e j = a := by simp only [a, mul_assoc, hjj]
  have : ¬ ∀ y : R, IsNilpotent (y * a) := fun h => ha0 (hnil a h)
  push Not at this
  obtain ⟨y, hy⟩ := this
  have hu := not_isNilpotent_mul_mul_of_mul_eq (e i) a y hal hy
  obtain ⟨ν, hν⟩ := exists_eq_smul_idempotent_of_mem_corner k R hint hnil e he hne hmax i
    (a * y * e i) (by rw [← mul_assoc, ← mul_assoc, hal]) (by rw [mul_assoc, hii])
  have hν0 : ν ≠ 0 := by
    rintro rfl; rw [zero_smul] at hν; exact hu (hν ▸ IsNilpotent.zero)
  set b := ν⁻¹ • (e j * y * e i)
  have hab : a * b = e i := by
    simp only [b, mul_smul_comm, ← mul_assoc, har]
    rw [hν, smul_smul, inv_mul_cancel₀ hν0, one_smul]
  have hbe : b * e i = b := by simp only [b, smul_mul_assoc, mul_assoc, hii]
  obtain ⟨μ, hμ⟩ := exists_eq_smul_idempotent_of_mem_corner k R hint hnil e he hne hmax j (b * a)
    (by simp only [b, smul_mul_assoc, mul_smul_comm, ← mul_assoc, hjj]) (by rw [mul_assoc, har])
  have hμ0 : μ ≠ 0 := by
    rintro rfl; rw [zero_smul] at hμ; exact ha0 (by rw [← hal, ← hab, mul_assoc, hμ, mul_zero])
  refine ⟨a, fun r => ?_⟩
  set c := e i * r * e j
  obtain ⟨l, hl⟩ := exists_eq_smul_idempotent_of_mem_corner k R hint hnil e he hne hmax i (c * b)
    (by simp only [c, ← mul_assoc, hii]) (by rw [mul_assoc, hbe])
  refine ⟨μ⁻¹ * l, ?_⟩
  calc c = c * e j := by simp only [c, mul_assoc, hjj]
    _ = μ⁻¹ • (c * (b * a)) := by rw [hμ, mul_smul_comm, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
    _ = (μ⁻¹ * l) • a := by rw [← mul_assoc, hl, smul_mul_assoc, hal, smul_smul]

theorem _root_.GlobalTheory.AlgRing.finite_and_isSemisimpleRing :
    ∀ (k R : Type) [Field k] [IsAlgClosed k] [Ring R] [Algebra k R] (d : ℕ),
      (∀ x : R, IsIntegral k x) → (∀ x : R, (∀ y : R, IsNilpotent (y * x)) → x = 0) →
      (∀ (m : ℕ) (e : Fin m → R), OrthogonalIdempotents e → (∀ i, e i ≠ 0) → m ≤ d) →
      Module.Finite k R ∧ IsSemisimpleRing R := by
  intro k R _ _ _ _ d hint hnil hidem
  have hfin : Module.Finite k R := by
    classical
    let P : ℕ → Prop := fun m => ∃ e : Fin m → R, OrthogonalIdempotents e ∧ ∀ i, e i ≠ 0
    have hP0 : P 0 := ⟨Fin.elim0, ⟨fun i => i.elim0, fun i => i.elim0⟩, fun i => i.elim0⟩
    obtain ⟨e, he, hne⟩ : P (Nat.findGreatest P d) := Nat.findGreatest_spec (Nat.zero_le d) hP0
    have hmax : ∀ e' : Fin (Nat.findGreatest P d + 1) → R, OrthogonalIdempotents e' →
        (∀ i, e' i ≠ 0) → False := fun e' he' hne' =>
      Nat.findGreatest_is_greatest (Nat.lt_succ_self _) (hidem _ e' he' hne') ⟨e', he', hne'⟩
    have hsum := sum_eq_one_of_maximal_orthogonalIdempotents k R hint hnil e he hne hmax
    choose a ha using fun p : Fin (Nat.findGreatest P d) × Fin (Nat.findGreatest P d) =>
      exists_smul_eq_corner_of_maximal_orthogonalIdempotents k R hint hnil e he hne hmax p.1 p.2
    refine ⟨⟨Finset.univ.image a, eq_top_iff.mpr fun r _ => ?_⟩⟩
    rw [show r = (∑ i, e i) * r * (∑ j, e j) by rw [hsum, one_mul, mul_one]]
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    refine Submodule.sum_mem _ fun j _ => Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨c, hc⟩ := ha (i, j) r
    rw [hc]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  refine ⟨hfin, ?_⟩
  have : IsArtinianRing R := IsArtinianRing.of_finite k R
  refine IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr (eq_bot_iff.mpr fun x hx => ?_)
  rw [Submodule.mem_bot]
  refine hnil x fun y => ?_
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson R
  have := Ideal.pow_mem_pow (Ideal.mul_mem_left _ y hx) n
  rw [hn] at this
  exact ⟨n, by simpa using this⟩

end GlobalTheory.AlgRing
