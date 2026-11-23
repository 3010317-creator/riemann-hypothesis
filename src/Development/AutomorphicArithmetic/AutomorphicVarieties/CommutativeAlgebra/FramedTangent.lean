module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan

@[expose] public section

open IsLocalRing Matrix TrivSqZeroExt UpperTheory.V.Alg
noncomputable section
namespace UpperTheory.V.Alg.FramedTangent

private abbrev D (O : Type) [CommRing O] [IsLocalRing O] := DualNumber (ResidueField O)

@[simp] private theorem res_dual {O : Type} [CommRing O] [IsLocalRing O] [IsCO O (D O)] (x : D O) : res O (D O) x = x.fst := by
  have := (co_res O).1; obtain ⟨a, ha⟩ := residue_surjective x.fst
  rw [← res_map (fstHom O (ResidueField O) (ResidueField O))]; change res O (ResidueField O) x.fst = x.fst; rw [← ha]; exact (res O _).commutes a

@[simp] private theorem fst_map {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [IsCO O (D O)]
    (f : R →ₐ[O] D O) (y : R) : (f y).fst = res O R y := by rw [← res_dual, res_map]

private theorem abstract {O R B S X : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [CommRing B] [Algebra O B] [IsCO O B]
    (i : B →ₐ[O] R) (z : S → R) (hz : ∀ s, z s ∈ maximalIdeal R) (wt : S → X) (H : X → Type) [∀ j, AddCommGroup (H j)]
    [∀ j, Module (ResidueField O) (H j)] (l : ∀ j, S → Module.Dual (ResidueField O) (H j)) (ha : ∀ j s x, wt s ≠ j → l j s x = 0)
    (hb : ∀ j x, (∀ s, l j s x = 0) → x = 0) (hc : ∀ j x, ∃ f : R →ₐ[O] D O, (∀ b, (f (i b)).snd = 0) ∧ ∀ s, (f (z s)).snd = l j s x)
    (hd : ∀ f : R →ₐ[O] D O, (∀ b, (f (i b)).snd = 0) → ∀ j, ∃ x, ∀ s, wt s = j → l j s x = (f (z s)).snd)
    (he : ∀ f : R →ₐ[O] D O, (∀ b, (f (i b)).snd = 0) → (∀ s, (f (z s)).snd = 0) → ∀ y, (f y).snd = 0) :
    ∃ (τ : Type) (_ : Fintype τ) (u : τ → S), maximalIdeal R ≤ Ideal.span (Set.range (z ∘ u)) ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 ∧
      (∀ c : τ → O, ∑ t, c t • (z ∘ u) t ∈ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 → ∀ t, c t ∈ maximalIdeal O) ∧
      ∀ j, Nat.card {t // (wt ∘ u) t = j} = Module.finrank (ResidueField O) (H j) := by
  classical
  have := (co_res O).2
  have snd_zero (f : R →ₐ[O] D O) (hf : ∀ b, (f (i b)).snd = 0) (T : Set R) (hT : T ⊆ maximalIdeal R) (h : ∀ s ∈ T, (f s).snd = 0) {y : R}
      (hy : y ∈ Ideal.span T ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2) : (f y).snd = 0 := by
    suffices Ideal.span T ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 ≤ RingHom.ker f from congrArg snd (this hy)
    refine sup_le (sup_le (Ideal.span_le.2 fun s hs => TrivSqZeroExt.ext ((fst_map f s).trans ((res_eq_zero_iff O R s).2 (hT hs))) (h s hs))
      (Ideal.map_le_iff_le_comap.2 fun b hb => TrivSqZeroExt.ext ((fst_map f _).trans ((res_map i b).trans ((res_eq_zero_iff O B b).2 hb))) (hf b))) ?_
    rw [sq, Ideal.mul_le]; intro a ha1 b hb1; rw [← res_eq_zero_iff O] at ha1 hb1; exact TrivSqZeroExt.ext (by simp [ha1]) (by simp [ha1, hb1])
  have span_of (T : Set R) (hT : T ⊆ maximalIdeal R) (H' : ∀ f : R →ₐ[O] D O, (∀ b, (f (i b)).snd = 0) → (∀ s ∈ T, (f s).snd = 0) → ∀ y, (f y).snd = 0) :
      maximalIdeal R ≤ Ideal.span T ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 := co_span O R B i T hT fun f f' h1 h2 => by
    have := H' { toFun := fun y => (res O R y, (f y).snd - (f' y).snd)
                 map_one' := TrivSqZeroExt.ext (map_one _) (by show (f 1).snd - (f' 1).snd = 0; simp)
                 map_mul' := fun y y' => TrivSqZeroExt.ext (map_mul _ y y') (by show (f (y * y')).snd - (f' (y * y')).snd = res O R y * _ + _ * res O R y'; simp; ring)
                 map_zero' := TrivSqZeroExt.ext (map_zero _) (by show (f 0).snd - (f' 0).snd = 0; simp)
                 map_add' := fun y y' => TrivSqZeroExt.ext (map_add _ y y') (by show (f (y + y')).snd - (f' (y + y')).snd = (_ - _) + (_ - _); simp; abel)
                 commutes' := fun a => TrivSqZeroExt.ext ((res O R).commutes a) (by show (f _).snd - (f' _).snd = 0; rw [AlgHom.commutes, AlgHom.commutes, sub_self]) }
      (fun b => sub_eq_zero.2 (congrArg snd (DFunLike.congr_fun h1 b))) (fun s hs => sub_eq_zero.2 (congrArg snd (h2 s hs)))
    ext y; exacts [by simp, sub_eq_zero.1 (this y)]
  obtain ⟨S0, hS0⟩ : ∃ S0 : Finset S, maximalIdeal R ≤ Ideal.span (z '' S0) ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 := by
    obtain ⟨T, hT, hT'⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 (IsNoetherian.noetherian (Ideal.span (Set.range z)))
    rw [← Set.image_univ] at hT; obtain ⟨S0, -, h⟩ := Finset.subset_set_image_iff.1 hT; subst h; refine ⟨S0, ?_⟩; rw [← Finset.coe_image]
    exact (span_of _ (Set.range_subset_iff.2 hz) fun f h h' => he f h fun s => h' _ ⟨s, rfl⟩).trans (by rw [Ideal.span, hT'])
  have db (j : X) : ∃ (κ : Type) (a : κ → {s : S0 // wt s = j}), Function.Injective a ∧ Nat.card κ = Module.finrank (ResidueField O) (H j) ∧
      (∀ x, (∀ t, l j (a t).1 x = 0) → x = 0) ∧ ∀ t, ∃ x, l j (a t).1 x = 1 ∧ ∀ t', t' ≠ t → l j (a t').1 x = 0 := by
    let l' (s : {s : S0 // wt s = j}) := l j s.1
    have hl' (x : H j) (hx : ∀ s, l' s x = 0) : x = 0 := by
      obtain ⟨f, hf, hf'⟩ := hc j x; exact hb j x fun s => (hf' s).symm.trans (snd_zero f hf _ (by rintro _ ⟨s, -, rfl⟩; exact hz s)
        (by rintro _ ⟨s, hs, rfl⟩; rw [hf']; exact if e : wt s = j then hx ⟨⟨s, hs⟩, e⟩ else ha j s x e) (hS0 (hz s)))
    have : FiniteDimensional (ResidueField O) (H j) := .of_injective (LinearMap.pi l') ((injective_iff_map_eq_zero _).2 fun x hx => hl' x (congrFun hx))
    obtain ⟨κ, a, ha', h1, h2⟩ := exists_linearIndependent' (ResidueField O) l'
    have htop : Submodule.span (ResidueField O) (Set.range l') = ⊤ := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span _ (Set.range l')), show (Submodule.span _ (Set.range l')).dualCoannihilator = ⊥
        from eq_bot_iff.2 fun x hx => by rw [Submodule.mem_dualCoannihilator] at hx; exact hl' x fun s => hx _ (Submodule.subset_span ⟨s, rfl⟩), Submodule.dualAnnihilator_bot]
    let b := Module.Basis.mk h2 (h1.trans htop).ge
    refine ⟨κ, a, ha', (Module.finrank_eq_nat_card_basis b).symm.trans Subspace.dual_finrank_eq, fun x hx => (Module.forall_dual_apply_eq_zero_iff (ResidueField O) x).1
      (DFunLike.congr_fun (b.ext fun t => by rw [Module.Basis.mk_apply]; exact hx t : Module.Dual.eval (ResidueField O) (H j) x = 0)), fun t => ?_⟩
    obtain ⟨x, hx⟩ := (Module.evalEquiv (ResidueField O) (H j)).surjective (b.coord t)
    have hcoord (t') : l' (a t') x = b.coord t (b t') := by rw [← hx, Module.Basis.mk_apply]; rfl
    exact ⟨x, by simp [l', hcoord], fun t' ht' => by simp [l', hcoord, ht']⟩
  choose κ a a1 a2 a3 a4 using db
  have : Finite (Σ j, κ j) := .of_injective (fun t : Σ j, κ j => (a t.1 t.2).1) fun ⟨j, t⟩ ⟨j', t'⟩ e => by
    obtain rfl : j = j' := (a j t).2.symm.trans ((congrArg (wt ∘ Subtype.val) e).trans (a j' t').2); exact congrArg (Sigma.mk j) (a1 j (Subtype.ext e))
  refine ⟨Σ j, κ j, Fintype.ofFinite _, fun t => (a t.1 t.2).1, span_of _ (Set.range_subset_iff.2 fun _ => hz _) fun f h h' => he f h fun s => ?_,
    fun c hcm ⟨j, t⟩ => ?_, fun j => (Nat.card_congr (Equiv.ofBijective (fun t : κ j => ⟨⟨j, t⟩, (a j t).2⟩)
      ⟨fun _ _ e => by simpa using e, fun ⟨⟨j', t⟩, e⟩ => by cases (a j' t).2.symm.trans e; exact ⟨t, rfl⟩⟩)).symm.trans (a2 j)⟩
  · obtain ⟨x, hx⟩ := hd f h (wt s); rw [← hx s rfl, a3 _ x fun t => (hx _ (a _ t).2).trans (h' _ ⟨⟨_, t⟩, rfl⟩), map_zero]
  · obtain ⟨x, x1, x2⟩ := a4 j t; obtain ⟨f, hf, hf'⟩ := hc j x
    have h3 := snd_zero f hf ∅ (Set.empty_subset _) (by simp) (by simpa using hcm)
    rw [map_sum, snd_sum, Finset.sum_eq_single ⟨j, t⟩] at h3
    · rw [map_smul, snd_smul, hf', x1, Algebra.smul_def, mul_one] at h3; exact (residue_eq_zero_iff _).1 h3
    · rintro ⟨j', t'⟩ - e; rw [map_smul, snd_smul, hf']
      exact if e' : j' = j then by subst e'; simp [x2 t' (e ∘ congrArg _)] else by simp [ha j _ x ((a j' t').2.trans_ne e')]
    · simp

private theorem mext {ι k : Type} [CommRing k] {M M' : Matrix ι ι (DualNumber k)} (h1 : M.map fst = M'.map fst) (h2 : M.map snd = M'.map snd) : M = M' :=
  Matrix.ext fun a b => TrivSqZeroExt.ext (congrFun (congrFun h1 a) b) (congrFun (congrFun h2 a) b)

private theorem msnd_mul {ι k : Type} [CommRing k] [Fintype ι] (M M' : Matrix ι ι (DualNumber k)) :
    (M * M').map snd = M.map fst * M'.map snd + M.map snd * M'.map fst := by ext a b; simp [Matrix.mul_apply, snd_sum, Finset.sum_add_distrib, mul_comm]

open Classical in
private def mask {ι X k : Type} [AddCommGroup X] [Zero k] (w : ι → X) (j : X) (Y : Matrix ι ι k) : Matrix ι ι k := of fun a b => if w a - w b = j then Y a b else 0

section
variable {O ι Γ : Type} [CommRing O] [IsLocalRing O] [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* Matrix ι ι (ResidueField O)}
@[simp] private theorem lift_fst [IsCO O (D O)] (r : Lift O rbar (D O)) (s : Γ) : (r.hom s).map fst = rbar s := Matrix.ext fun a b => by rw [← r.red, res_dual]; rfl
variable {X : Type} [AddCommGroup X] {w : ι → X}

private theorem framed_iff [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (Φ : FormData O w) [IsCO O (D O)] (r0 : Lift O rbar O) (F : Frame Γ)
    (L : ∀ q, Cond O (rbar.comp (F.ψ q))) {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B)
    (hL : ∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) (h0 : ∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) (i : B →ₐ[O] D O) (hi : ∀ b, (i b).snd = 0)
    (r : Lift O rbar (D O)) (α : F.T → Matrix ι ι (D O)) :
    IsFramed Φ r0.hom F L ρ i r α ↔ (∀ s, (r.hom s).map snd * rbar s⁻¹ ∈ Φ.g (ResidueField O)) ∧ (∀ q, ∀ n ∈ F.N q, (r.hom (F.ψ q n)).map snd = 0) ∧
      (∀ v, (α v).map fst = 1 ∧ (α v).map snd ∈ Φ.g (ResidueField O)) ∧ (α F.v0).map snd = 0 ∧
      ∀ v s, rbar (F.φ v s) * (α v).map snd + (r.hom (F.φ v s)).map snd = (α v).map snd * rbar (F.φ v s) := by
  have := (co_res O).1; have mfst1 : (1 : Matrix ι ι (D O)).map fst = 1 := Matrix.map_one fst rfl rfl
  have mfst (A M : Matrix ι ι (D O)) : (A * M).map fst = A.map fst * M.map fst := Matrix.map_mul (f := (fstHom O _ _).toRingHom)
  have msnd1 : (1 : Matrix ι ι (D O)).map snd = 0 := Matrix.ext fun _ _ => by simp [Matrix.one_apply, apply_ite snd]
  have hh (h : Matrix ι ι (D O)) : Φ.HH h ↔ h.map fst = 1 ∧ h.map snd ∈ Φ.g (ResidueField O) := by
    have e1 : (Φ.JR (D O)).map fst = Φ.JR (ResidueField O) := rfl; have e2 : (Φ.JR (D O)).map snd = 0 := rfl
    have e3 (e : h.map fst = 1) : (hᵀ * Φ.JR _ * h).map snd = (h.map snd)ᵀ * Φ.JR _ + Φ.JR _ * h.map snd := by simp [msnd_mul, mfst, transpose_map, e, e1, e2, add_comm]
    rw [FormData.HH, show h.map (res O _) = h.map fst from Matrix.ext fun _ _ => res_dual _]
    exact ⟨fun ⟨a1, a2, a3⟩ => ⟨a3, by rw [← e3 a3, a1, e2], fun a b e => by simp [a2 a b e]⟩,
      fun ⟨a1, a2, a3⟩ => ⟨mext (by simp [mfst, transpose_map, a1, e1]) (by rw [e3 a1, a2, e2]),
        fun a b e => TrivSqZeroExt.ext ((congrFun (congrFun a1 a) b).trans (Matrix.one_apply_ne (e ∘ congrArg _))) (a3 a b e), a1⟩⟩
  have inH {H : Type} [Group H] [TopologicalSpace H] {rb : H →* Matrix ι ι (ResidueField O)} (r0' : Lift O rb O) (r' : Lift O rb (D O)) :
      Φ.InH r0'.hom _ r' ↔ ∀ s, (r'.hom s).map snd * rb s⁻¹ ∈ Φ.g (ResidueField O) := forall_congr' fun s => by
    have e1 : ((r0'.hom s⁻¹).map (algebraMap O (D O))).map fst = rb s⁻¹ := lift_fst (r0'.map (Algebra.ofId O _)) s⁻¹
    simp [hh, mfst, msnd_mul, e1, show ((r0'.hom s⁻¹).map (algebraMap O (D O))).map snd = 0 from rfl, ← map_mul]
  have e1 (v) (s) : (((ρ v).hom s).map i).map fst = rbar (F.φ v s) := lift_fst ((ρ v).map i) s
  have e2 (v) (s) : (((ρ v).hom s).map i).map snd = 0 := Matrix.ext fun _ _ => hi _
  rw [IsFramed, inH r0 r]; refine and_congr_right fun h1 => and_congr (forall_congr' fun q => ?_) ?_
  · let r0q := r0.comap (F.ψ q) (F.hψ q); let r1 := r0q.map (Algebra.ofId O (D O)); have er1 (s) : (r1.hom s).map snd = 0 := rfl
    have h1q : L q _ r1 := by
      obtain ⟨I, hI⟩ := (hL q).closed O r0q fun s => by
        change Φ.HH (r0q.hom s * r0q.hom s⁻¹); rw [← map_mul, mul_inv_cancel, map_one]; exact ⟨by simp, fun _ _ hab => Matrix.one_apply_ne (hab ∘ congrArg _), by simp⟩
      exact (hI _ _).2 fun x hx => by have hx0 : x = 0 := (hI O (.id O O)).1 (h0 q) x hx; simp [hx0]
    rw [(hL q).tangent _ _ (fstHom O (ResidueField O) (ResidueField O)) (fun x => ⟨inl x, rfl⟩) ?_ r1 (r.comap (F.ψ q) (F.hψ q))
      ((inH r0q r1).2 fun s => by simp [er1, zero_mem]) ((inH r0q _).2 fun s => by change (r.hom (F.ψ q s)).map snd * _ ∈ _; simpa [← map_inv] using h1 (F.ψ q s))
      (Lift.ext (MonoidHom.ext fun s => (lift_fst r1 s).trans (lift_fst (r.comap (F.ψ q) (F.hψ q)) s).symm)) h1q]
    · exact forall₂_congr fun n _ => ⟨fun h => (congrArg (map · snd) h).trans (er1 n),
        fun h => mext ((lift_fst (r.comap (F.ψ q) (F.hψ q)) n).trans (lift_fst r1 n).symm) (h.trans (er1 n).symm)⟩
    · rw [eq_bot_iff, Ideal.mul_le]; intro x hx y hy; rw [← res_eq_zero_iff O, res_dual] at hx
      exact Ideal.mem_bot.2 (TrivSqZeroExt.ext (by simp [hx]) (by simp [hx, show y.fst = 0 from hy]))
  · simp only [hh]; refine and_congr_right fun h2 => and_congr ⟨fun h => by rw [h, msnd1], fun h => mext ((h2 _).1.trans mfst1.symm) (h.trans msnd1.symm)⟩
      (forall₂_congr fun v s => ⟨fun h => ?_, fun h => mext (by rw [mfst, mfst, lift_fst, e1, (h2 v).1, mul_one, one_mul]) ?_⟩)
    · simpa only [msnd_mul, lift_fst, (h2 v).1, e1, e2, mul_one, mul_zero, zero_add] using congrArg (map · snd) h
    · simpa only [msnd_mul, lift_fst, (h2 v).1, e1, e2, mul_one, mul_zero, zero_add] using h

private def ell {Φ : FormData O w} (F : Frame Γ) (hbar : Φ.Normalises rbar) (j : X) :
    (Γ × ι × ι) ⊕ (F.T × ι × ι) → Module.Dual (ResidueField O) (F.H1c (FormData.adRep hbar j))
  | .inl (s, a, b) => ⟨⟨fun x => ((x.1.1 s).1 * rbar s) a b, fun _ _ => by simp [add_mul]⟩, fun _ _ => by simp⟩
  | .inr (v, a, b) => ⟨⟨fun x => -(x.1.2 v).1 a b, fun _ _ => by simp [add_comm]⟩, fun _ _ => by simp⟩
end
end UpperTheory.V.Alg.FramedTangent

open UpperTheory.V.Alg.FramedTangent in
theorem UpperTheory.V.Alg.framed_tangent :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
      ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B), (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (i : B →ₐ[O] R) (r : Lift O rbar R) (α : F.T → Matrix ι ι R), IsUnivFramed Φ r0.hom F L ρ i r α →
      ∃ (τ : Type) (_ : Fintype τ) (z : τ → R) (wt : τ → X),
        (∀ t, ∃ a b, wt t = w a - w b ∧ ((∃ s, z t = r.hom s a b - algebraMap O R (r0.hom s a b)) ∨ ∃ v, z t = (α v - 1) a b)) ∧
        maximalIdeal R ≤ Ideal.span (Set.range z) ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 ∧
        (∀ c : τ → O, ∑ t, c t • z t ∈ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 → ∀ t, c t ∈ maximalIdeal O) ∧
        ∀ j, Nat.card {t // wt t = j} = Module.finrank (ResidueField O) (F.H1c (FormData.adRep hbar j)) := by
  intro O _ _ _ _ ι X _ _ _ w Φ _ Γ _ _ _ rbar r0 hbar _ F L _ hL h0 B _ _ _ ρ _ R _ _ _ i r α ⟨hF, hU⟩
  classical
  have := (co_res O).1; have := (co_res O).2
  have lift_lc (r' : Lift O rbar (D O)) : IsLocallyConstant r'.hom := (IsLocallyConstant.iff_eventually_eq _).2 fun x =>
    (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (IsLocallyConstant.iff_eventually_eq _).1 (IsLocallyConstant.desc _ _ (r'.cont a b 2)
      (by rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, sq, eq_bot_iff, Ideal.mul_le]; intro u hu v hv; rw [← res_eq_zero_iff O, res_dual] at hu hv
          exact Ideal.mem_bot.2 (TrivSqZeroExt.ext (by simp [hu]) (by simp [hu, hv])))) x).mono fun _ => Matrix.ext
  have hrbar : IsLocallyConstant rbar := funext (lift_fst (r0.map (Algebra.ofId O _))) ▸ (lift_lc (r0.map (Algebra.ofId O _))).comp (map · fst)
  have mask_mul (j : X) (Y A : Matrix ι ι (ResidueField O)) (hA : ∀ a b, w a ≠ w b → A a b = 0) : mask w j (Y * A) = mask w j Y * A := Matrix.ext fun a b => by
    by_cases e : w a - w b = j <;> simp only [mask, Matrix.mul_apply, of_apply, e, ↓reduceIte]
    exacts [Finset.sum_congr rfl fun c _ => if n : w c = w b then by simp [n, e] else by simp [hA c b n], (Finset.sum_eq_zero fun c _ => if n : w c = w b then by simp [n, e] else by simp [hA c b n]).symm]
  have mul_mask (j : X) (Y A : Matrix ι ι (ResidueField O)) (hA : ∀ a b, w a ≠ w b → A a b = 0) : mask w j (A * Y) = A * mask w j Y := Matrix.ext fun a b => by
    by_cases e : w a - w b = j <;> simp only [mask, Matrix.mul_apply, of_apply, e, ↓reduceIte]
    exacts [Finset.sum_congr rfl fun c _ => if n : w a = w c then by simp [← n, e] else by simp [hA a c n], (Finset.sum_eq_zero fun c _ => if n : w a = w c then by simp [← n, e] else by simp [hA a c n]).symm]
  have mask_mem (j : X) {Y : Matrix ι ι (ResidueField O)} (hY : Y ∈ Φ.g (ResidueField O)) : mask w j Y ∈ Φ.gw (ResidueField O) j := by
    refine ⟨⟨Matrix.ext fun a b => ?_, fun a b e => by simp [mask, hY.2 a b e]⟩, fun a b e => by simp [mask, e]⟩
    have hJ (u v : ι) (e : w u + w v ≠ Φ.c) : Φ.JR (ResidueField O) u v = 0 := by simp [FormData.JR, show Φ.J u v = 0 from by_contra fun n => e (Φ.hw u v n)]
    have h := congrFun (congrFun hY.1 a) b; simp only [Matrix.add_apply, Matrix.mul_apply, transpose_apply, Matrix.zero_apply, mask, of_apply] at h ⊢
    by_cases e : Φ.c - w a - w b = j
    · rw [← h]; congr 1 <;> refine Finset.sum_congr rfl fun c _ => ?_
      exacts [if n : w c + w b = Φ.c then by simp [show w c - w a = j by rw [← e, ← n]; abel] else by simp [hJ c b n],
        if n : w a + w c = Φ.c then by simp [show w c - w b = j by rw [← e, ← n]; abel] else by simp [hJ a c n]]
    · rw [Finset.sum_eq_zero fun c _ => if n : w c + w b = Φ.c then by simp [show w c - w a ≠ j from fun m => e (by rw [← m, ← n]; abel)] else by simp [hJ c b n],
        Finset.sum_eq_zero fun c _ => if n : w a + w c = Φ.c then by simp [show w c - w b ≠ j from fun m => e (by rw [← m, ← n]; abel)] else by simp [hJ a c n], add_zero]
  let z : (Γ × ι × ι) ⊕ (F.T × ι × ι) → R := Sum.elim (fun p => r.hom p.1 p.2.1 p.2.2 - algebraMap O R (r0.hom p.1 p.2.1 p.2.2)) fun p => (α p.1 - 1) p.2.1 p.2.2
  let wt : (Γ × ι × ι) ⊕ (F.T × ι × ι) → X := Sum.elim (fun p => w p.2.1 - w p.2.2) fun p => w p.2.1 - w p.2.2
  have z1 (f : R →ₐ[O] D O) (s a b) : (f (z (.inl (s, a, b)))).snd = ((r.map f).hom s).map snd a b := by show (f (_ - _)).snd = _; rw [map_sub, snd_sub, AlgHom.commutes]; exact sub_zero _
  have z2 (f : R →ₐ[O] D O) (v a b) : (f (z (.inr (v, a, b)))).snd = ((α v).map f).map snd a b := by show (f (α v a b - (1 : Matrix ι ι R) a b)).snd = _; by_cases e : a = b <;> simp [Matrix.one_apply, e]
  have hmap (f : R →ₐ[O] D O) : IsFramed Φ r0.hom F L ρ (f.comp i) (r.map f) fun v => (α v).map f := by
    obtain ⟨a1, a2, a3, a4, a5⟩ := hF; have hm (A A' : Matrix ι ι R) : (A * A').map f = A.map f * A'.map f := Matrix.map_mul (f := (f : R →+* D O))
    have map_HH (A : Matrix ι ι R) (hA : Φ.HH A) : Φ.HH (A.map f) :=
      ⟨by rw [show Φ.JR _ = (Φ.JR R).map f from Matrix.ext fun a b => (f.commutes (Φ.J a b)).symm, ← transpose_map, ← hm, ← hm, hA.1],
        fun a b hab => by simp [hA.2.1 a b hab], by rw [← hA.2.2]; exact Matrix.ext fun _ _ => res_map f _⟩
    refine ⟨fun s => ?_, fun q => ?_, fun v => map_HH _ (a3 v), by simp [a4], fun v s => Matrix.ext fun a b =>
      congrFun (congrFun (by simpa only [hm] using congrArg (map · f) (a5 v s) : (r.hom (F.φ v s)).map f * (α v).map f = (α v).map f * (((ρ v).hom s).map i).map f) a) b⟩
    · change Φ.HH ((r.hom s).map f * _); simpa [hm, show ((r0.hom s⁻¹).map (algebraMap O R)).map f = (r0.hom s⁻¹).map (algebraMap O _) from Matrix.ext fun _ _ => f.commutes _] using map_HH _ (a1 s)
    · obtain ⟨I, hI⟩ := (hL q).closed R (r.comap (F.ψ q) (F.hψ q)) fun s => by change Φ.HH (r.hom (F.ψ q s) * _); simpa [← map_inv] using a1 (F.ψ q s)
      exact (hI _ f).2 fun x hx => by have hx0 : x = 0 := (hI R (.id O R)).1 (a2 q) x hx; simp [hx0]
  have inv1 (s) : rbar s⁻¹ * rbar s = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have inv2 (s) : rbar s * rbar s⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  refine Exists.elim (abstract i z ?_ wt (fun j => F.H1c (FormData.adRep hbar j)) (ell F hbar) ?_ ?_ ?_ ?_ ?_) ?_; rotate_right
  · rintro τ ⟨hτ, u, u1, u2, u3⟩; refine ⟨τ, hτ, z ∘ u, wt ∘ u, fun t => ?_, u1, u2, u3⟩
    rcases uxh : u t with ⟨s, a, b⟩ | ⟨v, a, b⟩; exacts [⟨a, b, by simp [wt, uxh], .inl ⟨s, by simp [z, uxh]⟩⟩, ⟨a, b, by simp [wt, uxh], .inr ⟨v, by simp [z, uxh]⟩⟩]
  · rintro (⟨s, a, b⟩ | ⟨v, a, b⟩) <;> rw [← res_eq_zero_iff O]
    · show res O R (_ - _) = 0; rw [map_sub, r.red, ← r0.red, AlgHom.commutes, sub_eq_zero]; exact (res O O).commutes _
    · show res O R (α v a b - (1 : Matrix ι ι R) a b) = 0; rw [map_sub, show res O R (α v a b) = (1 : Matrix ι ι _) a b from congrFun (congrFun (hF.2.2.1 v).2.2 a) b]; by_cases e : a = b <;> simp [Matrix.one_apply, e]
  · rintro j (⟨s, a, b⟩ | ⟨v, a, b⟩) x e
    · change w a - w b ≠ j at e; have hfix : mask w j (x.1.1 s).1 = (x.1.1 s).1 := Matrix.ext fun a' b' => by by_cases h : w a' - w b' = j <;> simp [mask, h, (x.1.1 s).2.2 a' b']
      change ((x.1.1 s).1 * rbar s) a b = 0; rw [← hfix, ← mask_mul j _ _ (hbar.2.2 s)]; simp [mask, e]
    · exact neg_eq_zero.2 ((x.1.2 v).2.2 a b e)
  · intro j x hx; refine Subtype.ext (Prod.ext (funext fun s => Subtype.ext ?_) (funext fun v => Subtype.ext (Matrix.ext fun a b => neg_eq_zero.1 (hx (.inr (v, a, b))))))
    have h0s : (x.1.1 s).1 * rbar s = 0 := Matrix.ext fun a b => hx (.inl (s, a, b)); show (x.1.1 s).1 = 0; rw [← mul_one (x.1.1 s).1, ← inv2 s, ← mul_assoc, h0s, zero_mul]
  · intro j x; let i0 : B →ₐ[O] D O := (inlAlgHom O (ResidueField O) (ResidueField O)).comp (res O B)
    let r1 : Lift O rbar (D O) :=
      ⟨⟨⟨fun s => of fun a b => (rbar s a b, ((x.1.1 s).1 * rbar s) a b), mext ((map_one rbar).trans (Matrix.map_one fst (by simp) (by simp)).symm) (by
          change (x.1.1 1).1 * rbar 1 = (1 : Matrix ι ι _).map snd; rw [show x.1.1 1 = 0 by simpa using x.2.2.1 1 1]; ext; simp [Matrix.one_apply, apply_ite snd])⟩,
        fun s t => mext (by have mfst (A M : Matrix ι ι (D O)) : (A * M).map fst = A.map fst * M.map fst := Matrix.map_mul (f := (fstHom O _ _).toRingHom); rw [mfst]; exact map_mul rbar s t) (by
          have h : (x.1.1 (s * t)).1 = (x.1.1 s).1 + rbar s * (x.1.1 t).1 * rbar s⁻¹ := congrArg Subtype.val (x.2.2.1 s t); rw [msnd_mul]
          change (x.1.1 (s * t)).1 * rbar (s * t) = rbar s * ((x.1.1 t).1 * rbar t) + (x.1.1 s).1 * rbar s * rbar t
          rw [h, add_mul, mul_assoc _ (rbar s⁻¹), ← map_mul, inv_mul_cancel_left, map_mul, add_comm]; simp only [mul_assoc])⟩,
        fun a b N => (x.2.1.prodMk hrbar).comp fun p => Ideal.Quotient.mk (maximalIdeal (D O) ^ N) (p.2 a b, (p.1.1 * p.2) a b), fun _ _ _ => res_dual _⟩
    obtain ⟨f, ⟨f1, f2, f3⟩, -⟩ := hU _ i0 r1 (fun v => of fun a b => ((1 : Matrix ι ι _) a b, (-(x.1.2 v).1) a b)) ((framed_iff Φ r0 F L ρ hL h0 i0 (fun _ => rfl) r1 _).2
      ⟨fun s => by change (x.1.1 s).1 * rbar s * rbar s⁻¹ ∈ _; rw [mul_assoc, inv2, mul_one]; exact (x.1.1 s).2.1,
        fun q n hn => by change (x.1.1 (F.ψ q n)).1 * _ = 0; simp [x.2.2.2.1 q n hn], fun v => ⟨rfl, neg_mem (x.1.2 v).2.1⟩, by change -(x.1.2 F.v0).1 = 0; simp [x.2.2.2.2.2],
        fun v s => by
          have h : (x.1.1 (F.φ v s)).1 = rbar (F.φ v s) * (x.1.2 v).1 * rbar (F.φ v s)⁻¹ - (x.1.2 v).1 := congrArg Subtype.val (x.2.2.2.2.1 v s)
          change rbar (F.φ v s) * -(x.1.2 v).1 + (x.1.1 (F.φ v s)).1 * rbar (F.φ v s) = -(x.1.2 v).1 * rbar (F.φ v s); rw [h, sub_mul, mul_assoc, inv1, mul_one, mul_neg, neg_mul]; abel⟩)
    refine ⟨f, fun b => by rw [show f (i b) = i0 b from DFunLike.congr_fun f1 b]; rfl, ?_⟩
    rintro (⟨s, a, b⟩ | ⟨v, a, b⟩); exacts [by rw [z1, f2]; rfl, by rw [z2, f3]; rfl]
  · intro f hf j; obtain ⟨b1, b2, b3, b4, b5⟩ := (framed_iff Φ r0 F L ρ hL h0 (f.comp i) hf _ _).1 (hmap f)
    have madd (Y Z : Matrix ι ι (ResidueField O)) : mask w j (Y + Z) = mask w j Y + mask w j Z := Matrix.ext fun a b => by by_cases e : w a - w b = j <;> simp [mask, e]
    have msub (Y Z : Matrix ι ι (ResidueField O)) : mask w j (Y - Z) = mask w j Y - mask w j Z := Matrix.ext fun a b => by by_cases e : w a - w b = j <;> simp [mask, e]
    refine ⟨⟨(fun s => ⟨_, mask_mem j (b1 s)⟩, fun v => ⟨_, mask_mem j (neg_mem (b3 v).2)⟩),
      IsLocallyConstant.desc _ Subtype.val (((lift_lc (r.map f)).prodMk (hrbar.comp_continuous continuous_inv)).comp fun p => mask w j (p.1.map snd * p.2)) Subtype.val_injective,
      fun s t => Subtype.ext ?_, fun q n hn => Subtype.ext (Matrix.ext fun _ _ => by simp [b2 q n hn, mask]),
      fun v s => Subtype.ext ?_, Subtype.ext (Matrix.ext fun _ _ => by simp [b4, mask])⟩, ?_⟩
    · show mask w j _ = mask w j _ + rbar s * mask w j _ * rbar s⁻¹
      rw [← mul_mask j _ _ (hbar.2.2 s), ← mask_mul j _ _ (hbar.2.2 s⁻¹), ← madd, MonoidHom.map_mul, msnd_mul, lift_fst, lift_fst, mul_inv_rev,
        MonoidHom.map_mul, add_mul, mul_assoc _ (rbar t), ← mul_assoc (rbar t), inv2, one_mul, add_comm]; simp only [mul_assoc]
    · show mask w j _ = rbar (F.φ v s) * mask w j _ * rbar (F.φ v s)⁻¹ - mask w j _
      rw [← mul_mask j _ _ (hbar.2.2 _), ← mask_mul j _ _ (hbar.2.2 _), ← msub, eq_sub_of_add_eq' (b5 v s), sub_mul, mul_assoc, inv2]; congr 1; simp only [mul_neg, neg_mul, mul_one]; abel
    · rintro (⟨s, a, b⟩ | ⟨v, a, b⟩) e
      · change w a - w b = j at e; show (mask w j (((r.map f).hom s).map snd * rbar s⁻¹) * rbar s) a b = _; rw [z1, ← mask_mul j _ _ (hbar.2.2 s), mul_assoc, inv1, mul_one]; simp [mask, e]
      · change w a - w b = j at e; show -(mask w j _ a b) = _; rw [z2, neg_eq_iff_eq_neg]; simp [mask, e]
  · intro f hf hz y; let f0 : R →ₐ[O] D O := (inlAlgHom O (ResidueField O) (ResidueField O)).comp (res O R)
    have key (y) (hy : (f y).snd = 0) : f0 y = f y := TrivSqZeroExt.ext (by simp [f0]) hy.symm
    have := (hU _ _ _ _ (hmap f)).unique (y₁ := f0) (y₂ := f) ⟨AlgHom.ext fun b => key _ (hf b),
      Lift.ext (MonoidHom.ext fun s => Matrix.ext fun a b => key _ ((z1 f s a b).symm.trans (hz _))),
      fun v => Matrix.ext fun a b => key _ ((z2 f v a b).symm.trans (hz _))⟩ ⟨rfl, rfl, fun _ => rfl⟩
    rw [← this]; rfl
