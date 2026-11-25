module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.CutColumns
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Discriminant
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.Foundation
public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ValuationLambdaFieldProperties
public import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
public import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeRename
public import Formalism.ThetaLogCoordinates.ResidueClassEstimates.FinalT
public import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Order.Interval.Finset.Box
import Std.Tactic.BVDecide.Normalize.BitVec

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf
section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section LamAbs

variable {R : Type} [CommRing R] {F : Type} [Field F] {σ τ : Type} {J : ℕ}

theorem lam_prod_monomial {ι : Type} (s : Finset ι) (f : ι → τ →₀ ℕ) (a : ι → R) :
    ∏ i ∈ s, monomial (f i) (a i) = monomial (∑ i ∈ s, f i) (∏ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.prod_insert hi, ih, monomial_mul_monomial]

abbrev lam_ph (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (j : Fin J) : MvPolynomial σ R →ₐ[R] MvPolynomial τ R :=
  aeval fun v => (X (g j v) : MvPolynomial τ R) ^ e j v

theorem lam_expand (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (y : Fin J → MvPolynomial σ R) :
    ∏ j, lam_ph g e j (y j) = ∑ m ∈ Fintype.piFinset (fun j => (y j).support),
      monomial (∑ j, imgMon (g j) (e j) (m j)) (∏ j, AddMonoidAlgebra.coeff (y j) (m j)) := by
  classical
  have h : ∀ j, lam_ph g e j (y j) = ∑ m ∈ (y j).support, monomial (imgMon (g j) (e j) m) (AddMonoidAlgebra.coeff (y j) m) := by
    intro j
    conv_lhs => rw [(y j).as_sum]

    rw [map_sum]
    exact Finset.sum_congr rfl fun m _ => aeval_pow_monomial _ _ _ _
  rw [Finset.prod_congr rfl fun j _ => h j, Finset.prod_univ_sum]
  exact Finset.sum_congr rfl fun m _ => lam_prod_monomial _ _ _

theorem lam_coeff (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (l : τ →₀ ℕ) (S : Fin J → Set (σ →₀ ℕ))
    (hinj : ∀ m m' : Fin J → σ →₀ ℕ, (∀ j, m j ∈ S j) → (∀ j, m' j ∈ S j) →
      ∑ j, imgMon (g j) (e j) (m j) = ∑ j, imgMon (g j) (e j) (m' j) → m = m')
    (y : Fin J → MvPolynomial σ F) (hy : ∀ j, y j ∈ restrictSupport F (S j)) (s : Fin J → σ →₀ ℕ)
    (hs : ∀ j, s j ∈ S j) :
    AddMonoidAlgebra.coeff (monomial l (1 : F) * ∏ j, lam_ph g e j (y j)) (l + ∑ j, imgMon (g j) (e j) (s j)) =
      ∏ j, AddMonoidAlgebra.coeff (y j) (s j) := by
  classical
  rw [coeff_monomial_mul, one_mul, lam_expand, coeff_sum, Finset.sum_eq_single s]
  · rw [coeff_monomial, ite_eq_left rfl]
  · intro m hm hne
    rw [coeff_monomial, ite_eq_right]
    intro h
    apply hne
    refine hinj m s (fun j => ?_) hs h
    have := Fintype.mem_piFinset.mp hm j
    exact ((MvPolynomial.mem_restrictSupport_iff (R := F)).mp (hy j)) (Finset.mem_coe.mpr this)
  · intro hnot
    rw [coeff_monomial, ite_eq_left rfl]
    rw [Fintype.mem_piFinset] at hnot
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    exact Finset.prod_eq_zero (Finset.mem_univ j) (MvPolynomial.notMem_support_iff.mp hj)

theorem lam_dual {I : Type} {M : Type} [AddCommGroup M] [Module F M] (u : I → M)
    (hu : LinearIndependent F u) :
    ∃ ψ : M →ₗ[F] (I →₀ F), (∀ a, ψ (u a) a = 1) ∧ ∀ a b, b ≠ a → ψ (u a) b = 0 := by
  classical
  obtain ⟨ψ, hψ⟩ := LinearMap.exists_leftInverse_of_injective (Finsupp.linearCombination F u)
    (LinearMap.ker_eq_bot.mpr hu)
  have h1 : ∀ a, ψ (u a) = Finsupp.single a 1 := by
    intro a
    have h2 : Finsupp.linearCombination F u (Finsupp.single a 1) = u a := by simp
    rw [← h2]
    exact congrArg (fun f => f (Finsupp.single a 1)) hψ
  refine ⟨ψ, fun a => by rw [h1]; simp, fun a b hb => by rw [h1, Finsupp.single_apply, ite_eq_right hb.symm]⟩

theorem lam_li_fixed (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (l : τ →₀ ℕ) (S : Fin J → Set (σ →₀ ℕ))
    (hinj : ∀ m m' : Fin J → σ →₀ ℕ, (∀ j, m j ∈ S j) → (∀ j, m' j ∈ S j) →
      ∑ j, imgMon (g j) (e j) (m j) = ∑ j, imgMon (g j) (e j) (m' j) → m = m')
    {I : Fin J → Type} [∀ j, Fintype (I j)] (u : ∀ j, I j → MvPolynomial σ F)
    (hu : ∀ j, LinearIndependent F (u j)) (hS : ∀ j i, u j i ∈ restrictSupport F (S j)) :
    LinearIndependent F fun a : ∀ j, I j => monomial l (1 : F) * ∏ j, lam_ph g e j (u j (a j)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc b
  have hstar : ∀ s : Fin J → σ →₀ ℕ, ∑ a, c a * ∏ j, AddMonoidAlgebra.coeff (u j (a j)) (s j) = 0 := by
    intro s
    by_cases hs : ∀ j, s j ∈ S j
    · have h1 := congrArg (AddMonoidAlgebra.coeff · (l + ∑ j, imgMon (g j) (e j) (s j))) hc
      rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at h1
      rw [← h1]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [MvPolynomial.coeff_smul, lam_coeff g e l S hinj (fun j => u j (a j)) (fun j => hS j (a j)) s hs, smul_eq_mul]
    · push Not at hs
      obtain ⟨j0, hj0⟩ := hs
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [Finset.prod_eq_zero (Finset.mem_univ j0) (li_coeff_zero (hS j0 (a j0)) hj0), mul_zero]
  choose ψ hψ using fun j => lam_dual (u j) (hu j)
  let supp : ∀ j, Finset (σ →₀ ℕ) := fun j => Finset.univ.biUnion fun a => (u j a).support
  let w : ∀ j, (σ →₀ ℕ) → F := fun j m => ψ j (monomial m 1) (b j)
  have hexp : ∀ j (a : I j), (ψ j (u j a)) (b j) = ∑ m ∈ supp j, AddMonoidAlgebra.coeff (u j a) m * w j m := by
    intro j a
    conv_lhs => rw [(u j a).as_sum]

    rw [map_sum, Finsupp.finsetSum_apply]
    have hsub : (u j a).support ⊆ supp j := fun m hm => Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _, hm⟩
    rw [← Finset.sum_subset hsub]
    · refine Finset.sum_congr rfl fun m _ => ?_
      have : (monomial m (AddMonoidAlgebra.coeff (u j a) m) : MvPolynomial σ F) = AddMonoidAlgebra.coeff (u j a) m • monomial m (1 : F) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]
    · intro m _ hm
      rw [MvPolynomial.notMem_support_iff.mp hm, zero_mul]
  have h1 : ∑ a, c a * ∏ j, (ψ j (u j (a j))) (b j) = c b := by
    rw [Finset.sum_eq_single b]
    · rw [Finset.prod_eq_one fun j _ => (hψ j).1 (b j), mul_one]
    · intro a _ hab
      obtain ⟨j, hj⟩ := Function.ne_iff.mp hab
      rw [Finset.prod_eq_zero (Finset.mem_univ j) ((hψ j).2 (a j) (b j) hj.symm), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  have h2 : ∑ a, c a * ∏ j, (ψ j (u j (a j))) (b j) = 0 := by
    have e1 : ∀ a : ∀ j, I j, c a * ∏ j, (ψ j (u j (a j))) (b j) =
        ∑ s ∈ Fintype.piFinset supp, (c a * ∏ j, AddMonoidAlgebra.coeff (u j (a j)) (s j)) * ∏ j, w j (s j) := by
      intro a
      rw [Finset.prod_congr rfl fun j _ => hexp j (a j), Finset.prod_univ_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.prod_mul_distrib, mul_assoc]
    rw [Finset.sum_congr rfl fun a _ => e1 a, Finset.sum_comm]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← Finset.sum_mul, hstar s, zero_mul]
  rw [← h1, h2]

theorem lam_li_all {Φ : Type} (g : Fin J → σ → τ) (e : Fin J → σ → ℕ) (l : Φ → τ →₀ ℕ)
    (S : Φ → Fin J → Set (σ →₀ ℕ)) (I : Φ → Fin J → Type) [∀ f j, Fintype (I f j)]
    (u : ∀ f j, I f j → MvPolynomial σ F) (hu : ∀ f j, LinearIndependent F (u f j))
    (hS : ∀ f j i, u f j i ∈ restrictSupport F (S f j))
    (hinj : ∀ f f' (m m' : Fin J → σ →₀ ℕ), (∀ j, m j ∈ S f j) → (∀ j, m' j ∈ S f' j) →
      l f + ∑ j, imgMon (g j) (e j) (m j) = l f' + ∑ j, imgMon (g j) (e j) (m' j) → f = f' ∧ m = m') :
    LinearIndependent F fun x : (Σ f, ∀ j, I f j) =>
      monomial (l x.1) (1 : F) * ∏ j, lam_ph g e j (u x.1 j (x.2 j)) := by
  classical
  refine li_graded _ (fun x => x.1)
    (fun f => {n | ∃ m : Fin J → σ →₀ ℕ, (∀ j, m j ∈ S f j) ∧ n = l f + ∑ j, imgMon (g j) (e j) (m j)}) ?_ ?_ ?_
  · rintro k k' n ⟨m, hm, rfl⟩ ⟨m', hm', h⟩
    exact (hinj k k' m m' hm hm' h).1
  · intro x
    rw [MvPolynomial.mem_restrictSupport_iff]
    intro n hn
    have hn' : AddMonoidAlgebra.coeff (monomial (l x.1) (1 : F) * ∏ j, lam_ph g e j (u x.1 j (x.2 j))) n ≠ 0 :=
      MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hn)
    rw [coeff_monomial_mul'] at hn'
    split_ifs at hn' with hle
    · rw [one_mul, lam_expand, coeff_sum] at hn'
      obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
      rw [coeff_monomial] at hm0
      split_ifs at hm0 with heq
      · refine ⟨m, fun j => ?_, ?_⟩
        · exact ((MvPolynomial.mem_restrictSupport_iff (R := F)).mp (hS x.1 j (x.2 j)))
            (Finset.mem_coe.mpr (Fintype.mem_piFinset.mp hm j))
        · rw [heq]; exact (add_tsub_cancel_of_le hle).symm
      · exact absurd rfl hm0
    · exact absurd rfl hn'
  · intro k
    have hfix := lam_li_fixed g e (l k) (S k)
      (fun m m' hm hm' h => (hinj k k m m' hm hm' (by rw [h])).2) (u k) (hu k) (hS k)
    have hι : Function.Injective
        (fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} => (x.2 ▸ x.1.2 : ∀ j, I k j)) := by
      rintro ⟨⟨f, a⟩, h⟩ ⟨⟨f', a'⟩, h'⟩ hxx
      simp only at h h'
      subst h
      subst h'
      simp only at hxx
      rw [hxx]
    have hcomp := hfix.comp _ hι
    have heq : (fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} =>
        monomial (l x.1.1) (1 : F) * ∏ j, lam_ph g e j (u x.1.1 j (x.1.2 j))) =
        ((fun a : ∀ j, I k j => monomial (l k) (1 : F) * ∏ j, lam_ph g e j (u k j (a j))) ∘
          fun x : {x : (Σ f, ∀ j, I f j) // x.1 = k} => (x.2 ▸ x.1.2 : ∀ j, I k j)) := by
      funext x
      obtain ⟨⟨f, a⟩, h⟩ := x
      simp only at h
      subst h
      rfl
    rw [heq]
    exact hcomp

end LamAbs

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def lamG : Fin X.F.J → ℤ × Fin (r + K) → Fin n' × Fin (r + K) := fun _ v => (posOf n' v.1, v.2)

def lamE : Fin X.F.J → ℤ × Fin (r + K) → ℕ := fun j v => p ^ (X.F.dist (j.val : ℤ) v.1 + X.Rj p K (j.val : ℤ))

omit [NeZero n'] in
def lamL (la : Fin n' → Fin (r + K) → ℕ) : Fin n' × Fin (r + K) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => la v.1 v.2

def lamS (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) :
    Set (ℤ × Fin (r + K) →₀ ℕ) :=
  {m | (∀ v, m v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) ∧
    m ∈ segDegSet (r := r) K (X.bfam p K la e (j.val : ℤ)) ∧ m ∈ X.resSet p K (j.val : ℤ)}

end Dat

def RestLamA : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → ∀ (j : ℤ) (b : ℤ → ℕ),
    (∀ x, x ∉ X.F.letters j → b x = 0) →
    ∃ y : Fin (Module.finrank O (X.Mj p K O j b)) → SegRing O r K, (∀ i, y i ∈ X.Mj p K O j b) ∧
      LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (y i)

def RestLamInj (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ la ∈ X.LA p K, ∀ e ∈ X.EE p K la, ∀ la' ∈ X.LA p K, ∀ e' ∈ X.EE p K la',
    ∀ m m' : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j, m j ∈ X.lamS p K la e j) → (∀ j, m' j ∈ X.lamS p K la' e' j) →
      Dat.lamL K la + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j) =
        Dat.lamL K la' + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m' j) → (la = la' ∧ e = e') ∧ m = m'

def RestLamDeg (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ la ∈ X.LA p K, ∀ e ∈ X.EE p K la, X.IsCLabel p K (Dat.lamL K la) ∧
    ∀ m : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j, m j ∈ X.lamS p K la e j) →
      ∀ t, ∑ c : Fin (r + K), (Dat.lamL K la + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j)) (t, c) = X.a' p K t

theorem lam_map_phc {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {n' r : ℕ} [NeZero n'] (X : Dat n' r)
    (p K : ℕ) (j : Fin X.F.J) (P : SegRing R r K) :
    MvPolynomial.map f (X.phc p K R (j.val : ℤ) P) = lam_ph (X.lamG K) (X.lamE p K) j (MvPolynomial.map f P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Dat.phc, lam_ph]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | mul_X q v h =>
    simp only [map_mul, h, map_X]
    simp [Dat.phc, lam_ph, Dat.lamG, Dat.lamE]

theorem lam_mem_lamS {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ) [NeZero K] (O : Type) [CommRing O]
    (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) {y : SegRing O r K}
    (hy : y ∈ X.Mj p K O (j.val : ℤ) (X.bfam p K la e (j.val : ℤ))) : y ∈ restrictSupport O (X.lamS p K la e j) := by
  classical
  obtain ⟨⟨h1, h2⟩, h3⟩ := hy
  have hs := XX'_supported O X.F (j.val : ℤ) _ _ _ h1
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro m hm
  have hm' : m ∈ y.support := Finset.mem_coe.mp hm
  refine ⟨fun v hv => ?_, (MvPolynomial.mem_restrictSupport_iff (R := O)).mp h2 hm,
    (MvPolynomial.mem_restrictSupport_iff (R := O)).mp h3 hm⟩
  have hvars : v ∈ y.vars := by
    rw [MvPolynomial.mem_vars_iff_mem_support]
    exact ⟨m, hm', Finsupp.mem_support_iff.mpr hv⟩
  exact (MvPolynomial.mem_supported.mp hs) (Finset.mem_coe.mpr hvars)

theorem restLam_of_rests (C₀ : ℝ) (hA : RestLamA) (hI : RestLamInj C₀) (hD : RestLamDeg C₀) : RestLam C₀ := by
  intro p n' r K _ _ _ X O _ _ _ Sd hX hLa hk
  classical
  let SS := (X.LA p K).sigma fun la => X.EE p K la
  let Φ := {x // x ∈ SS}
  have hΦ : ∀ f : Φ, f.1.1 ∈ X.LA p K ∧ f.1.2 ∈ X.EE p K f.1.1 := fun f => Finset.mem_sigma.mp f.2
  let nn : Φ → Fin X.F.J → ℕ := fun f j =>
    Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K f.1.1 f.1.2 (j.val : ℤ)))
  have hex := fun (f : Φ) (j : Fin X.F.J) => hA p n' r K X O Sd hX (j.val : ℤ) (X.bfam p K f.1.1 f.1.2 (j.val : ℤ))
    (fun x hx => by simp [Dat.bfam, hx])
  choose y hyM hyL using hex
  set res := MvPolynomial.map (σ := ℤ × Fin (r + K)) (IsLocalRing.residue O) with hres
  have hli := lam_li_all (F := FF O) (X.lamG K) (X.lamE p K) (fun f : Φ => Dat.lamL K f.1.1)
    (fun f j => X.lamS p K f.1.1 f.1.2 j) (fun f j => Fin (nn f j)) (fun f j i => res (y f j i))
    (fun f j => hyL f j)
    (fun f j i => map_mem_restrictSupport _ _ (lam_mem_lamS X p K O f.1.1 f.1.2 j (hyM f j i)))
    (by
      intro f f' m m' hm hm' h
      obtain ⟨⟨h1, h2⟩, h3⟩ := hI p n' r K X hX hLa hk f.1.1 (hΦ f).1 f.1.2 (hΦ f).2 f'.1.1 (hΦ f').1 f'.1.2 (hΦ f').2
        m m' hm hm' h
      refine ⟨Subtype.ext ?_, h3⟩
      obtain ⟨⟨la, e⟩, hf⟩ := f
      obtain ⟨⟨la', e'⟩, hf'⟩ := f'
      simp only at h1 h2
      subst h1
      subst h2
      rfl)

  have hmem : ∀ x : (Σ f : Φ, ∀ j, Fin (nn f j)),
      monomial (Dat.lamL K x.1.1.1) (1 : FF O) * ∏ j, lam_ph (X.lamG K) (X.lamE p K) j (res (y x.1 j (x.2 j))) ∈
        X.LamBar p K O := by
    rintro ⟨f, a⟩
    let Yf : Fin X.F.J → SegRing O r K := fun i => y f i (a i)
    let y' : ℤ → SegRing O r K := fun j => if h : 0 ≤ j ∧ j.toNat < X.F.J then Yf ⟨j.toNat, h.2⟩ else 0
    have hy'i : ∀ i : Fin X.F.J, y' (i.val : ℤ) = Yf i := by
      intro i
      have h : 0 ≤ (i.val : ℤ) ∧ ((i.val : ℤ)).toNat < X.F.J := ⟨by positivity, by simpa using i.isLt⟩
      simp only [y', dite_eq_left h]
      exact congrArg Yf (Fin.ext (by simp))
    obtain ⟨hlab, hdeg⟩ := hD p n' r K X hX hLa hk f.1.1 (hΦ f).1 f.1.2 (hΦ f).2
    have hprod : (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y' j)) =
        ∏ j : Fin X.F.J, lam_ph (R := O) (X.lamG K) (X.lamE p K) j (Yf j) := by
      rw [Finset.prod_range]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [hy'i]
      rfl
    refine Submodule.subset_span ⟨(∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y' j)) *
      monomial (Dat.lamL K f.1.1) 1, ⟨fun j => X.bfam p K f.1.1 f.1.2 j, y', Dat.lamL K f.1.1, ?_, hlab, rfl, ?_⟩, ?_⟩
    · intro j
      by_cases h : 0 ≤ j ∧ j.toNat < X.F.J
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le h.1
        have hk' : k < X.F.J := by simpa using h.2
        have := hy'i ⟨k, hk'⟩
        simp only at this
        rw [this]
        exact hyM f ⟨k, hk'⟩ (a ⟨k, hk'⟩)
      · simp only [y', dite_eq_right h]
        exact Submodule.zero_mem _
    · rw [hprod, lam_expand]
      unfold RRdeg
      rw [MvPolynomial.mem_restrictSupport_iff]
      intro n hn
      have hn' := MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hn)
      rw [mul_comm, coeff_monomial_mul'] at hn'
      split_ifs at hn' with hle
      · rw [one_mul, coeff_sum] at hn'
        obtain ⟨m, hm, hm0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn'
        rw [coeff_monomial] at hm0
        split_ifs at hm0 with heq
        · have hn2 : n = Dat.lamL K f.1.1 + ∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j) := by
            rw [heq]; exact (add_tsub_cancel_of_le hle).symm
          intro t
          rw [hn2]
          refine hdeg m (fun j => ?_) t
          exact (MvPolynomial.mem_restrictSupport_iff (R := O)).mp
            (lam_mem_lamS X p K O f.1.1 f.1.2 j (hyM f j (a j))) (Finset.mem_coe.mpr (Fintype.mem_piFinset.mp hm j))
        · exact absurd rfl hm0
      · exact absurd rfl hn'
    · rw [map_mul, map_monomial, map_one, mul_comm, Finset.prod_range, map_prod]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [lam_map_phc, hy'i]
  have hfin : Module.Finite (FF O) (X.LamBar p K O) := by
    have := finite_restrictSupport (FF O) _ _ (degSet_finite n' (r + K) (X.a' p K))
    refine Submodule.finiteDimensional_of_le
      (S₂ := restrictSupport (FF O) {m : Fin n' × Fin (r + K) →₀ ℕ | ∀ t, ∑ c : Fin (r + K), m (t, c) = X.a' p K t}) ?_
    unfold Dat.LamBar
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨_, _, _, -, -, -, h⟩ := hg
    exact map_mem_restrictSupport _ _ h
  have hli' : LinearIndependent (FF O) (fun x : (Σ f : Φ, ∀ j, Fin (nn f j)) =>
      (⟨_, hmem x⟩ : X.LamBar p K O)) := by
    refine LinearIndependent.of_comp (X.LamBar p K O).subtype ?_
    exact hli
  have hcard := hli'.fintype_card_le_finrank
  refine le_trans (le_of_eq ?_) hcard
  rw [Fintype.card_sigma]
  simp only [Fintype.card_pi, Fintype.card_fin]
  rw [← Finset.sum_sigma (X.LA p K) (fun la => X.EE p K la)
    (fun x => ∏ j : Fin X.F.J, Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K x.1 x.2 (j.val : ℤ))))]
  exact (Finset.sum_coe_sort SS
    (fun x => ∏ j : Fin X.F.J, Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K x.1 x.2 (j.val : ℤ))))).symm

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

structure LamGeo {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) : Prop where
  U1 : ∀ j j' : Fin X.F.J, ∀ x ∈ X.toLate (j.val : ℤ), ∀ x' ∈ X.toLate (j'.val : ℤ), posOf n' x = posOf n' x' →
    j = j' ∧ x = x'
  U2 : ∀ j j' : Fin X.F.J, ∀ x ∈ X.F.letters (j.val : ℤ), X.F.IsW (j.val : ℤ) x → ∀ x' ∈ X.F.letters (j'.val : ℤ),
    X.F.IsW (j'.val : ℤ) x' → posOf n' x = posOf n' x' → j = j' ∧ x = x'
  LK : ∀ j j' : Fin X.F.J, ∀ x ∈ X.F.letters (j.val : ℤ), X.F.IsW (j.val : ℤ) x → ∀ x' ∈ X.toLate (j'.val : ℤ),
    posOf n' x = posOf n' x' → (∃ i < r, x' = X.F.fr (j'.val : ℤ) i) ∧
      X.Pz p K (j.val : ℤ) x = X.Pz p K (j'.val : ℤ) x' * X.Qc p K (j'.val : ℤ)
  EX : ∀ t ∈ X.F.TT, ∃ j : Fin X.F.J, ∃ x ∈ X.toLate (j.val : ℤ), posOf n' x = t

def RestLamGeo (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    LamGeo X p K

def RestLamTau : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r), X.Hyp p K →
    ∀ (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) (i : Fin r),
      X.bfam p K la e (j.val : ℤ) (X.F.fr (j.val : ℤ) i.val) = e j i

theorem lam_digit {P la la' A A' : ℕ} (h1 : la < P) (h2 : la' < P) (h : la + P * A = la' + P * A') :
    la = la' ∧ A = A' := by
  have hP : 0 < P := lt_of_le_of_lt (Nat.zero_le _) h1
  have e1 : (la + P * A) % P = la := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  have e2 : (la' + P * A') % P = la' := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
  have hla : la = la' := by rw [← e1, ← e2, h]
  refine ⟨hla, ?_⟩
  subst hla
  have h3 : P * A = P * A' := by omega
  exact Nat.eq_of_mul_eq_mul_left hP h3

section Eval

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

theorem lam_img_apply (j : Fin X.F.J) (m : ℤ × Fin (r + K) →₀ ℕ)
    (hm : ∀ v, m v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) (t : Fin n') (c : Fin (r + K)) :
    imgMon (X.lamG K j) (X.lamE p K j) m (t, c) =
      ∑ x ∈ X.F.letters (j.val : ℤ), if posOf n' x = t then X.Pz p K (j.val : ℤ) x * m (x, c) else 0 := by
  classical
  unfold imgMon
  rw [Finsupp.sum_apply]
  have hsub : m.support ⊆ X.F.letters (j.val : ℤ) ×ˢ (Finset.univ : Finset (Fin (r + K))) := by
    intro v hv
    exact Finset.mem_product.mpr ⟨(hm v (Finsupp.mem_support_iff.mp hv)).1, Finset.mem_univ _⟩
  rw [Finsupp.sum_of_support_subset m hsub _ (by intro v _; simp), Finset.sum_product]
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [Finsupp.single_apply, Dat.lamG, Prod.mk.injEq]
  by_cases h : posOf n' x = t
  · simp [h, Dat.lamE, Dat.Pz]
  · simp [h]

open Classical in
def segmentWeightExponent (m : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ)) (t : Fin n') (c : Fin (r + K)) : ℕ :=
  ∑ j : Fin X.F.J, ∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
    if posOf n' x = t then m j (x, c) else 0

theorem lam_eval (hG : LamGeo X p K) (m : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ))
    (hm : ∀ j v, m j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) (j0 : Fin X.F.J) (x0 : ℤ) (hx0 : x0 ∈ X.toLate (j0.val : ℤ))
    (c : Fin (r + K)) :
    (∑ j, imgMon (X.lamG K j) (X.lamE p K j) (m j)) (posOf n' x0, c) =
      X.Pz p K (j0.val : ℤ) x0 * (m j0 (x0, c) + X.Qc p K (j0.val : ℤ) * segmentWeightExponent X K m (posOf n' x0) c) := by
  classical
  rw [Finsupp.finsetSum_apply, Finset.sum_congr rfl fun j _ => lam_img_apply X p K j (m j) (hm j) _ c]
  have hsplit : ∀ j : Fin X.F.J,
      (∑ x ∈ X.F.letters (j.val : ℤ), if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) =
      (∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
        if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) +
      ∑ x ∈ X.toLate (j.val : ℤ), if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0 := by
    intro j
    unfold Dat.toLate
    exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
  have hlate : (∑ j : Fin X.F.J, ∑ x ∈ X.toLate (j.val : ℤ),
      if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) =
      X.Pz p K (j0.val : ℤ) x0 * m j0 (x0, c) := by
    rw [Finset.sum_eq_single j0]
    · rw [Finset.sum_eq_single x0]
      · rw [ite_eq_left rfl]
      · intro x hx hne
        rw [ite_eq_right]
        intro h
        exact hne (hG.U1 j0 j0 x hx x0 hx0 h).2
      · intro h; exact absurd hx0 h
    · intro j _ hne
      refine Finset.sum_eq_zero fun x hx => ?_
      rw [ite_eq_right]
      intro h
      exact hne (hG.U1 j j0 x hx x0 hx0 h).1
    · intro h; exact absurd (Finset.mem_univ _) h
  have hW : (∑ j : Fin X.F.J, ∑ x ∈ (X.F.letters (j.val : ℤ)).filter fun x => X.F.IsW (j.val : ℤ) x,
      if posOf n' x = posOf n' x0 then X.Pz p K (j.val : ℤ) x * m j (x, c) else 0) =
      X.Pz p K (j0.val : ℤ) x0 * (X.Qc p K (j0.val : ℤ) * segmentWeightExponent X K m (posOf n' x0) c) := by
    unfold segmentWeightExponent
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hxl, hxW⟩ := Finset.mem_filter.mp hx
    split_ifs with h
    · rw [(hG.LK j j0 x hxl hxW x0 hx0 h).2]; ring
    · simp
  rw [hlate, hW]; ring

end Eval

theorem restLamInj_of (C₀ : ℝ) (hGeo : RestLamGeo C₀) (hTau : RestLamTau) : RestLamInj C₀ := by
  intro p n' r K _ _ _ X hX hLa hk la hla e he la' hla' e' he' m m' hm hm' heq
  classical
  have hG := hGeo p n' r K X hX hLa hk
  have hok : ∀ j v, m j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ) := fun j => (hm j).1
  have hok' : ∀ j v, m' j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ) := fun j => (hm' j).1
  have hlaS := Fintype.mem_piFinset.mp hla
  have hlaS' := Fintype.mem_piFinset.mp hla'

  have hdec : ∀ (j0 : Fin X.F.J) (x0 : ℤ), x0 ∈ X.toLate (j0.val : ℤ) → ∀ c : Fin (r + K),
      la (posOf n' x0) c = la' (posOf n' x0) c ∧ m j0 (x0, c) = m' j0 (x0, c) ∧
        segmentWeightExponent X K m (posOf n' x0) c = segmentWeightExponent X K m' (posOf n' x0) c := by
    intro j0 x0 hx0 c
    have h1 := congrArg (fun f => f (posOf n' x0, c)) heq
    simp only [Finsupp.add_apply] at h1
    rw [lam_eval X p K hG m hok j0 x0 hx0 c, lam_eval X p K hG m' hok' j0 x0 hx0 c] at h1
    have hl1 : la (posOf n' x0) c < X.Pz p K (j0.val : ℤ) x0 :=
      ((Finset.mem_filter.mp (hlaS (posOf n' x0))).2.2 (j0.val : ℤ) x0 hx0 rfl).1 c
    have hl2 : la' (posOf n' x0) c < X.Pz p K (j0.val : ℤ) x0 :=
      ((Finset.mem_filter.mp (hlaS' (posOf n' x0))).2.2 (j0.val : ℤ) x0 hx0 rfl).1 c
    obtain ⟨g1, g2⟩ := lam_digit hl1 hl2 h1
    refine ⟨g1, ?_⟩
    by_cases hfc : (∃ i < r, x0 = X.F.fr (j0.val : ℤ) i) ∧ c.val < r
    · obtain ⟨⟨i, hi, rfl⟩, hc⟩ := hfc
      have hcc : c = Fin.castAdd K ⟨c.val, hc⟩ := Fin.ext rfl
      have a1 : m j0 (X.F.fr (j0.val : ℤ) i, c) < X.Qc p K (j0.val : ℤ) := by
        rw [hcc]; exact (hm j0).2.2 i hi ⟨c.val, hc⟩
      have a2 : m' j0 (X.F.fr (j0.val : ℤ) i, c) < X.Qc p K (j0.val : ℤ) := by
        rw [hcc]; exact (hm' j0).2.2 i hi ⟨c.val, hc⟩
      exact lam_digit a1 a2 g2
    · have hw0 : ∀ mm : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), (∀ j v, mm j v ≠ 0 → v ∈ okVars X.F K (j.val : ℤ)) →
          segmentWeightExponent X K mm (posOf n' x0) c = 0 := by
        intro mm hmm
        unfold segmentWeightExponent
        refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun x hx => ?_
        obtain ⟨hxl, hxW⟩ := Finset.mem_filter.mp hx
        split_ifs with h
        · by_contra hne
          apply hfc
          refine ⟨(hG.LK j j0 x hxl hxW x0 hx0 h).1, ?_⟩
          by_contra hc
          exact (hmm j (x, c) hne).2 (not_lt.mp hc) hxW
        · rfl
      rw [hw0 m hok, hw0 m' hok'] at g2 ⊢
      simp only [mul_zero, add_zero] at g2
      exact ⟨g2, rfl⟩
  have hlaeq : la = la' := by
    funext t c
    by_cases ht : t ∈ X.F.TT
    · obtain ⟨j0, x0, hx0, rfl⟩ := hG.EX t ht
      exact (hdec j0 x0 hx0 c).1
    · have ha : X.a' p K t = 0 := by
        unfold Dat.a' Dat.d
        rw [ite_eq_right ht]; simp
      have b1 := (Finset.mem_filter.mp (hlaS t)).2.1
      have b2 := (Finset.mem_filter.mp (hlaS' t)).2.1
      rw [ha] at b1 b2
      have c1 := Finset.single_le_sum (f := fun c => la t c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      have c2 := Finset.single_le_sum (f := fun c => la' t c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
      omega
  have hmeq : m = m' := by
    funext j
    ext v
    obtain ⟨x, c⟩ := v
    by_cases hv : (x, c) ∈ okVars X.F K (j.val : ℤ)
    · by_cases hW : X.F.IsW (j.val : ℤ) x
      · have hTT : posOf n' x ∈ X.F.TT := by
          have := hv.1
          unfold Frames.letters at this
          exact (Finset.mem_filter.mp this).2
        obtain ⟨j0, x0, hx0, hpos⟩ := hG.EX _ hTT
        have h3 := (hdec j0 x0 hx0 c).2.2
        have hwv : ∀ mm : Fin X.F.J → (ℤ × Fin (r + K) →₀ ℕ), segmentWeightExponent X K mm (posOf n' x0) c = mm j (x, c) := by
          intro mm
          unfold segmentWeightExponent
          rw [Finset.sum_eq_single j]
          · rw [Finset.sum_eq_single x]
            · rw [ite_eq_left hpos.symm]
            · intro y hy hne
              obtain ⟨hyl, hyW⟩ := Finset.mem_filter.mp hy
              rw [ite_eq_right]
              intro h
              exact hne (hG.U2 j j y hyl hyW x hv.1 hW (h.trans hpos)).2
            · intro h; exact absurd (Finset.mem_filter.mpr ⟨hv.1, hW⟩) h
          · intro j' _ hne
            refine Finset.sum_eq_zero fun y hy => ?_
            obtain ⟨hyl, hyW⟩ := Finset.mem_filter.mp hy
            rw [ite_eq_right]
            intro h
            exact hne (hG.U2 j' j y hyl hyW x hv.1 hW (h.trans hpos)).1
          · intro h; exact absurd (Finset.mem_univ _) h
        rw [hwv m, hwv m'] at h3
        exact h3
      · exact (hdec j x (Finset.mem_filter.mpr ⟨hv.1, hW⟩) c).2.1
    · have z1 : m j (x, c) = 0 := by
        by_contra h; exact hv (hok j _ h)
      have z2 : m' j (x, c) = 0 := by
        by_contra h; exact hv (hok' j _ h)
      rw [z1, z2]
  refine ⟨⟨hlaeq, ?_⟩, hmeq⟩
  funext j i
  have d1 := (hm j).2.1 (X.F.fr (j.val : ℤ) i.val)
  have d2 := (hm' j).2.1 (X.F.fr (j.val : ℤ) i.val)
  rw [hTau p n' r K X hX] at d1 d2
  rw [← d1, ← d2, hmeq]

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem lam_m_zero {a b m J : ℤ} (ha : 0 ≤ a) (ha' : a < J) (hb : 0 ≤ b) (hb' : b < J) (h : b = a + m * J) :
    m = 0 := by
  subst h
  rcases lt_trichotomy m 0 with hm | hm | hm
  · have : m * J ≤ -J := by nlinarith
    omega
  · exact hm
  · have : J ≤ m * J := by nlinarith
    omega

private theorem exists_index_eq_fr_of_between {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁)
    (j x : ℤ) (hx : posOf n' x ∈ F.TT) :
    ∀ k, k < r → F.fr j 0 ≤ x → x ≤ F.fr j k → ∃ i ≤ k, x = F.fr j i := by
  intro k
  induction k with
  | zero =>
    intro _ h1 h2
    exact ⟨0, le_refl _, le_antisymm h2 h1⟩
  | succ k ih =>
    intro hk h1 h2
    rcases le_or_gt x (F.fr j k) with h | h
    · obtain ⟨i, hi, hxi⟩ := ih (by omega) h1 h
      exact ⟨i, by omega, hxi⟩
    · rcases lt_or_eq_of_le h2 with h' | h'
      · exact absurd hx (hV.2.2.2.2.2.1 j k x hk h h')
      · exact ⟨k + 1, le_refl _, h'⟩

theorem lam_W_late {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) {L₁ N₁ : ℕ} (hV : X.F.Valid L₁ N₁) (j x : ℤ)
    (hx : x ∈ X.F.letters j) (hW : X.F.IsW j x) : x ∈ X.toLate (j - 1) ∧ ∃ i < r, x = X.F.fr (j - 1) i := by
  classical
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hx
  obtain ⟨⟨hx1, hx2⟩, hxT⟩ := hx
  have hW' : x ≤ X.F.fr (j - 1) (r - 1) := hW
  obtain ⟨i, hi, rfl⟩ := exists_index_eq_fr_of_between X.F hV (j - 1) x hxT (r - 1) (by omega) hx1 hW'
  refine ⟨?_, i, by omega, rfl⟩
  have hg := hV.2.2.2.1 (j - 1 - 1)
  have h1 : j - 1 - 1 + 1 = j - 1 := by ring
  rw [h1] at hg
  have hm0 := TE.fr_le hV (j - 1 - 1) 0 (r - 1) (Nat.zero_le _) (by omega)
  have hmi := TE.fr_le hV (j - 1) i (r - 1) hi (by omega)
  have hm0i := TE.fr_le hV (j - 1) 0 i (Nat.zero_le _) (by omega)
  unfold Dat.toLate
  simp only [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · unfold Frames.letters
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hmi⟩, hxT⟩
  · unfold Frames.IsW
    omega

private theorem eq_of_mod_eq_of_mem_Ioc_fr_last {n' r : ℕ} [NeZero n'] [NeZero r] (F : Frames n' r) {L₁ N₁ : ℕ}
    (hV : F.Valid L₁ N₁) (s a b x x' : ℤ) (hsa : s ≤ a) (haJ : a < s + F.J) (hsb : s ≤ b)
    (hbJ : b < s + F.J) (hx1 : F.fr (a - 1) (r - 1) < x) (hx2 : x ≤ F.fr a (r - 1))
    (hx1' : F.fr (b - 1) (r - 1) < x') (hx2' : x' ≤ F.fr b (r - 1))
    (hp : x % (n' : ℤ) = x' % (n' : ℤ)) : a = b ∧ x = x' := by
  have hn : (0 : ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have hper := hV.2.1 (s - 1) (r - 1)
  rw [show s - 1 + (F.J : ℤ) = s + F.J - 1 by ring] at hper
  have m1 := (eFr_strictMono hV).monotone (by omega : s - 1 ≤ a - 1)
  have m2 := (eFr_strictMono hV).monotone (by omega : a ≤ s + F.J - 1)
  have m3 := (eFr_strictMono hV).monotone (by omega : s - 1 ≤ b - 1)
  have m4 := (eFr_strictMono hV).monotone (by omega : b ≤ s + F.J - 1)
  dsimp only [eFr] at m1 m2 m3 m4
  have e1 : x % (n' : ℤ) + n' * (x / n') = x := by rw [Int.emod_def]; ring
  have e2 : x' % (n' : ℤ) + n' * (x' / n') = x' := by rw [Int.emod_def]; ring
  have hq := lam_m_zero (a := x - F.fr (s - 1) (r - 1) - 1) (b := x' - F.fr (s - 1) (r - 1) - 1)
    (m := x' / n' - x / n') (J := n') (by omega) (by omega) (by omega) (by omega)
    (by linear_combination e1 - e2 - hp)
  have hxx : x = x' := by
    have hq' : x' / (n' : ℤ) = x / n' := by linarith
    rw [hq'] at e2
    linarith
  refine ⟨?_, hxx⟩
  subst hxx
  rcases lt_trichotomy a b with h | h | h
  · have : F.fr a (r - 1) ≤ F.fr (b - 1) (r - 1) := (eFr_strictMono hV).monotone (by omega)
    omega
  · exact h
  · have : F.fr b (r - 1) ≤ F.fr (a - 1) (r - 1) := (eFr_strictMono hV).monotone (by omega)
    omega

private theorem mem_Ioc_and_posOf_mem_of_mem_late {n' r : ℕ} [NeZero n'] (X : Dat n' r) (j x : ℤ) (h : x ∈ X.toLate j) :
    X.F.fr (j - 1) (r - 1) < x ∧ x ≤ X.F.fr j (r - 1) ∧ posOf n' x ∈ X.F.TT := by
  classical
  unfold Dat.toLate at h
  simp only [Finset.mem_filter] at h
  obtain ⟨h1, h2⟩ := h
  unfold Frames.letters at h1
  simp only [Finset.mem_filter, Finset.mem_Icc] at h1
  unfold Frames.IsW at h2
  exact ⟨by omega, h1.1.2, h1.2⟩

private theorem mem_late_of_mem_Ioc_of_posOf_mem {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) {L₁ N₁ : ℕ}
    (hV : X.F.Valid L₁ N₁) (j x : ℤ) (h1 : X.F.fr (j - 1) (r - 1) < x) (h2 : x ≤ X.F.fr j (r - 1))
    (h3 : posOf n' x ∈ X.F.TT) : x ∈ X.toLate j := by
  classical
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h0 := TE.fr_le hV (j - 1) 0 (r - 1) (Nat.zero_le _) (by omega)
  unfold Dat.toLate
  simp only [Finset.mem_filter]
  refine ⟨?_, ?_⟩
  · unfold Frames.letters
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, h2⟩, h3⟩
  · unfold Frames.IsW
    omega

private theorem Rj_eq_log_floor {n' r : ℕ} (X : Dat n' r) (p K : ℕ) (j : ℤ) :
    X.Rj p K j = Nat.log p ⌊X.a / (8 * X.Y * Dat.k (r := r) K ^ 2 * ↑X.Ns)⌋₊ - X.F.dist j (X.F.fr (j - 1) 0) := by
  unfold Dat.Rj
  rw [div_mul_eq_div_div, ← Nat.cast_pow, Nat.floor_div_natCast]
  exact Nat.log_div_base_pow p _ _

private theorem Pz_eq_Pz_mul_Qc {n' r : ℕ} (X : Dat n' r) (p K : ℕ) (j c x x' s : ℤ)
    (h1 : X.F.fr c (r - 1) = X.F.fr (j - 1) (r - 1) + s)
    (h2 : X.F.fr (c - 1) 0 = X.F.fr (j - 1 - 1) 0 + s)
    (h3 : X.F.fr (c + 1) (r - 1) = X.F.fr j (r - 1) + s)
    (h4 : X.F.fr (c + 1 - 1) 0 = X.F.fr (j - 1) 0 + s)
    (hx' : x' = x + s) (hxT : x ≤ X.F.fr (j - 1) (r - 1))
    (hTT : X.F.fr (j - 1) (r - 1) < X.F.fr j (r - 1))
    (hA : X.F.fr (j - 1) 0 ≤ X.F.fr j (r - 1))
    (hB : X.F.fr (j - 1 - 1) 0 ≤ X.F.fr (j - 1) (r - 1))
    (hC : X.F.fr (j - 1 - 1) 0 < X.F.fr (j - 1) 0) :
    X.Pz p K j x = X.Pz p K c x' * X.Qc p K c := by
  have hRj := Rj_eq_log_floor X p K j
  have hRc := Rj_eq_log_floor X p K c
  have hRc1 := Rj_eq_log_floor X p K (c + 1)
  unfold Dat.Pz Dat.Qc
  rw [hRj, hRc, hRc1, ← pow_add]
  congr 1
  unfold Frames.dist
  omega

theorem restLamGeo (C₀ : ℝ) : RestLamGeo C₀ := by
  classical
  intro p n' r K _ _ _ X hH _ _
  have hV := hH.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hn : (0 : ℤ) < n' := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n')
  have hJ : 1 ≤ X.F.J := hV.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j j' x hx x' hx' hp
    obtain ⟨a1, a2, a3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x hx
    obtain ⟨b1, b2, b3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x' hx'
    have hj := j.isLt
    have hj' := j'.isLt
    obtain ⟨e1, e2⟩ := eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV 0 _ _ x x' (by omega) (by omega) (by omega) (by omega)
      a1 a2 b1 b2 (by rw [← posOf_val, ← posOf_val, hp])
    exact ⟨Fin.ext (by omega), e2⟩
  · intro j j' x hx hW x' hx' hW' hp
    obtain ⟨hl, -⟩ := lam_W_late X hV _ x hx hW
    obtain ⟨hl', -⟩ := lam_W_late X hV _ x' hx' hW'
    obtain ⟨a1, a2, a3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x hl
    obtain ⟨b1, b2, b3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x' hl'
    have hj := j.isLt
    have hj' := j'.isLt
    obtain ⟨e1, e2⟩ := eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV (-1) _ _ x x' (by omega) (by omega) (by omega) (by omega)
      a1 a2 b1 b2 (by rw [← posOf_val, ← posOf_val, hp])
    exact ⟨Fin.ext (by omega), e2⟩
  · intro j j' x hx hW x' hx' hp
    obtain ⟨hl, i, hi, hxi⟩ := lam_W_late X hV _ x hx hW
    obtain ⟨a1, a2, a3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x hl
    obtain ⟨b1, b2, b3⟩ := mem_Ioc_and_posOf_mem_of_mem_late X _ x' hx'
    have hj := j.isLt
    have hj' := j'.isLt
    have hTT : X.F.fr (((j : ℕ) : ℤ) - 1) (r - 1) < X.F.fr ((j : ℕ) : ℤ) (r - 1) :=
      eFr_strictMono hV (by omega)
    have hf1 := TE.fr_le hV (((j : ℕ) : ℤ) - 1) 0 (r - 1) (Nat.zero_le _) (by omega)
    have hf2 := TE.fr_le hV (((j : ℕ) : ℤ) - 1 - 1) 0 (r - 1) (Nat.zero_le _) (by omega)
    have hg := hV.2.2.2.1 (((j : ℕ) : ℤ) - 1 - 1)
    rw [sub_add_cancel] at hg
    have hA : X.F.fr (((j : ℕ) : ℤ) - 1) 0 ≤ X.F.fr ((j : ℕ) : ℤ) (r - 1) := by omega
    have hC : X.F.fr (((j : ℕ) : ℤ) - 1 - 1) 0 < X.F.fr (((j : ℕ) : ℤ) - 1) 0 := by omega
    have hB : X.F.fr (((j : ℕ) : ℤ) - 1 - 1) 0 ≤ X.F.fr (((j : ℕ) : ℤ) - 1) (r - 1) := by omega
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj0
    · have q1 : X.F.fr (((j : ℕ) : ℤ) - 1 + X.F.J - 1) (r - 1)
          = X.F.fr (((j : ℕ) : ℤ) - 1 - 1) (r - 1) + n' := by
        rw [show ((j : ℕ) : ℤ) - 1 + X.F.J - 1 = ((j : ℕ) : ℤ) - 1 - 1 + X.F.J by ring]
        exact hV.2.1 _ _
      have q2 := hV.2.1 (((j : ℕ) : ℤ) - 1) (r - 1)
      have hpy : (x + n') % (n' : ℤ) = x' % (n' : ℤ) := by
        rw [Int.add_emod_right, ← posOf_val, ← posOf_val, hp]
      obtain ⟨e1, e2⟩ := eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV 0 (((j : ℕ) : ℤ) - 1 + X.F.J) ((j' : ℕ) : ℤ) (x + n') x'
        (by omega) (by omega) (by omega) (by omega) (by rw [q1]; omega) (by rw [q2]; omega) b1 b2 hpy
      refine ⟨⟨i, hi, ?_⟩, ?_⟩
      · rw [← e1, ← e2, hxi]
        exact (hV.2.1 _ _).symm
      · rw [← e1, ← e2]
        refine Pz_eq_Pz_mul_Qc X p K _ _ x _ n' (hV.2.1 _ _) ?_ ?_ ?_ rfl a2 hTT hA hB hC
        · rw [show ((j : ℕ) : ℤ) - 1 + X.F.J - 1 = ((j : ℕ) : ℤ) - 1 - 1 + X.F.J by ring]
          exact hV.2.1 _ _
        · rw [show ((j : ℕ) : ℤ) - 1 + X.F.J + 1 = ((j : ℕ) : ℤ) + X.F.J by ring]
          exact hV.2.1 _ _
        · rw [show ((j : ℕ) : ℤ) - 1 + X.F.J + 1 - 1 = ((j : ℕ) : ℤ) - 1 + X.F.J by ring]
          exact hV.2.1 _ _
    · obtain ⟨e1, e2⟩ := eq_of_mod_eq_of_mem_Ioc_fr_last X.F hV 0 (((j : ℕ) : ℤ) - 1) ((j' : ℕ) : ℤ) x x'
        (by omega) (by omega) (by omega) (by omega) a1 a2 b1 b2
        (by rw [← posOf_val, ← posOf_val, hp])
      refine ⟨⟨i, hi, ?_⟩, ?_⟩
      · rw [← e1, ← e2]
        exact hxi
      · rw [← e1, ← e2]
        refine Pz_eq_Pz_mul_Qc X p K _ (((j : ℕ) : ℤ) - 1) x x 0 (by rw [add_zero]) (by rw [add_zero])
          ?_ ?_ (by rw [add_zero]) a2 hTT hA hB hC
        · rw [sub_add_cancel, add_zero]
        · rw [sub_add_cancel, add_zero]
  · intro t ht
    have hper := hV.2.1 (-1) (r - 1)
    obtain ⟨y, hy⟩ : ∃ y : ℤ, y = X.F.fr (-1) (r - 1) + 1
        + (((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) % (n' : ℤ) := ⟨_, rfl⟩
    have hy0 := Int.emod_nonneg (((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) (ne_of_gt hn)
    have hy1 := Int.emod_lt_of_pos (((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) hn
    have ht' := t.isLt
    have hypos : posOf n' y = t := by
      have hmod : y % (n' : ℤ) = ((t : ℕ) : ℤ) := by
        have hy2 : y = ((t : ℕ) : ℤ)
            + (n' : ℤ) * (-((((t : ℕ) : ℤ) - (X.F.fr (-1) (r - 1) + 1)) / (n' : ℤ))) := by
          rw [hy, Int.emod_def]
          ring
        rw [hy2, Int.add_mul_emod_self_left]
        exact Int.emod_eq_of_lt (by omega) (by omega)
      unfold posOf
      apply Fin.ext
      simp only
      rw [hmod, Int.toNat_natCast]
      exact Nat.mod_eq_of_lt ht'
    have hyB : y ≤ X.F.fr (((X.F.J - 1 : ℕ)) : ℤ) (r - 1) := by
      rw [show (((X.F.J - 1 : ℕ)) : ℤ) = -1 + X.F.J by omega, hper]
      omega
    have hex : ∃ k : ℕ, y ≤ X.F.fr (k : ℤ) (r - 1) := ⟨_, hyB⟩
    have hk0 := Nat.find_spec hex
    have hk0le := Nat.find_min' hex hyB
    have hmin : ∀ m < Nat.find hex, ¬ y ≤ X.F.fr (m : ℤ) (r - 1) := fun m hm => Nat.find_min hex hm
    generalize Nat.find hex = k0 at hk0 hk0le hmin
    have hlow : X.F.fr ((k0 : ℤ) - 1) (r - 1) < y := by
      rcases Nat.eq_zero_or_pos k0 with h0 | h0
      · subst h0
        rw [Nat.cast_zero, zero_sub]
        omega
      · have h := hmin (k0 - 1) (by omega)
        rw [show (((k0 - 1 : ℕ)) : ℤ) = (k0 : ℤ) - 1 by omega] at h
        omega
    refine ⟨⟨k0, by omega⟩, y, ?_, hypos⟩
    exact mem_late_of_mem_Ioc_of_posOf_mem X hV _ y hlow hk0 (by rw [hypos]; exact ht)

theorem restLamTau : RestLamTau := by
  classical
  intro p n' r K _ _ _ X hH la e j i
  have hV := hH.valid
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hi := i.isLt
  have hj := j.isLt
  have hle : X.F.fr ((j : ℕ) : ℤ) i ≤ X.F.fr ((j : ℕ) : ℤ) (r - 1) :=
    TE.fr_le hV _ i (r - 1) (by omega) (by omega)
  have h0i : X.F.fr ((j : ℕ) : ℤ) 0 ≤ X.F.fr ((j : ℕ) : ℤ) i :=
    TE.fr_le hV _ 0 i (Nat.zero_le _) hi
  have hg := hV.2.2.2.1 (((j : ℕ) : ℤ) - 1)
  rw [sub_add_cancel] at hg
  have h00 := TE.fr_le hV (((j : ℕ) : ℤ) - 1) 0 (r - 1) (Nat.zero_le _) (by omega)
  have hT := (hV.2.2.2.2.1 ((j : ℕ) : ℤ) i hi).1
  have hmem : X.F.fr ((j : ℕ) : ℤ) i ∈ X.F.letters ((j : ℕ) : ℤ) := by
    unfold Frames.letters
    simp only [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, hle⟩, hT⟩
  have hnW : ¬ X.F.IsW ((j : ℕ) : ℤ) (X.F.fr ((j : ℕ) : ℤ) i) := by
    unfold Frames.IsW
    omega
  unfold Dat.bfam
  rw [ite_eq_left hmem, ite_eq_right hnW, ite_eq_left h0i]
  rw [Finset.sum_eq_single i]
  · rw [ite_eq_left rfl]
    unfold Dat.eZ
    rw [dite_eq_left (by omega)]
    congr 1
    ext
    have hm : ((j : ℕ) : ℤ) % (X.F.J : ℤ) = ((j : ℕ) : ℤ) := Int.emod_eq_of_lt (by omega) (by omega)
    simp only [hm, Int.toNat_natCast]
    exact Nat.mod_eq_of_lt hj
  · intro b _ hb
    rw [ite_eq_right]
    intro h
    apply hb
    have hbl := b.isLt
    rcases lt_trichotomy (b : ℕ) (i : ℕ) with hlt | heq | hgt
    · have h1 := hV.2.2.1 ((j : ℕ) : ℤ) b (by omega)
      have h2 := TE.fr_le hV ((j : ℕ) : ℤ) ((b : ℕ) + 1) i (by omega) hi
      omega
    · exact Fin.ext heq
    · have h1 := hV.2.2.1 ((j : ℕ) : ℤ) i (by omega)
      have h2 := TE.fr_le hV ((j : ℕ) : ℤ) ((i : ℕ) + 1) b (by omega) hbl
      omega
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem restLamInj (C₀ : ℝ) : RestLamInj C₀ := restLamInj_of C₀ (restLamGeo C₀) restLamTau

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Kit

variable (D : Formalism.BasicNotions.D7) (hV : admB2 D) {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {n : ℕ} [NeZero n] (S : Set ℤ)

include hV

theorem mem_vg_mul {a b : ℤ} {P Q : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P)
    (hQ : (b : WithTop ℤ) ≤ valS LZ S Q) : ((a + b : ℤ) : WithTop ℤ) ≤ valS LZ S (P * Q) := by
  have h := ((hV R ℤ n LZ S).1 P Q).1
  rw [h, WithTop.coe_add]
  exact add_le_add hP hQ

omit hV [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_vg_C (c : R) : ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (C c : MvPolynomial (ℤ × Fin n) R) :=
  by
  unfold valS
  refine Finset.le_inf fun k hk => ?_
  have h := sDegs_C (R := R) LZ S (lastIdx n) c k hk
  rw [Set.mem_singleton_iff] at h
  subst h
  exact le_rfl

theorem mem_vg_pow {a : ℤ} {P : MvPolynomial (ℤ × Fin n) R} (hP : (a : WithTop ℤ) ≤ valS LZ S P) (m : ℕ) :
    (((m : ℤ) * a : ℤ) : WithTop ℤ) ≤ valS LZ S (P ^ m) := by
  induction m with
  | zero => simpa using mem_vg_C (R := R) (n := n) S 1
  | succ k ih =>
    have e : (((k + 1 : ℕ) : ℤ) * a : ℤ) = (k : ℤ) * a + a := by push_cast; ring
    rw [e, pow_succ]
    exact mem_vg_mul D hV S ih hP

theorem mem_vg_prod {κ : Type} (s : Finset κ) (f : κ → MvPolynomial (ℤ × Fin n) R) (a : κ → ℤ)
    (h : ∀ i ∈ s, (a i : WithTop ℤ) ≤ valS LZ S (f i)) :
    ((∑ i ∈ s, a i : ℤ) : WithTop ℤ) ≤ valS LZ S (∏ i ∈ s, f i) := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using mem_vg_C (R := R) (n := n) S 1
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact mem_vg_mul D hV S (h i (Finset.mem_insert_self i s))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

omit hV [IsDomain R] [IsDiscreteValuationRing R] in
theorem mem_vg_X (v : ℤ × Fin n) (he : Even v.1) :
    ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (X v : MvPolynomial (ℤ × Fin n) R) := by
  unfold valS
  refine Finset.le_inf fun k hk => ?_
  have hk0 : (0 : ℤ) ≤ k := by
    by_cases hS : v.1 ∈ S
    · have hv : LZ.vec v.1 = true := by simp [LZ, he]
      have h := sDegs_X_vec (R := R) LZ S (lastIdx n) v.1 v.2 hS hv k hk
      have h01 : k = 0 ∨ k = 1 := by simpa using h
      rcases h01 with h | h <;> simp [h]
    · have h := sDegs_X_out (R := R) LZ S (lastIdx n) v hS k hk
      rw [Set.mem_singleton_iff] at h
      simp [h]
  exact WithTop.coe_le_coe.mpr hk0

theorem mem_vg_monom {κ : Type} (s : Finset κ) (v : κ → ℤ × Fin n) (e : κ → ℕ) (he : ∀ i ∈ s, Even (v i).1) :
    ((0 : ℤ) : WithTop ℤ) ≤ valS LZ S (∏ i ∈ s, (X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) := by
  have h0 : ∀ i ∈ s, (((fun _ => (0 : ℤ)) i : ℤ) : WithTop ℤ) ≤
      valS LZ S ((X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) := by
    intro i hi
    simpa using mem_vg_pow D hV S (mem_vg_X (R := R) S (v i) (he i hi)) (e i)
  simpa using mem_vg_prod D hV S s (fun i => (X (v i) : MvPolynomial (ℤ × Fin n) R) ^ e i) (fun _ => 0) h0

end Kit

namespace Dat

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) (p K : ℕ)

def discPowerTimesMonomial (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) : MvPolynomial (ℤ × Fin r) O :=
  X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat)

omit [NeZero n'] [NeZero r] in
def memMu (O : Type) [CommRing O] (j : ℤ) (u : Fin r × Fin r → ℕ) : MvPolynomial (ℤ × Fin r) O :=
  ∏ v : Fin r × Fin r, MvPolynomial.X (X.F.fr j v.1.val, v.2) ^ u v

def memPl (O : Type) [CommRing O] (j : ℤ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) :
    MvPolynomial (ℤ × Fin r) O :=
  segRen X.F j O r (Psi O (plPart μ) (Ican (plPart μ)))

def memA (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    MvPolynomial (ℤ × Fin r) O :=
  X.discPowerTimesMonomial p K O j b * X.memMu O j q.2.2 * X.memPl K O j q.1

def memG (O : Type) [CommRing O] (j : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    MvPolynomial (ℤ × Fin K) O :=
  segRen X.F j O K (Psi O (tanPart q.1) q.2.1)

def memM [NeZero K] (j : ℤ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) : ℤ → ℤ :=
  Function.extend (segE X.F j)
    (fun i => if Even (segE X.F j i) then tanPart μ i.succ 0 else tanPart μ i.castSucc 0) 0

theorem famEl_eq (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) :
    X.famEl p K O j b q = plEmb O r K (X.memA p K O j b q) * nmEmb O r K (X.memG K O j q) := by
  first
  | (simp only [famEl, memA, discPowerTimesMonomial, memMu, memPl, memG, PsiPl, PsiTan, segRen, plEmb, nmEmb, map_mul,
      rename_rename, Function.comp_def, plVar, tanVar]
     ring)

end Dat

def RestMemA (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      X.memA p K O j b q.1 ∈ supported O {v : ℤ × Fin r | v.1 ∈ X.F.letters j} ∧
      X.memG K O j q.1 ∈ supported O {v : ℤ × Fin K | v.1 ∈ X.F.letters j ∧ ¬ X.F.IsW j v.1} ∧
      ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x →
        (Even x → lam1S LZ {y | y ≤ x} (X.memG K O j q.1) ≤ ((X.memM K j q.1.1 x : ℤ) : WithBot ℤ) ∧
            ((X.memM K j q.1.1 x + (X.m0 K : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ {y | y < x} (X.memA p K O j b q.1)) ∧
        (¬ Even x → lam1S LZ {y | y < x} (X.memG K O j q.1) ≤ ((X.memM K j q.1.1 x : ℤ) : WithBot ℤ) ∧
            ((X.memM K j q.1.1 x + (X.m0 K : ℤ) : ℤ) : WithTop ℤ) ≤ valS LZ {y | y ≤ x} (X.memA p K O j b q.1)) ∧
        geR (valS LZ {y | y < x} (X.memA p K O j b q.1)) (X.thc p K j b x)

def RestMemB (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      ∀ mm ∈ (plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1)).support,
        ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x → (ordDeg mm x : ℝ) ≤ X.oc p K j x

def RestMemC (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1) ∈ Pol O (r + K) b

def RestMemD (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b),
      plEmb O r K (X.memA p K O j b q.1) * nmEmb O r K (X.memG K O j q.1) ∈ restrictSupport O (X.resSet p K j)

theorem restMem_of_rests (C₀ : ℝ) (hA : RestMemA C₀) (hB : RestMemB C₀) (hC : RestMemC C₀) (hD : RestMemD C₀) :
    RestMem C₀ := by
  intro p n' r K _ _ _ X O _ _ _ hS hX hCLa hCk j b hb q
  have hA' := hA p n' r K X O hS hX hCLa hCk j b hb q
  have hB' := hB p n' r K X O hS hX hCLa hCk j b hb q
  have hC' := hC p n' r K X O hS hX hCLa hCk j b hb q
  have hD' := hD p n' r K X O hS hX hCLa hCk j b hb q
  rw [X.famEl_eq p K O j b q.1]
  simp only [Dat.Mj, XX', Submodule.mem_inf]
  refine ⟨⟨⟨Submodule.subset_span ⟨X.memA p K O j b q.1, X.memG K O j q.1, X.memM K j q.1.1,
    hA'.1, hA'.2.1, hA'.2.2, rfl⟩, ?_⟩, hC'⟩, hD'⟩
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro mm hmm
  exact hB' mm hmm

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem mem_isSt_Ican {N r : ℕ} [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    IsSt ν (Ican ν) := by
  classical
  have hbe : 0 ≤ be := by
    have := (H.rng N le_rfl 0).1
    rwa [H.fin] at this
  have hlast : ν (Fin.last N) 0 = be := by
    have := H.fin 0
    rw [← stg_eq ν N (by omega)] at this
    exact this
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rw [Ican_eq H, ite_eq_right]
    intro h
    exact hc (mem_colRange_of_le_entry ν (Fin.last N) 0 (by omega) (by rw [hlast]; exact h.2))
  · intro c
    rw [Ican_eq H, pEnd_eq]
    by_cases h1 : 1 ≤ c
    · rw [ite_eq_left h1]
      by_cases h2 : c ≤ be
      · rw [ite_eq_left ⟨h1, h2⟩, colH_all fun m => by rw [H.fin]; exact h2, Finset.card_univ, Fintype.card_fin]
      · rw [ite_eq_right fun h => h2 h.2, colH_none fun m => by rw [H.fin]; omega, Finset.card_empty]
    · rw [ite_eq_right h1, ite_eq_right fun h => h1 h.1, colH_all fun m => by rw [H.fin]; omega, Finset.card_empty]
      omega
  · intro c t
    unfold tabCol
    by_cases h1 : 1 ≤ c
    · rw [ite_eq_left h1, ite_eq_left (by omega : (1 : ℤ) ≤ c + 1), Ican_eq H, Ican_eq H]
      by_cases h2 : c + 1 ≤ be
      · rw [ite_eq_left ⟨by omega, h2⟩, ite_eq_left ⟨h1, by omega⟩]
      · rw [ite_eq_right fun h => h2 h.2]
        simp
    · rw [ite_eq_right h1]
      have hc0 : Ican ν c = ∅ := by rw [Ican_eq H, ite_eq_right fun h => h1 h.1]
      rw [hc0, Finset.sdiff_empty]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

section Ctx

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem exists_path_decomposition (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ)
    (q : X.Idx p K j (X.restr j b)) :
    ∃ (dd b' b'' : Fin (segN X.F j) → ℕ) (P : PPath (r + K) (segN X.F j) (segLL X.F j) dd)
      (P1 : PPath r (segN X.F j) (segLL X.F j) b') (P2 : PPath K (segN X.F j) (segLL X.F j) b''),
      P.mu = q.1.1 ∧ P1.mu = plPart q.1.1 ∧ P2.mu = tanPart q.1.1 ∧ (∀ i, b' i + b'' i = dd i) ∧
      (∀ i, Formalism.MainNotions.CovariantDegrees.CondC (segLL X.F j) (plPart q.1.1) (tanPart q.1.1) i) ∧
      X.IsPATH p K j (X.restr j b) q.1.1 dd ∧ X.IsGood p K j (X.restr j b) q.1.1 ∧
      IsSt (tanPart q.1.1) q.1.2.1 ∧
      (∀ v, q.1.2.2 v + 2 * X.beS p K j (X.restr j b) < X.Qc p K j) ∧
      ∀ (i : Fin (segN X.F j)) (i' : Fin r), segE X.F j i = X.F.fr j i'.val →
        dd i + ∑ c, q.1.2.2 (i', c) = X.restr j b (X.F.fr j i'.val) := by
  obtain ⟨dd, hP, hG, hSt, hu, hd⟩ := q.2
  obtain ⟨P, hPμ⟩ := hP.path
  have hNK : segN X.F j + r ≤ K := le_trans (Nat.add_le_add_right (hX.card j) r) hX.NsK
  have h10 : BracketPolynomialSpan D := hAdm.2.2.2.2.2.2.2.2.2.1
  obtain ⟨b', b'', hsum, ⟨P1, h1⟩, ⟨P2, h2⟩, hC⟩ :=
    (h10 (segN X.F j) r K (segLL X.F j) dd hNK (plPart q.1.1) (tanPart q.1.1)).mp ⟨P, by rw [hPμ, joinPT_parts]⟩
  exact ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hP, hG, hSt, hu, hd⟩

theorem mem_W_vec (hX : X.Hyp p K) (j : ℤ) (l : Fin (segN X.F j)) (hl : l.val < r) :
    (segLL X.F j).vec l = true := by
  have hW : X.F.IsW j (segE X.F j l) := (TE.dict_w hX.valid l).mpr hl
  rw [comb_vec]
  exact comb_W_even X.F j hX.valid _ (segE_mem X.F j l) hW

theorem mem_tan_zero (hX : X.Hyp p K) (j : ℤ) {dd : Fin (segN X.F j) → ℕ}
    (P : PPath (r + K) (segN X.F j) (segLL X.F j) dd) (s : Fin (segN X.F j + 1)) (hs : s.val ≤ r) (c : Fin K) :
    tanPart P.mu s c = 0 := by
  apply le_antisymm
  · exact T.mu_nonpos P s.val s.isLt (Fin.natAdd r c) (by simp only [Fin.val_natAdd]; omega)
  · exact comb_nonneg_of_vec P s (fun l hl => mem_W_vec hX j l (by omega)) _

theorem tangent_degree_zero_at_w (hX : X.Hyp p K) (j : ℤ) {dd b'' : Fin (segN X.F j) → ℕ}
    (P : PPath (r + K) (segN X.F j) (segLL X.F j) dd) (P2 : PPath K (segN X.F j) (segLL X.F j) b'')
    (h2 : P2.mu = tanPart P.mu) (i : Fin (segN X.F j)) (hW : X.F.IsW j (segE X.F j i)) : b'' i = 0 := by
  have hi : i.val < r := (TE.dict_w hX.valid i).mp hW
  have hs := T.step_vec P2 i (mem_W_vec hX j i hi)
  have h3 := hs.2.2
  rw [h2] at h3
  have : ∑ a, (tanPart P.mu i.succ a - tanPart P.mu i.castSucc a) = 0 :=
    Finset.sum_eq_zero fun a _ => by
      rw [mem_tan_zero hX j P i.succ (by simp only [Fin.val_succ]; omega) a,
        mem_tan_zero hX j P i.castSucc (by simp only [Fin.val_castSucc]; omega) a, sub_zero]
  rw [this] at h3
  exact_mod_cast h3.symm

theorem mem_thc_restr (hX : X.Hyp p K) (j : ℤ) (b : ℤ → ℕ) (x : ℤ) (hx : x ∈ X.toLate j) :
    X.thc p K j (X.restr j b) x = X.thc p K j b x := by
  classical
  obtain ⟨ho1, ho2⟩ := oldest_letter_in_segment p n' r K X hX j x hx
  unfold Dat.thc
  split_ifs with hW
  · rfl
  · have hl : X.F.oldest j x ∈ X.toLate j := (mem_late X j _).mpr ⟨ho1, hW⟩
    unfold Dat.restr
    rw [ite_eq_left hl]

theorem mem_det_supported (R : Type) [CommRing R] {n : ℕ} (y : Fin n → ℤ) (s : Set (ℤ × Fin n))
    (h : ∀ a c, (y a, c) ∈ s) :
    Matrix.det (Matrix.of fun a c : Fin n => (MvPolynomial.X (y a, c) : MvPolynomial (ℤ × Fin n) R)) ∈
      supported R s := by
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun σ _ => ?_
  rw [Units.smul_def, zsmul_eq_mul]
  refine Subalgebra.mul_mem _ (intCast_mem _ _) (Subalgebra.prod_mem _ fun i _ => ?_)
  exact Algebra.subset_adjoin ⟨_, h (σ i) i, rfl⟩

theorem disc_power_monomial_mem_supported (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) (s : Set (ℤ × Fin r))
    (h : ∀ (a c : Fin r), (X.F.fr (j - 1) a.val, c) ∈ s) : X.discPowerTimesMonomial p K O j b ∈ supported O s := by
  have hXm : ∀ v ∈ s, (MvPolynomial.X v : MvPolynomial (ℤ × Fin r) O) ∈ supported O s :=
    fun v hv => Algebra.subset_adjoin ⟨v, hv, rfl⟩
  unfold Dat.discPowerTimesMonomial Dat.Dw
  refine Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (mem_det_supported O _ s h) _)
    (Subalgebra.prod_mem _ fun i _ => Subalgebra.pow_mem _ (hXm _ (h i 0)) _)

theorem mem_Mu_supported (O : Type) [CommRing O] (j : ℤ) (u : Fin r × Fin r → ℕ) (s : Set (ℤ × Fin r))
    (h : ∀ (a c : Fin r), (X.F.fr j a.val, c) ∈ s) : X.memMu O j u ∈ supported O s := by
  have hXm : ∀ v ∈ s, (MvPolynomial.X v : MvPolynomial (ℤ × Fin r) O) ∈ supported O s :=
    fun v hv => Algebra.subset_adjoin ⟨v, hv, rfl⟩
  unfold Dat.memMu
  exact Subalgebra.prod_mem _ fun v _ => Subalgebra.pow_mem _ (hXm _ (h v.1 v.2)) _

theorem mem_vg_A (D : Formalism.BasicNotions.D7) (hB2 : admB2 D) (hX : X.Hyp p K) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ))
    (S : Set ℤ) (hS : ∀ a : Fin r, X.F.fr (j - 1) a.val ∈ S) (a : ℤ)
    (ha : (a : WithTop ℤ) ≤ valS LZ S (X.memPl K O j q.1)) :
    (((X.m0 K : ℤ) + a : ℤ) : WithTop ℤ) ≤ valS LZ S (X.memA p K O j b q) := by
  have hV := hX.valid
  have hevW : ∀ a : Fin r, Even (X.F.fr (j - 1) a.val) := fun a => (hV.2.2.2.2.1 (j - 1) a.val a.isLt).2
  have hevT : ∀ a : Fin r, Even (X.F.fr j a.val) := fun a => (hV.2.2.2.2.1 j a.val a.isLt).2
  have hD : ((1 : ℤ) : WithTop ℤ) ≤ valS LZ S (X.Dw O j) := by
    unfold Dat.Dw
    rw [(hB2 O ℤ r LZ S).2.2 (fun a => X.F.fr (j - 1) a.val) (fr_injective X.F hV (j - 1))
      (fun a => ⟨hS a, by simp [LZ, hevW a]⟩)]
    exact le_rfl
  have h1 := mem_vg_pow D hB2 S hD (X.m0 K)
  have h2 := mem_vg_monom D hB2 (R := O) S Finset.univ (fun i : Fin r => (X.F.fr (j - 1) i.val, (0 : Fin r)))
    (fun i => ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat) (fun i _ => hevW i)
  have h3 := mem_vg_monom D hB2 (R := O) S Finset.univ (fun v : Fin r × Fin r => (X.F.fr j v.1.val, v.2))
    q.2.2 (fun v _ => hevT v.1)
  have h4 := mem_vg_mul D hB2 S (mem_vg_mul D hB2 S (mem_vg_mul D hB2 S h1 h2) h3) ha
  unfold Dat.memA Dat.discPowerTimesMonomial Dat.memMu
  have e : (X.m0 K : ℤ) * 1 + 0 + 0 + a = (X.m0 K : ℤ) + a := by ring
  rw [e] at h4
  exact h4

end Ctx

theorem restMemA_of (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (C₀ : ℝ) : RestMemA C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hb q
  classical
  have : Fact p.Prime := ⟨hX.prime⟩
  have hV := hX.valid
  have hB2 : admB2 D := hAdm.2.1
  have hA3 : Formalism.MainNotions.CovariantDegrees.DefiniteRankOne D := hAdm.2.2.2.2.2.2.2.2.1
  obtain ⟨dd, b', b'', P, P1, P2, hPμ, h1, h2, hsum, hC, hPATH, hGood, hSt, hu, hd⟩ := exists_path_decomposition D hAdm hX j b q
  have H := plHyp_of X p K hX j _ _ dd hPATH
  have hI' : IsSt P1.mu (Ican P1.mu) := by rw [h1]; exact mem_isSt_Ican H
  have hI'' : IsSt P2.mu q.1.2.1 := by rw [h2]; exact hSt
  have u1 := standard_polynomial_mem_bounds (segLL X.F j) b' (fun th M => (hA3 p O S _ r (segLL X.F j) b' th M).1) P1 _ hI'
  have u2 := standard_polynomial_mem_bounds (segLL X.F j) b'' (fun th M => (hA3 p O S _ K (segLL X.F j) b'' th M).1) P2 _ hI''
  rw [h1] at u1
  rw [h2] at u2
  refine ⟨?_, ?_, ?_⟩
  · unfold Dat.memA
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ ?_ ?_) ?_
    · exact disc_power_monomial_mem_supported O j b _ fun a _ => TE.frp_mem hV j a.val a.isLt
    · exact mem_Mu_supported O j _ _ fun a _ => k_fr_mem_letters X.F hV j a.isLt
    · unfold Dat.memPl
      refine mem_supported.mpr fun v hv => ?_
      obtain ⟨u, _, rfl⟩ := mem_vars_rename _ _ (Finset.mem_coe.mp hv)
      exact segE_mem X.F j u.1
  · unfold Dat.memG
    refine mem_supported.mpr fun v hv => ?_
    obtain ⟨u, hu', rfl⟩ := mem_vars_rename _ _ (Finset.mem_coe.mp hv)
    exact ⟨segE_mem X.F j u.1, fun hW => pol_vars_deg u2.1 hu'
      (tangent_degree_zero_at_w hX j P P2 (by rw [h2, hPμ]) u.1 hW)⟩
  · intro x hx hW
    obtain ⟨i, rfl⟩ := segE_surj X.F j hx
    obtain ⟨sA1, sA2, -, -⟩ := seg_val X.F j (Psi O (plPart q.1.1) (Ican (plPart q.1.1))) i
    obtain ⟨-, -, sG3, sG4⟩ := seg_val X.F j (Psi O (tanPart q.1.1) q.1.2.1) i
    have hxl : segE X.F j i ∈ X.toLate j := (mem_late X j _).mpr ⟨hx, hW⟩
    have hM : X.memM K j q.1.1 (segE X.F j i) =
        (if Even (segE X.F j i) then tanPart q.1.1 i.succ 0 else tanPart q.1.1 i.castSucc 0) :=
      (segE_strictMono X.F j).injective.extend_apply _ _ i
    have hWlt : ∀ a : Fin r, X.F.fr (j - 1) a.val < segE X.F j i := by
      intro a
      have h3 : ¬ segE X.F j i ≤ X.F.fr (j - 1) (r - 1) := hW
      have h4 := kfr_le X.F hV (j - 1) (by have := a.isLt; omega : a.val ≤ r - 1) (by have := a.isLt; omega)
      omega
    have vlt := mem_vg_A D hB2 hX O j b q.1 {y | y < segE X.F j i} hWlt (plPart q.1.1 i.castSucc (lastIdx r))
      (by unfold Dat.memPl; rw [sA2]; exact (u1.2 i.castSucc).1)
    have vle := mem_vg_A D hB2 hX O j b q.1 {y | y ≤ segE X.F j i} (fun a => (hWlt a).le)
      (plPart q.1.1 i.succ (lastIdx r)) (by unfold Dat.memPl; rw [sA1]; exact (u1.2 i.succ).1)
    have hCi := hC i
    unfold Formalism.MainNotions.CovariantDegrees.CondC at hCi
    refine ⟨fun he => ⟨?_, ?_⟩, fun he => ⟨?_, ?_⟩, ?_⟩
    · rw [hM, ite_eq_left he]
      unfold Dat.memG
      rw [sG3]; exact (u2.2 i.succ).2
    · refine le_trans (WithTop.coe_le_coe.mpr ?_) vlt
      rw [hM, ite_eq_left he]
      rw [ite_eq_left ((comb_vec X.F j i).mpr he)] at hCi
      omega
    · rw [hM, ite_eq_right he]
      unfold Dat.memG
      rw [sG4]; exact (u2.2 i.castSucc).2
    · refine le_trans (WithTop.coe_le_coe.mpr ?_) vle
      rw [hM, ite_eq_right he]
      rw [ite_eq_right (fun h => he ((comb_vec X.F j i).mp h))] at hCi
      omega
    · refine geR_of_le vlt ?_
      rw [← mem_thc_restr hX j b _ hxl]
      have := (hGood i hW).1
      push_cast
      linarith

end

section
open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Geo

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

theorem fr_add_mul_period (hV : F.Valid L₁ N₁) (j : ℤ) (i : ℕ) (m : ℤ) :
    F.fr (j + m * F.J) i = F.fr j i + m * n' :=
  fr_period hV j i m

theorem sum_posOf_per (x m : ℤ) : posOf n' (x + m * n') = posOf n' x := by
  unfold posOf
  congr 3
  simp

theorem dist_add_mul_period (hV : F.Valid L₁ N₁) (j x m : ℤ) : F.dist (j + m * F.J) (x + m * n') = F.dist j x := by
  unfold Frames.dist
  rw [fr_add_mul_period hV]
  congr 1
  ring

theorem sum_prod_Ioc (g : ℕ → ℤ) (hg : Monotone g) (P : ℤ → Prop) [DecidablePred P] (ψ : ℤ → ℝ) (m : ℕ) :
    ∏ j ∈ Finset.range m, ∏ x ∈ (Finset.Ioc (g j) (g (j + 1))).filter P, ψ x =
      ∏ x ∈ (Finset.Ioc (g 0) (g m)).filter P, ψ x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, ih, ← Finset.prod_union
      (Finset.disjoint_filter_filter (Finset.Ioc_disjoint_Ioc_of_le le_rfl)), ← Finset.filter_union,
      Finset.Ioc_union_Ioc_eq_Ioc (hg (Nat.zero_le m)) (hg (Nat.le_succ m))]

end Geo

section GeoX

variable {n' r : ℕ} [NeZero n'] [NeZero r] (X : Dat n' r) {L₁ N₁ : ℕ} (p K : ℕ)

theorem mem_late_iff (hV : X.F.Valid L₁ N₁) (j x : ℤ) :
    x ∈ X.toLate j ↔ (eFr X.F (j - 1) < x ∧ x ≤ eFr X.F j) ∧ posOf n' x ∈ X.F.TT := by
  classical
  have : X.toLate j = nonW X.F j := rfl
  rw [this, nonW_eq hV, Finset.mem_filter, Finset.mem_Ioc]

theorem exists_shift_of_posOf_eq_of_mem_late (hV : X.F.Valid L₁ N₁) {j j' x x' : ℤ} (hx : x ∈ X.toLate j) (hx' : x' ∈ X.toLate j')
    (h : posOf n' x = posOf n' x') : ∃ m : ℤ, j' = j + m * X.F.J ∧ x' = x + m * n' := by
  have h1 : x % (n' : ℤ) = x' % (n' : ℤ) := by rw [← posOf_val, ← posOf_val, h]
  have h2 : (n' : ℤ) ∣ x' - x := Int.ModEq.dvd h1
  obtain ⟨m, hm⟩ := h2
  have hm' : x' = x + m * n' := by linarith [mul_comm (n' : ℤ) m]
  refine ⟨m, ?_, hm'⟩
  have a1 := (mem_late_iff X hV j x).mp hx
  have a2 := (mem_late_iff X hV j' x').mp hx'
  have p1 : eFr X.F (j + m * X.F.J) = eFr X.F j + m * n' := fr_add_mul_period hV j (r - 1) m
  have p0 : eFr X.F (j + m * X.F.J - 1) = eFr X.F (j - 1) + m * n' := by
    have := fr_add_mul_period hV (j - 1) (r - 1) m
    rw [show j + m * X.F.J - 1 = j - 1 + m * X.F.J by ring]
    exact this
  exact idx_unique (eFr_strictMono hV) (x := x') a2.1.1 a2.1.2 (by rw [p0]; linarith [a1.1.1])
    (by rw [p1]; linarith [a1.1.2])

theorem sum_Rj_per (hV : X.F.Valid L₁ N₁) (j m : ℤ) : X.Rj p K (j + m * X.F.J) = X.Rj p K j := by
  unfold Dat.Rj
  have e : j + m * X.F.J - 1 = (j - 1) + m * X.F.J := by ring
  rw [e, fr_add_mul_period hV (j - 1) 0 m, dist_add_mul_period hV]

theorem sum_Pz_per (hV : X.F.Valid L₁ N₁) (j x m : ℤ) :
    X.Pz p K (j + m * X.F.J) (x + m * n') = X.Pz p K j x := by
  unfold Dat.Pz
  rw [dist_add_mul_period hV, sum_Rj_per X p K hV]

theorem sum_Qc_per (hV : X.F.Valid L₁ N₁) (j m : ℤ) : X.Qc p K (j + m * X.F.J) = X.Qc p K j := by
  unfold Dat.Qc
  have e : j + m * X.F.J + 1 = (j + 1) + m * X.F.J := by ring
  rw [e, fr_add_mul_period hV (j + 1) (r - 1) m, fr_add_mul_period hV j (r - 1) m, sum_Rj_per X p K hV, sum_Rj_per X p K hV]
  congr 2
  ring

theorem sum_uniqP (hV : X.F.Valid L₁ N₁) (j j' x x' : ℤ) (hx : x ∈ X.toLate j) (hx' : x' ∈ X.toLate j')
    (h : posOf n' x = posOf n' x') : X.Pz p K j x = X.Pz p K j' x' := by
  obtain ⟨m, rfl, rfl⟩ := exists_shift_of_posOf_eq_of_mem_late X hV hx hx' h
  exact (sum_Pz_per X p K hV j x m).symm

theorem sum_perW (hV : X.F.Valid L₁ N₁) (j : ℤ) (i : Fin r) :
    X.Bw p K (j + X.F.J) (X.F.fr (j + X.F.J - 1) i.val) = X.Bw p K j (X.F.fr (j - 1) i.val) := by
  have e1 : X.F.fr (j + X.F.J - 1) i.val = X.F.fr (j - 1) i.val + 1 * n' := by
    have := fr_add_mul_period hV (j - 1) i.val 1
    rw [show j + (X.F.J : ℤ) - 1 = j - 1 + 1 * X.F.J by ring]
    exact this
  have e2 : j + (X.F.J : ℤ) = j + 1 * X.F.J := by ring
  unfold Dat.Bw
  rw [e1, e2, sum_posOf_per, dist_add_mul_period hV, sum_Rj_per X p K hV]

theorem prod_tiling (hV : X.F.Valid L₁ N₁) (φ : Fin n' → ℝ) :
    ∏ t ∈ X.F.TT, φ t = ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x) := by
  classical
  have hm := eFr_strictMono hV
  have h1 : ∀ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x) =
      ∏ x ∈ (Finset.Ioc ((fun i : ℕ => eFr X.F ((i : ℤ) - 1)) j) ((fun i : ℕ => eFr X.F ((i : ℤ) - 1)) (j + 1))).filter
        (fun x => posOf n' x ∈ X.F.TT), φ (posOf n' x) := by
    intro j _
    have : X.toLate (j : ℤ) = nonW X.F j := rfl
    rw [this, nonW_eq hV]
    simp
  rw [Finset.prod_congr rfl h1, sum_prod_Ioc (fun i : ℕ => eFr X.F ((i : ℤ) - 1))
    (fun a b hab => hm.monotone (by omega)) (fun x => posOf n' x ∈ X.F.TT) (fun x => φ (posOf n' x)) X.F.J]
  have h2 : eFr X.F ((X.F.J : ℤ) - 1) = eFr X.F (((0 : ℕ) : ℤ) - 1) + n' := by
    have := hV.2.1 (-1) (r - 1)
    simp only [eFr]
    have e1 : ((X.F.J : ℤ) - 1) = -1 + X.F.J := by ring
    have e2 : (((0 : ℕ) : ℤ) - 1) = -1 := by norm_num
    rw [e1, e2, this]
  simp only [h2]
  set a := eFr X.F (((0 : ℕ) : ℤ) - 1) with ha
  symm
  refine Finset.prod_bij (fun x _ => posOf n' x) ?_ ?_ ?_ ?_
  · intro x hx
    exact (Finset.mem_filter.mp hx).2
  · intro x hx y hy hxy
    exact posOf_injOn a (Finset.mem_Ioc.mp (Finset.mem_filter.mp hx).1) (Finset.mem_Ioc.mp (Finset.mem_filter.mp hy).1) hxy
  · intro t ht
    have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
    have b0 := Int.emod_nonneg ((t.val : ℤ) - (a + 1)) hn.ne'
    have b1 := Int.emod_lt_of_pos ((t.val : ℤ) - (a + 1)) hn
    have hpos : posOf n' (a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ)) = t := by
      have e : a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ) =
          (t.val : ℤ) + (-(((t.val : ℤ) - (a + 1)) / (n' : ℤ))) * n' := by
        have := Int.emod_add_mul_ediv ((t.val : ℤ) - (a + 1)) (n' : ℤ)
        linarith
      rw [e, sum_posOf_per, posOf_natCast]
    refine ⟨a + 1 + ((t.val : ℤ) - (a + 1)) % (n' : ℤ), ?_, hpos⟩
    rw [Finset.mem_filter, Finset.mem_Ioc, hpos]
    exact ⟨⟨by omega, by omega⟩, ht⟩
  · intro x _
    rfl

theorem sum_LLsub (hV : X.F.Valid L₁ N₁) (j x : ℤ) (hx : x ∈ X.F.LLset j) : x ∈ X.toLate j ∧ x < X.F.fr j 0 := by
  classical
  unfold Frames.LLset at hx
  rw [Finset.mem_filter, Finset.mem_Ioo] at hx
  refine ⟨(mem_late_iff X hV j x).mpr ⟨⟨hx.1.1, ?_⟩, hx.2⟩, hx.1.2⟩
  exact hx.1.2.le.trans (fr_zero_le_eFr hV j)

theorem sum_frlate (hV : X.F.Valid L₁ N₁) (j : ℤ) (i : Fin r) : X.F.fr j i.val ∈ X.toLate j := by
  refine (mem_late_iff X hV j _).mpr ⟨⟨?_, ?_⟩, (hV.2.2.2.2.1 j i.val i.isLt).1⟩
  · have h1 := hV.2.2.2.1 (j - 1)
    rw [sub_add_cancel] at h1
    exact lt_of_lt_of_le h1 (fr_zero_le hV j i.val i.isLt)
  · exact _root_.Formalism.MainNotions.SelectionLemmas.Pf.bk_fr_le hV j i.val (r - 1) (by have := i.isLt; omega) (Nat.sub_lt (NeZero.pos r) Nat.one_pos)

theorem sum_split (hV : X.F.Valid L₁ N₁) (j : ℤ) (ψ : ℤ → ℝ) :
    ∏ x ∈ X.toLate j, ψ x = (∏ x ∈ X.F.LLset j, ψ x) * ∏ i : Fin r, ψ (X.F.fr j i.val) := by
  classical
  have hinj : Function.Injective (fun i : Fin r => X.F.fr j i.val) := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
    · exact absurd hab (ne_of_lt (_root_.Formalism.MainNotions.SelectionLemmas.Pf.bk_fr_lt hV j a.val b.val h b.isLt))
    · exact absurd hab.symm (ne_of_lt (_root_.Formalism.MainNotions.SelectionLemmas.Pf.bk_fr_lt hV j b.val a.val h a.isLt))
  have hU : X.toLate j = X.F.LLset j ∪ Finset.univ.image (fun i : Fin r => X.F.fr j i.val) := by
    ext x
    rw [Finset.mem_union, Finset.mem_image]
    constructor
    · intro hx
      have a1 := (mem_late_iff X hV j x).mp hx
      by_cases h0 : x < X.F.fr j 0
      · left
        unfold Frames.LLset
        rw [Finset.mem_filter, Finset.mem_Ioo]
        exact ⟨⟨a1.1.1, h0⟩, a1.2⟩
      · right
        obtain ⟨i, hi, rfl⟩ := comb_frame_top X.F hV j x a1.2 (not_lt.mp h0) (r - 1)
          (Nat.sub_lt (NeZero.pos r) Nat.one_pos) a1.1.2
        exact ⟨⟨i, hi⟩, Finset.mem_univ _, rfl⟩
    · rintro (hx | ⟨i, -, rfl⟩)
      · exact (sum_LLsub X hV j x hx).1
      · exact sum_frlate X hV j i
  have hdisj : Disjoint (X.F.LLset j) (Finset.univ.image (fun i : Fin r => X.F.fr j i.val)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx'
    have := (sum_LLsub X hV j _ hx).2
    have := fr_zero_le hV j i.val i.isLt
    omega
  rw [hU, Finset.prod_union hdisj, Finset.prod_image (fun a _ b _ h => hinj h)]

theorem J_le_card_TT_of_valid (hV : X.F.Valid L₁ N₁) : X.F.J ≤ X.F.TT.card := by
  classical
  refine le_trans ?_ (sum_card_nonW hV)
  calc X.F.J = ∑ _j ∈ Finset.range X.F.J, 1 := by simp
    _ ≤ _ := Finset.sum_le_sum fun j _ => Finset.card_pos.mpr
      ⟨X.F.fr (j : ℤ) (⟨0, NeZero.pos r⟩ : Fin r).val, sum_frlate X hV (j : ℤ) ⟨0, NeZero.pos r⟩⟩

end GeoX
end

section
open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

def sumEta (r : ℕ) (Y : ℝ) : ℝ := (1 - 5 / Y) * (1 - 1 / Y) * (1 - (r : ℝ) / (2 * Y))

theorem sum_total_loss (r J N : ℕ) (k Y A : ℝ) (hr : 2 ≤ r) (hk : 5 ≤ k) (hY : 1 ≤ Y) (hJN : J ≤ N) (hN : 1 ≤ N)
    (hA : 1 - 1 / (32 * Y) ≤ A) (hA1 : A ≤ 1) (hlt : 0 < 1 - 1 * (N : ℝ) * (r : ℝ) ^ 2 * k / Y) :
    0 ≤ 1 - 5 / Y ∧ 0 ≤ 1 - 1 / Y ∧ 0 ≤ 1 - (r : ℝ) / (2 * Y) ∧ 1 - 5 / Y ≤ 1 ∧ 1 - 1 / Y ≤ 1 ∧
      1 - (r : ℝ) / (2 * Y) ≤ 1 ∧
      1 - 1 * (N : ℝ) * (r : ℝ) ^ 2 * k / Y ≤ A ^ J * sumEta r Y ^ N := by
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set u := 1 / Y with hu
  have hu0 : 0 < u := by positivity
  have e1 : 1 * (N : ℝ) * (r : ℝ) ^ 2 * k / Y = N * ((r : ℝ) ^ 2 * k * u) := by rw [hu]; ring
  have e5 : 5 / Y = 5 * u := by rw [hu]; ring
  have er : (r : ℝ) / (2 * Y) = (r : ℝ) / 2 * u := by rw [hu]; field_simp
  have e32 : 1 / (32 * Y) = u / 32 := by rw [hu]; field_simp
  rw [e1] at hlt ⊢
  rw [e32] at hA
  unfold sumEta
  rw [e5, er]
  have h1 : (r : ℝ) ^ 2 * k * u < 1 := by nlinarith
  have hr2k : 10 * (r : ℝ) ≤ (r : ℝ) ^ 2 * k := by nlinarith
  have h5 : 5 * u ≤ 1 := by nlinarith
  have h1u : u ≤ 1 := by nlinarith
  have hru : (r : ℝ) / 2 * u ≤ 1 := by nlinarith
  have hru0 : 0 ≤ (r : ℝ) / 2 * u := by positivity
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith, ?_⟩
  have hA0 : 0 ≤ A := by nlinarith
  obtain ⟨s1, p1, q1⟩ := sub_le_mul_one_sub_and_mem_unit_interval (P := 1 - 5 * u) (c := u) (s := 1 - 5 * u) (by linarith) (by linarith) hu0.le h1u le_rfl
  obtain ⟨s2, p2, q2⟩ := sub_le_mul_one_sub_and_mem_unit_interval (c := (r : ℝ) / 2 * u) p1 q1 hru0 hru s1
  set η := (1 - 5 * u) * (1 - u) * (1 - (r : ℝ) / 2 * u) with hη
  have hAη : 1 - (7 + (r : ℝ) / 2) * u ≤ A * η := by
    have : (1 - u / 32) * η ≤ A * η := mul_le_mul_of_nonneg_right hA p2
    nlinarith
  have hε : (7 + (r : ℝ) / 2) * u ≤ (r : ℝ) ^ 2 * k * u := by
    apply mul_le_mul_of_nonneg_right _ hu0.le
    nlinarith
  have hpow : A ^ N ≤ A ^ J := pow_le_pow_of_le_one hA0 hA1 hJN
  have hηN : 0 ≤ η ^ N := pow_nonneg p2 N
  calc 1 - (N : ℝ) * ((r : ℝ) ^ 2 * k * u) ≤ 1 + (N : ℝ) * (-((7 + (r : ℝ) / 2) * u)) := by nlinarith
    _ ≤ (1 + -((7 + (r : ℝ) / 2) * u)) ^ N := one_add_mul_le_pow (by linarith) N
    _ ≤ (A * η) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    _ = A ^ N * η ^ N := mul_pow _ _ _
    _ ≤ A ^ J * η ^ N := mul_le_mul_of_nonneg_right hpow hηN

section Main

variable {n' r : ℕ} [NeZero n'] {X : Dat n' r} {p K : ℕ}

theorem sum_fac_LL (F : SumFacts X p K) (h5 : 0 ≤ 1 - 5 / X.Y) (h1 : 0 ≤ 1 - 1 / X.Y) (h1' : 1 - 1 / X.Y ≤ 1)
    (hr0 : 0 ≤ 1 - (r : ℝ) / (2 * X.Y)) (hr1 : 1 - (r : ℝ) / (2 * X.Y) ≤ 1) (t : Fin n') (ht : t ∈ X.F.TT) :
    sumEta r X.Y * sumBin r K (X.deg t) ≤ sumBin r K (X.a' p K t) := by
  refine le_trans ?_ (F.compA t ht)
  have hb : 0 ≤ sumBin r K (X.deg t) := zero_le_one.trans (sum_one_le_bin _ _ _)
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ hb
  unfold sumEta
  have : (1 - 5 / X.Y) * (1 - 1 / X.Y) ≤ 1 - 5 / X.Y := by nlinarith
  nlinarith [mul_nonneg h5 h1]

theorem sum_fac_fr (F : SumFacts X p K) (hr : 0 < r) (h1 : 0 ≤ 1 - 1 / X.Y)
    (hr0 : 0 ≤ 1 - (r : ℝ) / (2 * X.Y)) (j : ℤ) (i : Fin r) :
    sumEta r X.Y * sumBin r K (X.deg (posOf n' (X.F.fr j i.val))) ≤
      sumBin r K ((X.Bw p K (j + 1) (X.F.fr j i.val) - (X.m0 K : ℤ)).toNat) *
        (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) *
        ((X.Pz p K j (X.F.fr j i.val) : ℕ) : ℝ) ^ (r + K - 1) * ((X.Qc p K j : ℕ) : ℝ) ^ K := by
  have ht := (sum_late_mem (F.frlate j i)).2.2.2
  have hA := F.compA _ ht
  have hW := F.compW j i
  set t := posOf n' (X.F.fr j i.val)
  set B := sumBin r K ((X.Bw p K (j + 1) (X.F.fr j i.val) - (X.m0 K : ℤ)).toNat)
  set Qr := ((X.Qc p K j : ℕ) : ℝ)
  set Pr := ((X.Pz p K j (X.F.fr j i.val) : ℕ) : ℝ)
  have hmax : max 0 (1 - (r : ℝ) / (2 * X.Y)) = 1 - (r : ℝ) / (2 * X.Y) := max_eq_right hr0
  have hexp : r + K - 1 = (r - 1) + K := by omega
  have e : B * (Qr ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) * Pr ^ (r + K - 1) * Qr ^ K =
      (1 - (r : ℝ) / (2 * X.Y)) * ((Pr * Qr) ^ (r + K - 1) * B) := by
    rw [hmax, mul_pow, hexp, pow_add Qr]
    ring
  rw [e]
  have hW' : sumBin r K (X.a' p K t) * (1 - 1 / X.Y) ≤ (Pr * Qr) ^ (r + K - 1) * B := by
    have : (((X.Pz p K j (X.F.fr j i.val) * X.Qc p K j : ℕ) : ℝ)) = Pr * Qr := by push_cast; rfl
    rw [← this]; exact hW
  have h2 : sumBin r K (X.deg t) * (1 - 5 / X.Y) * (1 - 1 / X.Y) ≤ (Pr * Qr) ^ (r + K - 1) * B :=
    (mul_le_mul_of_nonneg_right hA h1).trans hW'
  have h3 := mul_le_mul_of_nonneg_left h2 hr0
  refine le_trans (le_of_eq ?_) h3
  unfold sumEta
  ring

theorem restSum_of (hF : ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → (1088 : ℝ) ≤ X.CLa → (1088 : ℝ) ≤ X.Ck → SumFacts X p K ∧ 1 ≤ X.Ns) : RestSum 1088 1 := by
  classical
  intro p n' r K _ _ _ X hX hLa hk G hG0 hGdep hGsum
  obtain ⟨F, hNs⟩ := hF p n' r K X hX hLa hk
  have hp : 0 < p := hX.prime.pos
  have hr : 0 < r := by have := hX.r2; omega
  have hRHS0 : 0 ≤ ∑ la ∈ X.LA p K, ∑ e ∈ X.EE p K la, ∏ j : Fin X.F.J,
      G (j.val : ℤ) (X.bfam p K la e (j.val : ℤ)) :=
    Finset.sum_nonneg fun la _ => Finset.sum_nonneg fun e _ => Finset.prod_nonneg fun j _ => hG0 _ _
  have hq0 : (0 : ℝ) < ((p : ℝ) ^ n') ^ (r * K) := by positivity
  rw [zpow_neg, zpow_natCast, inv_mul_le_iff₀ hq0]
  have hbd : X.bound K 1 = (1 - 1 * (X.F.TT.card : ℝ) * (r : ℝ) ^ 2 * Dat.k (r := r) K / X.Y) *
      ∏ t ∈ X.F.TT, sumBin r K (X.deg t) := rfl
  have hprod0 : 0 ≤ ∏ t ∈ X.F.TT, sumBin r K (X.deg t) :=
    Finset.prod_nonneg fun t _ => zero_le_one.trans (sum_one_le_bin _ _ _)
  rcases le_or_gt (1 - 1 * (X.F.TT.card : ℝ) * (r : ℝ) ^ 2 * Dat.k (r := r) K / X.Y) 0 with hb | hb
  · rw [hbd]
    have h1 := mul_nonneg (neg_nonneg.mpr hb) hprod0
    have h2 := mul_nonneg hq0.le hRHS0
    nlinarith

  obtain ⟨hA0l, hA00⟩ := first_sum_factor_bounds hX.Y1 F.a32 hNs
  have hA01 : X.firstSumFactor ≤ 1 := by
    unfold Dat.firstSumFactor
    have : 0 ≤ 1 / X.a ^ (X.Ns ^ 2) := by
      have : 0 ≤ X.a := by have := F.a32; have := hX.Y1; linarith
      positivity
    linarith
  have hJ1 : 1 ≤ X.F.J := hX.valid.1
  have hk5 : (5 : ℝ) ≤ Dat.k (r := r) K := by
    unfold Dat.k
    have := hX.NsK; have := hX.r2
    exact_mod_cast (by omega : 5 ≤ r + K)
  obtain ⟨h5, h1, hr0, -, h1', hr1, htot⟩ := sum_total_loss r X.F.J X.F.TT.card (Dat.k (r := r) K) X.Y X.firstSumFactor hX.r2 hk5 hX.Y1
    F.JN (hJ1.trans F.JN) hA0l hA01 hb

  have hTf0 : ∀ j, 0 ≤ X.sumTf p K j := fun j => by
    unfold Dat.sumTf
    exact pow_nonneg (mul_nonneg (by positivity) (le_max_left _ _)) _
  have hWf0 : ∀ j, 0 ≤ X.sumWf p K j := fun j =>
    Finset.prod_nonneg fun i _ => zero_le_one.trans (sum_one_le_bin _ _ _)
  have hseg0 : ∀ j b, 0 ≤ X.segBound p K j b := fun j b => by
    rw [Dat.sum_segBound_eq]
    exact mul_nonneg (mul_nonneg (mul_nonneg hA00 (hWf0 j)) (hTf0 j))
      (Finset.prod_nonneg fun x _ => zero_le_one.trans (sum_one_le_bin _ _ _))
  have step1 : ∀ la ∈ X.LA p K, ∏ j : Fin X.F.J, X.segBound p K (j.val : ℤ) (X.nz p K la (j.val : ℤ)) ≤
      ∑ e ∈ X.EE p K la, ∏ j : Fin X.F.J, G (j.val : ℤ) (X.bfam p K la e (j.val : ℤ)) := by
    intro la hla
    have e1 : ∀ e : Fin X.F.J → Fin r → ℕ, ∏ j : Fin X.F.J, G (j.val : ℤ) (X.bfam p K la e (j.val : ℤ)) =
        ∏ j : Fin X.F.J, G (j.val : ℤ) (X.setTau (j.val : ℤ) (X.nz p K la (j.val : ℤ)) (e j)) :=
      fun e => Finset.prod_congr rfl fun j _ => hGdep _ _ _ (sum_bfam_late la e j)
    rw [Finset.sum_congr rfl fun e _ => e1 e]
    have e2 := Finset.prod_univ_sum (fun j : Fin X.F.J => X.sumTset p K la (j.val : ℤ))
      (fun j ej => G (j.val : ℤ) (X.setTau (j.val : ℤ) (X.nz p K la (j.val : ℤ)) ej))
    have e3 : X.EE p K la = Fintype.piFinset (fun j : Fin X.F.J => X.sumTset p K la (j.val : ℤ)) := by
      unfold Dat.EE Dat.sumTset
      congr
    rw [e3, ← e2]
    refine Finset.prod_le_prod₀ (fun j _ => hseg0 _ _) fun j _ => ?_
    exact hGsum (j.val : ℤ) _ (family_degrees_admissible hr hp (fun j x hx => (F.LLsub j x hx).1) la hla _)
      (fun i => X.nz p K la (j.val : ℤ) (X.F.fr (j.val : ℤ) i.val))
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (Finset.sum_le_sum step1) hq0.le)

  have step2 : ∑ la ∈ X.LA p K, ∏ j : Fin X.F.J, X.segBound p K (j.val : ℤ) (X.nz p K la (j.val : ℤ)) =
      (∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * X.sumWf p K (j : ℤ) * X.sumTf p K (j : ℤ))) * ∏ t : Fin n', X.sumSt p K t := by
    rw [← sum_LA, Finset.mul_sum]
    refine Finset.sum_congr rfl fun la _ => ?_
    rw [← Fin.prod_univ_eq_prod_range (fun j : ℕ => X.firstSumFactor * X.sumWf p K (j : ℤ) * X.sumTf p K (j : ℤ)),
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => Dat.sum_segBound_eq X p K _ _
  rw [step2]

  have step3 : ∏ j ∈ Finset.range X.F.J, ((∏ x ∈ X.F.LLset (j : ℤ), sumBin r K (X.a' p K (posOf n' x))) *
      ∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1)) ≤ ∏ t : Fin n', X.sumSt p K t := by
    have hs := Finset.prod_sdiff (f := fun t => X.sumSt p K t) (Finset.subset_univ X.F.TT)
    rw [← hs, F.tiling]
    have hc : (1 : ℝ) ≤ ∏ t ∈ Finset.univ \ X.F.TT, X.sumSt p K t :=
      sum_one_le_prod _ _ fun t ht => sum_St_nontop t (Finset.mem_sdiff.mp ht).2
    have hm : ∏ j ∈ Finset.range X.F.J, ((∏ x ∈ X.F.LLset (j : ℤ), sumBin r K (X.a' p K (posOf n' x))) *
        ∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1)) ≤
        ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), X.sumSt p K (posOf n' x) := by
      refine Finset.prod_le_prod₀ (fun j _ => mul_nonneg
        (Finset.prod_nonneg fun x _ => zero_le_one.trans (sum_one_le_bin _ _ _))
        (Finset.prod_nonneg fun i _ => by positivity)) fun j hj => ?_
      rw [F.split (j : ℤ) (fun x => X.sumSt p K (posOf n' x))]
      refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun i _ => by positivity)
        (Finset.prod_nonneg fun x _ => sum_St_nonneg _)
      · exact Finset.prod_le_prod₀ (fun x _ => zero_le_one.trans (sum_one_le_bin _ _ _)) fun x hx =>
          sum_St_LL F hr hp ⟨j, Finset.mem_range.mp hj⟩ hx
      · exact Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => sum_St_fr F hr hp (j : ℤ) i
    have hnn : 0 ≤ ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), X.sumSt p K (posOf n' x) :=
      Finset.prod_nonneg fun j _ => Finset.prod_nonneg fun x _ => sum_St_nonneg _
    nlinarith
  have hC0 : 0 ≤ ∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * X.sumWf p K (j : ℤ) * X.sumTf p K (j : ℤ)) :=
    Finset.prod_nonneg fun j _ => mul_nonneg (mul_nonneg hA00 (hWf0 _)) (hTf0 _)
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left step3 hC0) hq0.le)

  have hW : ∏ j ∈ Finset.range X.F.J, X.sumWf p K (j : ℤ) = ∏ j ∈ Finset.range X.F.J, X.sumWf p K ((j : ℤ) + 1) :=
    (prod_range_shift_of_periodic (fun j => X.sumWf p K j) X.F.J hJ1 (fun j => by
      unfold Dat.sumWf
      exact Finset.prod_congr rfl fun i _ => by rw [F.perW j i])).symm
  have hQ : ((p : ℝ) ^ n') ^ (r * K) = ∏ j ∈ Finset.range X.F.J, (((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ K) ^ r := by
    have := F.prodQ
    have h' : (p : ℝ) ^ n' = ∏ j ∈ Finset.range X.F.J, ((X.Qc p K (j : ℤ) : ℕ) : ℝ) := by
      rw [← Nat.cast_pow, ← this]; push_cast; rfl
    rw [h', ← Finset.prod_pow]
    exact Finset.prod_congr rfl fun j _ => by rw [← pow_mul, mul_comm]
  have regroup : ((p : ℝ) ^ n') ^ (r * K) * ((∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * X.sumWf p K (j : ℤ) * X.sumTf p K (j : ℤ))) *
      ∏ j ∈ Finset.range X.F.J, ((∏ x ∈ X.F.LLset (j : ℤ), sumBin r K (X.a' p K (posOf n' x))) *
      ∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1))) =
      ∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * ((∏ x ∈ X.F.LLset (j : ℤ), sumBin r K (X.a' p K (posOf n' x))) *
        (X.sumWf p K ((j : ℤ) + 1) * X.sumTf p K (j : ℤ) *
          (∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1)) *
          (((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ K) ^ r))) := by
    rw [hQ]
    simp only [Finset.prod_mul_distrib]
    rw [hW]
    ring
  rw [regroup, hbd]
  refine le_trans (mul_le_mul_of_nonneg_right htot hprod0) ?_
  have hfin : X.firstSumFactor ^ X.F.J * sumEta r X.Y ^ X.F.TT.card * ∏ t ∈ X.F.TT, sumBin r K (X.deg t) =
      ∏ j ∈ Finset.range X.F.J, (X.firstSumFactor * ∏ x ∈ X.toLate (j : ℤ), (sumEta r X.Y * sumBin r K (X.deg (posOf n' x)))) := by
    rw [Finset.prod_mul_distrib, ← F.tiling (fun t => sumEta r X.Y * sumBin r K (X.deg t)), Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_const, Finset.card_range]
    ring
  rw [hfin]
  have heta0 : 0 ≤ sumEta r X.Y := mul_nonneg (mul_nonneg h5 h1) hr0
  refine Finset.prod_le_prod₀ (fun j _ => mul_nonneg hA00 (Finset.prod_nonneg fun x _ =>
    mul_nonneg heta0 (zero_le_one.trans (sum_one_le_bin _ _ _)))) fun j _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ hA00
  rw [F.split (j : ℤ) (fun x => sumEta r X.Y * sumBin r K (X.deg (posOf n' x)))]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun i _ => mul_nonneg heta0 (zero_le_one.trans (sum_one_le_bin _ _ _)))
    (Finset.prod_nonneg fun x _ => zero_le_one.trans (sum_one_le_bin _ _ _))
  · exact Finset.prod_le_prod₀ (fun x _ => mul_nonneg heta0 (zero_le_one.trans (sum_one_le_bin _ _ _))) fun x hx =>
      sum_fac_LL F h5 h1 h1' hr0 hr1 _ (sum_late_mem (F.LLsub _ _ hx).1).2.2.2
  · have e : X.sumWf p K ((j : ℤ) + 1) * X.sumTf p K (j : ℤ) *
        (∏ i : Fin r, ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1)) *
        (((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ K) ^ r =
        ∏ i : Fin r, (sumBin r K ((X.Bw p K ((j : ℤ) + 1) (X.F.fr (j : ℤ) i.val) - (X.m0 K : ℤ)).toNat) *
          (((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) *
          ((X.Pz p K (j : ℤ) (X.F.fr (j : ℤ) i.val) : ℕ) : ℝ) ^ (r + K - 1) * ((X.Qc p K (j : ℤ) : ℕ) : ℝ) ^ K) := by
      simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      unfold Dat.sumWf Dat.sumTf
      simp only [add_sub_cancel_right, mul_pow]
    rw [e]
    exact Finset.prod_le_prod₀ (fun i _ => mul_nonneg heta0 (zero_le_one.trans (sum_one_le_bin _ _ _))) fun i _ =>
      sum_fac_fr F hr h1 hr0 (j : ℤ) i

end Main
end

section
open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Num

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem Rj_add_first_frame_gap_le_last_frame_gap_add_Rj_succ (hX : X.Hyp p K) (j : ℤ) :
    (X.Rj p K j : ℤ) + (X.F.fr j 0 - X.F.fr (j - 1) 0) ≤
      X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + X.Rj p K (j + 1) := by
  have B := basics hX
  have h1 := pow_Rj_le hX j
  have h2 := lt_pow_Rj hX (j + 1)
  have d1 := den_pos hX j
  have d2 := den_pos hX (j + 1)
  unfold Tj at h1 h2
  rw [le_div_iff₀ d1] at h1
  rw [div_lt_iff₀ d2] at h2
  simp only [add_sub_cancel_right] at h2
  have hc0 : 0 < 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
    have h2 : (0 : ℝ) < X.Y := by linarith [B.Y1]
    have h3 : (0 : ℝ) < Dat.k (r := r) K := by linarith [B.k5]
    have h4 : (0 : ℝ) < X.Ns := by linarith [B.Ns1]
    positivity
  have h3 : (p : ℝ) ^ (X.Rj p K j + X.F.dist j (X.F.fr (j - 1) 0)) <
      (p : ℝ) ^ (X.Rj p K (j + 1) + 1 + X.F.dist (j + 1) (X.F.fr j 0)) := by
    rw [pow_add, pow_add _ (X.Rj p K (j + 1) + 1)]
    refine lt_of_mul_lt_mul_right ?_ hc0.le
    calc (p : ℝ) ^ X.Rj p K j * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0) * (8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ))
        = (p : ℝ) ^ X.Rj p K j * (8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0)) := by
          ring
      _ ≤ X.a := h1
      _ < _ := h2
      _ = _ := by ring
  have h4 := (pow_lt_pow_iff_right₀ B.p1).mp h3
  have b1 := mem_letters_bounds (reflection_mem_Glev_castSucc hX.valid j)
  have b2 := mem_letters_bounds (reflection_mem_Glev_castSucc hX.valid (j + 1))
  simp only [add_sub_cancel_right] at b2
  unfold Frames.dist at h4
  omega

theorem frame_zero_strict_mono (hX : X.Hyp p K) (j : ℤ) : X.F.fr (j - 1) 0 < X.F.fr j 0 := by
  have h1 := hX.valid.2.2.2.1 (j - 1)
  rw [sub_add_cancel] at h1
  exact lt_of_le_of_lt (fr_zero_le_eFr hX.valid (j - 1)) h1

theorem sum_PzQc (hX : X.Hyp p K) (j v : ℤ) (hv : v ≤ X.F.fr j (r - 1)) :
    X.Pz p K j v * X.Qc p K j = p ^ (X.F.dist (j + 1) v + X.Rj p K (j + 1)) := by
  have h := Rj_add_first_frame_gap_le_last_frame_gap_add_Rj_succ hX j
  have h0 := frame_zero_strict_mono hX j
  have hm : X.F.fr j (r - 1) < X.F.fr (j + 1) (r - 1) := eFr_strictMono hX.valid (by omega : j < j + 1)
  unfold Dat.Pz Dat.Qc
  rw [← pow_add]
  congr 1
  unfold Frames.dist
  omega

theorem sum_prodQ (hX : X.Hyp p K) : ∏ j ∈ Finset.range X.F.J, X.Qc p K (j : ℤ) = p ^ n' := by
  unfold Dat.Qc
  rw [Finset.prod_pow_eq_pow_sum]
  congr 1
  have key : ((∑ j ∈ Finset.range X.F.J, (X.F.fr ((j : ℤ) + 1) (r - 1) - X.F.fr (j : ℤ) (r - 1) +
      (X.Rj p K ((j : ℤ) + 1) : ℤ) - (X.Rj p K (j : ℤ) : ℤ)).toNat : ℕ) : ℤ) = n' := by
    push_cast
    have e : ∀ j ∈ Finset.range X.F.J, (((X.F.fr ((j : ℤ) + 1) (r - 1) - X.F.fr (j : ℤ) (r - 1) +
        (X.Rj p K ((j : ℤ) + 1) : ℤ) - (X.Rj p K (j : ℤ) : ℤ)).toNat : ℕ) : ℤ) =
        (fun i : ℕ => X.F.fr (i : ℤ) (r - 1) + (X.Rj p K (i : ℤ) : ℤ)) (j + 1) -
          (fun i : ℕ => X.F.fr (i : ℤ) (r - 1) + (X.Rj p K (i : ℤ) : ℤ)) j := by
      intro j _
      have h := Rj_add_first_frame_gap_le_last_frame_gap_add_Rj_succ hX (j : ℤ)
      have h0 := frame_zero_strict_mono hX (j : ℤ)
      rw [Int.toNat_of_nonneg (by omega)]
      push_cast
      ring
    have tel := Finset.sum_range_sub (fun i : ℕ => X.F.fr (i : ℤ) (r - 1) + (X.Rj p K (i : ℤ) : ℤ)) X.F.J
    rw [Finset.sum_congr rfl e]
    refine tel.trans ?_
    have p1 := fr_add_mul_period hX.valid 0 (r - 1) 1
    have p2 := sum_Rj_per X p K hX.valid 0 1
    simp only [zero_add, one_mul] at p1 p2
    rw [p1, p2]
    push_cast
    ring
  exact_mod_cast key

theorem thirty_two_Y_le_a (hX : X.Hyp p K) : 32 * X.Y ≤ X.a := by
  have B := basics hX
  refine le_trans ?_ (l42b hX 0 _ (reflection_mem_Glev_castSucc hX.valid 0))
  have h1 : (1 : ℝ) ≤ (p : ℝ) ^ (X.F.dist 0 (X.F.fr (0 - 1) 0) + X.Rj p K 0) := one_le_pow₀ B.p1.le
  have hk2 : (25 : ℝ) ≤ Dat.k (r := r) K ^ 2 := by linarith [pow_le_pow_left₀ (by norm_num) B.k5 2]
  have hY0 : (0 : ℝ) < X.Y := by linarith [B.Y1]
  have h2 : 32 * X.Y ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 := by linarith [mul_le_mul_of_nonneg_left hk2 hY0.le]
  have h3 : 8 * X.Y * Dat.k (r := r) K ^ 2 ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) :=
    le_mul_of_one_le_right (by positivity) B.Ns1
  have h4 : 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) ≤
      8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist 0 (X.F.fr (0 - 1) 0) + X.Rj p K 0) :=
    le_mul_of_one_le_right (by have := B.Ns1; positivity) h1
  linarith

theorem sum_aP (hX : X.Hyp p K) (hLa : (1088 : ℝ) ≤ X.CLa) (hk : (1088 : ℝ) ≤ X.Ck) (j y : ℤ)
    (hy : y ∈ X.F.letters j) :
    (36 / 5 : ℝ) * (X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j y + X.Rj p K j)) ≤
      (X.a' p K (posOf n' y) : ℝ) := by
  have h41 := (top_count_lower_bounds_of_occurrence 1088 (by norm_num) top_occurs_in_at_most_two_segments p n' r K X hX hLa hk).1 _ (mem_letters_bounds hy).2.2
  have hd := (hX.degs _ (mem_letters_bounds hy).2.2).1
  have h2 := l42b hX j y hy
  linarith

theorem sum_kP (hX : X.Hyp p K) (hLa : (1088 : ℝ) ≤ X.CLa) (hk : (1088 : ℝ) ≤ X.Ck) (j x : ℤ)
    (hx : x ∈ X.toLate j) : (r + K) * X.Pz p K j x ≤ X.a' p K (posOf n' x) := by
  have B := basics hX
  have h := sum_aP hX hLa hk j x (sum_late_mem hx).1
  have hP : (0 : ℝ) < (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
    have : (0 : ℝ) < p := by linarith [B.p1]
    positivity
  have h1 : Dat.k (r := r) K ≤ X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
    have hk0 : (0 : ℝ) < Dat.k (r := r) K := by linarith [B.k5]
    have a1 : Dat.k (r := r) K ≤ Dat.k (r := r) K ^ 2 := le_self_pow₀ (by linarith [B.k5]) two_ne_zero
    have a2 : Dat.k (r := r) K ^ 2 ≤ X.Y * Dat.k (r := r) K ^ 2 := le_mul_of_one_le_left (by positivity) B.Y1
    have a3 : X.Y * Dat.k (r := r) K ^ 2 ≤ X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) :=
      le_mul_of_one_le_right (by have := B.Y1; positivity) B.Ns1
    linarith
  have h2 := mul_le_mul_of_nonneg_right h1 hP.le
  have h3 : Dat.k (r := r) K * (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) ≤ (X.a' p K (posOf n' x) : ℝ) := by
    have : 0 ≤ X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := by
      have := B.Y1; have := B.Ns1; positivity
    linarith
  unfold Dat.k at h3
  unfold Dat.Pz
  exact_mod_cast h3

theorem sumBin_eq (n : ℕ) : sumBin r K n = (((n + (r + K - 1)).choose (r + K - 1) : ℕ) : ℝ) := by
  unfold sumBin
  have : n + (r + K) - 1 = n + (r + K - 1) := Nat.add_sub_assoc (by have := NeZero.pos r; omega) n
  rw [this]

theorem sum_M_le : ((r + K - 1 : ℕ) : ℝ) ≤ Dat.k (r := r) K := by
  unfold Dat.k
  exact_mod_cast Nat.sub_le _ _

theorem sum_compA (hX : X.Hyp p K) (hLa : (1088 : ℝ) ≤ X.CLa) (hk : (1088 : ℝ) ≤ X.Ck) (t : Fin n')
    (ht : t ∈ X.F.TT) : sumBin r K (X.deg t) * (1 - 5 / X.Y) ≤ sumBin r K (X.a' p K t) := by
  have B := basics hX
  have hk0 : (0 : ℝ) < Dat.k (r := r) K := by linarith [B.k5]
  have hY0 : (0 : ℝ) < X.Y := by linarith [B.Y1]
  have hu : 0 < Dat.k (r := r) K * X.Y := by positivity
  have ha0 : 0 ≤ X.a := by have := thirty_two_Y_le_a hX; linarith

  have hE0 : (X.E₀ : ℝ) * (Dat.k (r := r) K * X.Y) ≤ X.a := by
    have h1 := Tj_ge hX 0
    have d1 := den_pos hX 0
    unfold Tj at h1
    rw [le_div_iff₀ d1] at h1
    have hp1 : (1 : ℝ) ≤ (p : ℝ) ^ X.F.dist 0 (X.F.fr (0 - 1) 0) := one_le_pow₀ B.p1.le
    have w1 : Dat.k (r := r) K * X.Y ≤
        8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist 0 (X.F.fr (0 - 1) 0) := by
      have a1 : Dat.k (r := r) K * X.Y ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 := by linarith [mul_le_mul_of_nonneg_left (le_self_pow₀ (show (1 : ℝ) ≤ Dat.k (r := r) K by linarith [B.k5]) two_ne_zero) hY0.le]
      have a2 : 8 * X.Y * Dat.k (r := r) K ^ 2 ≤ 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) :=
        le_mul_of_one_le_right (by positivity) B.Ns1
      have a3 : 8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) ≤
          8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist 0 (X.F.fr (0 - 1) 0) :=
        le_mul_of_one_le_right (by have := B.Ns1; positivity) hp1
      linarith
    have hE : (X.E₀ : ℝ) ≤ 4 * (p : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1) := by
      linarith [le_mul_of_one_le_left (show (0 : ℝ) ≤ (X.E₀ : ℝ) + X.mStar + 1 by linarith) (show (1 : ℝ) ≤ p by linarith [B.p1])]
    calc (X.E₀ : ℝ) * (Dat.k (r := r) K * X.Y)
        ≤ (4 * (p : ℝ) * ((X.E₀ : ℝ) + X.mStar + 1)) *
          (8 * X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist 0 (X.F.fr (0 - 1) 0)) :=
          mul_le_mul hE w1 hu.le (le_trans (Nat.cast_nonneg _) hE)
      _ ≤ X.a := h1

  have hEt : (X.Et p K t : ℝ) * (Dat.k (r := r) K * X.Y) ≤ 4 * X.a := by
    have h1 := Et_le top_occurs_in_at_most_two_segments hX t
    rw [le_div_iff₀ (by positivity)] at h1
    have hNk : (X.Ns : ℝ) ≤ Dat.k (r := r) K := by
      unfold Dat.k
      have := hX.NsK
      exact_mod_cast (by omega : X.Ns ≤ r + K)
    have h2 : 4 * (X.Ns : ℝ) * X.a ≤ 4 * Dat.k (r := r) K * X.a := by linarith [mul_le_mul_of_nonneg_right hNk ha0]
    have h3 : Dat.k (r := r) K * ((X.Et p K t : ℝ) * (Dat.k (r := r) K * X.Y)) ≤ Dat.k (r := r) K * (4 * X.a) := by
      linarith
    exact le_of_mul_le_mul_left h3 hk0
  have hdeg := (hX.degs t ht).1
  have hnat : X.deg t ≤ X.a' p K t + X.E' t + X.Et p K t := by
    unfold Dat.a' Dat.d
    rw [ite_eq_left ht]
    omega
  have hnat' : (X.deg t : ℝ) ≤ (X.a' p K t : ℝ) + X.E' t + X.Et p K t := by exact_mod_cast hnat
  have hE' : (X.E' t : ℝ) ≤ X.E₀ := by exact_mod_cast hX.E'le t ht
  set θ : ℝ := 5 / (Dat.k (r := r) K * X.Y) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hu]
    linarith [B.k5, hLa, hk, le_mul_of_one_le_right (show (0 : ℝ) ≤ Dat.k (r := r) K by linarith [B.k5]) B.Y1]
  have key : (X.E₀ : ℝ) + X.Et p K t ≤ θ * X.deg t := by
    rw [hθ, div_mul_eq_mul_div, le_div_iff₀ hu]
    linarith
  have hcmp := choose_add_mul_one_sub_le_pow_mul_choose_add (X.a' p K t) (X.deg t) (r + K - 1) 1 θ hθ1 (fun l _ => by
    have hl : (0 : ℝ) ≤ θ * (1 + l) := by positivity
    calc ((X.deg t : ℝ) + 1 + l) * (1 - θ) = (X.deg t : ℝ) + 1 + l - θ * X.deg t - θ * (1 + l) := by ring
      _ ≤ 1 * ((X.a' p K t : ℝ) + 1 + l) := by linarith)
  rw [one_pow, one_mul] at hcmp
  rw [sumBin_eq, sumBin_eq]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) hcmp
  have hM := sum_M_le (r := r) (K := K)
  have : ((r + K - 1 : ℕ) : ℝ) * θ ≤ 5 / X.Y := by
    calc ((r + K - 1 : ℕ) : ℝ) * θ ≤ Dat.k (r := r) K * θ := mul_le_mul_of_nonneg_right hM hθ0
      _ = 5 / X.Y := by rw [hθ]; field_simp
  linarith

theorem sum_compW (hX : X.Hyp p K) (hLa : (1088 : ℝ) ≤ X.CLa) (hk : (1088 : ℝ) ≤ X.Ck) (j : ℤ) (i : Fin r) :
    sumBin r K (X.a' p K (posOf n' (X.F.fr j i.val))) * (1 - 1 / X.Y) ≤
    (((X.Pz p K j (X.F.fr j i.val) * X.Qc p K j : ℕ) : ℝ)) ^ (r + K - 1) *
      sumBin r K ((X.Bw p K (j + 1) (X.F.fr j i.val) - (X.m0 K : ℤ)).toNat) := by
  classical
  have B := basics hX
  have hk0 : (0 : ℝ) < Dat.k (r := r) K := by linarith [B.k5]
  have hY0 : (0 : ℝ) < X.Y := by linarith [B.Y1]
  have hu : 0 < Dat.k (r := r) K * X.Y := by positivity
  have hrr : r - 1 < r := Nat.sub_lt (NeZero.pos r) Nat.one_pos
  have hvle : X.F.fr j i.val ≤ X.F.fr j (r - 1) := _root_.Formalism.MainNotions.SelectionLemmas.Pf.bk_fr_le hX.valid j i.val (r - 1) (by have := i.isLt; omega) hrr
  have hvlet : X.F.fr j i.val ∈ X.F.letters (j + 1) := by
    unfold Frames.letters
    rw [Finset.mem_filter, Finset.mem_Icc, add_sub_cancel_right]
    refine ⟨⟨fr_zero_le hX.valid j i.val i.isLt, ?_⟩, (hX.valid.2.2.2.2.1 j i.val i.isLt).1⟩
    exact hvle.trans (eFr_strictMono hX.valid (by omega : j < j + 1)).le
  rw [sum_PzQc hX j _ hvle]
  have hn := sum_aP hX hLa hk (j + 1) _ hvlet
  set v := X.F.fr j i.val
  set P' : ℕ := p ^ (X.F.dist (j + 1) v + X.Rj p K (j + 1)) with hP'
  set n : ℕ := X.a' p K (posOf n' v) with hnn
  have hP'0 : 0 < P' := pow_pos hX.prime.pos _
  have hP'r : (0 : ℝ) < (P' : ℝ) := by exact_mod_cast hP'0
  have hP'1 : (1 : ℝ) ≤ (P' : ℝ) := by exact_mod_cast hP'0
  have hn' : (36 / 5 : ℝ) * (X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (P' : ℝ)) ≤ (n : ℝ) := by
    rw [hP']; push_cast; exact hn
  set Bn : ℕ := (X.Bw p K (j + 1) v - (X.m0 K : ℤ)).toNat with hBn
  have hB1 : ((X.Bw p K (j + 1) v - (X.m0 K : ℤ) : ℤ) : ℝ) ≤ (Bn : ℝ) := by
    exact_mod_cast Int.self_le_toNat _
  have hB2 : ((X.Bw p K (j + 1) v - (X.m0 K : ℤ) : ℤ) : ℝ) =
      ((n / P' : ℕ) : ℝ) - (Dat.k (r := r) K + r + 1) - (Dat.k (r := r) K * X.Ns + 1) := by
    have hBw : X.Bw p K (j + 1) v = ((n / P' : ℕ) : ℤ) - ((r + K + r + 1 : ℕ) : ℤ) := rfl
    rw [hBw]
    unfold Dat.m0 Dat.k
    generalize n / P' = q
    push_cast
    ring
  have hdiv := natDiv_gt n P' hP'0
  have hrk := B.rk
  have hc : Dat.k (r := r) K + r + 3 + Dat.k (r := r) K * X.Ns ≤ 4 * (Dat.k (r := r) K * X.Ns) := by
    have : Dat.k (r := r) K ≤ Dat.k (r := r) K * X.Ns := le_mul_of_one_le_right hk0.le B.Ns1
    linarith [B.k5]
  have hPB : (n : ℝ) - 4 * (Dat.k (r := r) K * X.Ns) * P' ≤ (P' : ℝ) * Bn := by
    have h1 : (n : ℝ) / P' - 1 - (Dat.k (r := r) K + r + 1) - (Dat.k (r := r) K * X.Ns + 1) ≤ (Bn : ℝ) := by
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hP'r.le
    have h3 : (P' : ℝ) * ((n : ℝ) / P') = n := by field_simp
    have h4 := mul_le_mul_of_nonneg_right hc hP'r.le
    linarith [hY0]
  set θ : ℝ := 1 / (Dat.k (r := r) K * X.Y) with hθ
  have hθ0 : 0 ≤ θ := by positivity
  have hθ1 : θ ≤ 1 := by
    rw [hθ, div_le_one hu]
    exact one_le_mul_of_one_le_of_one_le (by linarith [B.k5]) B.Y1
  have key : 4 * (Dat.k (r := r) K * X.Ns) * P' ≤ θ * n := by
    rw [hθ, div_mul_eq_mul_div, one_mul, le_div_iff₀ hu]
    have : 4 * (Dat.k (r := r) K * X.Ns) * P' * (Dat.k (r := r) K * X.Y) =
        4 * (X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (P' : ℝ)) := by ring
    rw [this]
    have h0 : 0 ≤ X.Y * Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) * (P' : ℝ) := by
      have := B.Ns1; positivity
    linarith
  have hcmp := choose_add_mul_one_sub_le_pow_mul_choose_add Bn n (r + K - 1) (P' : ℝ) θ hθ1 (fun l _ => by
    have hl : (0 : ℝ) ≤ θ * (1 + l) := by positivity
    have hl2 : (1 : ℝ) + l ≤ (P' : ℝ) * (1 + l) := le_mul_of_one_le_left (by positivity) hP'1
    calc ((n : ℝ) + 1 + l) * (1 - θ) = (n : ℝ) + 1 + l - θ * n - θ * (1 + l) := by ring
      _ ≤ (P' : ℝ) * Bn + (P' : ℝ) * (1 + l) := by linarith
      _ = (P' : ℝ) * ((Bn : ℝ) + 1 + l) := by ring)
  rw [sumBin_eq, sumBin_eq]
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)) hcmp
  have hM := sum_M_le (r := r) (K := K)
  have : ((r + K - 1 : ℕ) : ℝ) * θ ≤ 1 / X.Y := by
    calc ((r + K - 1 : ℕ) : ℝ) * θ ≤ Dat.k (r := r) K * θ := mul_le_mul_of_nonneg_right hM hθ0
      _ = 1 / X.Y := by rw [hθ]; field_simp
  linarith

theorem sum_facts (hX : X.Hyp p K) (hLa : (1088 : ℝ) ≤ X.CLa) (hk : (1088 : ℝ) ≤ X.Ck) : SumFacts X p K := {
  tiling := prod_tiling X hX.valid
  split := sum_split X hX.valid
  LLsub := sum_LLsub X hX.valid
  frlate := sum_frlate X hX.valid
  uniqP := sum_uniqP X p K hX.valid
  kP := sum_kP hX hLa hk
  compA := sum_compA hX hLa hk
  compW := sum_compW hX hLa hk
  prodQ := sum_prodQ hX
  perW := sum_perW X p K hX.valid
  JN := J_le_card_TT_of_valid X hX.valid
  a32 := thirty_two_Y_le_a hX }

end Num

theorem restSum : RestSum 1088 1 :=
  restSum_of fun p n' r K _ _ _ X hX hLa hk => ⟨sum_facts hX hLa hk, Ns_one_le hX⟩
end

section
open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem div_mul_sub_le_div_sub_div (n s P Q ee kk rr : ℕ) (hP : 0 < P) (hQ : 0 < Q) (hs : s < kk * P) (he : ee < rr * Q) :
    ((n / (P * Q) : ℕ) : ℤ) - ((kk + rr + 1 : ℕ) : ℤ) ≤ ((((n - s) / P - ee) / Q : ℕ) : ℤ) := by
  have hA : ((n / (P * Q) : ℕ) : ℤ) * ((P : ℤ) * Q) ≤ n := by exact_mod_cast Nat.div_mul_le_self n (P * Q)
  have hU : (((n - s : ℕ)) : ℤ) < (((n - s) / P : ℕ) : ℤ) * P + P := by exact_mod_cast Nat.lt_div_mul_add hP
  have hW : ((((n - s) / P - ee : ℕ)) : ℤ) < ((((n - s) / P - ee) / Q : ℕ) : ℤ) * Q + Q := by
    exact_mod_cast Nat.lt_div_mul_add hQ
  have hns : (n : ℤ) - s ≤ ((n - s : ℕ) : ℤ) := by omega
  have hue : (((n - s) / P : ℕ) : ℤ) - ee ≤ ((((n - s) / P - ee : ℕ)) : ℤ) := by omega
  have hP' : (0 : ℤ) < P := by exact_mod_cast hP
  have hQ' : (1 : ℤ) ≤ Q := by exact_mod_cast hQ
  set A : ℤ := ((n / (P * Q) : ℕ) : ℤ)
  set U : ℤ := (((n - s) / P : ℕ) : ℤ)
  set W : ℤ := ((((n - s) / P - ee) / Q : ℕ) : ℤ)
  have st1 : A * Q - kk < U + 1 := by
    by_contra! hc
    have := mul_le_mul_of_nonneg_left hc hP'.le
    nlinarith
  have st2 : A - rr - kk < W + 1 := by
    by_contra! hc
    have h1 := mul_le_mul_of_nonneg_left hc (by linarith : (0 : ℤ) ≤ Q)
    have hk0 : (0 : ℤ) ≤ kk := by positivity
    have h2 := mul_le_mul_of_nonneg_left hQ' hk0
    nlinarith
  push_cast
  linarith

section Pad

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

theorem eZ_lt_mul_Qc (hX : X.Hyp p K) (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ)
    (he : e ∈ X.EE p K la) (j : ℤ) (i : Fin r) : X.eZ e j i < r * X.Qc p K j := by
  have hV := hX.valid
  have hJ : 0 < X.F.J := hV.1
  unfold Dat.eZ
  rw [dite_eq_left hJ]
  have hmem := Fintype.mem_piFinset.1
    (Fintype.mem_piFinset.1 he ⟨(j % (X.F.J : ℤ)).toNat % X.F.J, Nat.mod_lt _ hJ⟩) i
  rw [Finset.mem_filter, Finset.mem_range] at hmem
  have h0 : (0 : ℤ) ≤ j % (X.F.J : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hJ.ne')
  have h1 : j % (X.F.J : ℤ) < X.F.J := Int.emod_lt_of_pos _ (by exact_mod_cast hJ)
  have hv : ((((j % (X.F.J : ℤ)).toNat % X.F.J : ℕ)) : ℤ) = j % (X.F.J : ℤ) := by
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hq : X.Qc p K ((((j % (X.F.J : ℤ)).toNat % X.F.J : ℕ)) : ℤ) = X.Qc p K j := by
    rw [hv]
    have e1 : j % (X.F.J : ℤ) + (j / (X.F.J : ℤ)) * X.F.J = j := by
      exact Int.emod_add_ediv_mul j (X.F.J : ℤ)
    have e2 := sum_Qc_per (p := p) (K := K) X hV (j % (X.F.J : ℤ)) (j / (X.F.J : ℤ))
    rw [e1] at e2
    exact e2.symm
  rw [hq] at hmem
  exact hmem.1

theorem sum_la_lt (la : Fin n' → Fin (r + K) → ℕ) (hla : la ∈ X.LA p K) (j x : ℤ)
    (hx : x ∈ X.toLate j) : ∑ c, la (posOf n' x) c < (r + K) * X.Pz p K j x := by
  classical
  have hmem := Fintype.mem_piFinset.1 hla (posOf n' x)
  have hmem2 := Finset.mem_filter.1 hmem
  have hlt := (hmem2.2.2 j x hx rfl).1
  have hne : (Finset.univ : Finset (Fin (r + K))).Nonempty :=
    ⟨⟨0, by have := NeZero.ne r; omega⟩, Finset.mem_univ _⟩
  calc ∑ c, la (posOf n' x) c < ∑ _c : Fin (r + K), X.Pz p K j x :=
        Finset.sum_lt_sum_of_nonempty hne (fun c _ => hlt c)
    _ = (r + K) * X.Pz p K j x := by simp

end Pad

theorem restPad : RestPad 1088 := by
  classical
  intro p n' r K _ _ _ X hX hLa hk la hla e he j
  have hV := hX.valid
  have hp := hX.prime.pos
  have hr : 0 < r := NeZero.pos r
  constructor
  · intro x hx hW
    have hb := mem_letters_bounds hx
    obtain ⟨i, hi, rfl⟩ := comb_frame_top X.F hV (j - 1) x hb.2.2 hb.1 (r - 1) (Nat.sub_lt hr Nat.one_pos) hW
    have hval : X.bfam p K la e j (X.F.fr (j - 1) i) =
        (X.nz p K la (j - 1) (X.F.fr (j - 1) i) - X.eZ e (j - 1) ⟨i, hi⟩) / X.Qc p K (j - 1) := by
      unfold Dat.bfam
      rw [ite_eq_left hx, ite_eq_left hW, Finset.sum_eq_single (⟨i, hi⟩ : Fin r)]
      · rw [ite_eq_left rfl]
      · intro b _ hb'
        rw [ite_eq_right]
        intro heq
        apply hb'
        apply Fin.ext
        by_contra hne
        rcases lt_or_gt_of_ne hne with h | h
        · exact absurd heq.symm (ne_of_lt (_root_.Formalism.MainNotions.SelectionLemmas.Pf.bk_fr_lt hV (j - 1) b.val i h hi))
        · exact absurd heq (ne_of_lt (_root_.Formalism.MainNotions.SelectionLemmas.Pf.bk_fr_lt hV (j - 1) i b.val h b.isLt))
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [hval]
    have hPQ := sum_PzQc hX (j - 1) _ hW
    rw [sub_add_cancel] at hPQ
    unfold Dat.Bw
    rw [← hPQ]
    unfold Dat.nz
    exact div_mul_sub_le_div_sub_div _ _ _ _ _ (r + K) r (Pz_pos hp _ _) (by unfold Dat.Qc; exact pow_pos hp _)
      (sum_la_lt la hla (j - 1) _ (sum_frlate X hV (j - 1) ⟨i, hi⟩)) (eZ_lt_mul_Qc hX la e he (j - 1) ⟨i, hi⟩)
  · intro x hx
    have hl := sum_LLsub X hV j x hx
    obtain ⟨h1, h2, -, -⟩ := sum_late_mem hl.1
    have hval : X.bfam p K la e j x = X.nz p K la j x := by
      unfold Dat.bfam
      rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right (not_le.mpr hl.2)]
    rw [hval]
    exact family_degrees_admissible hr hp (fun j x hx => (sum_LLsub X hV j x hx).1) la hla j x hx
end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.SelectionLemmas.Pf.T

def LetterDictionaryBounds (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b →
    ∃ (n0 : ℕ) (od : Fin (segN X.F j) → Fin (segN X.F j)),
      HypT (segN X.F j) n0 r K (segLL X.F j) (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
        (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.a X.La p ∧
      (∀ μ dd, X.IsPATH p K j (X.restr j b) μ dd ↔
        IsPATHa (segLL X.F j) n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) μ dd) ∧
      (∀ μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ,
        GoodA (segLL X.F j) (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
          (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p μ →
        X.IsGood p K j (X.restr j b) μ) ∧
      ((rkA r K n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) : ℕ) : ℝ) =
        (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
        (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ)) ∧
      Real.exp (11 * ((segN X.F j : ℕ) : ℝ) ^ 2 * ell0 (segN X.F j) X.a - min X.La ((r + K : ℕ) : ℝ) / 32) ≤
        1 / X.a ^ (X.Ns ^ 2)

theorem good_path_weight_of_parts (C₀ : ℝ) (ha : PathWeightEqRank) (hT : LemT) (he : LetterDictionaryBounds C₀) : GoodPathWeight C₀ := by
  intro p n' r K _ _ _ X hX hCLa hCk j b hb
  obtain ⟨n0, od, hH, hPATH, hGood, hrk, hexp⟩ := he p n' r K X hX hCLa hCk j b hb
  obtain ⟨hfin, hcard⟩ := hT (segN X.F j) n0 r K (segLL X.F j) _ od _ X.a X.La p hH
  obtain ⟨hfinA, -⟩ := ha (segN X.F j) n0 r K (segLL X.F j) _ od _ X.a X.La p hH
  let S : Set ((Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K))) :=
    {q | ∃ dd, X.IsPATH p K j (X.restr j b) q.1 dd ∧ X.IsGood p K j (X.restr j b) q.1 ∧ IsSt (tanPart q.1) q.2}
  have hSA : S ⊆ SAll (r := r) (K := K) (segLL X.F j) n0
      (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) := by
    rintro q ⟨dd, hp, -, hs⟩
    exact ⟨⟨dd, (hPATH q.1 dd).mp hp⟩, hs⟩
  have hGS : SGood (r := r) (K := K) (segLL X.F j) n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
      (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p ⊆ S := by
    rintro q ⟨⟨dd, hp⟩, hg, hs⟩
    exact ⟨dd, (hPATH q.1 dd).mpr hp, hGood q.1 hg, hs⟩
  have hSfin : S.Finite := hfinA.subset hSA
  have hTS : Nat.card (X.Tset p K j (X.restr j b)) = S.ncard := Nat.card_coe_set_eq S
  refine ⟨hSfin.to_subtype, ?_⟩
  rw [hTS]
  have h1 : ((SGood (r := r) (K := K) (segLL X.F j) n0 (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
      (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p).ncard : ℝ) ≤ S.ncard := by
    exact_mod_cast Set.ncard_le_ncard hGS hSfin
  rw [mul_assoc, ← hrk]
  refine le_trans ?_ (le_trans hcard h1)
  exact mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

end
end Formalism.MainNotions.SelectionLemmas.Pf

namespace Formalism.MainNotions.SelectionLemmas.Pf.TE

section
open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem sort_getD_spec (s : Finset ℤ) (r : ℕ) (hr : 0 < r) (hrs : r ≤ s.card) :
    (s.sort (· ≤ ·)).getD ((s.sort (· ≤ ·)).length - r) 0 ∈ s ∧
      (s.filter ((s.sort (· ≤ ·)).getD ((s.sort (· ≤ ·)).length - r) 0 ≤ ·)).card = r := by
  classical
  have hlen : (s.sort (· ≤ ·)).length = s.card := Finset.length_sort _
  have hk : (s.sort (· ≤ ·)).length - r < s.card := by omega
  set f := s.orderEmbOfFin rfl with hf
  have hget : (s.sort (· ≤ ·)).getD ((s.sort (· ≤ ·)).length - r) 0 = f ⟨(s.sort (· ≤ ·)).length - r, hk⟩ := by
    rw [hf, Finset.orderEmbOfFin_apply, List.getD_eq_getElem]
    · simp [Fin.getElem_fin]
    · omega
  rw [hget]
  refine ⟨Finset.orderEmbOfFin_mem s rfl _, ?_⟩
  have hset : s.filter (f ⟨(s.sort (· ≤ ·)).length - r, hk⟩ ≤ ·) =
      (Finset.univ.filter (fun i : Fin s.card => (s.sort (· ≤ ·)).length - r ≤ i.val ∧ i.val < s.card)).map f.toEmbedding := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hy, hle⟩
      have hr : y ∈ Set.range f := by rw [hf, Finset.range_orderEmbOfFin]; exact hy
      obtain ⟨i, rfl⟩ := hr
      exact ⟨i, ⟨f.le_iff_le.1 hle, i.isLt⟩, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s rfl i, f.le_iff_le.2 hi.1⟩
  rw [hset, Finset.card_map, card_fin_range _ _ _ le_rfl]
  omega

variable {n' r : ℕ} [NeZero n'] [NeZero r] {F : Frames n' r} {L₁ N₁ : ℕ}

theorem oldest_spec (hV : F.Valid L₁ N₁) (j : ℤ) (i : Fin (segN F j)) (hi : r ≤ i.val) :
    F.oldest j (segE F j i) ∈ F.letters j ∧ Even (F.oldest j (segE F j i)) ∧ F.oldest j (segE F j i) < segE F j i ∧
      ((F.letters j).filter fun z => F.oldest j (segE F j i) ≤ z ∧ z < segE F j i ∧ Even z).card = r := by
  classical
  set E := segE F j i with hE
  have hmono : StrictMono (segE F j) := fun a b hab => by
    simp only [segE]
    exact Subtype.coe_lt_coe.2 (((F.letters j).orderIsoOfFin rfl).strictMono hab)
  have hsurj : ∀ x ∈ F.letters j, ∃ k, segE F j k = x := fun x hx =>
    ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, by simp [segE]⟩
  have hlow : ∀ i' < r, F.fr (j - 1) i' < E := by
    intro i' hi'
    obtain ⟨k, hk⟩ := hsurj _ (frp_mem hV j i' hi')
    have hki := idx_w hV k i' hi' hk
    rw [← hk]
    apply hmono
    show k.val < i.val
    omega
  have hcard : r ≤ ((F.letters j).filter fun z => Even z ∧ z < E).card := by
    have hsub : (Finset.range r).image (F.fr (j - 1)) ⊆ (F.letters j).filter fun z => Even z ∧ z < E := by
      intro x hx
      simp only [Finset.mem_image, Finset.mem_range] at hx
      obtain ⟨i', hi', rfl⟩ := hx
      simp only [Finset.mem_filter]
      exact ⟨frp_mem hV j i' hi', (hV.2.2.2.2.1 (j - 1) i' hi').2, hlow i' hi'⟩
    have hinj : Set.InjOn (F.fr (j - 1)) (Finset.range r) := fun a ha b hb h =>
      fr_inj hV _ a b (Finset.mem_range.1 ha) (Finset.mem_range.1 hb) h
    calc r = ((Finset.range r).image (F.fr (j - 1))).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ _ := Finset.card_le_card hsub
  obtain ⟨hm, hc⟩ := sort_getD_spec ((F.letters j).filter fun z => Even z ∧ z < E) r
    (Nat.pos_of_ne_zero (NeZero.ne r)) hcard
  have hold : F.oldest j E = (((F.letters j).filter fun z => Even z ∧ z < E).sort (· ≤ ·)).getD
      ((((F.letters j).filter fun z => Even z ∧ z < E).sort (· ≤ ·)).length - r) 0 := rfl
  rw [hold]
  simp only [Finset.mem_filter] at hm
  refine ⟨hm.1, hm.2.1, hm.2.2, ?_⟩
  rw [Finset.filter_filter] at hc
  refine Eq.trans ?_ hc
  exact congrArg Finset.card (Finset.filter_congr (fun z _ => by tauto))

theorem exists_od (hV : F.Valid L₁ N₁) (j : ℤ) : ∃ od : Fin (segN F j) → Fin (segN F j), ∀ i, r ≤ i.val →
    segE F j (od i) = F.oldest j (segE F j i) ∧ od i < i ∧ (segLL F j).vec (od i) = true ∧
      (Finset.univ.filter fun l : Fin (segN F j) => od i ≤ l ∧ l < i ∧ (segLL F j).vec l = true).card = r := by
  classical
  have hmono : StrictMono (segE F j) := fun a b hab => by
    simp only [segE]
    exact Subtype.coe_lt_coe.2 (((F.letters j).orderIsoOfFin rfl).strictMono hab)
  have hsurj : ∀ x ∈ F.letters j, ∃ k, segE F j k = x := fun x hx =>
    ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, by simp [segE]⟩
  have hmem : ∀ l, segE F j l ∈ F.letters j := fun l => by
    simp only [segE]
    exact Subtype.mem _
  have hex : ∀ i : Fin (segN F j), ∃ k, r ≤ i.val → segE F j k = F.oldest j (segE F j i) := by
    intro i
    by_cases h : r ≤ i.val
    · obtain ⟨k, hk⟩ := hsurj _ (oldest_spec hV j i h).1
      exact ⟨k, fun _ => hk⟩
    · exact ⟨i, fun h' => absurd h' h⟩
  choose g hg using hex
  refine ⟨g, ?_⟩
  intro i hi
  have hk := hg i hi
  obtain ⟨-, hev, hlt, hc⟩ := oldest_spec hV j i hi
  refine ⟨hk, hmono.lt_iff_lt.1 (by rw [hk]; exact hlt), by simp [segLL, LZ, hk, hev], ?_⟩
  rw [← hk] at hc
  refine Eq.trans ?_ hc
  have hset : (F.letters j).filter (fun z => segE F j (g i) ≤ z ∧ z < segE F j i ∧ Even z) =
      (Finset.univ.filter fun l : Fin (segN F j) => g i ≤ l ∧ l < i ∧ (segLL F j).vec l = true).map
        ⟨segE F j, hmono.injective⟩ := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_univ, true_and, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hz, h1, h2, h3⟩
      obtain ⟨l, rfl⟩ := hsurj z hz
      exact ⟨l, ⟨hmono.le_iff_le.1 h1, hmono.lt_iff_lt.1 h2, by simp [segLL, LZ, h3]⟩, rfl⟩
    · rintro ⟨l, ⟨h1, h2, h3⟩, rfl⟩
      exact ⟨hmem l, hmono.le_iff_le.2 h1, hmono.lt_iff_lt.2 h2, by simpa [segLL, LZ] using h3⟩
  rw [hset, Finset.card_map]
end

section
open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace Formalism.MainNotions.SelectionLemmas.Pf.T

section Asm

variable {p n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r}

omit [NeZero r] in
theorem letters_eq_image (F : Frames n' r) (j : ℤ) : F.letters j = Finset.univ.image (segE F j) := by
  ext x
  constructor
  · intro hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, ?_⟩
    simp [segE]
  · intro hx
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨i, rfl⟩ := hx
    exact ((F.letters j).orderIsoOfFin rfl i).2

theorem dist_cast {F : Frames n' r} {j x : ℤ} (hx : x ∈ F.letters j) : (F.dist j x : ℤ) = F.fr j (r - 1) - x := by
  have hx' := (Finset.mem_filter.mp hx).1
  rw [Finset.mem_Icc] at hx'
  exact Int.toNat_of_nonneg (by omega)

theorem dist_lt {F : Frames n' r} {j : ℤ} {i i' : Fin (segN F j)} (h : i < i') :
    F.dist j (segE F j i') + 1 ≤ F.dist j (segE F j i) := by
  have h1 := dist_cast (segE_mem F j i)
  have h2 := dist_cast (segE_mem F j i')
  have hm := segE_strictMono F j h
  omega

theorem dist_add_two_le_of_same_vec {F : Frames n' r} {j : ℤ} {i i' : Fin (segN F j)} (h : i < i')
    (hv : (segLL F j).vec i = (segLL F j).vec i') : F.dist j (segE F j i') + 2 ≤ F.dist j (segE F j i) := by
  have h1 := dist_cast (segE_mem F j i)
  have h2 := dist_cast (segE_mem F j i')
  have hv' : decide (Even (segE F j i)) = decide (Even (segE F j i')) := hv
  rw [decide_eq_decide] at hv'
  have h3 : segE F j i + 1 ≠ segE F j i' := by
    intro he
    rw [← he, Int.even_add_one] at hv'
    tauto
  have hd := dist_lt h
  omega

theorem beS_eq (hV : X.F.Valid X.L₁ X.N₁) (j : ℤ) (b' : ℤ → ℕ) :
    X.beS p K j b' = beA (segN X.F j - r) (fun i => X.Bdeg p K j b' (segE X.F j i)) := by
  unfold Dat.beS beA
  rw [← Finset.sum_filter, letters_eq_image, Finset.filter_image, Finset.sum_image]
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext i
    simp [dict_early hV]
  · exact fun a _ b _ hab => (segE_strictMono X.F j).injective hab

omit [NeZero n'] [NeZero r] [NeZero K] in
theorem prod_fin_lt (N r : ℕ) (hr : r ≤ N) (h : ℕ → ℝ) :
    ∏ i : Fin N, (if i.val < r then h i.val else 1) = ∏ i : Fin r, h i.val := by
  rw [Fin.prod_univ_eq_prod_range (fun i => if i < r then h i else 1) N,
    Fin.prod_univ_eq_prod_range h r, Finset.prod_ite, Finset.prod_const_one, mul_one]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem final_num (hX : X.Hyp p K) (hLa : 1088 ≤ X.CLa) (hk : 1088 ≤ X.Ck) (N : ℕ) (hN : N ≤ X.Ns) :
    Real.exp (11 * (N : ℝ) ^ 2 * ell0 N X.a - min X.La ((r + K : ℕ) : ℝ) / 32) ≤ 1 / X.a ^ (X.Ns ^ 2) := by
  have ha := four_hundred_sixteen_le_a hX
  have hab := a_big hX
  have hL := log_a_ge hX
  have hNs : (N : ℝ) ≤ X.Ns := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hapos : 0 < X.a := by linarith
  have h1 : 1 + 2 * X.a * (N : ℝ) ≤ X.a ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hNs hapos.le, mul_le_mul_of_nonneg_left hab hapos.le,
      mul_le_mul ha ha (by norm_num) hapos.le]
  have hpos1 : 0 < 1 + 2 * X.a * (N : ℝ) := by
    nlinarith [mul_nonneg hapos.le hN0]
  have hl0 : ell0 N X.a ≤ 2 * Real.log X.a := by
    unfold ell0
    have e : Real.log (X.a ^ 2) = 2 * Real.log X.a := by
      rw [Real.log_pow]
      norm_num
    rw [← e]
    exact Real.log_le_log hpos1 h1
  have hl0nn : 0 ≤ ell0 N X.a := by
    unfold ell0
    exact Real.log_nonneg (by nlinarith [mul_nonneg hapos.le hN0])
  have hS : 0 ≤ (X.Ns : ℝ) ^ 2 * Real.log X.a := mul_nonneg (sq_nonneg _) (by linarith)
  have hmin : 1088 * ((X.Ns : ℝ) ^ 2 * Real.log X.a) ≤ min X.La ((r + K : ℕ) : ℝ) := by
    apply le_min
    · show 1088 * ((X.Ns : ℝ) ^ 2 * Real.log X.a) ≤ X.CLa * (X.Ns : ℝ) ^ 2 * Real.log X.a
      nlinarith [mul_le_mul_of_nonneg_right hLa hS]
    · nlinarith [mul_le_mul_of_nonneg_right hk hS, hX.P1]
  have hN2 : (N : ℝ) ^ 2 ≤ (X.Ns : ℝ) ^ 2 := by gcongr
  have hexp : 11 * (N : ℝ) ^ 2 * ell0 N X.a - min X.La ((r + K : ℕ) : ℝ) / 32 ≤
      -((X.Ns : ℝ) ^ 2 * Real.log X.a) := by
    nlinarith [mul_le_mul hN2 hl0 hl0nn (sq_nonneg _)]
  have e2 : Real.log (X.a ^ (X.Ns ^ 2)) = (X.Ns : ℝ) ^ 2 * Real.log X.a := by
    rw [Real.log_pow]
    push_cast
    ring
  calc Real.exp (11 * (N : ℝ) ^ 2 * ell0 N X.a - min X.La ((r + K : ℕ) : ℝ) / 32)
      ≤ Real.exp (-((X.Ns : ℝ) ^ 2 * Real.log X.a)) := Real.exp_le_exp.mpr hexp
    _ = 1 / X.a ^ (X.Ns ^ 2) := by
      rw [Real.exp_neg, one_div, ← e2, Real.exp_log (pow_pos hapos _)]

theorem letter_dictionary_bounds (h41 : TopCountLowerBounds 1088) : LetterDictionaryBounds 1088 := by
  classical
  intro p n' r K _ _ _ X hX hLa hk j b hA
  have hV := hX.valid
  obtain ⟨h41a, -⟩ := h41 p n' r K X hX hLa hk
  obtain ⟨od, hod⟩ := exists_od hV j
  have hNr := r_le_segN hV j
  have h2r := two_r_le hV j
  have hNNs : segN X.F j ≤ X.Ns := hX.card j
  have Bs := basics hX
  have hN6 : (6 : ℝ) ≤ X.Ns := by exact_mod_cast six_le_Ns hX
  have ha := a_big hX
  have ha416 := four_hundred_sixteen_le_a hX
  have hlog := log_a_ge hX
  have hkb := k_big hX hk
  have hp0 : (0 : ℝ) < p := by linarith [Bs.p1]
  have ha0 : (0 : ℝ) < X.a := by linarith
  have hk5 := Bs.k5
  have hkdef : Dat.k (r := r) K = ((r + K : ℕ) : ℝ) := rfl
  have hPpos : ∀ x : ℤ, (0 : ℝ) < (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := fun x => by positivity
  have hP1 : ∀ x : ℤ, (1 : ℝ) ≤ (p : ℝ) ^ (X.F.dist j x + X.Rj p K j) := fun x => one_le_pow₀ Bs.p1.le
  have Bb : ∀ i : Fin (segN X.F j), i.val < segN X.F j - r →
      (X.a' p K (posOf n' (segE X.F j i)) : ℝ) / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) -
          2 * Dat.k (r := r) K * (X.Ns : ℝ) ≤ (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ∧
        (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤
          (X.a' p K (posOf n' (segE X.F j i)) : ℝ) / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) :=
    fun i hi => Bdeg_bounds hX j b hA _ (segE_mem X.F j i) ((dict_early hV i).2 hi)
  have cb := fun i : Fin (segN X.F j) => c_bounds hX h41a j _ (segE_mem X.F j i)

  have Bup : ∀ i : Fin (segN X.F j), i.val < segN X.F j - r →
      (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤
        2 * X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) := fun i hi =>
    le_trans (Bb i hi).2 (div_le_div_of_nonneg_right (cb i).2.2 (hPpos _).le)
  have hkN : Dat.k (r := r) K * 6 ≤ Dat.k (r := r) K * (X.Ns : ℝ) := mul_le_mul_of_nonneg_left hN6 (by linarith)
  have hk2 : Dat.k (r := r) K * (X.Ns : ℝ) * 5 ≤ Dat.k (r := r) K ^ 2 * (X.Ns : ℝ) := by
    have : 0 ≤ Dat.k (r := r) K * (X.Ns : ℝ) := by positivity
    nlinarith

  have cge : ∀ i : Fin (segN X.F j), 36 * (Dat.k (r := r) K * (X.Ns : ℝ)) ≤
      (X.a' p K (posOf n' (segE X.F j i)) : ℝ) / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) := by
    intro i
    rw [le_div_iff₀ (hPpos _)]
    refine le_trans ?_ (cb i).1
    refine mul_le_mul_of_nonneg_right ?_ (hPpos _).le
    nlinarith [Bs.Y1]
  have H : HypT (segN X.F j) (segN X.F j - r) r K (segLL X.F j)
      (fun i => X.Bdeg p K j (X.restr j b) (segE X.F j i)) od
      (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.a X.La p := by
    refine
      { hN := by omega
        r1 := by have := hX.r2; omega
        a3 := by linarith
        p13 := hX.p13
        H1 := ?_
        H2 := ?_
        vec_true_of_early := fun i hi => (comb_vec X.F j i).2 (comb_W_even X.F j hV _ (segE_mem X.F j i) ((dict_w hV i).2 hi))
        vec_true_of_late := fun i hi => (comb_vec X.F j i).2 (dict_lateV hV i hi)
        two_r_le_n0 := h2r
        N_add_r_le_K := by have := hX.NsK; omega
        H4 := ?_
        N_le_a := ?_
        od_lt := fun i hi => (hod i hi).2.1
        od_vec := fun i hi => (hod i hi).2.2.1
        od_card := fun i hi => (hod i hi).2.2.2
        bb_pos := fun i _ => div_pos ha0 (hPpos _)
        bb_le := ?_
        La_pos := ?_ }
    · intro i hi
      have h1 := Bb i hi
      have h2 := cge i
      refine ⟨?_, ?_⟩
      · show ((r + K : ℕ) : ℝ) ≤ (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ)
        rw [← hkdef]
        nlinarith
      · show (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ 2 * X.a
        refine le_trans h1.2 (le_trans (div_le_self (Nat.cast_nonneg _) (hP1 _)) (cb i).2.2)
    · intro i i' hii hi' hv
      show (p : ℝ) ^ 2 / 5 * (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤
        (X.Bdeg p K j (X.restr j b) (segE X.F j i') : ℝ)
      have hi : i.val < segN X.F j - r := lt_trans hii hi'
      have hd := dist_add_two_le_of_same_vec hii hv
      have hPP : (p : ℝ) ^ (X.F.dist j (segE X.F j i') + X.Rj p K j) * (p : ℝ) ^ 2 ≤
          (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) := by
        rw [← pow_add]
        exact pow_le_pow_right₀ Bs.p1.le (by omega)
      set P' := (p : ℝ) ^ (X.F.dist j (segE X.F j i') + X.Rj p K j) with hP'
      have hP'0 : 0 < P' := hPpos _
      have h1 : (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ 2 * X.a / (P' * (p : ℝ) ^ 2) :=
        le_trans (Bup i hi) (div_le_div_of_nonneg_left (by linarith) (by positivity) hPP)
      have h2 : (p : ℝ) ^ 2 / 5 * (2 * X.a / (P' * (p : ℝ) ^ 2)) = 2 / 5 * (X.a / P') := by
        field_simp
      have h3 : (p : ℝ) ^ 2 / 5 * (X.Bdeg p K j (X.restr j b) (segE X.F j i) : ℝ) ≤ 2 / 5 * (X.a / P') := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      have h4 := (Bb i' hi').1
      have h5 := cge i'
      have h6 : 9 / 10 * (X.a / P') ≤ (X.a' p K (posOf n' (segE X.F j i')) : ℝ) / P' := by
        rw [← mul_div_assoc]
        exact div_le_div_of_nonneg_right (cb i').2.1 hP'0.le
      linarith
    · have hr3 : (r : ℝ) ≤ X.Ns := by
        have : r ≤ X.Ns := by omega
        exact_mod_cast this
      have hNR : ((segN X.F j : ℕ) : ℝ) ≤ X.Ns := by exact_mod_cast hNNs
      have hsq : (X.Ns : ℝ) ≤ (X.Ns : ℝ) ^ 2 := by nlinarith
      push_cast at hkb ⊢
      linarith
    · have hNR : ((segN X.F j : ℕ) : ℝ) ≤ X.Ns := by exact_mod_cast hNNs
      linarith
    · intro i l _ hli hl
      show (X.Bdeg p K j (X.restr j b) (segE X.F j l) : ℝ) ≤
        4 * (X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) / (p : ℝ)
      have hd := dist_lt hli
      have hPP : (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) * (p : ℝ) ≤
          (p : ℝ) ^ (X.F.dist j (segE X.F j l) + X.Rj p K j) := by
        rw [← pow_succ]
        exact pow_le_pow_right₀ Bs.p1.le (by omega)
      set P' := (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j) with hP'
      have hP'0 : 0 < P' := hPpos _
      have h1 : (X.Bdeg p K j (X.restr j b) (segE X.F j l) : ℝ) ≤ 2 * X.a / (P' * (p : ℝ)) :=
        le_trans (Bup l hl) (div_le_div_of_nonneg_left (by linarith) (by positivity) hPP)
      have h2 : 4 * (X.a / P') / (p : ℝ) = 2 * (2 * X.a / (P' * (p : ℝ))) := by field_simp; ring
      rw [h2]
      linarith
    · unfold Dat.La
      have : (0 : ℝ) < X.CLa := by linarith
      have : (0 : ℝ) < Real.log X.a := by linarith
      positivity
  refine ⟨segN X.F j - r, od, H, ?_, ?_, ?_, final_num hX hLa hk _ hNNs⟩
  · intro μ dd
    constructor
    · intro h
      refine ⟨h.path, fun i hi => h.degs i ((dict_early hV i).2 hi), fun i m hi hm => ?_⟩
      have hlt : i.val - (segN X.F j - r) < r := by have := i.2; omega
      have := h.head i ⟨i.val - (segN X.F j - r), hlt⟩
        ((dict_tau hV i ⟨i.val - (segN X.F j - r), hlt⟩).2 (by simp only; omega)) m hm
      rw [this, beS_eq hV]
    · intro h
      refine ⟨h.path, fun i hi => h.degs i ((dict_early hV i).1 hi), fun i i' hi m hm => ?_⟩
      have hidx := (dict_tau hV i i').1 hi
      have := h.head i m (by omega) (by omega)
      rw [this, beS_eq hV]
  · intro μ hG i hnW
    have hi : r ≤ i.val := by rw [dict_w hV] at hnW; omega
    obtain ⟨g1, g2, g3⟩ := hG i hi
    have hodn := oldest_lt_n0 H i hi
    have hoe := (hod i hi).1
    have hXi : Xi r K (fun i => X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) X.La p i =
        X.La * X.a / ((p : ℝ) * Dat.k (r := r) K * (p : ℝ) ^ (X.F.dist j (segE X.F j i) + X.Rj p K j)) := by
      unfold Xi
      rw [hkdef]
      have := (hPpos (segE X.F j i)).ne'
      have hk0 : ((r + K : ℕ) : ℝ) ≠ 0 := by rw [← hkdef]; linarith
      field_simp
    refine ⟨le_trans ?_ g1, ?_, ?_⟩
    · unfold Dat.thc
      rw [← hoe]
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      show _ ≤ ((X.Bdeg p K j (X.restr j b) (segE X.F j (od i)) : ℕ) : ℝ)
      unfold Dat.Bdeg
      by_cases hW : X.F.IsW j (segE X.F j (od i))
      · rw [ite_eq_left hW, ite_eq_left hW]
        have := Int.self_le_toNat (X.Bw p K j (segE X.F j (od i)) - (X.m0 K : ℤ))
        exact_mod_cast this
      · rw [ite_eq_right hW, ite_eq_right hW]
    · intro hE
      refine le_trans (g2 ((comb_vec X.F j i).2 hE)) ?_
      unfold Dat.oc
      rw [ite_eq_left hE, hXi, ← hoe]
      have h1 := Bup (od i) hodn
      have h2 : (p : ℝ) ^ (-((X.F.dist j (segE X.F j (od i)) : ℤ) + (X.Rj p K j : ℤ))) =
          1 / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j) := by
        rw [zpow_neg, ← Nat.cast_add, zpow_natCast, one_div]
      rw [h2]
      have h3 : 4 * X.a * (1 / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j)) =
          2 * (2 * X.a / (p : ℝ) ^ (X.F.dist j (segE X.F j (od i)) + X.Rj p K j)) := by ring
      rw [h3]
      linarith
    · intro hE
      have hv : (segLL X.F j).vec i = false := by
        cases hvv : (segLL X.F j).vec i with
        | true => exact absurd ((comb_vec X.F j i).1 hvv) hE
        | false => rfl
      refine le_trans (g3 hv) ?_
      unfold Dat.oc
      rw [ite_eq_right hE, hXi, add_zero]
  · unfold rkA
    push_cast
    have hpt : ∀ i : Fin (segN X.F j),
        ((if i.val < segN X.F j - r then
          (Nat.choose (X.Bdeg p K j (X.restr j b) (segE X.F j i) + (r + K) - 1) (r + K - 1) : ℕ) else 1 : ℕ) : ℝ) =
        (if r ≤ i.val ∧ i.val < segN X.F j - r then
          ((Nat.choose (b (segE X.F j i) + (r + K) - 1) (r + K - 1) : ℕ) : ℝ) else 1) *
        (if i.val < r then ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ) else 1) := by
      intro i
      by_cases h1 : i.val < r
      · have hW := (dict_w hV i).2 h1
        rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h1, one_mul]
        unfold Dat.Bdeg
        rw [ite_eq_left hW, dict_wE hV i h1]
      · by_cases h2 : i.val < segN X.F j - r
        · have hW : ¬ X.F.IsW j (segE X.F j i) := fun h => h1 ((dict_w hV i).1 h)
          have hlate : segE X.F j i ∈ X.toLate j := by
            unfold Dat.toLate; rw [Finset.mem_filter]; exact ⟨segE_mem X.F j i, hW⟩
          rw [ite_eq_left h2, ite_eq_left ⟨by omega, h2⟩, ite_eq_right h1, mul_one]
          unfold Dat.Bdeg Dat.restr
          rw [ite_eq_right hW, ite_eq_left hlate]
        · rw [ite_eq_right h2, ite_eq_right (by omega), ite_eq_right h1]; simp
    have hL : (∏ i : Fin (segN X.F j), ((if i.val < segN X.F j - r then
          (Nat.choose (X.Bdeg p K j (X.restr j b) (segE X.F j i) + (r + K) - 1) (r + K - 1) : ℕ) else 1 : ℕ) : ℝ)) =
        (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
        (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ)) := by
      rw [Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib,
        prod_fin_lt (segN X.F j) r hNr (fun m => ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) m) - (X.m0 K : ℤ)).toNat +
          (r + K) - 1) (r + K - 1) : ℕ) : ℝ))]
      congr 1
      rw [LLset_eq_image hV, Finset.prod_image (fun a _ b _ h => (segE_strictMono X.F j).injective h),
        Finset.prod_filter]
    exact_mod_cast hL

end Asm
end

end Formalism.MainNotions.SelectionLemmas.Pf.TE

namespace Formalism.MainNotions.SelectionLemmas.Pf.T

section
open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

theorem glueT_lt (t : ℕ) (be : ℤ) (τ : Fin (K + t) → ℤ) (m : Fin (r + K)) (h : m.val < r - t) :
    glueT t be τ m = be := by
  unfold glueT; rw [dite_eq_left h]

theorem glueT_ge (t : ℕ) (ht : t ≤ r) (be : ℤ) (τ : Fin (K + t) → ℤ) (m : Fin (r + K)) (h : r - t ≤ m.val) :
    glueT t be τ m = τ ⟨m.val - (r - t), by have := m.2; omega⟩ := by
  unfold glueT; rw [dite_eq_right (by omega), dite_eq_left]

theorem dom_of_strip_up {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip ν μ b) (hν : Dominant ν) : Dominant μ := by
  intro m m' hmm
  rcases eq_or_lt_of_le hmm with he | hlt
  · rw [he]
  · have hm1 : (m'.val - 1) + 1 < n := by have := m'.2; have : m.val < m'.val := hlt; omega
    have h2 := h.2.1 ⟨m'.val - 1, by have := m'.2; omega⟩ hm1
    have hme : (⟨(m'.val - 1) + 1, hm1⟩ : Fin n) = m' := Fin.ext (by simp only; have : m.val < m'.val := hlt; omega)
    rw [hme] at h2
    have h3 : ν ⟨m'.val - 1, by have := m'.2; omega⟩ ≤ ν m :=
      hν (by rw [Fin.le_def]; simp only; have : m.val < m'.val := hlt; omega)
    exact le_trans h2 (le_trans h3 (h.1 m))

theorem dom_of_strip_down {n : ℕ} {ν μ : Fin n → ℤ} {b : ℕ} (h : HStrip μ ν b) (hν : Dominant ν) : Dominant μ := by
  intro m m' hmm
  rcases eq_or_lt_of_le hmm with he | hlt
  · rw [he]
  · have hlt' : m.val < m'.val := hlt
    have hm1 : m.val + 1 < n := by have := m'.2; omega
    have h2 := h.2.1 m hm1
    have h3 : ν m' ≤ ν ⟨m.val + 1, hm1⟩ := hν (by rw [Fin.le_def]; simp only; omega)
    exact le_trans (h.1 m') (le_trans h3 h2)

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

open Classical in
theorem tau_count (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (H : HypT N n0 r K LL B od bb a La p)
    (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) :
    ∀ (t s : ℕ) (hst : s + t = N) (_ht : t ≤ r) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ), VP LL n0 B s μ0 →
      (Af hfin s μ0).card = stCount (K + t) (tailT t (μ0 ⟨s, by omega⟩)) := by
  intro t
  induction t with
  | zero =>
    intro s hst _ μ0 hv
    have hsN : s = N := by omega
    subst hsN
    have hμ : μ0 ∈ SP (r := r) (K := K) LL n0 B := (sp_iff H μ0).2 hv
    have hA : Af hfin s μ0 = (finite_St (tanPart μ0)).toFinset.image (fun I => (μ0, I)) := by
      ext q
      unfold Af
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_image]
      constructor
      · rintro ⟨⟨_, h2⟩, h3'⟩
        have hq : q.1 = μ0 := funext fun t => h3' t (by have := t.2; omega)
        exact ⟨q.2, by rw [← hq]; exact h2, Prod.ext hq.symm rfl⟩
      · rintro ⟨I, hI, rfl⟩
        exact ⟨⟨hμ, hI⟩, fun t _ => rfl⟩
    have hdom : Dominant (pEnd (tanPart μ0)) := by
      intro x y hxy
      exact hv.2.1 (Fin.last s) (by simp) (by rw [Fin.le_def] at hxy ⊢; simp; omega)
    rw [hA, Finset.card_image_of_injective _ (fun x y h => (Prod.ext_iff.1 h).2), ← Set.ncard_eq_toFinset_card _ (finite_St (tanPart μ0)),
      wt_eq D h3 _ hdom]
    show stCount K _ = stCount K _
    congr 1
    funext l
    have := tailT_apply (r := r) (K := K) 0 (Nat.zero_le r) (μ0 ⟨s, by omega⟩) l
    rw [show (tailT 0 (μ0 ⟨s, by omega⟩) : Fin (K + 0) → ℤ) l = _ from this]
    unfold pEnd tanPart
    congr 1
  | succ t ih =>
    intro s hst ht μ0 hv
    have hs : s < N := by omega
    have hN := H.hN
    have hn0 : n0 ≤ s := by omega
    have hla : ∀ m, μ0 (⟨s, hs⟩ : Fin N).castSucc m ≤ (beA n0 B : ℤ) := fun m => vp_le hv s (by omega) le_rfl m
    have hlad : Dominant (μ0 (⟨s, hs⟩ : Fin N).castSucc) := hv.2.1 _ (by simp)
    generalize hlaeq : μ0 (⟨s, hs⟩ : Fin N).castSucc = la at hla hlad
    have hheads : ∀ m : Fin (r + K), m.val + 1 < r - t → la m = (beA n0 B : ℤ) := by
      intro m hm
      have hs1 : s - 1 < N := by omega
      have h1 := ((hv.2.2 ⟨s - 1, hs1⟩ (by simp only; omega)).2 (by simp only; omega)).2 m (by simp only; omega)
      have he : (⟨s - 1, hs1⟩ : Fin N).succ = (⟨s, hs⟩ : Fin N).castSucc := Fin.ext (by simp; omega)
      rw [he, hlaeq] at h1
      exact h1
    have hν : ∀ l : Fin (K + t + 1), (tailT (t + 1) la : Fin (K + t + 1) → ℤ) l =
        la ⟨(r - (t + 1)) + l.val, by have := l.2; omega⟩ := fun l => tailT_apply (t + 1) ht la l
    have hνdom : Dominant (tailT (t + 1) la : Fin (K + t + 1) → ℤ) := by
      intro x y hxy
      rw [hν, hν]
      exact hlad (by rw [Fin.le_def] at hxy ⊢; simp only; omega)
    set ν : Fin (K + t + 1) → ℤ := tailT (t + 1) la with hνdef
    set T := Fintype.piFinset (fun l : Fin (K + t) => Finset.Icc (ν l.succ) (ν l.castSucc)) with hT
    have hτ : ∀ τ ∈ T, ∀ l : Fin (K + t), ν l.succ ≤ τ l ∧ τ l ≤ ν l.castSucc := by
      intro τ hτ l
      rw [hT, Fintype.mem_piFinset] at hτ
      exact Finset.mem_Icc.mp (hτ l)
    have hinj : Set.InjOn (glueT (r := r) t (beA n0 B : ℤ)) (T : Set (Fin (K + t) → ℤ)) := by
      intro τ _ τ' _ h
      rw [← tailT_glueT (r := r) t (by omega) (beA n0 B : ℤ) τ, h, tailT_glueT (r := r) t (by omega)]
    have hE : ∀ q ∈ Af hfin s μ0, q.1 (⟨s, hs⟩ : Fin N).succ ∈ T.image (glueT (r := r) t (beA n0 B : ℤ)) := by
      intro q hq
      obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
      rw [hlaeq] at hstq
      obtain ⟨⟨d, hS⟩, hh⟩ := hstq.2 hn0
      generalize q.1 (⟨s, hs⟩ : Fin N).succ = la' at hS hh
      rw [Finset.mem_image]
      refine ⟨tailT t la', ?_, ?_⟩
      · rw [hT, Fintype.mem_piFinset]
        intro l
        have hl := l.2
        rw [Finset.mem_Icc, hν, hν, tailT_apply t (by omega)]
        constructor
        · have := hS.1 ⟨(r - t) + l.val, by omega⟩
          have he : (⟨(r - (t + 1)) + (l.succ : Fin (K + t + 1)).val, by simp; omega⟩ : Fin (r + K)) =
              ⟨(r - t) + l.val, by omega⟩ := Fin.ext (by simp; omega)
          rw [he]; exact this
        · have := hS.2.1 ⟨(r - (t + 1)) + l.val, by omega⟩ (by simp only; omega)
          have he : (⟨(r - (t + 1)) + l.val + 1, by omega⟩ : Fin (r + K)) = ⟨(r - t) + l.val, by omega⟩ :=
            Fin.ext (by simp only; omega)
          rw [he] at this
          exact this
      · funext m
        by_cases hm : m.val < r - t
        · rw [glueT_lt t _ _ m hm, hh m (by simp only; omega)]
        · rw [glueT_ge t (by omega) _ _ m (by omega), tailT_apply t (by omega)]
          congr 1
          exact Fin.ext (by simp only; omega)
    have hterm : ∀ τ ∈ T, (Af hfin (s + 1) (Function.update μ0 (⟨s, hs⟩ : Fin N).succ
        (glueT (r := r) t (beA n0 B : ℤ) τ))).card = stCount (K + t) τ := by
      intro τ hτT
      have hb := hτ τ hτT
      have hτanti : ∀ l l' : Fin (K + t), l ≤ l' → τ l' ≤ τ l := by
        intro l l' hll
        rcases eq_or_lt_of_le hll with he | hlt
        · rw [he]
        · have h1 := (hb l').2
          have h2 := (hb l).1
          have h3 : ν l'.castSucc ≤ ν l.succ := hνdom (by rw [Fin.le_def]; simp; exact hlt)
          linarith
      have hτbe : ∀ l : Fin (K + t), τ l ≤ (beA n0 B : ℤ) := by
        intro l
        refine le_trans (hb l).2 ?_
        rw [hν]; exact hla _
      have hd' : Dominant (glueT (r := r) t (beA n0 B : ℤ) τ) := by
        intro m m' hmm
        by_cases h1 : m'.val < r - t
        · rw [glueT_lt t _ _ m' h1, glueT_lt t _ _ m (by omega)]
        · rw [glueT_ge t (by omega) _ _ m' (by omega)]
          by_cases h2 : m.val < r - t
          · rw [glueT_lt t _ _ m h2]; exact hτbe _
          · rw [glueT_ge t (by omega) _ _ m (by omega)]
            exact hτanti _ _ (by rw [Fin.le_def]; simp only; omega)
      have hS1 : ∀ x, la x ≤ glueT (r := r) t (beA n0 B : ℤ) τ x := by
        intro x
        by_cases h1 : x.val < r - t
        · rw [glueT_lt t _ _ x h1]; exact hla x
        · rw [glueT_ge t (by omega) _ _ x (by omega)]
          have h2 := (hb ⟨x.val - (r - t), by have := x.2; omega⟩).1
          rw [hν] at h2
          have he : (⟨(r - (t + 1)) + ((⟨x.val - (r - t), by have := x.2; omega⟩ : Fin (K + t)).succ :
              Fin (K + t + 1)).val, by have := x.2; simp; omega⟩ : Fin (r + K)) = x := Fin.ext (by simp; omega)
          rw [he] at h2
          exact h2
      have hst' : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) (glueT (r := r) t (beA n0 B : ℤ) τ) := by
        rw [hlaeq]
        refine ⟨fun h => absurd h (by simp only; omega), fun _ => ⟨⟨(∑ x, (glueT (r := r) t (beA n0 B : ℤ) τ x - la x)).toNat,
          hS1, ?_, ?_⟩, fun m hm => glueT_lt t _ _ m (by simp only at hm; omega)⟩⟩
        · intro x hx
          by_cases h1 : x.val + 1 < r - t
          · rw [glueT_lt t _ _ _ (by simp only; exact h1), hheads x h1]
          · rw [glueT_ge t (by omega) _ _ _ (by simp only; omega)]
            have h2 := (hb ⟨x.val + 1 - (r - t), by have := x.2; omega⟩).2
            rw [hν] at h2
            have he : (⟨(r - (t + 1)) + ((⟨x.val + 1 - (r - t), by have := x.2; omega⟩ : Fin (K + t)).castSucc :
                Fin (K + t + 1)).val, by have := x.2; simp; omega⟩ : Fin (r + K)) = x := Fin.ext (by simp; omega)
            rw [he] at h2
            exact h2
        · exact (Int.toNat_of_nonneg (Finset.sum_nonneg fun x _ => sub_nonneg.mpr (hS1 x))).symm
      have hv' := vp_update hs hv _ hd' hst'
      rw [ih (s + 1) (by omega) (by omega) _ hv']
      congr 1
      show tailT t (Function.update μ0 (⟨s, hs⟩ : Fin N).succ (glueT (r := r) t (beA n0 B : ℤ) τ)
        (⟨s, hs⟩ : Fin N).succ) = τ
      rw [Function.update_self, tailT_glueT t (by omega)]
    rw [Af_card_sum hfin s hs μ0 _ hE, Finset.sum_image hinj, Finset.sum_congr rfl hterm]
    have h4' := h4 (K + t) ν hνdom
    show _ = stCount (K + t + 1) (tailT (t + 1) (μ0 (⟨s, hs⟩ : Fin N).castSucc))
    rw [hlaeq]
    exact h4'.symm

end
end

section
open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

variable {N r K : ℕ}

def prodFrom (r K n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) : ℕ :=
  ∏ i : Fin N, if s ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1

theorem prodFrom_succ (n0 : ℕ) (B : Fin N → ℕ) (s : ℕ) (hs : s < N) (hsn : s < n0) :
    prodFrom r K n0 B s = Nat.choose (B ⟨s, hs⟩ + (r + K) - 1) (r + K - 1) * prodFrom r K n0 B (s + 1) := by
  classical
  unfold prodFrom
  have hpt : ∀ i : Fin N, (if s ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1) =
      (if i = ⟨s, hs⟩ then Nat.choose (B ⟨s, hs⟩ + (r + K) - 1) (r + K - 1) else 1) *
      (if s + 1 ≤ i.val ∧ i.val < n0 then Nat.choose (B i + (r + K) - 1) (r + K - 1) else 1) := by
    intro i
    by_cases he : i = ⟨s, hs⟩
    · subst he
      rw [ite_eq_left ⟨le_rfl, hsn⟩, ite_eq_left rfl, ite_eq_right (by simp), mul_one]
    · have hne : i.val ≠ s := fun h => he (Fin.ext h)
      rw [ite_eq_right he, one_mul]
      by_cases h1 : s ≤ i.val ∧ i.val < n0
      · rw [ite_eq_left h1, ite_eq_left ⟨by omega, h1.2⟩]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]
  rw [Finset.prod_congr rfl fun i _ => hpt i, Finset.prod_mul_distrib, Finset.prod_ite_eq' ]
  simp

theorem prodFrom_self_eq_one (n0 : ℕ) (B : Fin N → ℕ) : prodFrom r K n0 B n0 = 1 := by
  unfold prodFrom
  refine Finset.prod_eq_one fun i _ => ?_
  rw [ite_eq_right (by omega)]

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

open Classical in
theorem pre_count (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (h5 : GenericProjectionCriterion D)
    (H : HypT N n0 r K LL B od bb a La p) (hfin : (SAll (r := r) (K := K) LL n0 B).Finite) :
    ∀ (u s : ℕ) (hsu : s + u = n0) (μ0 : Fin (N + 1) → Fin (r + K) → ℤ), VP LL n0 B s μ0 →
      (Af hfin s μ0).card = stCount (r + K) (μ0 ⟨s, by have := H.hN; omega⟩) * prodFrom r K n0 B s := by
  have hN := H.hN
  have hn : 0 < r + K := by have := H.r1; omega
  intro u
  induction u with
  | zero =>
    intro s hsu μ0 hv
    have hs : s = n0 := by omega
    subst hs
    rw [tau_count D h3 h4 H hfin r s (by omega) le_rfl μ0 hv, prodFrom_self_eq_one, mul_one,
      ← stCount_cast (Nat.add_comm K r) (μ0 ⟨s, by omega⟩)]
    congr 1
    funext l
    rw [tailT_apply r le_rfl]
    congr 1
    exact Fin.ext (by simp)
  | succ u ih =>
    intro s hsu μ0 hv
    have hsn : s < n0 := by omega
    have hs : s < N := by omega
    have hlad : Dominant (μ0 (⟨s, hs⟩ : Fin N).castSucc) := hv.2.1 _ (by simp)
    rw [prodFrom_succ n0 B s hs hsn, ← mul_assoc]
    show _ = stCount (r + K) (μ0 (⟨s, hs⟩ : Fin N).castSucc) * _ * _
    cases hvec : LL.vec ⟨s, hs⟩ with
    | true =>
      rw [pieri_vec D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]
      rw [Af_card_sum hfin s hs μ0 _ ?_]
      · refine Finset.sum_congr rfl fun la' hla' => ?_
        rw [Finset.mem_filter] at hla'
        have hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la' :=
          ⟨fun _ => by rw [ite_eq_left hvec]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩
        have hv' := vp_update hs hv la' (dom_of_strip_up hla'.2 hlad) hst
        rw [ih (s + 1) (by omega) _ hv']
        congr 2
        show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'
        rw [Function.update_self]
      · intro q hq
        obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
        have hS := hstq.1 hsn
        rw [ite_eq_left hvec] at hS
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        exact ⟨fun x => Finset.mem_Icc.mpr ⟨hS.1 x, strip_le_add hS x⟩, hS⟩
    | false =>
      rw [pieri_cov D h5 (r + K) hn _ (B ⟨s, hs⟩) hlad, Finset.sum_mul]
      rw [Af_card_sum hfin s hs μ0 _ ?_]
      · refine Finset.sum_congr rfl fun la' hla' => ?_
        rw [Finset.mem_filter] at hla'
        have hst : StepOK LL n0 B ⟨s, hs⟩ (μ0 (⟨s, hs⟩ : Fin N).castSucc) la' :=
          ⟨fun _ => by rw [ite_eq_right (by simp [hvec])]; exact hla'.2, fun h => absurd h (by simp only; omega)⟩
        have hv' := vp_update hs hv la' (dom_of_strip_down hla'.2 hlad) hst
        rw [ih (s + 1) (by omega) _ hv']
        congr 2
        show Function.update μ0 (⟨s, hs⟩ : Fin N).succ la' (⟨s, hs⟩ : Fin N).succ = la'
        rw [Function.update_self]
      · intro q hq
        obtain ⟨_, hstq⟩ := Af_step H hfin s hs μ0 q hq
        have hS := hstq.1 hsn
        rw [ite_eq_right (by simp [hvec])] at hS
        rw [Finset.mem_filter, Fintype.mem_piFinset]
        refine ⟨fun x => Finset.mem_Icc.mpr ⟨?_, hS.1 x⟩, hS⟩
        have := strip_le_add hS x
        linarith

end

theorem path_weight_eq_rank (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (h4 : ColumnFamilyLowerSet D) (h5 : GenericProjectionCriterion D) : PathWeightEqRank := by
  classical
  intro N n0 r K _ _ LL B od bb a La p H
  have hfin := finite_SAll H
  refine ⟨hfin, ?_⟩
  have hv : VP (r := r) (K := K) LL n0 B 0 (fun _ => 0) :=
    ⟨rfl, fun _ _ _ _ _ => le_rfl, fun i hi => absurd hi (by omega)⟩
  have h := pre_count D h3 h4 h5 H hfin n0 0 (by omega) (fun _ => 0) hv
  have hA : Af hfin 0 (fun _ => 0) = hfin.toFinset := by
    unfold Af
    rw [Finset.filter_eq_self]
    intro q hq t ht
    rw [Set.Finite.mem_toFinset] at hq
    have ht0 : t = 0 := Fin.ext (by simpa using ht)
    rw [ht0]
    exact ((sp_iff H q.1).1 hq.1).1
  rw [Set.ncard_eq_toFinset_card _ hfin, ← hA, h]
  have h0 : stCount (r + K) ((fun _ => 0 : Fin (N + 1) → Fin (r + K) → ℤ) ⟨0, by omega⟩) = 1 := stCount_zero D h3 (r + K)
  rw [h0, one_mul]
  unfold prodFrom rkA
  refine Finset.prod_congr rfl fun i _ => ?_
  simp
end

section
open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas
open Formalism.InvariantFactorPaths

variable {N r K : ℕ}

theorem entry_eq_of_lt (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s m : ℕ)
    (hs : s < N + 1) (hm : m < r + K) :
    BranchingDimensions.Letters.ent (D := toL r K LL B) μ s m = μ ⟨s, hs⟩ ⟨m, hm⟩ :=
  dite_eq_left (⟨hs, hm⟩ : s < N + 1 ∧ m < r + K)

theorem entry_eq_zero_of_ge (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s m : ℕ)
    (hm : ¬ m < r + K) : BranchingDimensions.Letters.ent (D := toL r K LL B) μ s m = 0 :=
  dite_eq_right (fun h : s < N + 1 ∧ m < r + K => hm h.2)

theorem sum_Icc_one_eq_sum_range {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.Icc 1 n, f i = ∑ m ∈ Finset.range n, f (m + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

theorem prod_Icc_one_eq_prod_range {M : Type} [CommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∏ i ∈ Finset.Icc 1 n, f i = ∏ m ∈ Finset.range n, f (m + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Finset.prod_range_succ]

theorem prod_fin_ite_lt_eq {M : Type} [CommMonoid M] (n j : ℕ) (hj : j ≤ n) (h : ℕ → M) :
    ∏ i : Fin n, (if i.val < j then h i.val else 1) = ∏ i ∈ Finset.range j, h i := by
  rw [Fin.prod_univ_eq_prod_range (fun m => if m < j then h m else 1) n]
  rw [← Finset.prod_subset (Finset.range_subset_range.mpr hj)]
  · refine Finset.prod_congr rfl fun m hm => ?_
    rw [ite_eq_left (Finset.mem_range.mp hm)]
  · intro m _ hm
    rw [ite_eq_right (by simpa using hm)]

theorem sum_fin_ite_lt_eq {M : Type} [AddCommMonoid M] (n j : ℕ) (hj : j ≤ n) (h : ℕ → M) :
    ∑ i : Fin n, (if i.val < j then h i.val else 0) = ∑ i ∈ Finset.range j, h i := by
  rw [Fin.sum_univ_eq_sum_range (fun m => if m < j then h m else 0) n]
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr hj)]
  · refine Finset.sum_congr rfl fun m hm => ?_
    rw [ite_eq_left (Finset.mem_range.mp hm)]
  · intro m _ hm
    rw [ite_eq_right (by simpa using hm)]

theorem beta_eq_sum_thresholds (LL : Letters (Fin N)) (B : Fin N → ℕ) (n0 : ℕ) (hn : n0 ≤ N) :
    ∑ i ∈ Finset.Icc 1 n0, (toL r K LL B).B i = beA n0 B := by
  unfold beA
  rw [sum_Icc_one_eq_sum_range, ← sum_fin_ite_lt_eq N n0 hn (fun m => (toL r K LL B).B (m + 1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i.val < n0
  · rw [ite_eq_left hi, ite_eq_left hi, toL_B LL B (i.val + 1) ⟨by omega, by have := i.2; omega⟩]
    congr 1
  · rw [ite_eq_right hi, ite_eq_right hi]

theorem rank_eq_prod_choose (LL : Letters (Fin N)) (B : Fin N → ℕ) (n0 : ℕ) (hn : n0 ≤ N) :
    ∏ i ∈ Finset.Icc 1 n0, ((toL r K LL B).B i + (r + K) - 1).choose (r + K - 1) = rkA r K n0 B := by
  unfold rkA
  rw [prod_Icc_one_eq_prod_range, ← prod_fin_ite_lt_eq N n0 hn (fun m => ((toL r K LL B).B (m + 1) + (r + K) - 1).choose (r + K - 1))]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i.val < n0
  · rw [ite_eq_left hi, ite_eq_left hi, toL_B LL B (i.val + 1) ⟨by omega, by have := i.2; omega⟩]
    congr 3
  · rw [ite_eq_right hi, ite_eq_right hi]

theorem entry_weight_eq_sum (LL : Letters (Fin N)) (B : Fin N → ℕ) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s : ℕ) (hs : s < N + 1) :
    BranchingDimensions.wsize (r + K) (BranchingDimensions.Letters.ent (D := toL r K LL B) μ s) = ∑ m : Fin (r + K), μ ⟨s, hs⟩ m := by
  unfold BranchingDimensions.wsize
  rw [Finset.sum_range]
  exact Finset.sum_congr rfl fun m _ => entry_eq_of_lt LL B μ s m.val hs m.2

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem toL_IsPATH (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hP : IsPATHa LL n0 B P.mu dd) : (toL r K LL B).IsPATH P.mu := by
  have hN := H.hN
  have hn0 := letters_n0_eq (r := r) (K := K) H
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m
    by_cases hm : m < r + K
    · rw [entry_eq_of_lt LL B P.mu 0 m (by omega) hm]
      have h0 : (⟨0, by omega⟩ : Fin (N + 1)) = 0 := rfl
      rw [h0, P.zero]; rfl
    · exact entry_eq_zero_of_ge LL B P.mu 0 m hm
  · intro i hi m hm
    have hi' : i ≤ N := hi
    have hm' : m + 1 < r + K := hm
    rw [entry_eq_of_lt LL B P.mu i (m + 1) (by omega) hm', entry_eq_of_lt LL B P.mu i m (by omega) (by omega)]
    exact P.dom _ (by rw [Fin.le_def]; simp)
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    have h2' : i0 + 1 ≤ N := h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, h2'⟩] at hv
    have hs := step_vec P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · have hm' : m < r + K := hm
      rw [entry_eq_of_lt LL B P.mu i0 m (by omega) hm', entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) hm']
      exact hs.1 ⟨m, hm'⟩
    · have hm' : m + 1 < r + K := hm
      rw [entry_eq_of_lt LL B P.mu i0 m (by omega) (by omega), entry_eq_of_lt LL B P.mu (i0 + 1) (m + 1) (by omega) hm']
      exact hs.2.1 ⟨m, by omega⟩ hm'
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    have h2' : i0 + 1 ≤ N := h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, h2'⟩] at hv
    have hs := step_cov P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel]
    refine ⟨fun m hm => ?_, fun m hm => ?_⟩
    · have hm' : m < r + K := hm
      rw [entry_eq_of_lt LL B P.mu i0 m (by omega) hm', entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) hm']
      exact hs.1 ⟨m, hm'⟩
    · have hm' : m + 1 < r + K := hm
      rw [entry_eq_of_lt LL B P.mu (i0 + 1) m (by omega) (by omega), entry_eq_of_lt LL B P.mu i0 (m + 1) (by omega) hm']
      exact hs.2.1 ⟨m, by omega⟩ hm'
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    rw [hn0] at h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, by omega⟩] at hv
    have hs := step_vec P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel, toL_B LL B (i0 + 1) ⟨h1, by omega⟩]
    show BranchingDimensions.wsize (r + K) _ - BranchingDimensions.wsize (r + K) _ = _
    rw [entry_weight_eq_sum LL B P.mu (i0 + 1) (by omega), entry_weight_eq_sum LL B P.mu i0 (by omega), ← Finset.sum_sub_distrib]
    have := hs.2.2
    rw [hP.degs ⟨i0, by omega⟩ (by simp only; omega)] at this
    exact this
  · intro i h1 h2 hv
    obtain ⟨i0, rfl⟩ : ∃ i0, i = i0 + 1 := ⟨i - 1, by omega⟩
    rw [hn0] at h2
    rw [toL_vec LL B (i0 + 1) ⟨h1, by omega⟩] at hv
    have hs := step_cov P ⟨i0, by omega⟩ hv
    rw [Nat.add_sub_cancel, toL_B LL B (i0 + 1) ⟨h1, by omega⟩]
    show BranchingDimensions.wsize (r + K) _ - BranchingDimensions.wsize (r + K) _ = _
    rw [entry_weight_eq_sum LL B P.mu (i0 + 1) (by omega), entry_weight_eq_sum LL B P.mu i0 (by omega), ← Finset.sum_sub_distrib]
    have := hs.2.2
    rw [hP.degs ⟨i0, by omega⟩ (by simp only; omega)] at this
    exact this
  · intro i' h1 h2 m hm
    have h2' : i' ≤ r := h2
    rw [hn0, entry_eq_of_lt LL B P.mu (n0 + i') m (by omega) (by omega)]
    have := hP.head ⟨n0 + i' - 1, by omega⟩ ⟨m, by omega⟩ (by simp only; omega) (by simp only; omega)
    have he : (⟨n0 + i' - 1, by omega⟩ : Fin N).succ = (⟨n0 + i', by omega⟩ : Fin (N + 1)) :=
      Fin.ext (by simp; omega)
    rw [he] at this
    rw [this]
    congr 1
    show beA n0 B = ∑ i ∈ Finset.Icc 1 (toL r K LL B).n0, (toL r K LL B).B i
    rw [hn0, beta_eq_sum_thresholds LL B n0 (by omega)]

theorem toL_wt (D : Formalism.BasicNotions.D7) (h3 : admB3 D) (μ : Fin (N + 1) → Fin (r + K) → ℤ)
    (hd : Dominant (pEnd (tanPart μ))) :
    (({I | IsSt (tanPart μ) I} : Set (ℤ → Finset (Fin K))).ncard : ℝ) = BranchingDimensions.Letters.wt (D := toL r K LL B) μ := by
  have h1 := h3 K N (tanPart μ) hd
  rw [← Nat.card_coe_set_eq]
  have h2 : ((Nat.card {I : ℤ → Finset (Fin K) // IsSt (tanPart μ) I} : ℕ) : ℝ) =
      (((Nat.card {I : ℤ → Finset (Fin K) // IsSt (tanPart μ) I} : ℕ) : ℚ) : ℝ) := by push_cast; rfl
  refine Eq.trans h2 ?_
  rw [h1]
  unfold BranchingDimensions.Letters.wt BranchingDimensions.weylDim
  push_cast
  rw [Finset.prod_comm, Finset.prod_range]
  refine Finset.prod_congr rfl fun j _ => ?_
  have hka : ∀ x : Fin K, BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N x.val = pEnd (tanPart μ) x := by
    intro x
    unfold BranchingDimensions.Letters.kaRows
    show BranchingDimensions.Letters.ent (D := toL r K LL B) μ N (r + x.val) = _
    rw [entry_eq_of_lt LL B μ N (r + x.val) (by omega) (by have := x.2; omega)]
    rfl
  refine Eq.trans ?_ (prod_fin_ite_lt_eq K j.val j.2.le (fun i =>
    (((BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N i : ℤ) : ℝ) - ((BranchingDimensions.Letters.kaRows (D := toL r K LL B) μ N j.val : ℤ) : ℝ) +
      (((j.val : ℕ) : ℝ) - (i : ℝ))) / (((j.val : ℕ) : ℝ) - (i : ℝ))))
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hij : i < j
  · have hij' : i.val < j.val := hij
    rw [ite_eq_left hij, ite_eq_left hij', hka i, hka j]
    push_cast
    ring
  · have hij' : ¬ i.val < j.val := hij
    rw [ite_eq_right hij, ite_eq_right hij']
    simp

end
end

section
open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas
open Formalism.InvariantFactorPaths

variable {N r K : ℕ}

section
variable {n0 : ℕ} {LL : Letters (Fin N)} {B : Fin N → ℕ} {od : Fin N → Fin N} {bb : Fin N → ℝ} {a La : ℝ} {p : ℕ}

theorem tail_positive_eq (H : HypT N n0 r K LL B od bb a La p) (μ : Fin (N + 1) → Fin (r + K) → ℤ) (s : ℕ) (hs : s ≤ n0) :
    BranchingDimensions.tailPos ((toL r K LL B).stLen s) (BranchingDimensions.Letters.stage (D := toL r K LL B) μ s) 0 =
      posS (μ ⟨s, by have := H.hN; omega⟩) := by
  have hN := H.hN
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have h0 : s - (toL r K LL B).n0 = 0 := by rw [hn0]; omega
  unfold BranchingDimensions.tailPos BranchingDimensions.Letters.stLen BranchingDimensions.Letters.stage posS
  rw [h0, Finset.filter_true_of_mem (fun _ _ => Nat.zero_le _)]
  show ∑ m ∈ Finset.range (r + K - 0), _ = _
  rw [Nat.sub_zero, Finset.sum_range]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.add_zero, entry_eq_of_lt LL B μ s m.val (by omega) m.2]

theorem tail_negative_eq (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hP : IsPATHa LL n0 B P.mu dd) (s : ℕ) (hs : s ≤ N) :
    BranchingDimensions.tailNeg ((toL r K LL B).stLen s) (BranchingDimensions.Letters.stage (D := toL r K LL B) P.mu s) 0 =
      negS (P.mu ⟨s, by omega⟩) := by
  have hN := H.hN
  have hn0 := letters_n0_eq (r := r) (K := K) H
  unfold BranchingDimensions.tailNeg BranchingDimensions.Letters.stLen BranchingDimensions.Letters.stage negS
  rw [hn0, Finset.filter_true_of_mem (fun _ _ => Nat.zero_le _)]
  show ∑ m ∈ Finset.range (r + K - (s - n0)),
    max (-(BranchingDimensions.Letters.ent (D := toL r K LL B) P.mu s (r + K - (s - n0) - 1 - m + (s - n0)))) 0 = _
  have hh : s - n0 ≤ r := by omega
  generalize hhd : s - n0 = h at hh
  rw [Finset.sum_range_reflect (fun x => max (-(BranchingDimensions.Letters.ent (D := toL r K LL B) P.mu s (x + h))) 0) (r + K - h)]
  have hsplit : ∑ m : Fin (r + K), max (-P.mu ⟨s, by omega⟩ m) 0 =
      ∑ m ∈ Finset.range (h + (r + K - h)), max (-(BranchingDimensions.Letters.ent (D := toL r K LL B) P.mu s m)) 0 := by
    rw [show h + (r + K - h) = r + K by omega, Finset.sum_range]
    exact Finset.sum_congr rfl fun m _ => by rw [entry_eq_of_lt LL B P.mu s m.val (by omega) m.2]
  rw [hsplit, Finset.sum_range_add]
  have hz : ∑ x ∈ Finset.range h, max (-(BranchingDimensions.Letters.ent (D := toL r K LL B) P.mu s x)) 0 = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    rw [Finset.mem_range] at hm
    rw [entry_eq_of_lt LL B P.mu s m (by omega) (by omega)]
    have := hP.head ⟨s - 1, by omega⟩ ⟨m, by omega⟩ (by simp only; omega) (by simp only; omega)
    have he : (⟨s - 1, by omega⟩ : Fin N).succ = (⟨s, by omega⟩ : Fin (N + 1)) := Fin.ext (by simp; omega)
    rw [he] at this
    rw [this]
    exact max_eq_right (by simp)
  rw [hz, zero_add]
  exact Finset.sum_congr rfl fun x _ => by rw [Nat.add_comm x h]

theorem count_from_eq_vcount (LL : Letters (Fin N)) (B : Fin N → ℕ) (M t : ℕ) (hM : M ≤ N) :
    countFrom (fun l => (toL r K LL B).vec l) M (t + 1) = vcount LL t M := by
  classical
  unfold countFrom vcount
  symm
  refine Finset.card_bij (fun l _ => l.val + 1) ?_ ?_ ?_
  · intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hl
    rw [Finset.mem_filter, Finset.mem_Icc]
    beta_reduce
    rw [toL_vec LL B (l.val + 1) ⟨by omega, by omega⟩]
    exact ⟨⟨by omega, by omega⟩, hl.2.2, by omega⟩
  · intro l _ l' _ h
    exact Fin.ext (by omega)
  · intro y hy
    rw [Finset.mem_filter, Finset.mem_Icc] at hy
    have hv : (toL r K LL B).vec y = true := hy.2.1
    rw [toL_vec LL B y ⟨hy.1.1, by omega⟩] at hv
    refine ⟨⟨y - 1, by omega⟩, ?_, by simp only; omega⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨by omega, by omega, hv⟩

theorem vcount_tau_eq_add (H : HypT N n0 r K LL B od bb a La p) (t : ℕ) (ht : t ≤ n0) :
    ∀ s, n0 ≤ s → s ≤ N → vcount LL t s = vcount LL t n0 + (s - n0) := by
  intro s hs
  induction s, hs using Nat.le_induction with
  | base => intro _; simp
  | succ s hs ih =>
    intro hsN
    rw [vcount_succ LL t s (by omega) (by omega), ih (by omega), ite_eq_left (H.vec_true_of_late ⟨s, by omega⟩ (by simp only; omega))]
    omega

theorem oldest_threshold_eq (H : HypT N n0 r K LL B od bb a La p) (i : Fin N) (hi : r ≤ i.val) :
    (toL r K LL B).Bo (i.val + 1) = B (od i) := by
  have hN := H.hN
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have hod := oldest_lt_n0 H i hi
  have hlt : (od i).val < i.val := H.od_lt i hi
  have hvc : vcount LL (od i).val i.val = r := by
    refine Eq.trans ?_ (H.od_card i hi)
    unfold vcount
    congr 1
  unfold BranchingDimensions.Letters.Bo BranchingDimensions.Letters.latestV
  rw [Nat.add_sub_cancel, hn0]
  show (List.map (toL r K LL B).B (latestList (fun l => (toL r K LL B).vec l) (min i.val n0))).getD
    (r - 1 - (i.val - n0)) 0 = _
  have hx : (1 ≤ (od i).val + 1 ∧ (od i).val + 1 ≤ min i.val n0) ∧ (toL r K LL B).vec ((od i).val + 1) = true := by
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [toL_vec LL B _ ⟨by omega, by omega⟩]
    exact H.od_vec i hi
  have hc : countFrom (fun l => (toL r K LL B).vec l) (min i.val n0) ((od i).val + 1) = (r - 1 - (i.val - n0)) + 1 := by
    rw [count_from_eq_vcount LL B _ _ (by omega)]
    rcases le_total i.val n0 with h | h
    · rw [Nat.min_eq_left h, hvc]; have := H.r1; omega
    · rw [Nat.min_eq_right h]
      have := vcount_tau_eq_add H (od i).val (by omega) i.val h (by omega)
      omega
  obtain ⟨he, hel⟩ := latest_list_get_of_count _ _ _ _ hx hc
  rw [List.getD_eq_getElem _ _ (by simpa using he), List.getElem_map, hel, toL_B LL B _ ⟨by omega, by omega⟩]
  congr 1

theorem threshold_letter_eq_Xi (H : HypT N n0 r K LL B od bb a La p) (i : Fin N) :
    (toL r K LL B).XT 13 La (toB bb p) (i.val + 1) = Xi r K bb La p i := by
  have hp0 : (0 : ℝ) < p := by
    have : (13 : ℝ) ≤ (p : ℝ) := by exact_mod_cast H.p13
    linarith
  unfold BranchingDimensions.Letters.XT toB Xi
  rw [dite_eq_left ⟨by omega, by have := i.2; omega⟩]
  show La * (13 * bb ⟨i.val + 1 - 1, _⟩ / (p : ℝ)) / (((13 : ℕ) : ℝ) * ((r + K : ℕ) : ℝ)) = _
  have he : (⟨i.val + 1 - 1, by have := i.2; omega⟩ : Fin N) = i := Fin.ext (by simp)
  rw [he]
  push_cast
  field_simp

theorem typ_of_Typical [NeZero r] (H : HypT N n0 r K LL B od bb a La p) {dd : Fin N → ℕ} (P : PPath (r + K) N LL dd)
    (hP : IsPATHa LL n0 B P.mu dd) (hT : (toL r K LL B).Typical ((toL r K LL B).XT 13 La (toB bb p)) P.mu) :
    Typ LL B od bb La p P.mu := by
  have hN := H.hN
  obtain ⟨hT1, hT2, hT3⟩ := hT
  intro i
  have hi2 := i.2
  refine ⟨fun hv => ?_, fun hv hi => ?_, fun hi => ?_⟩
  · have hin : i.val < n0 := by
      by_contra hcon
      have := H.vec_true_of_late i (by omega)
      rw [hv] at this
      exact absurd this (by simp)
    have h := hT1 (i.val + 1) (by omega) (by show i.val + 1 ≤ N; omega)
      (by rw [toL_vec LL B _ ⟨by omega, by omega⟩]; exact hv)
    rw [Nat.add_sub_cancel, tail_positive_eq H P.mu i.val (by omega), tail_positive_eq H P.mu (i.val + 1) (by omega), threshold_letter_eq_Xi H i] at h
    exact h
  · have h := hT2 (i.val + 1) (by show r < i.val + 1; omega) (by show i.val + 1 ≤ N; omega)
      (by rw [toL_vec LL B _ ⟨by omega, by omega⟩]; exact hv)
    rw [Nat.add_sub_cancel, tail_negative_eq H P hP i.val (by omega), tail_negative_eq H P hP (i.val + 1) (by omega), threshold_letter_eq_Xi H i] at h
    exact h
  · have h := hT3 (i.val + 1) (by show r < i.val + 1; omega) (by show i.val + 1 ≤ N; omega)
    rw [Nat.add_sub_cancel, oldest_threshold_eq H i hi] at h
    have he : BranchingDimensions.Letters.ent (D := toL r K LL B) P.mu i.val ((toL r K LL B).r - 1) =
        plPart P.mu i.castSucc (lastIdx r) := by
      show BranchingDimensions.Letters.ent (D := toL r K LL B) P.mu i.val (r - 1) = _
      rw [entry_eq_of_lt LL B P.mu i.val (r - 1) (by omega) (by have := H.r1; omega)]
      rfl
    rw [he] at h
    exact h

end

theorem atypical_path_small_weight (D : Formalism.BasicNotions.D7) (h3 : admB3 D) : AtypicalPathSmallWeight := by
  intro N n0 r K _ _ LL B od bb a La p H μ hμ hnT
  obtain ⟨dd, hP⟩ := hμ
  obtain ⟨P, rfl⟩ := hP.path
  have hN := H.hN
  have h2N := two_N_lt_K H
  have hn0 := letters_n0_eq (r := r) (K := K) H
  have hd : Dominant (pEnd (tanPart P.mu)) := by
    intro x y hxy
    exact P.dom (Fin.last N) (by rw [Fin.le_def] at hxy ⊢; simp; omega)
  have h := (BranchingDimensions.Top.lemma_t_one (toL r K LL B) a 13 La (toB bb p) (toL_Wf H) (toL_Hyp H) (toL_TData H) P.mu
    (toL_IsPATH H P hP)).2 (fun hT => hnT (typ_of_Typical H P hP hT))
  rw [toL_wt (LL := LL) (B := B) D h3 P.mu hd]
  have hk' : (((toL r K LL B).k' : ℕ) : ℝ) = (K : ℝ) - 2 * (N : ℝ) := by
    show ((K - 2 * N : ℕ) : ℝ) = _
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hrk : (toL r K LL B).rankAA = rkA r K n0 B := by
    unfold BranchingDimensions.Letters.rankAA
    rw [hn0]
    exact rank_eq_prod_choose LL B n0 (by omega)
  rw [hk', hrk] at h
  exact h
end

end Formalism.MainNotions.SelectionLemmas.Pf.T

namespace Formalism.MainNotions.SelectionLemmas.Pf

section
open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.SelectionLemmas.Pf.T

theorem lemT_of_adm (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : LemT :=
  lemT_of (path_weight_eq_rank D hAdm.2.2.1 hAdm.2.2.2.1 hAdm.2.2.2.2.1) path_count_finite (atypical_path_small_weight D hAdm.2.2.1) typical_path_orders_small

theorem good_path_weight_of_top_count (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) (h41 : TopCountLowerBounds 1088) : GoodPathWeight 1088 :=
  good_path_weight_of_parts 1088 (path_weight_eq_rank D hAdm.2.2.1 hAdm.2.2.2.1 hAdm.2.2.2.2.1) (lemT_of_adm D hAdm) (TE.letter_dictionary_bounds h41)
end

section
open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem good_path_weight (D : Formalism.BasicNotions.D7) (hAdm : AdmB D) : GoodPathWeight 1088 :=
  good_path_weight_of_top_count D hAdm (top_count_lower_bounds 1088 (by norm_num))
end

end Formalism.MainNotions.SelectionLemmas.Pf
