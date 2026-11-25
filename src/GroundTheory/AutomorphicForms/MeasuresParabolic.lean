module

public import GroundTheory.AutomorphicForms.Iwasawa
public import GroundTheory.AutomorphicForms.MeasuresChart
public import Mathlib.Topology.Algebra.Group.Units
public import GroundTheory.AutomorphicForms.MeasuresGL
import Mathlib.Tactic.TypeStar

@[expose] public section

namespace GroundTheory.Automorphic

open MeasureTheory Measure Topology Filter Set ValuativeRel Iwasawa
open scoped NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false

namespace Measures

/-- A subgroup of the general linear group cut out by a transitive pattern of allowed entries. -/
structure MatrixSupportChart {F : Type*} [Field F] {n : ℕ} (P : Fin n → Fin n → Prop)
    (G : Subgroup (GL (Fin n) F)) where
  /-- The matrices supported on the allowed positions. -/
  space : Submodule F (Matrix (Fin n) (Fin n) F)
  mem_space : ∀ A, A ∈ space ↔ ∀ i j, ¬ P i j → A i j = 0
  mem_group : ∀ g : GL (Fin n) F, g ∈ G ↔ (g : Matrix (Fin n) (Fin n) F) ∈ space
  trans : ∀ {i j k}, P i j → P j k → P i k

namespace MatrixSupportChart

variable {F : Type*} [Field F] {n : ℕ} {P : Fin n → Fin n → Prop}
  {G : Subgroup (GL (Fin n) F)} (D : MatrixSupportChart P G)

abbrev Index (P : Fin n → Fin n → Prop) := {ij : Fin n × Fin n // P ij.1 ij.2}

theorem mul_mem {A B : Matrix (Fin n) (Fin n) F} (hA : A ∈ D.space)
    (hB : B ∈ D.space) : A * B ∈ D.space := by
  refine (D.mem_space _).2 fun i j hij => ?_
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hik : P i k
  · rw [(D.mem_space _).1 hB k j (fun hkj => hij (D.trans hik hkj)), mul_zero]
  · rw [(D.mem_space _).1 hA i k hik, zero_mul]

variable [DecidableRel P]

/-- Read the allowed entries, extending a coordinate vector by zero in the inverse direction. -/
def coord : D.space ≃ₗ[F] (Index P → F) where
  toFun A s := (A : Matrix (Fin n) (Fin n) F) s.1.1 s.1.2
  invFun x := ⟨Matrix.of fun i j => if h : P i j then x ⟨(i, j), h⟩ else 0,
    (D.mem_space _).2 fun i j h => by simp [h]⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv A := by
    ext i j
    by_cases h : P i j
    · simp [h]
    · simp [h, (D.mem_space _).1 A.2 i j h]
  right_inv x := by
    funext s
    simp [s.2]

theorem coord_symm_single (t : Index P) :
    ((D.coord.symm (Pi.single t 1) : D.space) : Matrix (Fin n) (Fin n) F) =
      Matrix.single t.1.1 t.1.2 1 := by
  obtain ⟨⟨a, b⟩, hab⟩ := t
  change P a b at hab
  ext i j
  by_cases hi : a = i <;> by_cases hj : b = j <;>
    simp [coord, Pi.single_apply, Subtype.ext_iff, Prod.ext_iff] <;> grind

noncomputable def mulLeft (g : G) : D.space ≃ₗ[F] D.space :=
  (Units.mulLeftLinearEquiv F _ (g : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact D.mul_mem ((D.mem_group _).1 g.2) hA
    · exact ⟨((g⁻¹ : G) : GL (Fin n) F) * A, D.mul_mem ((D.mem_group _).1 (g⁻¹).2) hA,
        by simp [← mul_assoc]⟩)

noncomputable def mulRight (g : G) : D.space ≃ₗ[F] D.space :=
  (Units.mulRightLinearEquiv F (g : GL (Fin n) F)).ofSubmodules _ _ (by
    refine le_antisymm ?_ fun A hA => ?_
    · rintro _ ⟨A, hA, rfl⟩
      exact D.mul_mem hA ((D.mem_group _).1 g.2)
    · exact ⟨A * ((g⁻¹ : G) : GL (Fin n) F), D.mul_mem hA ((D.mem_group _).1 (g⁻¹).2),
        by simp [mul_assoc]⟩)

noncomputable def adjoint (g : G) : D.space ≃ₗ[F] D.space :=
  (D.mulLeft g).trans (D.mulRight g⁻¹)

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

include D in
theorem isClosed : IsClosed (G : Set (GL (Fin n) F)) := by
  have eq : (G : Set (GL (Fin n) F)) =
      ⋂ i, ⋂ j, ⋂ (_ : ¬ P i j), (fun g : GL (Fin n) F => g i j) ⁻¹' {0} := by
    ext g
    simp only [SetLike.mem_coe, D.mem_group, D.mem_space, Set.mem_iInter, Set.mem_preimage,
      Set.mem_singleton_iff]
  rw [eq]
  exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_singleton.preimage (GLnLocal.continuous_entry F n i j)

def toSpace (g : G) : D.space := ⟨(g : GL (Fin n) F), (D.mem_group _).1 g.2⟩

theorem isOpenEmbedding_toSpace : IsOpenEmbedding D.toSpace := by
  have hemb : IsEmbedding D.toSpace :=
    ((isOpenEmbedding_val F n).isEmbedding.comp IsEmbedding.subtypeVal).codRestrict
      (D.space : Set (Matrix (Fin n) (Fin n) F)) fun g : G => (D.mem_group _).1 g.2
  refine ⟨hemb, ?_⟩
  have hr : Set.range D.toSpace = Subtype.val ⁻¹' Set.range
      (Units.val : GL (Fin n) F → Matrix (Fin n) (Fin n) F) := by
    ext A
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨u, hu⟩
      exact ⟨⟨u, (D.mem_group _).2 (hu ▸ A.2)⟩, Subtype.ext hu⟩
  rw [hr]
  exact (isOpenEmbedding_val F n).isOpen_range.preimage continuous_subtypeVal

def coordHomeomorph : D.space ≃ₜ (Index P → F) where
  toEquiv := D.coord.toEquiv
  continuous_toFun := continuous_pi fun s => continuous_subtypeVal.matrix_elem s.1.1 s.1.2
  continuous_invFun := by
    refine Continuous.subtype_mk (continuous_matrix fun i j => ?_) _
    by_cases h : P i j
    · simpa only [Matrix.of_apply, h, dite_true] using
        (continuous_apply (⟨(i, j), h⟩ : Index P) : Continuous fun x : Index P → F => x _)
    · simpa only [Matrix.of_apply, h, dite_false] using
        (continuous_const : Continuous fun _ : Index P → F => (0 : F))

noncomputable def chart : LinearChart F (Index P) G where
  toFun g := D.coord (D.toSpace g)
  isOpenEmbedding := D.coordHomeomorph.isOpenEmbedding.comp D.isOpenEmbedding_toSpace
  left g := D.coord.symm.trans ((D.mulLeft g).trans D.coord)
  right g := D.coord.symm.trans ((D.mulRight g).trans D.coord)
  toFun_mul_left g x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl
  toFun_mul_right g x := by
    simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
    rfl

theorem modularCharacter_eq [LocallyCompactSpace G] (g : G) :
    modularCharacter g = distribHaarChar F (LinearEquiv.det (D.adjoint g)) := by
  borelize F ↥G
  rw [D.chart.modularCharacter_eq, LinearChart.leftModulus, LinearChart.rightModulus,
    distribHaarChar_pi_eq, distribHaarChar_pi_eq]
  have hr : D.mulRight g⁻¹ = (D.mulRight g)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    ext A : 2
    show (A : Matrix (Fin n) (Fin n) F) * ((g : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
      (((g⁻¹ : G) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = A
    simp [mul_assoc]
  change _ = distribHaarChar F (LinearEquiv.det (D.mulRight g⁻¹ * D.mulLeft g))
  have hl : LinearEquiv.det (D.chart.left g) = LinearEquiv.det (D.mulLeft g) :=
    LinearEquiv.det_conj (D.mulLeft g) D.coord
  have hr' : LinearEquiv.det (D.chart.right g) = LinearEquiv.det (D.mulRight g) :=
    LinearEquiv.det_conj (D.mulRight g) D.coord
  rw [hl, hr', hr, map_mul, map_inv, map_mul, map_inv, div_eq_mul_inv, mul_comm]

include D in
theorem modularCharacter_eq_one_of_mem_integralGL [LocallyCompactSpace G] (g : G)
    (hg : (g : GL (Fin n) F) ∈ GLnLocal.integralGL F n) : modularCharacter g = 1 := by
  borelize F ↥G
  let V : OpenSubgroup G := ⟨(GLnLocal.integralGL F n).subgroupOf G,
    (GLnLocal.isOpen_integralGL F n).preimage continuous_subtypeVal⟩
  have hV : IsCompact (V : Set G) :=
    D.isClosed.isClosedEmbedding_subtypeVal.isCompact_preimage (GLnLocal.isCompact_integralGL F n)
  obtain ⟨hl, hr⟩ := D.chart.modulus_eq_one_of_mem hV (v := g) hg
  rw [D.chart.modularCharacter_eq, hl, hr, div_one]

end MatrixSupportChart

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)

def lieParabolic : Submodule F (Matrix (Fin n) (Fin n) F) where
  carrier := {A | A.BlockTriangular β}
  add_mem' ha hb := ha.add hb
  zero_mem' := Matrix.blockTriangular_zero
  smul_mem' c A hA i j hij := by
    simp [hA hij]

abbrev ParabolicIndex : Type := {ij : Fin n × Fin n // ¬ β ij.2 < β ij.1}

def blockUpperSupport : MatrixSupportChart (fun i j => ¬ β j < β i) (blockUpper F n β) where
  space := lieParabolic F n β
  mem_space _ := ⟨fun h _ _ hij => h (not_not.mp hij), fun h _ _ hij => h _ _ (not_not.mpr hij)⟩
  mem_group _ := Iff.rfl
  trans h₁ h₂ := not_lt.mpr (le_trans (not_lt.mp h₁) (not_lt.mp h₂))

noncomputable def parabolicCoord : lieParabolic F n β ≃ₗ[F] (ParabolicIndex n β → F) :=
  (blockUpperSupport F n β).coord

theorem isClosed_blockUpper : IsClosed (blockUpper F n β : Set (GL (Fin n) F)) :=
  (blockUpperSupport F n β).isClosed

instance locallyCompactSpace_blockUpper : LocallyCompactSpace (blockUpper F n β) :=
  (isClosed_blockUpper F n β).locallyCompactSpace

noncomputable def adLie (p : blockUpper F n β) : lieParabolic F n β ≃ₗ[F] lieParabolic F n β :=
  (blockUpperSupport F n β).adjoint p

@[simp] theorem coe_adLie (p : blockUpper F n β) (A : lieParabolic F n β) :
    ((adLie F n β p A : lieParabolic F n β) : Matrix (Fin n) (Fin n) F) =
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * A *
        (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) :=
  rfl

noncomputable def parabolicChart : LinearChart F (ParabolicIndex n β) (blockUpper F n β) :=
  (blockUpperSupport F n β).chart

variable {F n β}

theorem modularCharacter_blockUpper (p : blockUpper F n β) :
    modularCharacter p = distribHaarChar F (LinearEquiv.det (adLie F n β p)) :=
  (blockUpperSupport F n β).modularCharacter_eq p

section Triangular

theorem coe_parabolicCoord_symm_single (t : ParabolicIndex n β) :
    (((parabolicCoord F n β).symm (Pi.single t 1) : lieParabolic F n β) :
      Matrix (Fin n) (Fin n) F) = Matrix.single t.1.1 t.1.2 1 :=
  (blockUpperSupport F n β).coord_symm_single t

theorem mul_single_mul_apply (A B : Matrix (Fin n) (Fin n) F) (a b i j : Fin n) :
    (A * Matrix.single a b (1 : F) * B) i j = A i a * B b j := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, ite_mul]

theorem det_adLie_of_mem_borel (p : blockUpper F n β) (hp : (p : GL (Fin n) F) ∈ borel F n) :
    (LinearEquiv.det (adLie F n β p) : F) = ∏ s : ParabolicIndex n β,
      ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1 *
        (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2 := by
  classical
  set P : Matrix (Fin n) (Fin n) F := ((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  set Q : Matrix (Fin n) (Fin n) F :=
    (((p : GL (Fin n) F)⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hP : P.IsUpperTriangular := hp
  have hQ : Q.IsUpperTriangular := (borel F n).inv_mem hp
  let A : (ParabolicIndex n β → F) →ₗ[F] (ParabolicIndex n β → F) :=
    (((parabolicCoord F n β).symm.trans ((adLie F n β p).trans (parabolicCoord F n β))) :
      (ParabolicIndex n β → F) →ₗ[F] (ParabolicIndex n β → F))
  have hdet : (LinearEquiv.det (adLie F n β p) : F) = LinearMap.det A := by
    rw [← LinearEquiv.det_conj (adLie F n β p) (parabolicCoord F n β), LinearEquiv.coe_det]
    rfl
  have hM : ∀ s t, LinearMap.toMatrix' A s t = P s.1.1 t.1.1 * Q t.1.2 s.1.2 := by
    intro s t
    rw [LinearMap.toMatrix'_apply]
    show ((adLie F n β p ((parabolicCoord F n β).symm (Pi.single t 1)) : lieParabolic F n β) :
      Matrix (Fin n) (Fin n) F) s.1.1 s.1.2 = _
    rw [coe_adLie, coe_parabolicCoord_symm_single, mul_single_mul_apply]
  let κ : ParabolicIndex n β → Lex (Fin n × (Fin n)ᵒᵈ) :=
    fun s => toLex (s.1.1, OrderDual.toDual s.1.2)
  have hκ : Function.Injective κ := by
    intro s t h
    simp only [κ, toLex_inj, Prod.mk.injEq, OrderDual.toDual_inj] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  have hBT : (LinearMap.toMatrix' A).BlockTriangular κ := by
    intro s t hts
    rw [hM]
    rcases Prod.Lex.lt_iff.1 hts with h | ⟨h1, h2⟩
    · have h' : t.1.1 < s.1.1 := h
      rw [hP h', zero_mul]
    · have h' : s.1.2 < t.1.2 := h2
      rw [hQ h', mul_zero]
  rw [hdet, ← LinearMap.det_toMatrix', hBT.det, Finset.prod_image fun s _ t _ h => hκ h]
  refine Finset.prod_congr rfl fun s _ => ?_
  let : Unique {t // κ t = κ s} :=
    ⟨⟨⟨s, rfl⟩⟩, fun t => Subtype.ext (hκ t.2)⟩
  rw [Matrix.det_unique]
  show LinearMap.toMatrix' A (default : {t // κ t = κ s}).1 (default : {t // κ t = κ s}).1 = _
  rw [hM]
  rfl

theorem modularCharacter_blockUpper_of_mem_borel (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ borel F n) :
    modularCharacter p = ∏ s : ParabolicIndex n β,
      modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1) /
        modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2) := by
  rw [modularCharacter_blockUpper, ← modulus_units, det_adLie_of_mem_borel p hp, map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_mul, inv_apply_self_of_mem_borel F n hp, map_inv₀, div_eq_mul_inv]

theorem modularCharacter_blockUpper_of_mem_borel' (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ borel F n) :
    modularCharacter p = ∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2},
      modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.1 s.1.1) /
        modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) s.1.2 s.1.2) := by
  classical
  rw [modularCharacter_blockUpper_of_mem_borel p hp]
  set f : Fin n → ℝ≥0 := fun i => modulus (((p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i)
  have hf : ∀ i, f i ≠ 0 := fun i => modulus_ne_zero (apply_self_ne_zero_of_mem_borel F n hp i)
  change ∏ s : ParabolicIndex n β, f s.1.1 / f s.1.2 =
    ∏ s : {ij : Fin n × Fin n // β ij.1 < β ij.2}, f s.1.1 / f s.1.2
  let g : Fin n × Fin n → ℝ≥0 := fun ij => f ij.1 / f ij.2
  rw [← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n => ¬ β ij.2 < β ij.1)
      (by simp) g,
    ← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 < β ij.2)
      (by simp) g]
  have hsplit : (Finset.univ.filter fun ij : Fin n × Fin n => ¬ β ij.2 < β ij.1) =
      (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 < β ij.2) ∪
        (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 = β ij.2) := by
    ext ij
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, not_lt]
    exact le_iff_lt_or_eq
  have hdisj : Disjoint (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 < β ij.2)
      (Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 = β ij.2) := by
    rw [Finset.disjoint_filter]
    intro ij _ h1 h2
    exact h1.ne h2
  rw [hsplit, Finset.prod_union hdisj]
  set S := Finset.univ.filter fun ij : Fin n × Fin n => β ij.1 = β ij.2
  have hswap : ∏ ij ∈ S, f ij.2 = ∏ ij ∈ S, f ij.1 := by
    refine Finset.prod_nbij' Prod.swap Prod.swap (fun ij hij => ?_) (fun ij hij => ?_)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hij ⊢
      exact hij.symm
    · simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Prod.fst_swap,
        Prod.snd_swap] at hij ⊢
      exact hij.symm
  have hone : ∏ ij ∈ S, g ij = 1 := by
    rw [Finset.prod_div_distrib, hswap, div_self]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hf _
  rw [hone, mul_one]

theorem modularCharacter_borel (b : blockUpper F n (id : Fin n → Fin n)) :
    modularCharacter b = ∏ i : Fin n,
      modulus (((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i) ^ ((n : ℤ) - 1 - 2 * i) := by
  classical
  rw [modularCharacter_blockUpper_of_mem_borel b b.2]
  set f : Fin n → ℝ≥0 := fun i => modulus (((b : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i i)
  have hf : ∀ i, f i ≠ 0 := fun i => modulus_ne_zero (apply_self_ne_zero_of_mem_borel F n b.2 i)
  have hsub : ∀ g : Fin n × Fin n → ℝ≥0,
      ∏ s : ParabolicIndex n (id : Fin n → Fin n), g s.1 =
        ∏ i : Fin n, ∏ j : Fin n, if i ≤ j then g (i, j) else 1 := by
    intro g
    rw [← Finset.prod_subtype (Finset.univ.filter fun ij : Fin n × Fin n => ¬ ij.2 < ij.1)
      (by simp), Finset.prod_filter, Fintype.prod_prod_type]
    simp only [not_lt]
  change ∏ s : ParabolicIndex n (id : Fin n → Fin n), f s.1.1 / f s.1.2 = _
  rw [Finset.prod_div_distrib, hsub (fun ij => f ij.1), hsub (fun ij => f ij.2),
    Finset.prod_comm (f := fun i j => if i ≤ j then f j else 1)]
  have h1 : ∀ i : Fin n, (∏ j : Fin n, if i ≤ j then f i else 1) = f i ^ (n - i) := by
    intro i
    rw [← Finset.prod_filter, Finset.prod_const, Finset.filter_le_eq_Ici, Fin.card_Ici]
  have h2 : ∀ j : Fin n, (∏ i : Fin n, if i ≤ j then f j else 1) = f j ^ ((j : ℕ) + 1) := by
    intro j
    rw [← Finset.prod_filter, Finset.prod_const, Finset.filter_ge_eq_Iic, Fin.card_Iic]
  simp only [h1, h2]
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_sub₀ (hf i)]
  congr 1
  have := i.is_lt
  push_cast [Nat.cast_sub this.le]
  ring

end Triangular

section Unipotent

variable (F n β)

abbrev UnipotentIndex : Type := {ij : Fin n × Fin n // β ij.1 < β ij.2}

variable {F n β}

theorem mul_mul_apply_mem_integer {A M B : Matrix (Fin n) (Fin n) F} (hA : ∀ i j, A i j ∈ 𝒪[F])
    (hM : ∀ i j, M i j ∈ 𝒪[F]) (hB : ∀ i j, B i j ∈ 𝒪[F]) (i j : Fin n) :
    (A * M * B) i j ∈ 𝒪[F] := by
  rw [Matrix.mul_apply]
  refine Subring.sum_mem _ fun b _ => Subring.mul_mem _ ?_ (hB b j)
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun a _ => Subring.mul_mem _ (hA i a) (hM a b)

theorem modularCharacter_eq_one_of_mem_integralGL (p : blockUpper F n β)
    (hp : (p : GL (Fin n) F) ∈ GLnLocal.integralGL F n) : modularCharacter p = 1 :=
  (blockUpperSupport F n β).modularCharacter_eq_one_of_mem_integralGL p hp

end Unipotent

variable [MeasurableSpace F] [BorelSpace F] [MeasurableSpace (GL (Fin n) F)]
  [BorelSpace (GL (Fin n) F)]

noncomputable def haarParabolic (μ₀ : Measure (ParabolicIndex n β → F)) :
    Measure (blockUpper F n β) :=
  (parabolicChart F n β).haar μ₀

variable (μ₀ : Measure (ParabolicIndex n β → F)) [μ₀.IsAddHaarMeasure]

instance isHaarMeasure_haarParabolic : (haarParabolic μ₀).IsHaarMeasure :=
  LinearChart.isHaarMeasure_haar _ μ₀

end Measures

end GroundTheory.Automorphic
