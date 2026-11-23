module
public import GroundTheory.AutomorphicForms.GL2.GJLeviZetaConv
import GroundTheory.AutomorphicForms.GL2.ExistsEqPowMulOfValuationLe

@[expose] public section
set_option maxSynthPendingDepth 1
noncomputable section
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
namespace GodementJacquet
open Matrix GLnLocal Parabolic MeasureTheory Polynomial ValuativeRel
open scoped NNReal ENNReal
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {α : Type*} [LinearOrder α] {β : Fin n → α}
  {W : Type*} [AddCommGroup W] [Module ℂ W] {σ : Representation ℂ (levi F n β) W}
  [MeasurableSpace (levi F n β)] [BorelSpace (levi F n β)]

private theorem zpow_mul_mem {a b : ℤ} {x : F} (hab : a ≤ b)
    (hx : (uniformizer F : F) ^ a * x ∈ 𝒪[F]) : (uniformizer F : F) ^ b * x ∈ 𝒪[F] := by
  have h := Subring.mul_mem _ (Subring.pow_mem _ (GLnLocal.uniformizer F).2 (b - a).toNat) hx
  rwa [← mul_assoc, ← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.2 hab),
    ← zpow_add₀ (Cartan.uniformizer_ne_zero F), sub_add_cancel] at h
def leviIntegrand (σ : Representation ℂ (levi F n β) W) (θ : levi F n β →* ℝ≥0)
    (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ) (m : levi F n β) : ℂ :=
  Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (θ m : ℂ) * detPow (m : GL (Fin n) F) s * ℓ (σ m w)
theorem leviIntegrand_eq (θ : levi F n β →* ℝ≥0) (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W)
    (ℓ : Module.Dual ℂ W) (s : ℂ) (m : levi F n β) : leviIntegrand σ θ Ψ w ℓ s m =
      Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * coeffIntegrand σ θ w ℓ s m := by
  simp only [leviIntegrand, coeffIntegrand]; ring
def BlockSmall (b : Set.range β) (t : ℤ) (X : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ i j, blockOf β i = b → (uniformizer F : F) ^ (-t) * X i j ∈ 𝒪[F]
theorem zeroBlock_blockDiag {b : Set.range β} {X : Matrix (Fin n) (Fin n) F}
    (hX : ∀ i j, β i ≠ β j → X i j = 0) : ∀ i j, β i ≠ β j → zeroBlock b X i j = 0 := fun i j h => by
  simp only [zeroBlock]; split_ifs; exacts [rfl, hX i j h]
theorem eq_zeroBlock_of_invariant {Ψ : Matrix (Fin n) (Fin n) F → ℂ} {r : ℕ}
    (hinv : ∀ X Y : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      (∀ i j, β i ≠ β j → Y i j = 0) → (∀ i j, ∃ a ∈ 𝒪[F], Y i j = (uniformizer F : F) ^ r * a) →
      Ψ (X + Y) = Ψ X) {b : Set.range β} {X : Matrix (Fin n) (Fin n) F}
    (hX : ∀ i j, β i ≠ β j → X i j = 0) (hsmall : BlockSmall b r X) : Ψ X = Ψ (zeroBlock b X) := by
  conv_lhs => rw [show X = zeroBlock b X + (X - zeroBlock b X) by abel]
  refine hinv _ _ (zeroBlock_blockDiag hX)
    (fun i j h => by simp [hX i j h, zeroBlock_blockDiag hX i j h]) fun i j => exists_eq_pow_mul_iff.2 ?_
  rw [Matrix.sub_apply]; simp only [zeroBlock]; split_ifs with hi
  · rw [sub_zero]; exact hsmall i j hi
  · simp [(𝒪[F]).zero_mem]
theorem neg_le_blockOrd {b : Set.range β} {m : levi F n β} {A : ℕ}
    (h : ∀ i j, blockOf β i = b →
      (uniformizer F : F) ^ A * ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F]) :
    -((blockSize β b : ℤ) * A) ≤ blockOrd F b m := by
  let B := ((leviBlock F m b : GL (Fiber β b) F) : Matrix (Fiber β b) (Fiber β b) F)
  have hϖ : ((uniformizer F : F) ^ A) ^ Fintype.card (Fiber β b) ≠ 0 :=
    pow_ne_zero _ (pow_ne_zero _ (Cartan.uniformizer_ne_zero F))
  have hmem : ((uniformizer F : F) ^ A • B).det ∈ 𝒪[F] :=
    det_mem_integer_of_fintype fun i j => by rw [Matrix.smul_apply, smul_eq_mul]; exact h i.1 j.1 i.2
  rw [Matrix.det_smul] at hmem
  have h0 := ord_nonneg_of_mem (mul_ne_zero hϖ (det_ne_zero_of_GL _)) hmem
  rw [LocalField.ord_mul hϖ (det_ne_zero_of_GL _), ← pow_mul, ← zpow_natCast, ord_zpow_uniformizer] at h0
  simp only [blockOrd, blockSize]; push_cast at h0 ⊢; linarith
theorem IsLeviSchwartz.sub {Ψ₁ Ψ₂ : Matrix (Fin n) (Fin n) F → ℂ} (h₁ : IsLeviSchwartz β Ψ₁)
    (h₂ : IsLeviSchwartz β Ψ₂) : IsLeviSchwartz β (Ψ₁ - Ψ₂) := by
  obtain ⟨r₁, A₁, hi₁, hs₁⟩ := h₁; obtain ⟨r₂, A₂, hi₂, hs₂⟩ := h₂
  refine ⟨max r₁ r₂, max A₁ A₂, fun X Y hX hY hYs => ?_, fun X hX h0 i j => ?_⟩
  · simp only [Pi.sub_apply, hi₁ X Y hX hY fun i j => exists_eq_pow_mul_iff.2 (zpow_mul_mem (by omega)
      (exists_eq_pow_mul_iff.1 (hYs i j))), hi₂ X Y hX hY fun i j => exists_eq_pow_mul_iff.2
      (zpow_mul_mem (by omega) (exists_eq_pow_mul_iff.1 (hYs i j)))]
  · by_cases h1 : Ψ₁ X = 0
    · simpa only [zpow_natCast] using zpow_mul_mem (Nat.cast_le.2 (le_max_right _ _))
        (by simpa only [zpow_natCast] using hs₂ X hX (by simpa [h1] using h0) i j)
    · simpa only [zpow_natCast] using zpow_mul_mem (Nat.cast_le.2 (le_max_left _ _))
        (by simpa only [zpow_natCast] using hs₁ X hX h1 i j)
def shiftBlock (b : Set.range β) (Ψ : Matrix (Fin n) (Fin n) F → ℂ) : Matrix (Fin n) (Fin n) F → ℂ :=
  fun X => Ψ ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) * X)
theorem blockUnif_inv_mul_apply (b : Set.range β) (X : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) * X : Matrix (Fin n) (Fin n) F) i j =
      (uniformizer F : F) ^ (-blockIndicator b i) * X i j := by
  rw [show ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal fun i => (uniformizer F : F) ^ (-blockIndicator b i) by
    rw [InvMemClass.coe_inv, blockUnif, ← diagPow_neg, Cartan.coe_diagPow]; rfl, Matrix.diagonal_mul]
private theorem blockUnif_inv_mul_blockDiag (b : Set.range β) {X : Matrix (Fin n) (Fin n) F}
    (hX : ∀ i j, β i ≠ β j → X i j = 0) : ∀ i j, β i ≠ β j →
    ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) * X : Matrix (Fin n) (Fin n) F) i j = 0 :=
  fun i j h => by rw [blockUnif_inv_mul_apply, hX i j h, mul_zero]
theorem blockIndicator_nonneg (b : Set.range β) (i : Fin n) : 0 ≤ blockIndicator b i := by
  simp only [blockIndicator]; split_ifs <;> norm_num
theorem blockIndicator_le_one (b : Set.range β) (i : Fin n) : blockIndicator b i ≤ 1 := by
  simp only [blockIndicator]; split_ifs <;> norm_num
theorem IsLeviSchwartz.shiftBlock {Ψ : Matrix (Fin n) (Fin n) F → ℂ} (hΨ : IsLeviSchwartz β Ψ)
    (b : Set.range β) : IsLeviSchwartz β (shiftBlock b Ψ) := by
  obtain ⟨r, A, hinv, hsupp⟩ := hΨ; refine ⟨r + 1, A + 1, fun X Y hX hY hYs => ?_, fun X hX h0 i j => ?_⟩
  · simp only [GodementJacquet.shiftBlock, Matrix.mul_add]
    refine hinv _ _ (blockUnif_inv_mul_blockDiag b hX) (blockUnif_inv_mul_blockDiag b hY) fun i j => ?_
    rw [exists_eq_pow_mul_iff, blockUnif_inv_mul_apply, ← mul_assoc, ← zpow_add₀ (Cartan.uniformizer_ne_zero F)]
    exact zpow_mul_mem (by push_cast; linarith [blockIndicator_le_one b i]) (exists_eq_pow_mul_iff.1 (hYs i j))
  · have h := hsupp _ (blockUnif_inv_mul_blockDiag b hX) h0 i j
    rw [blockUnif_inv_mul_apply, ← zpow_natCast, ← mul_assoc, ← zpow_add₀ (Cartan.uniformizer_ne_zero F)] at h
    simpa only [zpow_natCast] using zpow_mul_mem (b := ((A + 1 : ℕ) : ℤ))
      (by push_cast; linarith [blockIndicator_nonneg b i]) h
theorem integrable_of_le_indicator {μ : Measure (levi F n β)} {G H : levi F n β → ℂ} (hG : Continuous G)
    {C : ℝ} (hC : 0 ≤ C) {E : Set (levi F n β)} (hH : ∫⁻ m, E.indicator (fun m => ‖H m‖ₑ) m ∂μ < ⊤)
    (hle : ∀ m, ‖G m‖ ≤ C * E.indicator (fun m => ‖H m‖) m) : Integrable G μ := by
  refine ⟨hG.aestronglyMeasurable, (lintegral_mono (g := fun m => ENNReal.ofReal C *
    E.indicator (fun m => ‖H m‖ₑ) m) fun m => ?_).trans_lt ((lintegral_const_mul' (ENNReal.ofReal C) _
      ENNReal.ofReal_ne_top).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hH))⟩
  rw [← ofReal_norm]; refine (ENNReal.ofReal_le_ofReal (hle m)).trans_eq ?_
  by_cases hm : m ∈ E <;> simp [hm, ENNReal.ofReal_mul hC, ofReal_norm]
theorem continuous_leviIntegrand (hσ : IsSmooth σ) (θ : levi F n β →* ℝ≥0) (hθ : Continuous θ)
    {Ψ : Matrix (Fin n) (Fin n) F → ℂ} (hΨ : IsLeviSchwartz β Ψ) (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ) :
    Continuous (leviIntegrand σ θ Ψ w ℓ s) :=
  (funext (leviIntegrand_eq θ Ψ w ℓ s)) ▸ hΨ.isLocallyConstant.continuous.mul (continuous_coeffIntegrand hσ θ hθ w ℓ s)
theorem mem_of_isLeviSchwartz {Ψ : Matrix (Fin n) (Fin n) F → ℂ} {A : ℕ}
    (hsupp : ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) → Ψ X ≠ 0 →
      ∀ i j, (uniformizer F : F) ^ A * X i j ∈ 𝒪[F])
    {m : levi F n β} (hm : Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ≠ 0) :
    m ∈ {m : levi F n β | ∀ b, -((blockSize β b : ℤ) * A) ≤ blockOrd F b m} :=
  fun _ => neg_le_blockOrd fun i j _ => hsupp _ (mem_levi.1 m.2) hm i j
theorem integrable_leviIntegrand (hσ : IsSmooth σ) (θ : levi F n β →* ℝ≥0) (hθ : Continuous θ)
    {μ : Measure (levi F n β)} {Ψ : Matrix (Fin n) (Fin n) F → ℂ} (hΨ : IsLeviSchwartz β Ψ)
    (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ)
    (hconv : ∀ k : Set.range β → ℤ, ∫⁻ m, {m : levi F n β | ∀ b, k b ≤ blockOrd F b m}.indicator
      (fun m => ‖coeffIntegrand σ θ w ℓ s m‖ₑ) m ∂μ < ⊤) : Integrable (leviIntegrand σ θ Ψ w ℓ s) μ := by
  obtain ⟨C, hC⟩ := hΨ.exists_bound; obtain ⟨r, A, hinv, hsupp⟩ := id hΨ
  refine integrable_of_le_indicator (continuous_leviIntegrand hσ θ hθ hΨ w ℓ s)
    (le_max_right C 0) (hconv fun b => -((blockSize β b : ℤ) * A)) fun m => ?_
  rw [leviIntegrand_eq, norm_mul]
  by_cases h0 : Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 0
  · simp [h0, mul_nonneg (le_max_right C 0) (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)]
  · rw [Set.indicator_of_mem (mem_of_isLeviSchwartz hsupp h0)]
    exact mul_le_mul_of_nonneg_right ((hC _ (mem_levi.1 m.2)).trans (le_max_left _ _)) (norm_nonneg _)
theorem coe_blockUnif_inv_mul (b : Set.range β) (m : levi F n β) :
    (((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) *
      ((((blockUnif F b * m : levi F n β) : GL (Fin n) F)) : Matrix (Fin n) (Fin n) F) =
      ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := by
  rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel_left]
theorem integral_shiftBlock (μ : Measure (levi F n β)) [μ.IsMulLeftInvariant]
    {ω : Set.range β → ℂ} (hω : ∀ b v, σ (blockUnif F b) v = ω b • v) (θ : levi F n β →* ℝ≥0)
    (Ψ : Matrix (Fin n) (Fin n) F → ℂ) (w : W) (ℓ : Module.Dual ℂ W) (s : ℂ) (b : Set.range β) :
    ∫ m, leviIntegrand σ θ (shiftBlock b Ψ) w ℓ s m ∂μ =
      ((θ (blockUnif F b) : ℂ) * ω b * qs F s ^ blockSize β b) * ∫ m, leviIntegrand σ θ Ψ w ℓ s m ∂μ := by
  rw [← integral_mul_left_eq_self _ (blockUnif F b), ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
  simp only [leviIntegrand_eq, shiftBlock, coe_blockUnif_inv_mul, coeffIntegrand_blockUnif_mul hω]; ring
theorem eq_shiftBlock_of_small {Ψ : Matrix (Fin n) (Fin n) F → ℂ} {r : ℕ}
    (hinv : ∀ X Y : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      (∀ i j, β i ≠ β j → Y i j = 0) → (∀ i j, ∃ a ∈ 𝒪[F], Y i j = (uniformizer F : F) ^ r * a) →
      Ψ (X + Y) = Ψ X) {b : Set.range β} {X : Matrix (Fin n) (Fin n) F}
    (hX : ∀ i j, β i ≠ β j → X i j = 0) (hsmall : BlockSmall b ((r : ℤ) + 1) X) :
    Ψ X = shiftBlock b Ψ X := by
  have h2 : BlockSmall b r ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) * X :
      Matrix (Fin n) (Fin n) F) := fun i j hi => by
    rw [blockUnif_inv_mul_apply, ← mul_assoc, ← zpow_add₀ (Cartan.uniformizer_ne_zero F)]
    simp only [blockIndicator, hi, ↓reduceIte, show -(r : ℤ) + -1 = -((r : ℤ) + 1) by ring]
    exact hsmall i j hi
  rw [eq_zeroBlock_of_invariant hinv hX fun i j hi => zpow_mul_mem (by omega) (hsmall i j hi), shiftBlock,
    eq_zeroBlock_of_invariant hinv (blockUnif_inv_mul_blockDiag b hX) h2]
  congr 1; ext i j; simp only [zeroBlock]; split_ifs with hi
  · rfl
  · simp only [blockUnif_inv_mul_apply, blockIndicator, hi, ↓reduceIte, neg_zero, zpow_zero, one_mul]
theorem blockSmall_shift {b b' : Set.range β} (hb : b' ≠ b) {t : ℤ} {X : Matrix (Fin n) (Fin n) F}
    (h : BlockSmall b' t X) : BlockSmall b' t
      ((((blockUnif F b)⁻¹ : levi F n β) : GL (Fin n) F) * X : Matrix (Fin n) (Fin n) F) := fun i j hi => by
  rw [blockUnif_inv_mul_apply]; simp only [blockIndicator, hi, hb, ↓reduceIte, neg_zero, zpow_zero, one_mul]; exact h i j hi
theorem leviIntegrand_sub (θ : levi F n β →* ℝ≥0) (Ψ₁ Ψ₂ : Matrix (Fin n) (Fin n) F → ℂ) (w : W)
    (ℓ : Module.Dual ℂ W) (s : ℂ) :
    leviIntegrand σ θ (Ψ₁ - Ψ₂) w ℓ s = leviIntegrand σ θ Ψ₁ w ℓ s - leviIntegrand σ θ Ψ₂ w ℓ s := by
  funext m; simp only [leviIntegrand, Pi.sub_apply]; ring
theorem exists_removeBlocks (hσ : IsSmooth σ) (θ : levi F n β →* ℝ≥0) (hθ : Continuous θ)
    (μ : Measure (levi F n β)) [μ.IsHaarMeasure] {ω : Set.range β → ℂ}
    (hω : ∀ b v, σ (blockUnif F b) v = ω b • v) (w : W) (ℓ : Module.Dual ℂ W) {s₀ : ℝ}
    (hconv : ∀ s : ℂ, s₀ < s.re → ∀ k : Set.range β → ℤ,
      ∫⁻ m, {m : levi F n β | ∀ b, k b ≤ blockOrd F b m}.indicator
        (fun m => ‖coeffIntegrand σ θ w ℓ s m‖ₑ) m ∂μ < ⊤)
    {Ψ : Matrix (Fin n) (Fin n) F → ℂ} (hΨ : IsLeviSchwartz β Ψ) (S : Finset (Set.range β)) :
    ∃ Ψ' : Matrix (Fin n) (Fin n) F → ℂ, IsLeviSchwartz β Ψ' ∧
      (∀ b ∈ S, ∃ t : ℤ, ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
        BlockSmall b t X → Ψ' X = 0) ∧
      ∀ s : ℂ, s₀ < s.re → ∫ m, leviIntegrand σ θ Ψ' w ℓ s m ∂μ =
        (∏ b ∈ S, (1 - (θ (blockUnif F b) : ℂ) * ω b * qs F s ^ blockSize β b)) *
          ∫ m, leviIntegrand σ θ Ψ w ℓ s m ∂μ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨Ψ, hΨ, by simp, fun s _ => by simp⟩
  | insert b S hb ih =>
    obtain ⟨Ψ', hΨ', hvan, hint⟩ := ih; obtain ⟨r, -, hinv, -⟩ := id hΨ'
    refine ⟨Ψ' - shiftBlock b Ψ', hΨ'.sub (hΨ'.shiftBlock b), fun b' hb' => ?_, fun s hs => ?_⟩
    · rcases Finset.mem_insert.1 hb' with rfl | hb'S
      · exact ⟨(r : ℤ) + 1, fun X hX hsm => by rw [Pi.sub_apply, ← eq_shiftBlock_of_small hinv hX hsm, sub_self]⟩
      · obtain ⟨t, ht⟩ := hvan b' hb'S
        exact ⟨t, fun X hX hsm => by rw [Pi.sub_apply, ht X hX hsm, shiftBlock,
          ht _ (blockUnif_inv_mul_blockDiag b hX) (blockSmall_shift (by rintro rfl; exact hb hb'S) hsm), sub_zero]⟩
    · rw [leviIntegrand_sub]; simp only [Pi.sub_apply]
      rw [integral_sub (integrable_leviIntegrand hσ θ hθ hΨ' w ℓ s (hconv s hs))
        (integrable_leviIntegrand hσ θ hθ (hΨ'.shiftBlock b) w ℓ s (hconv s hs)),
        integral_shiftBlock μ hω, hint s hs, Finset.prod_insert hb]; ring
theorem isLocallyConstant_comp_of_invariant {Ψ : Matrix (Fin n) (Fin n) F → ℂ} {r : ℕ}
    (hinv : ∀ X Y : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      (∀ i j, β i ≠ β j → Y i j = 0) → (∀ i j, ∃ a ∈ 𝒪[F], Y i j = (uniformizer F : F) ^ r * a) →
      Ψ (X + Y) = Ψ X) {f : levi F n β → Matrix (Fin n) (Fin n) F}
    (hbd : ∀ m i j, β i ≠ β j → f m i j = 0) (hf : ∀ i j, Continuous fun m => f m i j) :
    IsLocallyConstant fun m => Ψ (f m) := by
  rw [IsLocallyConstant.iff_exists_open]
  refine fun m => ⟨⋂ i, ⋂ j, (fun x : levi F n β => f x i j) ⁻¹'
      {x : F | (uniformizer F : F) ^ (-(r : ℤ)) * (x - f m i j) ∈ 𝒪[F]},
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (isOpen_small r _).preimage (hf i j), by simp [(𝒪[F]).zero_mem], fun x hx => ?_⟩
  simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq] at hx
  rw [show f x = f m + (f x - f m) by abel]
  exact hinv _ _ (hbd m) (fun i j h => by simp [hbd x i j h, hbd m i j h])
    fun i j => exists_eq_pow_mul_iff.2 (hx i j)
theorem continuous_zeroBlock_apply (b : Set.range β) (i j : Fin n) :
    Continuous fun m : levi F n β => zeroBlock b ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j := by
  simp only [zeroBlock]; split_ifs
  · exact continuous_const
  · exact (continuous_entry F n i j).comp continuous_subtypeVal
theorem exists_two_of_blockSize {b : Set.range β} (hb : 2 ≤ blockSize β b) :
    ∃ i₀ j₀ : Fin n, blockOf β i₀ = b ∧ β i₀ = β j₀ ∧ i₀ ≠ j₀ := by
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card (α := Fiber β b) hb
  exact ⟨x.1, y.1, x.2, congrArg Subtype.val (x.2.trans y.2.symm), fun e => hxy (Subtype.ext e)⟩
theorem integral_indicator_eq_zero (hσ : IsSmooth σ) (hc : IsCuspidal σ)
    (θ : levi F n β →* ℝ≥0) (hθ : Continuous θ) (μ : Measure (levi F n β)) [μ.IsHaarMeasure]
    {Ψ : Matrix (Fin n) (Fin n) F → ℂ} {r A : ℕ}
    (hinv : ∀ X Y : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) →
      (∀ i j, β i ≠ β j → Y i j = 0) → (∀ i j, ∃ a ∈ 𝒪[F], Y i j = (uniformizer F : F) ^ r * a) →
      Ψ (X + Y) = Ψ X)
    (hsupp : ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) → Ψ X ≠ 0 →
      ∀ i j, (uniformizer F : F) ^ A * X i j ∈ 𝒪[F])
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ X : Matrix (Fin n) (Fin n) F, (∀ i j, β i ≠ β j → X i j = 0) → ‖Ψ X‖ ≤ C)
    (w : W) (ℓ : Module.Dual ℂ W) {N : ℕ}
    (hN : ∀ m : levi F n β, ℓ (σ m w) ≠ 0 → ∀ (b : Set.range β) (t : ℤ),
      (blockSize β b : ℤ) * (t + N) ≤ blockOrd F b m → ∀ i j, blockOf β i = b →
        (uniformizer F : F) ^ (-t) * ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F])
    (s : ℂ) (hconv : ∀ (w' : W) (k : Set.range β → ℤ),
      ∫⁻ m, {m : levi F n β | ∀ b, k b ≤ blockOrd F b m}.indicator
        (fun m => ‖coeffIntegrand σ θ w' ℓ s m‖ₑ) m ∂μ < ⊤)
    {b : Set.range β} (hb : 2 ≤ blockSize β b) (Pr : (Set.range β → ℤ) → Prop)
    (hPr : ∀ v, Pr v → (blockSize β b : ℤ) * ((r : ℤ) + N) ≤ v b) :
    ∫ m, {m : levi F n β | Pr fun b' => blockOrd F b' m}.indicator (leviIntegrand σ θ Ψ w ℓ s) m ∂μ = 0 := by
  classical
  obtain ⟨i₀, j₀, hi₀, hij, hne⟩ := exists_two_of_blockSize hb
  let R : Set (levi F n β) := {m | Pr fun b' => blockOrd F b' m}
  let G := R.indicator fun m : levi F n β =>
    Ψ (zeroBlock b ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * (θ m : ℂ) * detPow (m : GL (Fin n) F) s
  rw [integral_congr_ae (g := fun m => G m * ℓ (σ m w)) (Filter.Eventually.of_forall fun m => by
    show R.indicator (leviIntegrand σ θ Ψ w ℓ s) m = G m * ℓ (σ m w)
    by_cases hm : m ∈ R
    · simp only [G, Set.indicator_of_mem hm, leviIntegrand]
      by_cases hℓ0 : ℓ (σ m w) = 0
      · simp [hℓ0]
      · rw [eq_zeroBlock_of_invariant hinv (mem_levi.1 m.2) (hN m hℓ0 b r (hPr _ hm))]
    · simp [G, hm])]
  refine integral_eq_zero_of_cuspidal hc μ hij hne ℓ (fun m u hu => ?_) (fun w' => ?_) w
  · have hRu : m * u ∈ R ↔ m ∈ R := by simp [R, blockOrd_mul, blockOrd_of_mem_unipotentRadical _ hu]
    by_cases hm : m ∈ R
    · dsimp only [G]; rw [Set.indicator_of_mem (hRu.2 hm), Set.indicator_of_mem hm,
        zeroBlock_mul_unipotent hi₀ m hu, map_mul, map_eq_one_of_mem_unipotentRadical θ hθ hu,
        mul_one, Subgroup.coe_mul, detPow_mul, detPow_eq_qs_zpow (u : GL (Fin n) F),
        ordDet_of_mem_unipotentRadical hu, zpow_zero, mul_one]
    · simp [G, hm, mt hRu.1 hm]
  · let k (b' : Set.range β) : ℤ :=
      if b' = b then (blockSize β b : ℤ) * ((r : ℤ) + N) else -((blockSize β b' : ℤ) * A)
    have heq : (fun m => G m * ℓ (σ m w')) = fun m => (if m ∈ R then (1 : ℂ) else 0) *
        (Ψ (zeroBlock b ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) * coeffIntegrand σ θ w' ℓ s m) := by
      ext m; simp only [G, coeffIntegrand, Set.indicator]; split_ifs <;> ring
    refine integrable_of_le_indicator (heq ▸ (((isLocallyConstant_blockOrds (F := F) (β := β)).comp
      fun v => if Pr v then (1 : ℂ) else 0).continuous.mul ((isLocallyConstant_comp_of_invariant hinv
        (fun m => zeroBlock_blockDiag (mem_levi.1 m.2)) (continuous_zeroBlock_apply b)).continuous.mul
        (continuous_coeffIntegrand hσ θ hθ w' ℓ s)))) hC0 (hconv w' k) fun m => ?_
    by_cases h0 : m ∈ R ∧ Ψ (zeroBlock b ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) ≠ 0
    · obtain ⟨hm, hΨ0⟩ := h0
      rw [show G m * ℓ (σ m w') = Ψ (zeroBlock b ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) *
          coeffIntegrand σ θ w' ℓ s m by simp [G, hm, coeffIntegrand]; ring,
        norm_mul, Set.indicator_of_mem (s := {m | ∀ b', k b' ≤ blockOrd F b' m}) fun b' => by
          by_cases hb' : b' = b
          · subst hb'; simpa [k] using hPr _ hm
          · simpa [k, hb'] using neg_le_blockOrd fun i j hi => by
              simpa [zeroBlock, hi, hb'] using hsupp _ (zeroBlock_blockDiag (mem_levi.1 m.2)) hΨ0 i j]
      exact mul_le_mul_of_nonneg_right (hC _ (zeroBlock_blockDiag (mem_levi.1 m.2))) (norm_nonneg _)
    · rw [show G m = 0 from Set.indicator_apply_eq_zero.2 fun hm => by
        simp [not_not.1 fun hΨ => h0 ⟨hm, hΨ⟩], zero_mul, norm_zero]
      exact mul_nonneg hC0 (Set.indicator_nonneg (fun _ _ => norm_nonneg _) _)
theorem eval_laurent_sum {x : ℂ} (hx : x ≠ 0) {K₀ : ℤ} (hK₀ : K₀ ≤ 0) (S : Finset ℤ)
    (hS : ∀ k ∈ S, K₀ ≤ k) (a : ℤ → ℂ) :
    (∑ k ∈ S, Polynomial.C (a k) * Polynomial.X ^ (k - K₀).toNat).eval x / x ^ (-K₀).toNat =
      ∑ k ∈ S, a k * x ^ k := by
  rw [Polynomial.eval_finsetSum, Finset.sum_div]; refine Finset.sum_congr rfl fun k hk => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
    ← zpow_natCast, ← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.2 (hS k hk)),
    Int.toNat_of_nonneg (neg_nonneg.2 hK₀), mul_div_assoc, ← zpow_sub₀ hx]; congr 2; ring
theorem exists_laurent (hσ : IsSmooth σ) (hc : IsCuspidal σ) (θ : levi F n β →* ℝ≥0)
    (hθ : Continuous θ) (μ : Measure (levi F n β)) [μ.IsHaarMeasure]
    {Ψ : Matrix (Fin n) (Fin n) F → ℂ} (hΨ : IsLeviSchwartz β Ψ)
    (hvan : ∀ b, blockSize β b = 1 → ∃ t : ℤ, ∀ X : Matrix (Fin n) (Fin n) F,
      (∀ i j, β i ≠ β j → X i j = 0) → BlockSmall b t X → Ψ X = 0)
    (w : W) {ℓ : Module.Dual ℂ W} (hℓ : ℓ ∈ smoothVectors (Representation.dual σ)) {s₀ : ℝ}
    (hconv : ∀ s : ℂ, s₀ < s.re → ∀ (w' : W) (k : Set.range β → ℤ),
      ∫⁻ m, {m : levi F n β | ∀ b, k b ≤ blockOrd F b m}.indicator
        (fun m => ‖coeffIntegrand σ θ w' ℓ s m‖ₑ) m ∂μ < ⊤) :
    ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
      ∫ m, leviIntegrand σ θ Ψ w ℓ s m ∂μ = P.eval (qs F s) / qs F s ^ N := by
  classical
  obtain ⟨Ns, hNs⟩ := exists_block_small hσ hc w hℓ; obtain ⟨C, hC⟩ := hΨ.exists_bound
  obtain ⟨r, A, hinv, hsupp⟩ := id hΨ; choose! t ht using hvan
  let T (b : Set.range β) : ℤ := (blockSize β b : ℤ) * ((r : ℤ) + Ns)
  let nonB1 : Finset (Set.range β) := Finset.univ.filter fun b => blockSize β b ≠ 1
  let Q (S : Finset (Set.range β)) : Set (levi F n β) := {m | ∀ b ∈ S, blockOrd F b m < T b}
  have hcut (s : ℂ) (hs : s₀ < s.re) (S : Finset (Set.range β)) (hsub : S ⊆ nonB1) :
      ∫ m, leviIntegrand σ θ Ψ w ℓ s m ∂μ = ∫ m, (Q S).indicator (leviIntegrand σ θ Ψ w ℓ s) m ∂μ := by
    have hint := integrable_leviIntegrand hσ θ hθ hΨ w ℓ s (hconv s hs w)
    induction S using Finset.induction_on with
    | empty => simp [show Q ∅ = Set.univ by ext; simp [Q]]
    | insert b S hb ih =>
      rw [ih ((Finset.subset_insert b S).trans hsub),
        show Q S = Q (insert b S) ∪ {m | (∀ b' ∈ S, blockOrd F b' m < T b') ∧ T b ≤ blockOrd F b m} by
          ext m; simp only [Q, Set.mem_union, Set.mem_ofPred_eq, Finset.forall_mem_insert]
          exact ⟨fun h => (lt_or_ge (blockOrd F b m) (T b)).imp (⟨·, h⟩) (⟨h, ·⟩), fun h => h.elim And.right And.left⟩,
        Set.indicator_union_of_disjoint (Set.disjoint_left.2 fun m h1 h2 => (h1 b (Finset.mem_insert_self _ _)).not_ge h2.2),
        integral_add (hint.indicator (measurableSet_blockOrds fun v => ∀ b' ∈ insert b S, v b' < T b'))
          (hint.indicator (measurableSet_blockOrds fun v => (∀ b' ∈ S, v b' < T b') ∧ T b ≤ v b)),
        integral_indicator_eq_zero hσ hc θ hθ μ hinv hsupp (le_max_right C 0)
          (fun X hX => (hC X hX).trans (le_max_left _ _)) w ℓ hNs s (hconv s hs)
          (by have := (Finset.mem_filter.1 (hsub (Finset.mem_insert_self b S))).2; have := blockSize_pos β b; omega)
          (fun v => (∀ b' ∈ S, v b' < T b') ∧ T b ≤ v b) (fun _ hv => hv.2), add_zero]
  let K₀ : ℤ := -∑ b, (blockSize β b : ℤ) * A; let K₁ : ℤ := ∑ b, (max (T b) ((blockSize β b : ℤ) * (t b + Ns)) - 1)
  let e (m : levi F n β) : ℂ := Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (θ m : ℂ) * ℓ (σ m w)
  let Qk (k : ℤ) : Set (levi F n β) := {m | (∀ b ∈ nonB1, blockOrd F b m < T b) ∧ ∑ b, blockOrd F b m = k}
  refine ⟨(-K₀).toNat, ∑ k ∈ Finset.Icc K₀ K₁, Polynomial.C (∫ m, (Qk k).indicator e m ∂μ) *
    Polynomial.X ^ (k - K₀).toNat, fun s hs => ?_⟩
  rw [eval_laurent_sum (qs_ne_zero s) (neg_nonpos.2 (Finset.sum_nonneg fun _ _ => by positivity)) _
    (fun k hk => (Finset.mem_Icc.1 hk).1), hcut s hs nonB1 le_rfl]
  have hint := integrable_leviIntegrand hσ θ hθ hΨ w ℓ s (hconv s hs w)
  have he_eq (m : levi F n β) : qs F s ^ ordDet (m : GL (Fin n) F) * e m = leviIntegrand σ θ Ψ w ℓ s m := by
    simp only [leviIntegrand, e, detPow_eq_qs_zpow]; ring
  have hrange {m} (hm : m ∈ Q nonB1) (h0 : leviIntegrand σ θ Ψ w ℓ s m ≠ 0) :
      ordDet (m : GL (Fin n) F) ∈ Finset.Icc K₀ K₁ := by
    have hΨ0 : Ψ ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) ≠ 0 := fun h => h0 (by simp [leviIntegrand, h])
    rw [Finset.mem_Icc, ordDet_eq_sum_blockOrd]
    refine ⟨(Finset.sum_neg_distrib _).symm.trans_le
      (Finset.sum_le_sum fun b _ => mem_of_isLeviSchwartz hsupp hΨ0 b), Finset.sum_le_sum fun b _ => ?_⟩
    by_cases hb1 : blockSize β b = 1
    · refine le_of_not_gt fun hcon => hΨ0 (ht b hb1 _ (mem_levi.1 m.2) fun i j hi =>
        hNs m (fun h => h0 (by simp [leviIntegrand, h])) b (t b) ?_ i j hi)
      linarith [le_max_right (T b) ((blockSize β b : ℤ) * (t b + Ns))]
    · linarith [hm b (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb1⟩),
        le_max_left (T b) ((blockSize β b : ℤ) * (t b + Ns))]
  rw [integral_congr_ae (g := fun m => ∑ k ∈ Finset.Icc K₀ K₁, qs F s ^ k * (Qk k).indicator e m)
    (Filter.Eventually.of_forall fun m => by
      dsimp only
      by_cases hm : m ∈ Q nonB1
      · have hmk : m ∈ Qk (ordDet (m : GL (Fin n) F)) := ⟨hm, (ordDet_eq_sum_blockOrd m).symm⟩
        rw [Set.indicator_of_mem hm, eq_comm, Finset.sum_eq_single (ordDet (m : GL (Fin n) F))]
        · rw [Set.indicator_of_mem hmk, he_eq]
        · exact fun k _ hk => by simp [Set.indicator_of_notMem (s := Qk k)
            fun h => hk ((ordDet_eq_sum_blockOrd m).trans h.2).symm]
        · exact fun hmem => by rw [Set.indicator_of_mem hmk, he_eq]; exact not_not.1 (mt (hrange hm) hmem)
      · simp [hm, show ∀ k, m ∉ Qk k from fun _ h => hm h.1]),
    integral_finsetSum _ fun k _ => (((hint.indicator (measurableSet_blockOrds fun v =>
      (∀ b ∈ nonB1, v b < T b) ∧ ∑ b, v b = k)).const_mul (qs F s ^ k)⁻¹).congr
      (Filter.Eventually.of_forall fun m => by
        dsimp only; rw [← Set.indicator_const_mul]
        exact (congrFun (Set.indicator_congr fun m hm => by
          rw [← he_eq, (ordDet_eq_sum_blockOrd m).trans hm.2,
            inv_mul_cancel_left₀ (zpow_ne_zero k (qs_ne_zero s))]) m).symm)).const_mul _]
  exact Finset.sum_congr rfl fun k _ => by rw [integral_const_mul, mul_comm]
theorem exists_leviZeta (hσ : IsSmooth σ) [σ.IsIrreducible] (hc : IsCuspidal σ)
    (θ : levi F n β →* ℝ≥0) (hθ : Continuous θ) (μM : Measure (levi F n β)) [μM.IsHaarMeasure] :
    ∃ s₀ : ℝ, ∃ D : ℂ[X], D.eval 0 = 1 ∧ ∀ Ψ : Matrix (Fin n) (Fin n) F → ℂ, IsLeviSchwartz β Ψ →
      ∀ w : W, ∀ ℓ ∈ smoothVectors (Representation.dual σ),
        (∀ s : ℂ, s₀ < s.re → Integrable (leviIntegrand σ θ Ψ w ℓ s) μM) ∧
        ∃ (N : ℕ) (P : ℂ[X]), ∀ s : ℂ, s₀ < s.re →
          D.eval (qs F s) * ∫ m, leviIntegrand σ θ Ψ w ℓ s m ∂μM = P.eval (qs F s) / qs F s ^ N := by
  classical
  obtain ⟨ω, hω⟩ := exists_blockChar (F := F) hσ; obtain ⟨s₀, -, hconv⟩ := exists_lintegral_lt_top hσ hc θ hθ μM
  let B1 : Finset (Set.range β) := Finset.univ.filter fun b => blockSize β b = 1
  refine ⟨s₀, ∏ b ∈ B1, (1 - Polynomial.C ((θ (blockUnif F b) : ℂ) * ω b) * Polynomial.X),
    by rw [Polynomial.eval_prod]; exact Finset.prod_eq_one fun _ _ => by simp,
    fun Ψ hΨ w ℓ hℓ => ⟨fun s hs => integrable_leviIntegrand hσ θ hθ hΨ w ℓ s (hconv s hs w ℓ hℓ), ?_⟩⟩
  obtain ⟨Ψ', hΨ', hvan, hint⟩ := exists_removeBlocks hσ θ hθ μM hω w ℓ (fun s hs k => hconv s hs w ℓ hℓ k) hΨ B1
  obtain ⟨N, P, hNP⟩ := exists_laurent hσ hc θ hθ μM hΨ'
    (fun b hb => hvan b (Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩)) w hℓ (fun s hs w' k => hconv s hs w' ℓ hℓ k)
  refine ⟨N, P, fun s hs => ?_⟩; rw [← hNP s hs, hint s hs, Polynomial.eval_prod]; congr 1
  exact Finset.prod_congr rfl fun b hb => by simp [(Finset.mem_filter.1 hb).2]
end GodementJacquet
end GroundTheory.Automorphic
