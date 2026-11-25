module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.NotInSupportOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionTensorProductHasFiniteLength
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JhMultSubAddQuot
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurAdmissibleAlt
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.SocleJm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  [Fintype n] [DecidableEq n] {V X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup X] [Module ℂ X]

theorem one_le_jhMult_jac (e : (Σ a, m a) ≃ n) {ρ : Representation ℂ (Levi k m) X}
    (hρ : ρ.IsIrreducible) {τ : Representation ℂ (GL n k) V} (f : τ.IntertwiningMap (parInd e ρ))
    (hf : ∃ v, f v ≠ 0) : 1 ≤ jhMult ρ (jac e τ) := by
  obtain ⟨v, hv⟩ := hf
  obtain ⟨x, hx⟩ : ∃ x, (f v).1.1 x ≠ 0 := by
    by_contra! h
    exact hv (Subtype.ext (Subtype.ext (funext h)))
  let φ := GlobalTheory.SmGL.Model.evalOne e f
  have h1 : φ (Submodule.Quotient.mk (τ x v)) ≠ 0 := by
    have : φ (Submodule.Quotient.mk (τ x v)) = (f v).1.1 x := by
      show (f (τ x v)).1.1 1 = _
      rw [f.isIntertwining, parInd_apply, one_mul]
    rwa [this]
  have h2 : Function.Surjective φ := by
    intro w
    rcases eq_bot_or_eq_top φ.range with e' | e'
    · have h3 : φ (Submodule.Quotient.mk (τ x v)) ∈ φ.range :=
        (Representation.IntertwiningMap.mem_range _ _ _ _).2 ⟨_, rfl⟩
      rw [e'] at h3
      exact absurd h3 h1
    · have h3 : w ∈ φ.range := e' ▸ trivial
      exact (Representation.IntertwiningMap.mem_range _ _ _ _).1 h3
  exact ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (.of_surjective φ h2))

end GlobalTheory.CompanionTheory.SocleJm

namespace GlobalTheory.CompanionTheory.FrobJm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem piTensor_rep_isIrreducible (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h : ℕ} (x : Fin h → IrrGL (k := k)) :
    (piTensor fun a => (x a).rep).IsIrreducible := by
  have hKex : ∀ N : ℕ, ∃ K : Subgroup (GL (Fin N) k),
      IsOpen (K : Set (GL (Fin N) k)) ∧ IsCompact (K : Set (GL (Fin N) k)) := by
    intro N
    have hT2 : T2Space k := inferInstance
    let O : Subring k := (ValuativeRel.valuation k).integer
    have hOo : IsOpen (O : Set k) := (ValuativeRel.valuation k).isOpen_integer
    have hOc : IsCompact (O : Set k) := IsNonarchimedeanLocalField.isCompact_closedBall (K := k) 1
    let K : Subgroup (GL (Fin N) k) :=
      { carrier := {g | (∀ i j, (g : Matrix (Fin N) (Fin N) k) i j ∈ O) ∧
            ∀ i j, ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j ∈ O}
        mul_mem' := by
          rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
          refine ⟨fun i j => ?_, fun i j => ?_⟩
          · rw [Units.val_mul, Matrix.mul_apply]
            exact sum_mem fun l _ => mul_mem (ha1 i l) (hb1 l j)
          · rw [mul_inv_rev, Units.val_mul, Matrix.mul_apply]
            exact sum_mem fun l _ => mul_mem (hb2 i l) (ha2 l j)
        one_mem' := by
          refine ⟨fun i j => ?_, fun i j => ?_⟩
          · rw [Units.val_one, Matrix.one_apply]
            split_ifs
            exacts [one_mem _, zero_mem _]
          · rw [inv_one, Units.val_one, Matrix.one_apply]
            split_ifs
            exacts [one_mem _, zero_mem _]
        inv_mem' := by
          rintro a ⟨ha1, ha2⟩
          exact ⟨ha2, by rw [inv_inv]; exact ha1⟩ }
    have hKset : (K : Set (GL (Fin N) k)) =
        (⋂ i, ⋂ j, (fun g : GL (Fin N) k => (g : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k)) ∩
          ⋂ i, ⋂ j, (fun g : GL (Fin N) k => ((g⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j) ⁻¹' (O : Set k) := by
      ext g
      simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage]
      exact Iff.rfl
    refine ⟨K, ?_, ?_⟩
    · rw [hKset]
      refine IsOpen.inter (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_)
        (isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => hOo.preimage ?_)
      · exact Units.continuous_val.matrix_elem i j
      · exact Units.continuous_coe_inv.matrix_elem i j
    · rw [Units.isEmbedding_embedProduct.isInducing.isCompact_iff]
      let S : Set (Matrix (Fin N) (Fin N) k) := {A | ∀ i j, A i j ∈ O}
      have hS : IsCompact S := by
        rw [show S = Set.univ.pi fun _ : Fin N => Set.univ.pi fun _ => (O : Set k) by
          ext A
          exact ⟨fun h _ _ _ _ => h _ _, fun h i j => h i trivial j trivial⟩]
        exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hOc
      have hsub : Units.embedProduct (Matrix (Fin N) (Fin N) k) '' (K : Set (GL (Fin N) k)) =
          (S ×ˢ (MulOpposite.op '' S)) ∩
            {p | p.1 * MulOpposite.unop p.2 = 1 ∧ MulOpposite.unop p.2 * p.1 = 1} := by
        ext p
        constructor
        · rintro ⟨g, ⟨hg1, hg2⟩, rfl⟩
          exact ⟨⟨hg1, (g⁻¹ : GL (Fin N) k).val, hg2, rfl⟩, g.mul_inv, g.inv_mul⟩
        · rintro ⟨⟨hA, B, hB, hBp⟩, h1, h2⟩
          refine ⟨⟨p.1, MulOpposite.unop p.2, h1, h2⟩, ⟨hA, ?_⟩, rfl⟩
          show ∀ i j, (MulOpposite.unop p.2) i j ∈ O
          rw [← hBp]
          exact hB
      rw [hsub]
      refine (hS.prod (hS.image MulOpposite.continuous_op)).inter_right ?_
      exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd))
        continuous_const).inter
        (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)
  refine GlobalTheory.ProdFiniteLength.piTensor_isIrreducible_of_schur _ (fun a => (x a).2.rep.irr) ?_
  intro a φ hφ
  obtain ⟨K, hKo, hKc⟩ := hKex (x a).1
  exact _root_.GlobalTheory.SchurAdmissibility.schur_admissible _ K hKo hKc _ _ (x a).2.rep.irr
    (hA k _ _ _ (x a).2.rep.smooth (x a).2.rep.irr) φ hφ

theorem one_le_jm : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (_ : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ →
    ∀ f : τ.IntertwiningMap (prodIrr x hd), (∃ v, f v ≠ 0) → 1 ≤ jm x hd τ := by
  intro k _ _ _ _ hA h N x hd V _ _ τ _ f hf
  exact SocleJm.one_le_jhMult_jac (stdBlocks (fun a => (x a).1) hd) (piTensor_rep_isIrreducible hA x) f hf

end GlobalTheory.CompanionTheory.FrobJm
