module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapSurjectiveStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScalDet

open GlobalTheory.DblScal
open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem udat_mul {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} {R : Type} [Zero R] {ev : AF F → R}
    {p q : UD σ J} (hp : p ∈ UDAt σ J ev) (hq : q ∈ UDAt σ J ev) : p * q ∈ UDAt σ J ev := by
  intro u hu
  have e : ((((p * q : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) - 1 =
      ((((p : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) *
        (((q : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) +
      ((((q : UD σ J) : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) := by
    simp [sub_mul]
  rw [e, smul_add, ← Matrix.smul_mul, hp u hu, hq u hu, Matrix.zero_mul, add_zero]

theorem udat_one {σ : E →ₐ[F] E} {d : ℕ} {J : Matrix (Fin d) (Fin d) E} {R : Type} [Zero R] {ev : AF F → R} :
    (1 : UD σ J) ∈ UDAt σ J ev := by
  intro u _
  simp

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr hn)
  have key : (A.submatrix id e.symm)ᵀ * M * (A.submatrix id e.symm).map star =
      (Aᵀ * M * A.map star).submatrix e.symm e.symm := by
    ext i j; rfl
  have hd := congrArg Matrix.det key
  rw [Matrix.det_submatrix_equiv_self, hA, Matrix.det_mul, Matrix.det_mul] at hd
  intro h0
  rw [h0] at hd
  simp [Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg] at hd
  exact pow_ne_zero _ (by norm_num) hd.symm

theorem det_ne_zero_of_skew {σ : E →ₐ[F] E} {B : Base F E} {d r s : ℕ} {W : Spc F E d} (h : W.IsSkew σ B r s) :
    W.J.det ≠ 0 := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have h0 := det_ne_zero_of_hasSig (h.sig (InfinitePlace.mk φ))
  intro e
  apply h0
  rw [Matrix.det_smul, show W.J.map _ = RingHom.mapMatrix _ W.J from rfl, ← RingHom.map_det, e, map_zero, mul_zero]

theorem mulLaw : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (ψ : AddChar (AF F) ℂ) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v)
    (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (dd : DblCo σ X W) (omd : DblRep σ (n := n) W),
    IsUSplitting (adeleClass F) ψ dd (actB (cA σ)) omd → LocOps omd v →
    ∀ ιd, IsLinD ψ dd t b c ιd → ∀ cd, IsShapeD omd t c ιd cd →
    cd 1 = 1 ∧ ∀ p ∈ UDAt σ W.J (evFin F v), ∀ q ∈ UDAt σ W.J (evFin F v), cd (p * q) = cd p * cd q := by
  intro F E _ _ _ _ _ σ ψ n d X W v t b c dd omd hS hL ιd hI cd hD
  obtain ⟨φ0, hφ0, hne⟩ : ∃ φ ∈ SB (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v), ιd φ ≠ 0 := by
    have hmem : (intM (Fv F v) (Fin n) (Fin d ⊕ Fin d)).indicator (1 : Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v) → ℂ) ∈
        SB (Matrix (Fin n) (Fin d ⊕ Fin d) (Fv F v)) := indicator_intM_mem_SB
    obtain ⟨φ, hφ, he⟩ := hI.bij.surjOn hmem
    refine ⟨φ, hφ, fun h => ?_⟩
    have h0 := congrFun he 0
    rw [h, Set.indicator_of_mem (fun i j => by simp)] at h0
    simp at h0
  obtain ⟨Z, hZ⟩ : ∃ Z, ιd φ0 Z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have comp : ∀ p q : UD σ W.J, ∀ φ φ₁ φ₂ : (Fin n × Fin d ⊕ Fin n × Fin d → Fv F v) → ℂ,
      Acts (evFin F v) (omd q) φ φ₁ → Acts (evFin F v) (omd p) φ₁ φ₂ → Acts (evFin F v) (omd (p * q)) φ φ₂ := by
    intro p q φ φ₁ φ₂ hq hp r hr
    have h1 := hq r hr
    have hr1 : Rest (evFin F v) φ₁ r := ⟨hr.1, h1 ▸ hS.pres q _ hr.2⟩
    rw [map_mul, Module.End.mul_apply, h1, hp r hr1]
  refine ⟨?_, ?_⟩
  · have hA : Acts (evFin F v) (omd 1) φ0 φ0 := fun r _ => by rw [map_one, Module.End.one_apply]
    have e := congrFun (hD 1 udat_one φ0 hφ0 φ0 hφ0 hA) Z
    simp only [map_one, Units.val_one, Matrix.mul_one, Pi.smul_apply, smul_eq_mul] at e
    exact (mul_eq_right₀ hZ).mp e.symm
  · intro p hp q hq
    obtain ⟨φ₁, hφ₁, h1⟩ := hL q hq φ0 hφ0
    obtain ⟨φ₂, hφ₂, h2⟩ := hL p hp φ₁ hφ₁
    have e1 := hD q hq φ0 hφ0 φ₁ hφ₁ h1
    have e2 := hD p hp φ₁ hφ₁ φ₂ hφ₂ h2
    have e3 := hD (p * q) (udat_mul hp hq) φ0 hφ0 φ₂ hφ₂ (comp p q φ0 φ₁ φ₂ h1 h2)
    have hG : GlobalTheory.SplitFlip.invT (locMatD t c (p * q)) =
        GlobalTheory.SplitFlip.invT (locMatD t c p) * GlobalTheory.SplitFlip.invT (locMatD t c q) := by
      rw [map_mul, map_mul]
    set G := GlobalTheory.SplitFlip.invT (locMatD t c (p * q))
    have hY := congrFun (e3.symm.trans e2) (Z * (G⁻¹).val)
    rw [e1] at hY
    simp only [Pi.smul_apply, smul_eq_mul] at hY
    have k1 : Z * (G⁻¹).val * G.val = Z := by rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]
    have k2 : Z * (G⁻¹).val * (GlobalTheory.SplitFlip.invT (locMatD t c p)).val * (GlobalTheory.SplitFlip.invT (locMatD t c q)).val = Z := by
      rw [Matrix.mul_assoc, ← Units.val_mul, ← hG, k1]
    rw [k1, k2, ← mul_assoc] at hY
    exact mul_right_cancel₀ hZ hY

end GlobalTheory.DblScalDet

