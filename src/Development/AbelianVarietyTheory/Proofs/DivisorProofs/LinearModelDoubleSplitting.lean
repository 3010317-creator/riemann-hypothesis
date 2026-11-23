module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotallyDisconnectedProductLocallyCompactStatement
import GroundTheory.GlobalFields.LocalAtPlace
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblLin

open Matrix

def schrLin {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w : (κ → R) × (κ → R)) : ((κ → R) → ℂ) →ₗ[ℂ] ((κ → R) → ℂ) where
  toFun := schr ψ w
  map_add' f g := by funext x; simp only [schr, Pi.add_apply, mul_add]
  map_smul' a f := by funext x; simp only [schr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def conjLin {Y Y' : Type} (ι : (Y → ℂ) →ₗ[ℂ] (Y' → ℂ)) : (Y → ℂ) →ₗ[ℂ] (Y' → ℂ) where
  toFun φ := star (ι (star φ))
  map_add' f g := by rw [star_add, map_add (f := _), star_add]
  map_smul' a f := by rw [star_smul, map_smul, star_smul, star_star]; rfl

theorem star_mem_SB {Y : Type} [TopologicalSpace Y] {f : Y → ℂ} (hf : f ∈ SB Y) : star f ∈ SB Y :=
  ⟨hf.1.comp star, hf.2.comp_left (g := star) (star_zero ℂ)⟩

theorem conjLin_bijOn {Y Y' : Type} [TopologicalSpace Y] [TopologicalSpace Y'] (ι : (Y → ℂ) →ₗ[ℂ] (Y' → ℂ))
    (h : Set.BijOn ι (SB Y : Set (Y → ℂ)) (SB Y' : Set (Y' → ℂ))) :
    Set.BijOn (conjLin ι) (SB Y : Set (Y → ℂ)) (SB Y' : Set (Y' → ℂ)) := by
  refine ⟨fun φ hφ => star_mem_SB (h.mapsTo (star_mem_SB hφ)), fun φ hφ φ' hφ' e => ?_, fun g hg => ?_⟩
  · have e' : ι (star φ) = ι (star φ') := star_injective e
    exact star_injective (h.injOn (star_mem_SB hφ) (star_mem_SB hφ') e')
  · obtain ⟨φ, hφ, e⟩ := h.surjOn (star_mem_SB hg)
    refine ⟨star φ, star_mem_SB hφ, ?_⟩
    show star (ι (star (star φ))) = g
    rw [star_star, e, star_star]

def colsHomeo (m a b k : Type) [TopologicalSpace k] :
    Matrix m (a ⊕ b) k ≃ₜ Matrix m a k × Matrix m b k where
  toFun Y := (Y.submatrix id Sum.inl, Y.submatrix id Sum.inr)
  invFun p := Matrix.fromCols p.1 p.2
  left_inv Y := by ext i (j | j) <;> rfl
  right_inv p := by ext <;> rfl
  continuous_toFun := (continuous_id.matrix_submatrix _ _).prodMk (continuous_id.matrix_submatrix _ _)
  continuous_invFun := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    rcases j with j | j
    · exact (continuous_apply_apply i j).comp continuous_fst
    · exact (continuous_apply_apply i j).comp continuous_snd

theorem eqOn_SB_of_box {k : Type} [TopologicalSpace k] [T2Space k] [LocallyCompactSpace k] [TotallyDisconnectedSpace k]
    {κ : Type} [Fintype κ] {N : Type} [AddCommGroup N] [Module ℂ N] (L₁ L₂ : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] N)
    (h : ∀ a ∈ SB (κ → k), ∀ b ∈ SB (κ → k), L₁ (boxFun a b) = L₂ (boxFun a b)) :
    ∀ φ ∈ SB (κ ⊕ κ → k), L₁ φ = L₂ φ := by
  intro φ hφ
  let e : (κ ⊕ κ → k) ≃ₜ (κ → k) × (κ → k) := Homeomorph.sumArrowHomeomorphProdArrow
  let M₁ : GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) →ₗ[ℂ] N :=
    L₁ ∘ₗ (SB (κ ⊕ κ → k)).subtype ∘ₗ GlobalTheory.LocFlat.CFac.comapH e
  let M₂ : GlobalTheory.SplitWeil.SB ((κ → k) × (κ → k)) →ₗ[ℂ] N :=
    L₂ ∘ₗ (SB (κ ⊕ κ → k)).subtype ∘ₗ GlobalTheory.LocFlat.CFac.comapH e
  have hM : M₁ = M₂ := LinearMap.ext_on_range (GlobalTheory.LocFlat.CFac.Span.span_prodSB_eq_top _ _)
    fun q => h q.1.1 q.1.2 q.2.1 q.2.2
  have := LinearMap.congr_fun hM (GlobalTheory.LocFlat.CFac.comapH e.symm ⟨φ, hφ⟩)
  have e2 : ((GlobalTheory.LocFlat.CFac.comapH e (GlobalTheory.LocFlat.CFac.comapH e.symm ⟨φ, hφ⟩)).1 : (κ ⊕ κ → k) → ℂ) = φ := by
    funext x
    simp only [GlobalTheory.LocFlat.CFac.comapH_apply, Homeomorph.symm_apply_apply]
  simp only [M₁, M₂, LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [← e2]
  exact this

theorem coord_inl {m k : Type} [Fintype m] [DecidableEq m] [Field k] {d : ℕ} (B : Matrix m m k)
    (A : Matrix m (Fin d ⊕ Fin d) k) (c : GL (Fin d) k) :
    (B * A * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ).submatrix id Sum.inl = B * A.toCols₁ * (c⁻¹).valᵀ := by
  have e : ((GlobalTheory.DblScal.dsum c)⁻¹).val = Matrix.fromBlocks (c⁻¹).val 0 0 (c⁻¹).val := rfl
  conv_lhs => rw [e, fromBlocks_transpose, ← Matrix.fromCols_toCols A, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks]
  ext i j
  simp

theorem coord_inr {m k : Type} [Fintype m] [DecidableEq m] [Field k] {d : ℕ} (B : Matrix m m k)
    (A : Matrix m (Fin d ⊕ Fin d) k) (c : GL (Fin d) k) :
    (B * A * ((GlobalTheory.DblScal.dsum c)⁻¹).valᵀ).submatrix id Sum.inr = B * A.toCols₂ * (c⁻¹).valᵀ := by
  have e : ((GlobalTheory.DblScal.dsum c)⁻¹).val = Matrix.fromBlocks (c⁻¹).val 0 0 (c⁻¹).val := rfl
  conv_lhs => rw [e, fromBlocks_transpose, ← Matrix.fromCols_toCols A, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks]
  ext i j
  simp

end GlobalTheory.DblLin
