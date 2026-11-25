module

public import Formalism.PadicSubsetSums.CentralIdempotents.GaloisConjCentralIdempotent
public import Mathlib.Data.Matrix.PEquiv
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Mathlib.Tactic.Linter.Style

@[expose] public section

open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys.TranspLabel

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def permGL {α : Type} [Fintype α] [DecidableEq α] (π : α ≃ α) : GL α K :=
  ⟨π.symm.toPEquiv.toMatrix, π.toPEquiv.toMatrix, by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply], by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply]⟩

theorem glEquiv_perm {α : Type} [Fintype α] [DecidableEq α] (π : α ≃ α) (g : GL α K) :
    glEquiv K π g = permGL π * g * (permGL π)⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show Matrix.reindex π π (g : Matrix α α K) =
    π.symm.toPEquiv.toMatrix * (g : Matrix α α K) * π.toPEquiv.toMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

def repIsoOf {G : Type} [Group G] (V W : FDRep ℂ G) (L : (V : Type) ≃ₗ[ℂ] (W : Type))
    (h : ∀ g v, L (V.ρ g v) = W.ρ g (L v)) : V ≅ W :=
  Action.mkIso (LinearEquiv.toFGModuleCatIso L) (fun g => by
    ext v
    exact h g v)

def rhoEquiv {G : Type} [Group G] (σ : FDRep ℂ G) (P : G) : (σ : Type) ≃ₗ[ℂ] (σ : Type) :=
  LinearEquiv.ofLinear (σ.ρ P) (σ.ρ P⁻¹)
    (LinearMap.ext fun v => by
      show (σ.ρ P * σ.ρ P⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one]; rfl)
    (LinearMap.ext fun v => by
      show (σ.ρ P⁻¹ * σ.ρ P) v = v
      rw [← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rho_conj {G : Type} [Group G] (σ : FDRep ℂ G) (P X : G) (w : (σ : Type)) :
    σ.ρ P (σ.ρ X w) = σ.ρ (P * X * P⁻¹) (σ.ρ P w) := by
  rw [show σ.ρ (P * X * P⁻¹) (σ.ρ P w) = σ.ρ (P * X * P⁻¹ * P) w by rw [map_mul σ.ρ (P * X * P⁻¹) P]; rfl,
    inv_mul_cancel_right, map_mul]
  rfl

/-- The label can be computed using any enumeration of the matrix coordinates. -/
theorem labO_eq_lab_transp {C : LabelConv K} (O : LabelMap K C) {α : Type} [Fintype α]
    [DecidableEq α] (σ : FDRep ℂ (GL α K)) {d : ℕ} (e : α ≃ Fin d) :
    labO O σ = O.lab d (transp e σ) := by
  have hd : Fintype.card α = d := by simpa using Fintype.card_congr e
  subst d
  unfold labO
  apply O.lab_iso
  let e₀ := Fintype.equivFin α
  let π := e₀.trans e.symm
  have hA (γ : GL (Fin (Fintype.card α)) K) :
      (glEquiv K e).symm γ = glEquiv K π ((glEquiv K e₀).symm γ) := by
    apply Units.ext
    ext i j
    simp [π, Formalism.L2.PT.coe_glEquiv_symm, Formalism.L2.PT.coe_glEquiv]
  refine ⟨repIsoOf _ _ (rhoEquiv σ (permGL π)) fun γ v => ?_⟩
  show σ.ρ (permGL π) (σ.ρ ((glEquiv K e₀).symm γ) v) =
    σ.ρ ((glEquiv K e).symm γ) (σ.ρ (permGL π) v)
  rw [hA, glEquiv_perm]
  exact rho_conj σ _ _ v

theorem labO_transp {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (σ : FDRep ℂ (GL α K)) :
    labO O (transp e σ) = labO O σ := by
  rw [labO_eq_lab_transp O σ (e.trans (Fintype.equivFin β))]
  rfl

end GlobalTheory.SerOSys.TranspLabel
