module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponentsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorLocalVanishStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariant
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepBijectionSchwartzStatement
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
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Matrix
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.DblShape

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_hTens {σ : E →ₐ[F] E} {v : Pl (F := F)} {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (x u : Matrix α β (AE F E)) (hx : At (evFin F v) x) :
    At (evFin F v) ((-1 : AE F E) * hTens (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JA JB x u) := by
  intro r hr
  have h : ∀ i j, r • x i j = 0 := fun i j => by
    have := congrFun (congrFun (hx r hr) i) j
    simpa using this
  rw [← mul_smul_comm]
  unfold hTens
  simp only [Finset.smul_sum, ← smul_mul_assoc, h, zero_mul, Finset.sum_const_zero, mul_zero]

theorem local_intertw {σ : E →ₐ[F] E} {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {κ : Type} [Fintype κ] {ψ : AddChar (AF F) ℂ}
    (dd : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ) (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JB →* Module.End ℂ ((κ → AF F) → ℂ))
    (hS : IsUSplitting (adeleClass F) ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd) (v : Pl (F := F)) (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JB)
    (u : Matrix α β (AE F E)) (φ φ₁ φ₂ φ₃ φ₄ : (κ → Fv F v) → ℂ) (hφ : φ ∈ SB (κ → Fv F v))
    (hφ₁ : φ₁ ∈ SB (κ → Fv F v)) (hφ₂ : φ₂ ∈ SB (κ → Fv F v))
    (h1 : Acts (evFin F v) (dd.rho ψ u) φ φ₁) (h2 : Acts (evFin F v) (omd p) φ φ₂)
    (h3 : Acts (evFin F v) (omd p) φ₁ φ₃)
    (h4 : Acts (evFin F v) (dd.rho ψ (u * ((p : GL β (AE F E)) : Matrix β β (AE F E))ᵀ)) φ₂ φ₄) : φ₄ = φ₃ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have hΦ : tens (evFin F v) φ R ∈ GlobalTheory.WeilM.schA F κ := (hR φ hφ).2
  have himpl := hS.impl p u (tens (evFin F v) φ R) hΦ
  have hact : actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p u = u * ((p : GL β (AE F E)) : Matrix β β (AE F E))ᵀ := rfl
  rw [hact] at himpl
  have key : tens (evFin F v) φ₄ R = tens (evFin F v) φ₃ R := by
    rw [← h4 R (hR φ₂ hφ₂), ← h2 R (hR φ hφ), ← himpl, h1 R (hR φ hφ), h3 R (hR φ₁ hφ₁)]
  funext t
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i)) := by
    intro u' hu'; funext i; exact GlobalTheory.LatVac.at_liftV v _ u' hu'
  have hRz : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    simpa using (hR φ hφ).1 0 _ hz
  have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (t i))
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
  exact mul_right_cancel₀ hR0 this

end GlobalTheory.DblShape
