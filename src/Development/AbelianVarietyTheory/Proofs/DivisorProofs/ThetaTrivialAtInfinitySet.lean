module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelArchimedeanUnipotentSupportStatement
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section
open Matrix
namespace GlobalTheory.VacScalar

theorem hTens_eq_trace {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by
  simp only [hTens, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => arg 2; ext k; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem hTens_act {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (A : Matrix α α E)
    (Bm : Matrix β β E) (hA : Aᵀ * JA * A.map c = JA) (hB : Bmᵀ * JB * Bm.map c = JB) (x y : Matrix α β E) :
    hTens c JA JB (A * x * Bmᵀ) (A * y * Bmᵀ) = hTens c JA JB x y := by
  rw [hTens_eq_trace, hTens_eq_trace]
  have e1 : (A * y * Bmᵀ).map c = A.map c * y.map c * (Bm.map c)ᵀ := by
    rw [show (A * y * Bmᵀ).map c = (A * y).map c * (Bmᵀ).map c from Matrix.map_mul (f := c.toRingHom),
      show (A * y).map c = A.map c * y.map c from Matrix.map_mul (f := c.toRingHom), Matrix.transpose_map]
  have e2 : (Bm.map c)ᵀ * JBᵀ * Bm = JBᵀ := by
    conv_rhs => rw [← hB]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e1, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
  calc _ = Matrix.trace (Bm * (xᵀ * (Aᵀ * JA * A.map c) * y.map c * ((Bm.map c)ᵀ * JBᵀ))) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (xᵀ * JA * y.map c * ((Bm.map c)ᵀ * JBᵀ) * Bm) := by rw [hA, Matrix.trace_mul_comm]
    _ = Matrix.trace (xᵀ * JA * y.map c * JBᵀ) := by rw [Matrix.mul_assoc _ _ Bm, e2]

theorem symp_act {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E)
    (k : UG c JA × UG c JB) (x : Matrix α β E) :
    symp c ξ JA JB (actAB c k x) (actAB c k x) = symp c ξ JA JB x x := by
  simp only [symp, actAB]
  rw [hTens_act c JA JB _ _ k.1.2 k.2.2]


open Classical in
theorem pure_update_smul {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ w : Pl (F := F), (κ → Fv F w) → ℂ)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) (w : Pl (F := F))
    (c : ℂ) : pure f (Function.update φ w (c • φ w)) = c • pure f φ := by
  funext x
  have h1 := GlobalTheory.PureFactor.finprod_update φ w (c • φ w) hstd x
  have h2 := GlobalTheory.PureFactor.finprod_update φ w (φ w) hstd x
  rw [Function.update_eq_self] at h2
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem std_of_vac {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} (hG : G.IsGood B) (S : Finset (Pl (F := F)))
    (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ) (hvac : ∀ w, w ∉ S → φ w = G.M'.vac w) :
    ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
  filter_upwards [hG.hM'.std, S.finite_toSet.compl_mem_cofinite] with v hv hvS
  rw [hvac v hvS, hv]

theorem pure_eigen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (hT : IsTriple B G X om om') (S : Finset (Pl (F := F))) (f : SInf F (Fin a' × Fin (a + a')))
    (φ : ∀ w : Pl (F := F), (Fin a' × Fin (a + a') → Fv F w) → ℂ) (hSB : ∀ w, φ w ∈ SB (Fin a' × Fin (a + a') → Fv F w))
    (hvac : ∀ w, w ∉ S → φ w = G.M'.vac w) (w : Pl (F := F)) (hw : w ∉ S) :
    ∃ θ : 𝓞 E, ∀ γ ∈ latAtV G.V' G.W w, G.M'.co.rho B.ψ γ (pure f φ) =
      B.ψ (⅟(2 : AF F) * symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (inclR (F := F) (AF F) (θ : E)) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) γ γ) •
        pure f φ := by
  obtain ⟨-, -, θ, -, hθ⟩ := hT.geo.hM'.vac w
  refine ⟨θ, fun γ hγ => ?_⟩
  have hstd := std_of_vac hT.geo S φ hvac
  have hΦ := GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd
  have e := GlobalTheory.ThK.LocalOps.acts_pure w (G.M'.co.rho B.ψ γ) f φ _ hΦ
    (fun x => GlobalTheory.PureFactor.mulSupport_finite φ hstd x) (by rw [hvac w hw]; exact hθ γ hγ)
  rw [e, ← hvac w hw, pure_update_smul f φ hstd]
  rfl

end GlobalTheory.VacScalar
