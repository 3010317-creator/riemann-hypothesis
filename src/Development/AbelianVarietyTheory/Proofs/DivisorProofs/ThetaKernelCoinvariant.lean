module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAtUniformizerNotRootOfUnityStatement
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

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

namespace GlobalTheory.KCoinvGood

theorem augAt_le_SB {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} (om : Rep σ Y W) (v : Pl (F := F)) : augAt om v ≤ SB _ :=
  Submodule.span_le.mpr fun _ ⟨_, _, _, hφ, _, hφ₁, _, e⟩ => e ▸ sub_mem hφ₁ hφ

theorem acts_zero {F : Type} [Field F] [NumberField F] {R κ : Type} [Zero R] [Fintype κ] (ev : AF F → R)
    (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts ev T 0 0 := fun r _ => by
  have e : tens ev (0 : (κ → R) → ℂ) r = 0 := funext fun x => by simp [tens]
  rw [e, map_zero]

theorem ker_eq_of {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P] [Nontrivial P]
    (S A : Submodule ℂ V) (p : V →ₗ[ℂ] P) (hA : A ≤ LinearMap.ker p) (honto : S.map p = ⊤)
    (h : S ⊓ LinearMap.ker p = A ∨ S ⊓ LinearMap.ker p = S) : ∀ φ ∈ S, p φ = 0 ↔ φ ∈ A := by
  rcases h with h | h
  · intro φ hφ
    refine ⟨fun h0 => h ▸ ⟨hφ, h0⟩, fun hm => hA hm⟩
  · exfalso
    obtain ⟨x, hx⟩ := exists_ne (0 : P)
    have : x ∈ S.map p := honto ▸ Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := this
    have hy' : y ∈ S ⊓ LinearMap.ker p := by rw [h]; exact hy
    exact hx hy'.2

theorem factor_of {V P : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup P] [Module ℂ P]
    (S : Submodule ℂ V) (p : V →ₗ[ℂ] P) (l : V →ₗ[ℂ] ℂ) (honto : S.map p = ⊤) (hk : ∀ φ ∈ S, p φ = 0 → l φ = 0) :
    ∃ l₀ : P →ₗ[ℂ] ℂ, ∀ φ ∈ S, l φ = l₀ (p φ) := by
  set q := p.domRestrict S
  have hs : Function.Surjective q := by
    intro x
    have : x ∈ S.map p := honto ▸ Submodule.mem_top
    obtain ⟨y, hy, rfl⟩ := this
    exact ⟨⟨y, hy⟩, rfl⟩
  have hker : LinearMap.ker q ≤ LinearMap.ker (l.domRestrict S) := fun x hx => hk x.1 x.2 hx
  refine ⟨((LinearMap.ker q).liftQ (l.domRestrict S) hker).comp (q.quotKerEquivOfSurjective hs).symm.toLinearMap,
    fun φ hφ => ?_⟩
  have : (q.quotKerEquivOfSurjective hs).symm (p φ) = Submodule.Quotient.mk ⟨φ, hφ⟩ := by
    rw [LinearEquiv.symm_apply_eq]; rfl
  simp [this]

end GlobalTheory.KCoinvGood
