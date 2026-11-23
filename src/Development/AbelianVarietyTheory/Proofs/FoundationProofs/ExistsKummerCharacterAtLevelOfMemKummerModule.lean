module

public import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsRootOfMemUn
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterOfUpperHalfPlaneRoot
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelAddZeroCongr
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKummerCharacterAtLevelPadicIntSmul
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

theorem GlobalTheory.KZ.H3.exists_kum_of_mem_A : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ)
    [Fact l.Prime], JHol X → ∀ (n : ℕ), ∀ x ∈ X.A l, ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  intro Ω _ _ ε X l _ hJ n x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨f, hf, he⟩ := hy n
    have hm : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
    obtain ⟨a, b, hab⟩ := _root_.GlobalTheory.KZ.H3.UnRoot.exists_isRoot_of_mem_Un Ω ε X hJ (l ^ n) hm f hf
    exact _root_.GlobalTheory.KZ.H3.kum_of_isRoot Ω ε X l n y f a b he hab
  | zero => exact ⟨0, (_root_.GlobalTheory.KZ.H3.KumAdd.kum_add_zero_near Ω ε X l n).2.1⟩
  | add y z _ _ hy hz =>
    obtain ⟨χ, hχ⟩ := hy
    obtain ⟨χ', hχ'⟩ := hz
    exact ⟨χ + χ', (_root_.GlobalTheory.KZ.H3.KumAdd.kum_add_zero_near Ω ε X l n).1 y z χ χ' hχ hχ'⟩
  | smul c y _ hy =>
    obtain ⟨χ, hχ⟩ := hy
    exact ⟨_, _root_.GlobalTheory.KZ.H3.kum_smul Ω ε X l n c y χ hχ⟩
