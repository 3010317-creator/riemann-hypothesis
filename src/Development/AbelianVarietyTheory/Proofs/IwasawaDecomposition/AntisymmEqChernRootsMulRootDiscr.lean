module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernDvdOfDifferencesDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagRelativeTangentTopChernRenameBlockPerm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricPolyChernRoots
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameBlockPermSign
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeylAntisymmetrizationRenameSwapNeg
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.Basic.Real.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.XSubXDvdOfRenameSwapEqNeg
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.AntisymmChern

theorem antisymm_eq_chernRoots_mul_rootDiscr : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (Q : MvPolynomial (Root m) ℝ), ∃ R : MvPolynomial (ι × ℕ) ℝ, antisymm Q = chernRoots m R * rootDiscr m := by
  intro ι _ m Q
  classical
  obtain ⟨S, hS⟩ : rootDiscr m ∣ antisymm Q := _root_.GlobalTheory.GoodMetric.DiscrDvd.rootDiscr_dvd ι m (antisymm Q) fun τ i j hij =>
    _root_.GlobalTheory.swap_odd_dvd (⟨τ, i⟩ : Root m) ⟨τ, j⟩ (by simp [hij.ne]) _ (_root_.GlobalTheory.AntisymmSwap.rename_swap_antisymm ι m Q τ i j hij.ne)
  have hsym : ∀ w : ∀ τ, Equiv.Perm (Fin (m τ)), rename (Equiv.sigmaCongrRight w) S = S := by
    intro w
    have h1 := _root_.GlobalTheory.GoodMetric.antisymm_rename_sigmaCongrRight ι m Q w
    rw [hS, map_mul, _root_.GlobalTheory.GoodMetric.rename_sigmaCongrRight_rootDiscr ι m w, smul_mul_assoc] at h1
    have hs : ((∏ τ, Equiv.Perm.sign (w τ) : ℤˣ) : ℤ) ≠ 0 := Units.ne_zero _
    exact mul_left_cancel₀ (_root_.GlobalTheory.GoodMetric.rootDiscr_ne_zero ι m) (smul_right_injective _ hs h1)
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.BlockSymm.exists_chernRoots_eq_of_blockSymmetric ι m S hsym
  exact ⟨R, by rw [hS, hR, mul_comm]⟩

end GlobalTheory.AntisymmChern
