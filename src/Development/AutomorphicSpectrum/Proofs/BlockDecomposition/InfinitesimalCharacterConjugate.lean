module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorGlRelations
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorHermitianSkew
public import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
public import Mathlib.Basic.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultisetConjugateNegOfProd
public import Formalism.RealPlaceAnalysis.StatementE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetAdjointForm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetCapelliOperator
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

@[expose] public section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem hasInfChar_conj_eq (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ) (hB : IsHerm π B) (τ : E →+* ℂ) (m m' : Multiset ℂ)
    (hm : π.HasInfChar τ m) (hm' : π.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m') :
    m' = m.map fun z => -(starRingEnd ℂ) z := by
  obtain ⟨φ, hφ⟩ := hB.2
  refine _root_.GlobalTheory.CompanionTheory.Clozel.multiset_eq_map_neg_conj_of_polyEq a m m' hm.1 hm'.1 fun u => ?_
  have val : ∀ (σ : E →+* ℂ) (l : Multiset ℂ), π.HasInfChar σ l → ∀ w : ℂ,
      Formalism.REAL.qdet (EopV π σ) (w + ((a : ℂ) - 1) / 2) φ = (l.map (w + ·)).prod • φ := by
    intro σ l hl w
    apply Subtype.ext
    rw [_root_.GlobalTheory.CompanionTheory.Clozel.qdet_EopV_val E a π σ w φ, hl.2 w φ.1 φ.2]
    rfl
  have key := _root_.GlobalTheory.CompanionTheory.CapelliAdj.adj_qdet π.V B a (EopV π τ) (EopV π (NumberField.ComplexEmbedding.conjugate τ))
    (_root_.GlobalTheory.CompanionTheory.Clozel.glRel_EopV E a π _) (_root_.GlobalTheory.CompanionTheory.ClozelHerm.EopV_adjoint E a π B hB τ) (u + ((a : ℂ) - 1) / 2) φ φ
  have arg : (a : ℂ) - 1 - (starRingEnd ℂ) (u + ((a : ℂ) - 1) / 2) =
      -(starRingEnd ℂ) u + ((a : ℂ) - 1) / 2 := by
    simp only [map_add (f := _), map_div₀, map_sub, map_one, Complex.conj_natCast, map_ofNat]
    ring
  rw [arg, val τ m hm u, LinearMap.smul_apply, val _ m' hm' (-(starRingEnd ℂ) u)] at key
  simp only [map_smul, LinearMap.smul_apply, smul_smul, map_smulₛₗ, smul_eq_mul] at key
  exact mul_right_cancel₀ hφ key

end GlobalTheory.CompanionTheory.Clozel
