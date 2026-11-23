module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseIdealIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeQuotientClosedImmersionIdealSheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealSheafLeOfLeOnReductionsJacobson
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedImmersionOfProperClosedImmersionModIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseIdealSheafOfIdealComapSpecMapSupport
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
import Mathlib.Tactic.Linter.HaveILetI
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

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

namespace GlobalTheory.FormalAlg

theorem isIso_of_isIso_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (T X : Scheme.{0}) (φ : T ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)), IsProper φ → IsProper f → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (c : ∀ e, (Y e).left ⟶ T), (∀ e, IsPullback (c e) (Y e).hom (φ ≫ f) (thick R I e)) → (∀ e, IsPullback (c e ≫ φ) (Y e).hom f (thick R I e)) → IsIso φ := by
  intro R _ _ I hI T X φ f hφ hf Y c hpb hpb'
  have hc := fun e => _root_.GlobalTheory.FormalAlg.baseChange_quotient R (I ^ (e + 1)) T (Y e).left (φ ≫ f) (c e) (Y e).hom (hpb e)
  have hc' := fun e => _root_.GlobalTheory.FormalAlg.baseChange_quotient R (I ^ (e + 1)) X (Y e).left f (c e ≫ φ) (Y e).hom (hpb' e)

  have hK : (baseIdeal f I).comap φ = (c 0).ker := by
    rw [(hc 0).2.1, (_root_.GlobalTheory.FormalAlg.baseIdeal_calculus).1 R X T f φ I, zero_add, pow_one]
  haveI : IsClosedImmersion (c 0) := (hc 0).1
  haveI : IsClosedImmersion (c 0 ≫ φ) := (hc' 0).1
  have hφc : IsClosedImmersion φ := by
    refine _root_.GlobalTheory.ClosedLev.isClosedImmersion_of_mod R I hI T X φ f hφ inferInstance ?_
    rw [hK]
    have he : (c 0).ker.subschemeι ≫ φ = inv (c 0).toImage ≫ (c 0 ≫ φ) := by
      rw [IsIso.eq_inv_comp]
      exact Scheme.Hom.toImage_imageι_assoc _ _
    rw [he]
    infer_instance
  haveI := hφc

  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hker : φ.ker ≤ ⊥ := by
    refine _root_.GlobalTheory.FormalAlg.le_of_le_reductions R I hI X f φ.ker ⊥ inferInstance fun e => ?_
    rw [bot_sup_eq, ← (hc' e).2.1]
    exact Scheme.Hom.le_ker_comp (c e) φ
  have hbot : φ.ker = ⊥ := le_bot_iff.1 hker
  haveI : IsIso φ.imageι := by
    change IsIso φ.ker.subschemeι
    rw [hbot]
    infer_instance
  rw [← φ.toImage_imageι]
  infer_instance

end GlobalTheory.FormalAlg
