module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateEmbeddingIsCMTypeSqrtMinusD
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseCondOfSplitPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LamConductorExponent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PlacesBelowSplitCoprimeConductorOfAdmissible
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitsInCMFieldPlaceBelowOfCompletelySplit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0HasInfinityTypeConjRatio
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfield
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem toricCharacter_isCMHostValueDatum : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m) (s : ℕ), 1 ≤ s → (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 → IsHostDatum D.host (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0) (Z.lam0 l j a) := by
  intro D Z hZ l j a s hs hN
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hcm, hind⟩ := _root_.GlobalTheory.LamTie.CMType.phi_cmType D.R D.host
  obtain ⟨hκ, hinf⟩ := _root_.GlobalTheory.LamTie.InfType.toricLam0_hasInfinityType_conjRatio D Z hZ l j a s hN
  obtain ⟨hu, ht⟩ := _root_.GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield D Z hZ l j a
  have hb : IsBaseCond (cond0 D.host Z.w0) :=
    _root_.GlobalTheory.LamTie.isBaseCond_cond0 D.R D.host Z.q0 Z.w0 (fun p hp P hP => by
      obtain ⟨h1, -, h3, h4⟩ := hZ.places.splits p hp
      exact _root_.GlobalTheory.LamTie.SplitBelow.splits_below_of_absNorm D.host.E p h1 h3 h4 P hP) hZ.places
  refine ⟨hcm, hind, hs, hκ, hb, hu, ht, hinf, fun v P hP => ⟨fun h => absurd h (Finset.notMem_empty v), fun _ => ?_⟩⟩
  have hv : v = below P := HeightOneSpectrum.ext (hP.symm.trans (over_below P))
  subst hv
  exact _root_.GlobalTheory.LamTie.lam0_expAt D Z hZ l j a P

end GlobalTheory.LamTie
