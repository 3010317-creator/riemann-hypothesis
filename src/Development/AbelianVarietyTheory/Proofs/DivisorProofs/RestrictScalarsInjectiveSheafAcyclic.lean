module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GalMapMul
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHypercohomologyIsoOfInjectiveResolution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoinducedSheafInjectiveResolutionFreeExactStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNaturalHomotopyEquivChainsConstantPresheafStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveEtaleSheafRetractOfCoinduced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModuleInjectiveHomFreeEtaleSheafInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonEtaleHypercohomologyOfRetract
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

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.EtC.restr_injective_acyclic : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (I : Shv S) [Injective I]
    (P : PSh) (n : ℤ), 0 < n → Subsingleton (H R (disc.obj P) ((restr φ).obj I) n) := by
  intro R S _ _ φ I _ P n hn
  obtain ⟨J, hJ, i, r, hir⟩ := _root_.GlobalTheory.EtC.CoindRetract.coind_retract R S φ I
  obtain ⟨C, ε, hC0, hCi, hqi, hCz⟩ := GlobalTheory.T.exists_coinducedSheaf_injectiveResolution_freeExact R S φ J (_root_.GlobalTheory.EtC.HomInj.hom_free_injective R J)
  have h1 : Subsingleton (HK R (sgl ((free R).obj P)) ((restr φ).obj ((coind φ).obj J)) n) := by
    obtain ⟨e⟩ := _root_.GlobalTheory.EtC.InjResCmp.hyper_iso_of_injective_resolution R _ C ε hC0 hCi hqi (sgl ((free R).obj P)) n
    have := hCz P n hn
    exact e.injective.subsingleton
  have h2 : Subsingleton (HK R (sgl ((free R).obj P)) ((restr φ).obj I) n) :=
    _root_.GlobalTheory.EtC.RetractAcyc.subsingleton_of_retract R _ _ ((restr φ).map i) ((restr φ).map r)
      (by rw [← Functor.map_comp, hir]; exact (restr φ).map_id I) _ n h1
  obtain ⟨e, -, -⟩ := GlobalTheory.T.exists_natural_homotopyEquiv_chains_constant_presheaf R
  exact (GlobalTheory.T.quasiIso_hypercohomology_bijective R (e P).hom ((restr φ).obj I) n).1.subsingleton
