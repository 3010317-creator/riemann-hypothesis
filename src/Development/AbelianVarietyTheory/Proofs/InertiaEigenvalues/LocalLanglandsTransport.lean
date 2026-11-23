module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTransportFieldIso
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuationStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsDataTransportLocalFieldIsoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIsoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankinSelbergEpsilonTransportStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecUniqueOfLawsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportIrrGLBijectiveDegreeCharZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransportKeepsCuspidalTwistsCharactersStatement
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

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.FieldCompat

section Rep

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem repRel_symm {i : k ≃+* k'} {x : IrrGL (k := k)} {x' : IrrGL (k := k')} (H : RepRel i x x') : RepRel i.symm x' x := by
  obtain ⟨n, π, π', e, rfl, rfl, he⟩ := H
  refine ⟨n, π', π, e.symm, rfl, rfl, fun g v => ?_⟩
  obtain ⟨v, rfl⟩ := e.surjective v
  have hg : GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g := by
    ext a b
    simp [GeneralLinearGroup.map]
  rw [LinearEquiv.symm_apply_eq, e.symm_apply_apply, he, hg]

theorem cls_rep (x : IrrGL (k := k)) : cls x.2.rep = x := congrArg (Sigma.mk x.1) x.2.cl_rep

theorem exists_cls {x : IrrGL (k := k)} {n : ℕ} (hn : x.1 = n) : ∃ π : IrrRep (GL (Fin n) k), cls π = x := by
  subst hn
  exact ⟨x.2.rep, cls_rep x⟩

theorem isCusp_cls {n : ℕ} (π : IrrRep (GL (Fin n) k)) : (cls π).IsCusp ↔ 0 < n ∧ IsCuspidal π.ρ :=
  IrrGL.isCusp_of (π := π.ρ) (hs := π.smooth) (hi := π.irr)

theorem isSmoothChar_comp (i : k' ≃+* k) (hi : Continuous i) {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    IsSmoothChar (χ.comp (Units.map i.toRingHom.toMonoidHom)) := by
  have hc : Continuous (Units.map i.toRingHom.toMonoidHom : k'ˣ → kˣ) := Continuous.units_map _ hi
  exact IsOpen.preimage hc hχ

end Rep

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}

theorem charZero_compl (w : HeightOneSpectrum (𝓞 E)) : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective

def psiMap (i : w.adicCompletion E ≃+* w'.adicCompletion E') (ψ : AddChar (w.adicCompletion E) Circle) :
    AddChar (w'.adicCompletion E') Circle := ψ.compAddMonoidHom i.symm.toAddMonoidHom

theorem psiMap_apply (i : w.adicCompletion E ≃+* w'.adicCompletion E') (ψ : AddChar (w.adicCompletion E) Circle)
    (y : w'.adicCompletion E') : psiMap i ψ y = ψ (i.symm y) := rfl

theorem exists_of_wdRel {φ : Ω ≃+* Ω'} {y : WD h} {y' : WD h'} (H : WDRel φ y y') {n : ℕ} (hn : y.lpDim = n) :
    ∃ (b : WDRep h (Fin n → ℂ)) (b' : WDRep h' (Fin n → ℂ)), WD.mk b = y ∧ WD.mk b' = y' ∧
      b.N = b'.N ∧ ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, φ ((σ : G E Ω) z) = (σ' : G E' Ω') (φ z)) → b.ρ σ = b'.ρ σ' := by
  obtain ⟨m, b, b', rfl, hb', h1, h2⟩ := H
  obtain rfl : m = n := by simpa using hn
  exact ⟨b, b', rfl, hb', h1, h2⟩

end GlobalTheory.LocLanglands.FieldCompat

end
