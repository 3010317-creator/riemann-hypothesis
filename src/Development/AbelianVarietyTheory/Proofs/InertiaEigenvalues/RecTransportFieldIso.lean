module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionBaseChangePlacesStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousRingEquivLocalFieldPreservesValuation
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EpsilonUniqueOfInductiveStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLocalExtensionOfFiniteIndexWeilSubgroupStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinMapUniqueTransportPlaceIsoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalTraceCompletionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLinearEquivOfCharpolyEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceOverTransportRingIsoSymmStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateEpsilonTransportStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TraceBaseChangeFieldStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneSemisimpleStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupRestrictionStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupTransportStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaussSumNeZeroOfRamified
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
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.EpsUnique

theorem index_eq_finrank : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (h : IsPlaceOver A v), IsLocalExt L h → ∀ H : Subgroup (Weil h), (∀ σ : Weil h, σ ∈ H ↔ ∀ x : L, (σ : G K Ω) (algebraMap L Ω x) = algebraMap L Ω x) → H.index = Module.finrank K L := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ A v h hL H hH
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  let f : Weil h → (L →ₐ[K] Ω) := fun σ => (σ : G K Ω).toAlgHom.comp (IsScalarTower.toAlgHom K L Ω)
  have hf : ∀ σ τ : Weil h, f σ = f τ ↔ σ⁻¹ * τ ∈ H := fun σ τ => by
    rw [hH, AlgHom.ext_iff]
    refine forall_congr' fun x => ?_
    show (σ : G K Ω) (algebraMap L Ω x) = (τ : G K Ω) (algebraMap L Ω x) ↔
      (σ : G K Ω).symm ((τ : G K Ω) (algebraMap L Ω x)) = _
    rw [AlgEquiv.symm_apply_eq, eq_comm]
  have hs : Function.Surjective f := fun s => by
    obtain ⟨τ, hτ⟩ := hL (AlgEquiv.ofBijective (s.liftNormal Ω) (AlgHom.normal_bijective K Ω Ω _))
    exact ⟨τ, AlgHom.ext fun x => (hτ x).trans (s.liftNormal_commutes Ω x)⟩
  let g : Weil h ⧸ H → (L →ₐ[K] Ω) := Quotient.lift f fun σ τ hστ => (hf σ τ).2 (QuotientGroup.leftRel_apply.1 hστ)
  have hg : Function.Bijective g := by
    refine ⟨fun a b => Quotient.inductionOn₂ a b fun σ τ e => QuotientGroup.eq.2 ((hf σ τ).1 e), fun s => ?_⟩
    obtain ⟨σ, rfl⟩ := hs s
    exact ⟨QuotientGroup.mk σ, rfl⟩
  rw [Subgroup.index, Nat.card_eq_of_bijective g hg, Nat.card_eq_fintype_card, AlgHom.card]

theorem induces_of_eigenvector : ∀ (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (r : Weil h' →* Weil h), (∀ (σ : Weil h') (z : Ω), (r σ : G K Ω) z = (σ : G L Ω) z) → (∀ (M : Type) [Monoid M] (f : Weil h →* M), GlobalTheory.WeilDeligne.IsSmooth f → GlobalTheory.WeilDeligne.IsSmooth (f.comp r)) → ∀ (n : ℕ) (b : WDRep h (Fin n → ℂ)) (u : Fin n → ℂ) (ξ : Weil h' →* ℂˣ), n = Module.finrank K L → (∀ σ, b.ρ (r σ) u = (ξ σ : ℂ) • u) → Submodule.span ℂ (Set.range fun σ => b.ρ σ u) = ⊤ → ∃ hξ : GlobalTheory.WeilDeligne.IsSmooth ξ, Induces (WD.lpOfChar h' ξ hξ) (WD.mk b) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' r hr hs n b u ξ hn hu hsp
  have hu0 : u ≠ 0 := by
    rintro rfl
    haveI : Nonempty (Fin n) := ⟨⟨0, hn ▸ Module.finrank_pos⟩⟩
    refine bot_ne_top (α := Submodule ℂ (Fin n → ℂ)) (hsp ▸ (Submodule.span_eq_bot.2 ?_).symm)
    rintro _ ⟨σ, rfl⟩
    simp
  have hξ : GlobalTheory.WeilDeligne.IsSmooth ξ := (hs _ b.ρ b.smooth).of_le fun σ hσ => by
    have h1 := hu σ
    rw [show b.ρ (r σ) = 1 from hσ] at h1
    exact Units.ext (smul_left_injective ℂ hu0 (by simpa using h1.symm))
  refine ⟨hξ, 1, n, _, b, (LinearMap.proj (0 : Fin 1)).smulRight u, rfl, rfl, by simp [hn], fun σ' σ hσ x => ?_, ?_⟩
  · rw [show σ = r σ' from Subtype.ext (AlgEquiv.ext fun z => (hσ z).trans (hr σ' z).symm)]
    simp [hu, smul_smul, mul_comm]
  · rw [eq_top_iff, ← hsp]
    refine Submodule.span_mono ?_
    rintro _ ⟨σ, rfl⟩
    exact ⟨(σ, fun _ => 1), by simp⟩

section One

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem induces_of_charPol {x y : WD h} (hxy : ∀ σ, x.charPol σ = y.charPol σ) : Induces x y := by
  obtain ⟨m, a, rfl⟩ := x.exists_rep
  obtain ⟨n, b, rfl⟩ := y.exists_rep
  simp only [WD.charPol_mk] at hxy
  obtain ⟨e, he⟩ := GlobalTheory.TraceIso.exists_equiv_of_trace_eq a.ρ b.ρ (GlobalTheory.T.weil_deligne_semisimple E Ω A w h m a) (GlobalTheory.T.weil_deligne_semisimple E Ω A w h n b)
    fun g => by
      have h1 := hxy g
      rw [← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℂ (Fin m)),
        ← LinearMap.charpoly_toMatrix _ (Pi.basisFun ℂ (Fin n))] at h1
      rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin m)),
        LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)), Matrix.trace_eq_neg_charpoly_nextCoeff,
        Matrix.trace_eq_neg_charpoly_nextCoeff, h1]
  have hmn : n = m := by simpa using e.finrank_eq.symm
  refine ⟨m, n, a, b, e, rfl, rfl, by simp [hmn], fun σ' σ hσ u => ?_, ?_⟩
  · rw [show σ = σ' from Subtype.ext (AlgEquiv.ext hσ)]; exact he _ _
  · exact eq_top_iff.2 fun u _ => Submodule.subset_span ⟨(1, e.symm u), by simp⟩

theorem eps_eq_of_charPol {ε : EpsFamily A} (hε : IsDeligneEps ε) {ψ : AddChar (w.adicCompletion E) Circle}
    (hc : Continuous ψ) (h1 : ψ ≠ 1) {x y : WD h} (hxy : ∀ σ, x.charPol σ = y.charPol σ) :
    ε E w h ψ x = ε E w h ψ y := by
  have := hε.ind E E w w h h (isLocalExt_self h) ψ ψ hc h1 hc (fun z => by simp) x x y x
    (induces_of_charPol hxy) (induces_self x) rfl
  exact (mul_right_cancel this).symm

theorem exists_place (h : IsPlaceOver A w) (L : Type) [Field L] [NumberField L] [Algebra L Ω] [Algebra E L]
    [IsScalarTower E L Ω] : ∃ v : HeightOneSpectrum (𝓞 L), IsPlaceOver A v := by
  have hint : ∀ x : 𝓞 L, algebraMap L Ω x ∈ A := fun x => by
    have h1 : IsIntegral ℤ (algebraMap L Ω x) := x.2.map (algebraMap L Ω).toIntAlgHom
    have h2 : IsIntegral A (algebraMap L Ω x) := h1.tower_top
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
    exact hy ▸ y.2
  let f : 𝓞 L →+* A := ((algebraMap L Ω).comp (algebraMap (𝓞 L) L)).codRestrict A hint
  have hf : ∀ x : 𝓞 L, A.valuation (algebraMap L Ω x) < 1 ↔ x ∈ (IsLocalRing.maximalIdeal A).comap f := fun x =>
    (A.valuation_lt_one_iff (f x)).symm
  refine ⟨⟨(IsLocalRing.maximalIdeal A).comap f, inferInstance, fun h0 => ?_⟩, hf⟩
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot w.ne_bot
  have h3 := (hf (algebraMap (𝓞 E) (𝓞 L) x)).1 (by
    have := (h x).2 hx
    rwa [IsScalarTower.algebraMap_apply E L Ω] at this)
  rw [h0, Ideal.mem_bot] at h3
  exact hx0 (FaithfulSMul.algebraMap_injective (𝓞 E) (𝓞 L) (by simpa using h3))

theorem exists_addChar (L : Type) [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra E L]
    [IsScalarTower E L Ω] {v : HeightOneSpectrum (𝓞 L)} (hv : IsPlaceOver A v) (hL : IsLocalExt L h)
    {ψ : AddChar (w.adicCompletion E) Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1) :
    ∃ ψL : AddChar (v.adicCompletion L) Circle, Continuous ψL ∧ ψL ≠ 1 ∧
      ∀ z : L, ψL (algebraMap L _ z) = ψ (algebraMap E _ (Algebra.trace E L z)) := by
  obtain ⟨T, hT, hT'⟩ := GlobalTheory.T.local_trace_completion E L Ω A w v h hv hL
  refine ⟨ψ.compAddMonoidHom T, hc.comp hT, fun h0 => h1 ?_, fun z => by simp [hT']⟩
  ext x
  refine (HeightOneSpectrum.denseRange_algebraMap E w).induction_on (p := fun x => (ψ x : ℂ) = (1 : AddChar _ Circle) x) x
    (isClosed_eq (continuous_subtype_val.comp hc) (by simpa using continuous_const)) fun a => ?_
  obtain ⟨z, rfl⟩ := Algebra.trace_surjective E L a
  have := DFunLike.congr_fun h0 (algebraMap L _ z)
  simp only [AddChar.compAddMonoidHom_apply, hT', AddChar.one_apply] at this
  simp [this]

end One

section Two

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {E' Ω' : Type} [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω']
  {A' : ValuationSubring Ω'} {w' : HeightOneSpectrum (𝓞 E')} {h' : IsPlaceOver A' w'}
  {φ : Ω ≃+* Ω'} {j : E →+* E'} {i : w.adicCompletion E ≃+* w'.adicCompletion E'}

theorem addChar_transport (hP : PlaceIso A w A' w' φ j i) {ψ : AddChar (w.adicCompletion E) Circle}
    {ψ' : AddChar (w'.adicCompletion E') Circle} (hc : Continuous ψ) (h1 : ψ ≠ 1) (hψ : ∀ x, ψ' (i x) = ψ x) :
    Continuous ψ' ∧ ψ' ≠ 1 := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  haveI : CharZero (w'.adicCompletion E') := charZero_of_injective_algebraMap (algebraMap E' _).injective
  refine ⟨?_, fun h0 => h1 ?_⟩
  · have : (ψ' : _ → Circle) = ψ ∘ i.symm := funext fun x => by simp [← hψ]
    rw [this]
    exact hc.comp (GlobalTheory.LocalFieldIso.continuous_iso_keeps_valuation _ _ i hP.cont).1
  · ext x
    simp [← hψ, h0]

theorem valuation_lt_one_iff_map (hm : ∀ z, φ z ∈ A' ↔ z ∈ A) (z : Ω) :
    A'.valuation (φ z) < 1 ↔ A.valuation z < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ← map_inv₀, hm, hm, map_eq_zero_iff _ φ.injective]

end Two

end GlobalTheory.LocLanglands.EpsUnique

end
