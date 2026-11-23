module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistDataAgreeAcrossCoefficients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotMemSqOfRamificationIdx
public import Formalism.LocalToGlobal.UnitaryNorms.CharGal
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotBaseCondFalse
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionOfIntro
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCharDescent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunKilled
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.GoodPartLeTypeSubspace

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Rigid

theorem exists_frob (hc : GlobalTheory.TwSys.Cheb) (D : D7) (i : D.ntw.Tw) (Q : Finset (PlE D.host)) {p : ℕ} (hp : p ≠ 0)
    (γ : D.ntw.RCG i Q) :
    ∃ w, w ∉ Q ∧ w ∉ placesOver D.host.E p ∧ ∃ (B : ValuationSubring D.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om),
      Formalism.ConjugateSelfDual.IsPlaceOver B w ∧ Formalism.ConjugateSelfDual.IsFrob B (Formalism.ConjugateSelfDual.normV w) σ ∧ D.ntw.art i Q σ = γ := by
  classical
  obtain ⟨g, rfl⟩ := D.ntw.art_surj i Q γ
  obtain ⟨w, hwA, -, -, B, hB, -, σ, hσ, hU⟩ := hc D.host.E D.nd.Om (D.ntw.art i Q).ker (D.ntw.art_cont i Q) inferInstance g
    (Q ∪ (placesOver_finite_av D.host.E p hp).toFinset)
  refine ⟨w, fun h => hwA (Finset.mem_union_left _ h),
    fun h => hwA (Finset.mem_union_right _ ((Set.Finite.mem_toFinset _).2 h)), B, σ, hB, hσ, ?_⟩
  rwa [MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one] at hU

theorem pow_of_tied (hc : GlobalTheory.TwSys.Cheb) {D : D7} (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C)
    (v : D.what₂.places.Pl) (ψ : D.ntw.RCG (C.twI v) (C.Q v) →* (D.ntw.Ok (C.twI v) (C.k' v))ˣ)
    (ι : TwChar.RootIso D (C.twI v) (C.k' v))
    (hF : TwChar.FrobPick (C.twI v) (C.Q v) (C.k' v) ψ ι (tp.psi v)) (hT : PsiChoiceCompatible D cf C tp)
    (htw : TwistedAt D v) (hk : 1 ≤ C.k' v)
    (hL : ∀ z : ℂ, z ^ D.what₂.places.resChar v ^ C.k' v = 1 → ∃ x : D.what₂.LL, D.what₂.embLL x = z) :
    ∃ a : ℕ, a.Coprime (D.ntw.l (C.twI v)) ∧ C.psi' v = ψ ^ a := by
  haveI : NeZero (D.ntw.l (C.twI v) ^ C.k' v) := ⟨pow_ne_zero _ (D.ntw.lPrime _).out.ne_zero⟩
  have hL' : ∀ z : ℂ, z ^ (D.ntw.l (C.twI v) ^ C.k' v) = 1 → ∃ x : D.what₂.LL, D.what₂.embLL x = z := fun z hz =>
    hL z (by rw [← C.twI_l v]; exact hz)
  let j : D.ntw.Ok (C.twI v) (C.k' v) →+* FractionRing (C.Oe v) :=
    (algebraMap (C.Oe v) (FractionRing (C.Oe v))).comp (algebraMap (D.ntw.Ok (C.twI v) (C.k' v)) (C.Oe v))
  have hj : Function.Injective j := (IsFractionRing.injective (C.Oe v) (FractionRing (C.Oe v))).comp (C.Oe_inj v)
  obtain ⟨a, ha, hax⟩ := TwChar.exists_exponent ι (D.ntw.zk_prim _ _) D.what₂.embLL hL' (C.embW v) j hj
  refine ⟨a, Nat.Coprime.coprime_dvd_right (dvd_pow_self _ (by omega)) ha, MonoidHom.ext fun γ => Units.ext ?_⟩
  have hp : D.what₂.places.resChar v ≠ 0 := by rw [← C.twI_l v]; exact (D.ntw.lPrime _).out.ne_zero
  obtain ⟨w, hwQ, hwl, B, σ, hB, hσ, rfl⟩ := exists_frob hc D (C.twI v) (C.Q v) hp γ
  obtain ⟨u, hu, hχ⟩ := hF w hwQ B hB σ hσ
  obtain ⟨x, hx⟩ := hL' ((ι u : ℂˣ) : ℂ) (by rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 (ι u).2, Units.val_one])
  have h1 := hT v htw w hwQ hwl B σ hB hσ x (by rw [hχ, inv_inv]; exact hx)
  have h2 := hax u x hx
  have h3 := hj (h1.symm.trans h2)
  rw [MonoidHom.pow_apply, ← hu]
  exact h3



open Classical in
private abbrev PsiOkFlat {R : Ranks} (H : Host R) (Om : Type) [Field Om] [Algebra H.E Om]
    (Tw : Type) (l : Tw → ℕ) (Ok : Tw → ℕ → Type) [∀ i k, CommRing (Ok i k)]
    (zk : ∀ i k, (Ok i k)ˣ) (cc : Om ≃+* Om)
    (S0 : Tw → Finset (PlE H)) (RCG : Tw → Finset (PlE H) → Type) [∀ i Q, CommGroup (RCG i Q)]
    (art : ∀ i Q, Formalism.ConjugateSelfDual.G H.E Om →* RCG i Q)
    (i : Tw) (A Q : Finset (PlE H)) (k' : ℕ) (ψ' : RCG i Q →* (Ok i k')ˣ) : Prop :=
  (∀ P ∈ Q, Formalism.BasicNotions.IsSplitPl H P ∧ P.asIdeal.inertiaDeg ℤ = 1 ∧ Formalism.BasicNotions.eWL H.E P = 1) ∧
    Disjoint Q (S0 i ∪ A) ∧ 1 ≤ k' ∧ IsOpen ((ψ'.comp (art i Q)).ker : Set (Formalism.ConjugateSelfDual.G H.E Om)) ∧
    AntiHom cc (ψ'.comp (art i Q)) ∧ (∀ g, ψ'.comp (art i Q) g ∈ Subgroup.zpowers (zk i k')) ∧
    RamExactly (ψ'.comp (art i Q)) ↑Q ∧
    (∀ v ∈ placesOver H.E (l i), ∀ A' : ValuationSubring Om, Formalism.ConjugateSelfDual.IsPlaceOver A' v →
      ∀ σ ∈ ReciprocityTheory.Gal.Dec (F := H.E) A', (ψ'.comp (art i Q)) σ = 1)

private abbrev FrobPickFlat {R : Ranks} (H : Host R) (Om : Type) [Field Om] [Algebra H.E Om]
    (Tw : Type) (l : Tw → ℕ) (Ok : Tw → ℕ → Type) [∀ i k, CommRing (Ok i k)]
    (RCG : Tw → Finset (PlE H) → Type) [∀ i Q, CommGroup (RCG i Q)]
    (art : ∀ i Q, Formalism.ConjugateSelfDual.G H.E Om →* RCG i Q)
    (i : Tw) (Q : Finset (PlE H)) (k : ℕ) (ψ : RCG i Q →* (Ok i k)ˣ)
    (ι : rootsOfUnity (l i ^ k) (Ok i k) ≃* rootsOfUnity (l i ^ k) ℂ) (χ : HChar H.E) : Prop :=
  ∀ v, v ∉ Q → ∀ A' : ValuationSubring Om, Formalism.ConjugateSelfDual.IsPlaceOver A' v →
    ∀ σ : Formalism.ConjugateSelfDual.G H.E Om, Formalism.ConjugateSelfDual.IsFrob (F := H.E) A' (Formalism.ConjugateSelfDual.normV v) σ →
      ∃ u : rootsOfUnity (l i ^ k) (Ok i k), (u : (Ok i k)ˣ) = ψ (art i Q σ) ∧ χ.val v = ((ι u : rootsOfUnity (l i ^ k) ℂ) : ℂˣ)⁻¹

private abbrev TwPackFlat {R : Ranks} (H : Host R) (Tw : Type) (RCG : Tw → Finset (PlE H) → Type)
    [∀ i Q, CommGroup (RCG i Q)] (Ok : Tw → ℕ → Type) [∀ i k, CommRing (Ok i k)] : Type :=
  Σ (i : Tw) (Q : Finset (PlE H)) (k' : ℕ), RCG i Q →* (Ok i k')ˣ

private theorem transfer_flat {R₁ R₂ : Ranks} {H₁ : Host R₁} {H₂ : Host R₂} (a1 : R₁ = R₂) (a2 : HEq H₁ H₂)
    {Om₁ Om₂ : Type} {instOm₁ : Field Om₁} {instOm₂ : Field Om₂}
    {algOm₁ : letI := instOm₁; Algebra H₁.E Om₁} {algOm₂ : letI := instOm₂; Algebra H₂.E Om₂}
    (nOm : Om₁ = Om₂) (ninstOm : HEq instOm₁ instOm₂) (nalgOm : HEq algOm₁ algOm₂)
    {cc₁ : letI := instOm₁; Om₁ ≃+* Om₁} {cc₂ : letI := instOm₂; Om₂ ≃+* Om₂} (xcc : HEq cc₁ cc₂)
    {Tw₁ Tw₂ : Type} (xTw : Tw₁ = Tw₂) {l₁ : Tw₁ → ℕ} {l₂ : Tw₂ → ℕ} (xl : HEq l₁ l₂)
    {Ok₁ : Tw₁ → ℕ → Type} {Ok₂ : Tw₂ → ℕ → Type} {crOk₁ : ∀ i k, CommRing (Ok₁ i k)} {crOk₂ : ∀ i k, CommRing (Ok₂ i k)}
    (xOk : HEq Ok₁ Ok₂) (xcrOk : HEq crOk₁ crOk₂)
    {zk₁ : letI := crOk₁; ∀ i k, (Ok₁ i k)ˣ} {zk₂ : letI := crOk₂; ∀ i k, (Ok₂ i k)ˣ} (xzk : HEq zk₁ zk₂)
    {S0₁ : Tw₁ → Finset (PlE H₁)} {S0₂ : Tw₂ → Finset (PlE H₂)} (xS0 : HEq S0₁ S0₂)
    {RCG₁ : Tw₁ → Finset (PlE H₁) → Type} {RCG₂ : Tw₂ → Finset (PlE H₂) → Type}
    {grpRCG₁ : ∀ i Q, CommGroup (RCG₁ i Q)} {grpRCG₂ : ∀ i Q, CommGroup (RCG₂ i Q)} (xRCG : HEq RCG₁ RCG₂) (xgrpRCG : HEq grpRCG₁ grpRCG₂)
    {art₁ : letI := instOm₁; letI := algOm₁; letI := grpRCG₁; ∀ i Q, Formalism.ConjugateSelfDual.G H₁.E Om₁ →* RCG₁ i Q}
    {art₂ : letI := instOm₂; letI := algOm₂; letI := grpRCG₂; ∀ i Q, Formalism.ConjugateSelfDual.G H₂.E Om₂ →* RCG₂ i Q} (xart : HEq art₁ art₂)
    (i : Tw₁) (Q : Finset (PlE H₁)) (k : ℕ) (ψ : letI := grpRCG₁; letI := crOk₁; RCG₁ i Q →* (Ok₁ i k)ˣ) (A : Finset (PlE H₁))
    (ι : letI := crOk₁; rootsOfUnity (l₁ i ^ k) (Ok₁ i k) ≃* rootsOfUnity (l₁ i ^ k) ℂ) (χ : HChar H₁.E)
    (hO : letI := instOm₁; letI := algOm₁; letI := crOk₁; letI := grpRCG₁; PsiOkFlat H₁ Om₁ Tw₁ l₁ Ok₁ zk₁ cc₁ S0₁ RCG₁ art₁ i A Q k ψ)
    (hF : letI := instOm₁; letI := algOm₁; letI := crOk₁; letI := grpRCG₁; FrobPickFlat H₁ Om₁ Tw₁ l₁ Ok₁ RCG₁ art₁ i Q k ψ ι χ)
    (i₂ : Tw₂) (Q₂ : Finset (PlE H₂)) (k₂ : ℕ) (χ₂ : HChar H₂.E) (hi : HEq i₂ i) (hQ : HEq Q₂ Q) (hk : k₂ = k) (hχ : HEq χ₂ χ) :
    letI := instOm₁; letI := algOm₁; letI := crOk₁; letI := grpRCG₁; letI := instOm₂; letI := algOm₂; letI := crOk₂; letI := grpRCG₂
    ∃ (ψ₂ : RCG₂ i₂ Q₂ →* (Ok₂ i₂ k₂)ˣ) (ι₂ : rootsOfUnity (l₂ i₂ ^ k₂) (Ok₂ i₂ k₂) ≃* rootsOfUnity (l₂ i₂ ^ k₂) ℂ) (A₂ : Finset (PlE H₂)),
      PsiOkFlat H₂ Om₂ Tw₂ l₂ Ok₂ zk₂ cc₂ S0₂ RCG₂ art₂ i₂ A₂ Q₂ k₂ ψ₂ ∧ FrobPickFlat H₂ Om₂ Tw₂ l₂ Ok₂ RCG₂ art₂ i₂ Q₂ k₂ ψ₂ ι₂ χ₂ ∧
      l₂ i₂ = l₁ i ∧ ∀ a : ℤ, HEq (⟨i₂, Q₂, k₂, ψ₂ ^ a⟩ : TwPackFlat H₂ Tw₂ RCG₂ Ok₂) (⟨i, Q, k, ψ ^ a⟩ : TwPackFlat H₁ Tw₁ RCG₁ Ok₁) := by
  subst a1; subst a2; subst nOm; subst ninstOm; subst nalgOm; subst xcc
  subst xTw; subst xl; subst xOk; subst xcrOk; subst xzk; subst xS0
  subst xRCG; subst xgrpRCG; subst xart; subst hk; subst hi; subst hQ; subst hχ
  exact ⟨ψ, ι, A, hO, hF, rfl, fun _ => HEq.rfl⟩

theorem transfer {D₁ D₂ : D7} (h : SameExport D₁ D₂) (p : TwPack D₁) (A : Finset (PlE D₁.host))
    (ι : TwChar.RootIso D₁ p.1 p.2.2.1) (χ : HChar D₁.host.E) (hO : BlochKatoReduction.Gen.PsiOk p.1 A p.2.1 p.2.2.1 p.2.2.2)
    (hF : TwChar.FrobPick p.1 p.2.1 p.2.2.1 p.2.2.2 ι χ) (i₂ : D₂.ntw.Tw) (Q₂ : Finset (PlE D₂.host)) (k₂ : ℕ)
    (χ₂ : HChar D₂.host.E) (hi : HEq i₂ p.1) (hQ : HEq Q₂ p.2.1) (hk : k₂ = p.2.2.1) (hχ : HEq χ₂ χ) :
    ∃ (ψ₂ : D₂.ntw.RCG i₂ Q₂ →* (D₂.ntw.Ok i₂ k₂)ˣ) (ι₂ : TwChar.RootIso D₂ i₂ k₂) (A₂ : Finset (PlE D₂.host)),
      BlochKatoReduction.Gen.PsiOk i₂ A₂ Q₂ k₂ ψ₂ ∧ TwChar.FrobPick i₂ Q₂ k₂ ψ₂ ι₂ χ₂ ∧ D₂.ntw.l i₂ = D₁.ntw.l p.1 ∧
      ∀ a : ℤ, HEq (⟨i₂, Q₂, k₂, ψ₂ ^ a⟩ : TwPack D₂) (GlobalTheory.HeightCounting.twPackPow D₁ a p) := by
  obtain ⟨h1, h2, -, -, -⟩ := h
  obtain ⟨a1, a2, -, nOm, ninstOm, nalgOm, -, -⟩ := h1
  obtain ⟨i, Q, k, ψ⟩ := p
  exact transfer_flat a1 a2 (eq_of_heq nOm) ninstOm nalgOm
    h2.cc (eq_of_heq h2.Tw) h2.l h2.Ok h2.crOk h2.zk h2.S0 h2.RCG h2.grpRCG h2.art
    i Q k ψ A ι χ hO hF i₂ Q₂ k₂ χ₂ hi hQ hk hχ

end GlobalTheory.HeightCounting.Rigid
