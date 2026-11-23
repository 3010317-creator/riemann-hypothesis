module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentralCharacterIntegralProperties
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescription
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvariance
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescription
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalRankinSelbergBasicFacts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentatives
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeProjectionEigenform
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftFourierCoefficients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftHeckeEigenvalues
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevelCharacter
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLevel
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalType
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftRapidDecay
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftWhittakerExpansion
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.CoefZero
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt)
open scoped NumberField.AdeleRing ValuativeRel ComplexConjugate
open Ad3 Ad3.R

namespace UpperTheory.V.Z.Sym.Unl

theorem selfAdj : SelfAdj := by
  intro k N _ hk χ hχ g p hp hpN
  have hB := _root_.GlobalTheory.CompanionTheory.RankinQ.b0
  have hE := Ad3P.sEig k N hk χ g
  obtain ⟨hF, hEig⟩ := hE
  obtain ⟨ω, hω⟩ := _root_.GlobalTheory.CompanionTheory.RankinSelbergQ.f0 hB N χ
  obtain ⟨hsign, φ, hL⟩ := _root_.GlobalTheory.CompanionTheory.RSLift.adelic_lift_exists hB k N χ g.f g.a hF hEig.2.1 ω hω
  have hOmL := _root_.GlobalTheory.CompanionTheory.NewformLiftConductor.f0b hB k N χ hχ hsign ω hω
  have hHk := _root_.GlobalTheory.CompanionTheory.RankinHecke.hecke_types_of_lift hB _root_.GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant _root_.GlobalTheory.CompanionTheory.RankinStepC.c1 (_root_.GlobalTheory.CompanionTheory.NewformLiftConductor.f0b hB) (_root_.GlobalTheory.CompanionTheory.RSLift.adelic_lift_exists hB)
    (_root_.GlobalTheory.CompanionTheory.RankinSelberg.LiftLevel.lift_local_invariance hB) (_root_.GlobalTheory.CompanionTheory.RSq.f3a hB) k N hk χ hχ g.f g.a hF hEig ω φ hω hL
  have hW := _root_.GlobalTheory.CompanionTheory.RsWhittaker.whittaker_of_lift k N hk χ hχ g.f g.a hF hEig ω φ hω hL
  have hb := _root_.GlobalTheory.CompanionTheory.NewformLiftDecay.main hB k N hk χ hχ g.f g.a hF hEig ω φ hω hL
  obtain ⟨μ, 𝓕, mK, 𝓓, hS⟩ := _root_.GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain _root_.GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain
  have hG1 := _root_.GlobalTheory.CompanionTheory.FundamentalDomainCentralCharacter.fundamental_domain_integral_central_vanishing _root_.GlobalTheory.CompanionTheory.RS.rankinSelberg_measure_facts
  obtain ⟨v, hv⟩ := hB.2.2.1 p hp
  have hnd : ¬pOf v ∣ N := by rwa [hv]
  obtain ⟨C, hC⟩ := hb.1
  have hφ0 : φ ≠ 0 := by
    intro h0
    have h1 := hW.2.2.2 (-1)
    rw [h0, GlobalTheory.CompanionTheory.RSEigen.wh_zero] at h1
    exact GlobalTheory.CompanionTheory.RSEigen.wr_ne k h1.symm
  have hpr := GlobalTheory.CompanionTheory.RSEigen.pr_self_ne hS hG1 (ω := ω) hL.cont hb.1 hL.left hL.cen hφ0
  have hone : ∀ x : G2, cdet 1 x = 1 := by
    intro x
    simp [Ad3.R.cdet, GroundTheory.Global.HeckeCharacter.toIdele_apply]
  have hPr : GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.Pr μ 𝓕 φ 1 1 1 ≠ 0 := by
    simpa [GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.Pr, GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.Fn, hone, GlobalTheory.CompanionTheory.RSEigen.pr] using hpr
  have hloc1 : ∀ u, localChar (1 : HeckeCharacter ℚ) v u = 1 := by
    intro u
    ext
    simp [GroundTheory.Automorphic.GodementSection.coe_localChar,
      GroundTheory.Global.HeckeCharacter.localComponent_apply, GroundTheory.Global.HeckeCharacter.toIdele_apply]
  have hunr1 : IsUnramifiedChar (localChar (1 : HeckeCharacter ℚ) v) :=
    isUnramifiedChar_iff.2 (fun u _ => hloc1 u)
  have hstd := (hB.1 v).1
  obtain ⟨ϖ, B, hR⟩ := (_root_.GlobalTheory.CompanionTheory.RankinStepC.c1 (Qv v) (localAdelicChar ℚ v) hstd).1
  have key := GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.eig_relation (φ := φ) (ω := ω) (c := 1) (μ := μ) (𝓕 := 𝓕) (C := C)
    hL.cont hC hL.left hL.cen (by simp)
    (fun F hF hFb hFL hFC h => (hG1 μ 𝓕 mK 𝓓 hS F hF hFb hFL).1 hFC h) hS.vol
    (v := v) (hB.1 v).2.2.2.2.2.1 hB.2.2.2.1 (hB.2.2.2.2.2.2.2 v) hunr1
    (lam := lamOf k g.a v) (fun g W hW' => hHk.good v hnd g W hW') hR (h := 1)
    (GroundTheory.Automorphic.Reduction.finAt_one v) hPr
  have hω1 : ((localChar ω v ϖ : ℂˣ) : ℂ) = χ p := by
    rw [quasiChar_apply_eq_of_isUnramified (hOmL.good v hnd).1 hR.1, (hOmL.good v hnd).2, hv]
  rw [hloc1, hω1] at key
  simp only [lamOf, hv, Units.val_one, one_mul, map_mul, Complex.conj_ofReal] at key
  have hr : (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _).ne'
  have h : g.a p * (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)
      = (χ p * (starRingEnd ℂ) (g.a p)) * (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) :=
    key.trans (by ring)
  have h2 := mul_right_cancel₀ hr h
  linear_combination -h2

end UpperTheory.V.Z.Sym.Unl
