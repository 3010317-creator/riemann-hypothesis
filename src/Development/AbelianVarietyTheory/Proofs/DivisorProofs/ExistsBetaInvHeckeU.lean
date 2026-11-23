module

public import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOfBalanced
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCongruenceHeckeCharacterBoundedLevelTrivia
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotInertPlaceOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterBoundedConductorKillsIdeleNorms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterNonInertBoundedLevelKillsUnits
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedEtaCharacterKillsFiniteIdeleNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.TotallyPositiveExponents
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

namespace GlobalTheory.FunObj.SqNum

open GlobalTheory.HeckeUOps

theorem levelLe_one_two {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} (h : χ.LevelLe v 1) : χ.LevelLe v 2 :=
  fun x hx hle => h x hx (hle.trans (WithZero.exp_le_exp.2 (by norm_num)))

theorem exists_betaInv_heckeU {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T} (_hL : L.Is μ₀) (G : GridData L sc)
    (i j : Fin D.R.m) : ∃ χ : HeckeU D (botBig D i j), ∀ x, χ.f x = (betaH G i j)⁻¹.1 (finIdl D x) := by
  classical
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  choose! qf hqf using _root_.GlobalTheory.FunObj.SqNum.exists_prime_notInert_place G.pl
  have hS : ∀ q ∈ G.pl.S0.image qf, q.Prime ∧ ¬ InertQ D q := by
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hq
    exact ⟨(hqf v hv).1, (hqf v hv).2.1⟩
  have hlev : ∀ v, (G.ch.chiH (D.R.m - i)).UnrAt v ∨ ∃ q ∈ G.pl.S0.image qf, Formalism.L2.Host.OverP D.host q v ∧
      (G.ch.chiH (D.R.m - i)).LevelLe v 2 := by
    intro PP
    by_cases h : (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) ∈ G.pl.S0
    · refine Or.inr ⟨qf _, Finset.mem_image_of_mem _ h, ?_, ?_⟩
      · have := (hqf _ h).2.2
        simpa [HeightOneSpectrum.under, Formalism.L2.Host.OverP] using this
      · rcases G.pl.mem_S0_of_sum_eq.1 h with h0 | h1
        · exact levelLe_one_two (G.ch.lev0 _ k1 k2 PP h0).1
        · exact (G.ch.lev1 _ k1 k2 PP h1).1
    · exact Or.inl (G.ch.unr _ k1 k2 PP h)
  have hcu := GlobalTheory.ChrEqUnique.isUnitary_of_chrEq D _ _ (G.ch.chi_eq _ k1 k2)
  have hci : (G.ch.chiH (D.R.m - i)).HasInf (embT D) (fun τ => 2 * cen D sc.cGap τ (D.R.m - i)) := G.ch.inf _ k1 k2
  let χc : HeckeU D 0 := ofChar 0 _ _ hcu hci (_root_.GlobalTheory.HeckeCont.eq_one_of_cong D _ _ 2 (fun q hq => (hS q hq).1) hlev)
    (_root_.GlobalTheory.NormKill.chi_finIdl_norm_eq_one D _ _ _ 2 (G.ch.triv _ k1 k2) hci (fun q hq => (hS q hq).1) hlev)
    (fun τ => by simp) (_root_.GlobalTheory.FunObj.SqNum.hchar_finIdl_eq_one_of_zeroAt D _ _ 2 hS hlev)
  have he := L.C.isEta
  have hei : L.C.eta.HasInf (embT D) (fun _ => 1) := fun a => by
    rw [he.inf a, ← D.eTau.prod_comp]
    rfl
  let χe : HeckeU D 1 := ofChar 1 L.C.eta _ he.unitary hei (_root_.GlobalTheory.HeckeCont.eq_one_of_cong D _ ∅ 0 (by simp) fun v => Or.inl (he.unr v))
    (_root_.GlobalTheory.EtaTildeNorm.map_finIdl_norm D _ he) (fun τ => by simp) (_root_.GlobalTheory.FunObj.SqNum.hchar_finIdl_eq_one_of_zeroAt D _ ∅ 0 (by simp) fun v => Or.inl (he.unr v))
  have hr : rankV D (i + 1) (j + 1) = rankV D i j + D.R.t + sLen D := by simp only [rankV]; ring
  have hx := (ranks_exact D i j).1
  obtain ⟨u, hu⟩ := D.R.t_odd
  obtain ⟨w, hw⟩ := odd_sLen D
  rcases Nat.mod_two_eq_zero_or_one (rankV D i j) with h | h
  · refine ⟨inv _ χc (by rw [Int.even_iff]; omega), fun x => ?_⟩
    simp only [betaH, h, pow_zero, mul_one, inv_f]
    rfl
  · refine ⟨inv _ (mul 1 χc χe (by decide)) (by rw [Int.even_iff]; omega), fun x => ?_⟩
    simp only [betaH, h, pow_one, inv_f, mul_f]
    rfl

end GlobalTheory.FunObj.SqNum
