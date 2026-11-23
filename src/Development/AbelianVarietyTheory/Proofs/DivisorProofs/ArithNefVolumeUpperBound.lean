module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithKleimanHeightNefOfIsNef
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithLogSmallSectionsUpperBound
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLeOfSmallSectionLogCountUpperBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistNefSquarefreeMonomialsSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleGeometricDegreeNonnegOfSemiPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermLineBundleIsNefTens
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLineBundlePositivityPreservedIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPow
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisFunctionFieldArithmeticVarie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsBaseBundlesAndTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionsTwistedPowerEncardEqBall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoHermLineBundleGeometricDegreePowTensDivPo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoSelfIntersectionPowTensorDivPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefUpper

theorem log_ncard_smallSec {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p) :
    Real.log (P.L.smallSec.ncard : ℝ) = P.lc 1 0 1 := by
  have h := SmallBall.encard_eq_Bl P (Pair.rep_base k X p P).1 P.L.smallSec 1 zero_le_one fun u => by
    simp only [HermLB.smallSec, Set.mem_setOf_eq, one_pow]
  unfold Pair.lc
  rw [Set.ncard_def, Set.ncard_def, h]

theorem main : GlobalTheory.Published.ArCalc → AmpleHS → SemiPull → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L N : HermLB p) (a : ℝ), L.IsNef D → L.IsSelfInter a →
    ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop,
      Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) ≤ (a / (D + 1).factorial + ε) * (m : ℝ) ^ (D + 1) := by
  intro HC HA HS k _ X _ p D hX L N a hL ha ε hε
  obtain ⟨⟨x, hx⟩, -⟩ := _root_.GlobalTheory.ArithTrdeg.isTranscendenceBasis_functionField k X p D hX
  obtain ⟨H, hNH, hbox⟩ := _root_.GlobalTheory.HSNef.BoxTwist.exists_twist HC k X p D hX N x
  set G := N.tens H with hG

  have hnef : ∀ m : ℕ, ((L.pow m).tens G).IsNef D := fun m =>
    _root_.GlobalTheory.NefTens.isNef_tens HC k X p D hX _ _ (GlobalTheory.NefPow.isNef_pow HC k X p D hX L m hL) hNH
  obtain ⟨α, hα, hαlim⟩ := GlobalTheory.SelfInterGrowth.main HC k X p D hX L G a ha
  have hα0 : ∀ m, 0 ≤ α m := fun m => by
    obtain ⟨h, Hh, e⟩ := hα m
    rw [← e]
    exact (_root_.GlobalTheory.KleimanNef.htNef_of_isNef HC HA HS k X p D hX _ (hnef m)).2 h Hh _
  have hg0 : ∀ m, 0 ≤ gdeg ((L.pow m).tens G) D := fun m =>
    _root_.GlobalTheory.HSNef.gdeg_nonneg_of_semiPos k X p D hX _ (hnef m).semiPos
  have hglim := _root_.GlobalTheory.DegGrowth.main HC k X p D hX L G
  refine _root_.GlobalTheory.HSNefAsymp.eventually_le_of_bound D (fun m => Real.log (((L.pow m).tens N).smallSec.ncard : ℝ)) α
    (fun m => gdeg ((L.pow m).tens G) D) a (gdeg L D) hα0 hg0 hαlim hglim (fun m q hq => ?_) ε hε
  obtain ⟨P, hPL, hPA, hPbox⟩ := hbox ((L.pow m).tens N)
  have hiso : (P.L.tens P.A).Isometric ((L.pow m).tens G) := by
    rw [hPL, hPA]
    exact HermLB.isometric_tens_assoc _ _ _
  have T := _root_.GlobalTheory.HSNef.isometric_keeps HC k X p D hX _ _ hiso.symm
  have hb := _root_.GlobalTheory.HSNef.lc_le_bound HC HA HS k X p D hX P x (α m) q hx.1 hPbox (T.2.1 (hnef m)) (T.2.2.2.1 _ (hα m)) hq
  rw [hiso.gdeg_eq, ← log_ncard_smallSec] at hb
  have e : Real.log (P.L.smallSec.ncard : ℝ) = Real.log (((L.pow m).tens N).smallSec.ncard : ℝ) := by
    rw [hPL]
  simpa only [e] using hb

end GlobalTheory.NefUpper
