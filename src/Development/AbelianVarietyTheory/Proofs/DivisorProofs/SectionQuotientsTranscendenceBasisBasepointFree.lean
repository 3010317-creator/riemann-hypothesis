module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralQuotientRingSectionTupleLocus
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusAmpleSectionIsAffineModel
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithFunctionFieldCharZeroTrdeg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisSectionTupleQuotients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionProperties
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

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem gens_quot_trBasis : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (∀ j, x j ≠ 0) ∧ AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) ∧ FiniteDimensional (ratF x) X.functionField := by
  intro k _ X _ p D hX P hA e x hG
  obtain ⟨l, hl⟩ := hG.cover (genericPoint X)
  have hxl : x l ≠ 0 := ((_root_.GlobalTheory.HSAmp.nv_rules k X p P (e : ℤ) 0 (x l) (hG.mem l)).2.1).1 hl
  obtain ⟨U, hU, hUeq, -, hreg, hft, hfrac, -⟩ :=
    _root_.GlobalTheory.AffModel.main k X p D hX P hA e (x l) hG.pos (hG.mem l) hxl
  obtain ⟨hch, htr⟩ := _root_.GlobalTheory.ArithFnField.charZero_and_trdeg_functionField k X p D hX
  refine _root_.GlobalTheory.HSAmp.TrBasis.trBasis_of_integral_ratR X.functionField D x l (fnOf U hU).range htr hxl hft ?_ hfrac
  intro w hw
  refine _root_.GlobalTheory.FnInt.main k X p D hX P e x hG l w hxl ?_
  intro z hz
  rw [← hUeq] at hz
  exact (hreg w).2 hw z hz

end GlobalTheory.HSAmp
