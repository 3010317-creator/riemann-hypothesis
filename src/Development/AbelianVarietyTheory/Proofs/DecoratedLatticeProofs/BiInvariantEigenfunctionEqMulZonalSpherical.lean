module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasBoundedSumsOne
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SatakeTrivialRangeBound
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanAntitone
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceLocalFieldStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CartanDecompositionDominanceOrderStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBorelSphericalFunction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParahoricAndIntegralGLDoubleCosetReps
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SatakeSubsetSum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalDoubleCosetRepsMul
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumBorelSphericalOverDiagonalDoubleCosetReps
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntBiInvariant
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntEig
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZonalIntOneEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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

@[expose] public section

noncomputable section

open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ZonalUnique

theorem genVal_top_ne_zero (q N : ℕ) (α : Fin N → ℂˣ) : genVal q 0 N (Finset.univ.val.map α) N ≠ 0 := by
  simp only [genVal, Nat.sub_self, mul_zero, zero_mul, add_zero, pow_zero, one_mul, Multiset.map_map]
  have e : (Multiset.map ((fun b : ℂˣ => (b : ℂ)) ∘ α) Finset.univ.val).esymm N = ∏ i, (α i : ℂ) := by
    rw [Finset.esymm_map_val]
    have : (Finset.univ : Finset (Fin N)).powersetCard N = {Finset.univ} := by
      simpa using Finset.powersetCard_self (Finset.univ : Finset (Fin N))
    rw [this, Finset.sum_singleton]; rfl
  rw [e, Finset.prod_ne_zero_iff]
  exact fun i _ => (α i).ne_zero

theorem eq_mul_zonalInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)] (μK : Measure (GL (Fin N) k)) [μK.IsHaarMeasure], μK (KO k (Fin N)) = 1 → ∀ (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ α : Fin N → ℂˣ, ∃ ψ : GL (Fin N) k → ℂ, IsBorelSph k (borelParam (resCard k) α) ψ ∧ ∀ f : GL (Fin N) k → ℂ, (∀ κ ∈ KO k (Fin N), ∀ m, f (κ * m) = f m ∧ f (m * κ) = f m) → (∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m, ∑ g ∈ R, f (m * g) = genVal (resCard k) 0 N (Finset.univ.val.map α) s.card * f m) → ∀ m, f m = f 1 * zonalInt μK ψ m := by
  intro k _ _ _ _ N _ _ μK _ hK ϖ hϖ α
  have hq : (1 : ℕ) < resCard k := GlobalTheory.IndefiniteRowSideFullHecke.SatakeTrivialRangeBound.one_lt_resCard k
  have hγ : ∀ i, borelParam (resCard k) α i ≠ 0 := by
    intro i
    unfold borelParam
    refine mul_ne_zero (α i).ne_zero ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => by exact_mod_cast (show resCard k ≠ 0 by omega) (by exact_mod_cast h.1)
  obtain ⟨ψ, hψ⟩ := _root_.GlobalTheory.BorelSphExist.exists_isBorelSph k N _ hγ
  refine ⟨ψ, hψ, fun f hf he m => ?_⟩
  have hr : ∀ g, ∀ x ∈ KO k (Fin N), ψ (g * x) = ψ g := hψ.1
  have hωb := _root_.GlobalTheory.ZonalBi.zonalInt_biInvariant k N μK hK ψ hr
  have hω1 := _root_.GlobalTheory.ZonalOne.zonalInt_one_eq_one k N μK hK _ ψ hψ
  have hωe : ∀ (s : Finset (Fin N)) R, IsRepsK (torusElt k (Fin N) ϖ (indic s)) R → ∀ m,
      ∑ g ∈ R, zonalInt μK ψ (m * g) = genVal (resCard k) 0 N (Finset.univ.val.map α) s.card * zonalInt μK ψ m := by
    intro s R hR
    refine _root_.GlobalTheory.ZonalEig.zonalInt_eig k N μK hK ψ hr R _ fun m => ?_
    rw [_root_.GlobalTheory.ZonalSum.sum_mul_eq k N _ ψ hψ hγ _ R hR m, _root_.GlobalTheory.BorelCosetSum.sum_cosets_eq k N ϖ hϖ _ ψ hψ hγ s R hR,
      _root_.GlobalTheory.SatakeSubsetSum.satake_subset_sum (resCard k) N (by omega) α s.card, mul_comm]
  have hcN : genVal (resCard k) 0 N (Finset.univ.val.map α) N ≠ 0 := genVal_top_ne_zero _ N α
  have key := GlobalTheory.T.cartan_decomposition_dominance_order k N ϖ (fun n => genVal (resCard k) 0 N (Finset.univ.val.map α) n) hcN
    (_root_.GlobalTheory.SortedCartan.cartan_antitone k N ϖ hϖ) (GlobalTheory.T.cartan_decomposition_dominance_local_field k N ϖ hϖ) (fun g => (_root_.GlobalTheory.ParHeckeReps.exists_reps_both k Unit (Fin N)).2 g)
    (fun m => f m - f 1 * zonalInt μK ψ m)
    (fun κ hκ m => ⟨by rw [(hf κ hκ m).1, (hωb κ hκ m).1], by rw [(hf κ hκ m).2, (hωb κ hκ m).2]⟩)
    (fun s R hR m => by
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, he s R hR m, hωe s R hR m]
      ring)
    (by simp [hω1]) m
  exact sub_eq_zero.1 key

end GlobalTheory.ZonalUnique

end
