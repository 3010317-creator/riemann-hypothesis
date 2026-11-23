module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRapidDecaySiegelConeRealPoints
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DifferentiableAtChart
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealDiagonalInfGLEqPositiveIdeleDiagonal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTranslatesSmoothFunctionOfCompact
public import GroundTheory.AutomorphicForms.ReductionIwasawa
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelSetAdelicGLExistsCompactDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspFormOperatorAct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory

theorem cuspRapidDecaySiegelGL_of_finite (hfin : GlobalTheory.Published.AutomorphicFormsFiniteGL) :
    GlobalTheory.Published.CuspRapidDecaySiegelGL := by
  intro E _ _ _ a φ hφ ω hω hωB _ t ht lam
  obtain ⟨Ω, Kf, hΩ, hKf, hgeom⟩ := _root_.GlobalTheory.SiegelSetGL.exists_compact_decomp E a ω hω hωB t ht
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.finite_translates_of_isCompact E a φ hφ.1.level Kf hKf
  have hcore := fun f' : GL (Fin a) (Af E) =>
    _root_.GlobalTheory.cuspForm_rapidDecay_siegel hfin E a (finRep E a f' φ) (_root_.GlobalTheory.CuspStabFin.isCuspForm_act hfin E a (.fin f') φ hφ) Ω hΩ t ht lam
  choose C hC0 hC using hcore
  refine ⟨∑ f' ∈ S, C f', fun b hb r hr hchain hprod k hk => ?_⟩
  obtain ⟨d, hd, hdiag⟩ := _root_.GlobalTheory.SiegelTorusInf.exists_diag_infGL E a r hr
  rw [hdiag]
  obtain ⟨c, hc, f, hf, heq⟩ := hgeom r d hr hchain hd b hb k hk
  rw [heq]
  obtain ⟨f', hf', hff'⟩ := hS f hf
  have e : φ.1 (infGL E a (d * c) * finGL E a f) = (finRep E a f' φ).1 (infGL E a (d * c)) := by
    rw [← hff']; rfl
  rw [e]
  refine (hC f' r d hr hchain hd hprod c hc).trans ?_
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun i _ => hC0 i) hf')
    (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (hr i).le _)

end GlobalTheory
