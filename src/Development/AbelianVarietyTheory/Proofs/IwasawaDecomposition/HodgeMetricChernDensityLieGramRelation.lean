module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultOfNotMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BoundedDomainModelGramContDiffIsUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainModelEqMulOrigin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityGrassmannRelationOriginZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagComponentDimAndBaseDim
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeGramLocalModelAlgebraicChartHolomorphic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChange
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

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

namespace GlobalTheory.HodgeRelation

theorem chernTop_lieGram_rel_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (τ : GlobalTheory.AllWt.Psi H) (k' : ℕ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), 1 ≤ k' → chernTop ((∑ a ∈ Finset.range (k' + 1), MvPolynomial.C ((-1 : ℝ) ^ (k' - a)) * MvPolynomial.X (τ.1, a) * MvPolynomial.X (conjEmb τ.1, k' - a)) * Q) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) = 0 := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA τ k' Q hk
  obtain ⟨-, hXd⟩ := _root_.GlobalTheory.FlagBaseDim.dims E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL
  have hcard : Fintype.card (Fin X.dim) = Fintype.card (GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) := by
    simp [hXd, Fintype.card_prod]
  let ix : Fin X.dim ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q := Fintype.equivOfCardEq hcard
  obtain ⟨φ, g, cc, hcc, hφ, hg, hgu, hdom, hev⟩ :=
    _root_.GlobalTheory.PointChern.lieGram_local_model E H Dw l Xo c O β Y T F e σ U hG hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA ix
  set v := c'.e y
  set M : ReciprocityTheory.L2DbarEstimates.V X.dim → Mat Dw.mult ℂ := fun u => modelGram H Dw (coordOf ix u) with hM
  have hsm := _root_.GlobalTheory.PointChern.modelGram_smooth_isUnit E H Dw ix (φ v) hdom
  have hφr : ContDiffAt ℝ 2 φ v := (hφ.contDiffAt (n := 2)).restrict_scalars ℝ
  have hK2 : ∀ τ, MContDiffAt 2 (fun w => M (φ w) τ) v := fun τ a b => ((hsm τ).1 a b).comp v hφr
  obtain ⟨κ, hκ⟩ := _root_.GlobalTheory.PointChern.chernTop_model_eq_mul E H Dw ix (φ v) hdom
  change chernTop (relPoly τ k' * Q) _ v = 0
  rw [_root_.GlobalTheory.PointChern.chernTop_changeFrame _ _ (fun w => M (φ w)) g cc v hcc hg hgu hK2 (fun τ => (hsm τ).2) hev,
    _root_.GlobalTheory.ChernPull.chernTop_comp _ M φ v hφ (fun τ => (hsm τ).1) (fun τ => (hsm τ).2), hκ, _root_.GlobalTheory.PointChernRel.relation_top_zero E H Dw ix τ k' hk Q,
    mul_zero, mul_zero]

end GlobalTheory.HodgeRelation
