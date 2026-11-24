module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import GroundTheory.AutomorphicForms.L2LocalComponents.Summand
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

noncomputable section

open NumberField MeasureTheory GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL
open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum

namespace UpperTheory.V.KernelIndexFullLattice

section Defs

variable (E : Type) [Field E] [NumberField E] (a : ℕ)

abbrev G1 : Type := Reduction.normOneGL (K := E) (n := a)

abbrev Γ1 : Subgroup (G1 E a) := Reduction.rationalGLOne (K := E) (n := a)

variable [_root_.NumberField.IsTotallyComplex E]

def band : Set (GA E a) :=
  {g | a = 0 ∨ (1 ≤ Reduction.detModule E a g ∧
    Reduction.detModule E a g < Reduction.detModule E a (splitCentre E a 1))}


variable {E a} in
def muOne (μ : Measure (GA E a)) : Measure (G1 E a) := Measure.map retractOne (μ.restrict (band E a))

def quotMap (q : Quot (latticeGL E a)) : RightCosetSpace (Γ1 E a) :=
  RightCosetSpace.mk (Γ1 E a) (retractOne q.out)

variable {E a}

abbrev Pres (μ : Measure (GA E a)) (μ₁ : Measure (G1 E a)) : Prop :=
  MeasurePreserving (quotMap E a) (quotMeasure (latticeGL E a) μ) (RightCosetSpace.quotientMeasure (Γ1 E a) μ₁)

def cmp {μ : Measure (GA E a)} {μ₁ : Measure (G1 E a)} [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) :
    CuspL2 μ₁ →ₗᵢ[ℂ] L2 (latticeGL E a) μ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (quotMap E a) hp).comp (cuspidalL2 μ₁).subtypeₗᵢ

end Defs

def SplitEq : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (t : ℝ),
    splitCentre E a t =
      Reduction.centralSection E a ⟨Real.exp (a * Module.finrank ℚ E * t), Real.exp_pos _⟩

def MuHaar : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure],
    (muOne μ).IsHaarMeasure

def QuotPres : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure],
    Pres μ (muOne μ)

def LiftCmp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (μ₁ : Measure (G1 E a)) [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) (v : CuspL2 μ₁) (Φ : RightCosetSpace (Γ1 E a) → ℂ),
    (toLp μ₁ v : RightCosetSpace (Γ1 E a) → ℂ) =ᵐ[RightCosetSpace.quotientMeasure (Γ1 E a) μ₁] Φ →
    lift (latticeGL E a) (cmp hp v) =ᵐ[μ] fun g => Φ (RightCosetSpace.mk (Γ1 E a) (retractOne g))

def CmpEquiv : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (μ₁ : Measure (G1 E a)) [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) (g : GA E a) (v : CuspL2 μ₁),
    R (latticeGL E a) μ g (cmp hp v) = cmp hp (cuspRepT μ₁ (retractOne g) v)

def CmpForm : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (μ₁ : Measure (G1 E a)) [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) (φ : cuspForms E a), φ ∈ centralCuspForms E a →
    lift (latticeGL E a) (cmp hp (cuspVecL μ₁ φ)) =ᵐ[μ] φ.1

def Dense : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ₁ : Measure (G1 K n)) [μ₁.IsHaarMeasure],
    ((centralCuspForms K n).map (cuspVecL μ₁)).topologicalClosure = ⊤

def NeBot : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ₁ : Measure (G1 K n)) [μ₁.IsHaarMeasure]
    (V : Submodule ℂ (CuspL2 μ₁)) [CompleteSpace V] (hV : (cuspRepT μ₁).IsInvariant V),
    ((cuspRepT μ₁).restrict V hV).IsIrreducible → summandCuspForms V ≠ ⊥

def RangeLe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (μ₁ : Measure (G1 E a)) [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) (v : CuspL2 μ₁), cmp hp v ∈ L2cusp μ

def ContMem : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    (μ₁ : Measure (G1 E a)) [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) (φ : GA E a → ℂ), φ ∈ cuspCont E a →
    ∀ h : MemL2Quotient (latticeGL E a) μ φ, ∃ v : CuspL2 μ₁, cmp hp v = h.toL2

def KFinTr : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (μ₁ : Measure (G1 E a)) [μ₁.IsHaarMeasure] (hp : Pres μ μ₁) (v : CuspL2 μ₁),
    IsKFinL2 μ (cmp hp v) →
    IsOpen {h : AdelicGLn.FiniteAdelicGL E a | cuspRepT μ₁ (retractOne (finEmb E a h)) v = v} ∧
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : archCompact E a => archRepT μ₁ (k : archGroup E a) v))

def AbsCompact : Prop :=
  ∀ (G G₁ H L : Type) [Group G] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁]
    [T2Space G₁] [MeasurableSpace G₁] [OpensMeasurableSpace G₁]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (π : UnitaryRep G₁ H) (ν : Measure G₁) [IsFiniteMeasureOnCompacts ν] [ν.IsOpenPosMeasure]
    (ρ : G →* (L →L[ℂ] L)) (W : Submodule ℂ L) (hW : IsSubrep ρ W) (J : H →ₗᵢ[ℂ] L) (r : G → G₁),
    Function.Surjective r → (∀ g v, ρ g (J v) = J (π (r g) v)) → LinearMap.range J.toLinearMap = W →
    (∀ f : CompactlySupportedContinuousMap G₁ ℂ, IsCompactOperator (π.integrated ν (UnitaryRep.ccToL1 ν f))) →
    EnoughCompact hW.rep

def AbsIrr : Prop :=
  ∀ (G G₁ H L : Type) [Group G] [Group G₁] [TopologicalSpace G₁]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (π : UnitaryRep G₁ H) (ρ : G →* (L →L[ℂ] L)) (J : H →ₗᵢ[ℂ] L) (r : G → G₁),
    Function.Surjective r → (∀ g v, ρ g (J v) = J (π (r g) v)) →
    ∀ X : Submodule ℂ L, X ≤ LinearMap.range J.toLinearMap → IsIrredSubrep ρ X →
    ∃ (_ : CompleteSpace (X.comap J.toLinearMap)) (hV : π.IsInvariant (X.comap J.toLinearMap)),
      (π.restrict (X.comap J.toLinearMap) hV).IsIrreducible

def KFinMem : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ₁ : Measure (G1 K n)) [μ₁.IsHaarMeasure]
    (π : CuspidalAutomorphicRepresentation K n) (v : CuspL2 μ₁),
    v ∈ (π.carrier.map (cuspVecL μ₁)).topologicalClosure →
    IsOpen {h : AdelicGLn.FiniteAdelicGL K n | cuspRepT μ₁ (retractOne (finEmb K n h)) v = v} →
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : archCompact K n => archRepT μ₁ (k : archGroup K n) v)) →
    v ∈ π.carrier.map (cuspVecL μ₁)

def BrCusp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (φ : Sm E a),
    IsCuspForm φ → φ.1 ∈ cuspForms E a

def BrRep : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π₀ : CuspidalAutomorphicRepresentation E a),
    ∃ π : CuspSub E a, π.V.map (Sm E a).subtype = π₀.carrier.map (cuspForms E a).subtype

end UpperTheory.V.KernelIndexFullLattice
