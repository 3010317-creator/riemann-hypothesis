module

public import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineOneCut

abbrev fib {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Scheme.{0} :=
  pullback p (cpt A)

def fibMap {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    fib (ι ≫ p) ⟶ fib p :=
  pullback.map (ι ≫ p) (cpt A) p (cpt A) ι (𝟙 _) (𝟙 _) (by simp) (by simp)

def FibCover : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A))
  (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  IsOpenImmersion (fibMap p ι₁) ∧ IsOpenImmersion (fibMap p ι₂) ∧ Set.range (fibMap p ι₁) ∪ Set.range (fibMap p ι₂) = Set.univ

def ChartAcyc : Prop := Hyp → ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] {Z U : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z), IsOpenImmersion ι → IsAffine U → AICSch Z → IsUnit (q : A) →
  Acyc q (sch.obj (fib (ι ≫ p)))

end LateralTheory.E.LineOneCut
