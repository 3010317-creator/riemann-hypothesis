module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero
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

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}

theorem hom_ext' {s : X ⟶ Sp R} {P Q : Pt s} {φ ψ : P.Hom Q} (h : ∀ b, φ.ρ b = ψ.ρ b) : φ = ψ := by
  obtain ⟨ρ, e⟩ := φ
  obtain ⟨ρ', e'⟩ := ψ
  obtain rfl : ρ = ρ' := AlgHom.ext h
  rfl

instance ptCat (s : X ⟶ Sp R) : Category.{0} (Pt s) where
  Hom := Pt.Hom
  id := Pt.Hom.id
  comp := Pt.Hom.comp
  id_comp _ := hom_ext' fun _ ↦ rfl
  comp_id _ := hom_ext' fun _ ↦ rfl
  assoc _ _ _ := hom_ext' fun _ ↦ rfl

@[reducible] def FP (s : X ⟶ Sp R) : Pt s ⥤ CommAlgCat.{0} R where
  obj P := CommAlgCat.of R P.B
  map φ := CommAlgCat.ofHom φ.ρ

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {φ : X' ⟶ X}

@[reducible] def pushPt (h : φ ≫ s = s' ≫ spMap σ) (P : Pt s') : Pt s where
  B := P.B
  alg := ((algebraMap R' P.B).comp σ).toAlgebra
  x := P.x ≫ φ
  w := by rw [Category.assoc, h, ← Category.assoc, P.w, ← GlobalTheory.Cris.spMap_comp]

def pushHom (h : φ ≫ s = s' ≫ spMap σ) {P Q : Pt s'} (f : P ⟶ Q) : pushPt h P ⟶ pushPt h Q where
  ρ := { (f.ρ : P.B →+* Q.B) with commutes' := fun r ↦ f.ρ.commutes (σ r) }
  pt := by
    change spMap (f.ρ : P.B →+* Q.B) ≫ P.x ≫ φ = Q.x ≫ φ
    rw [← Category.assoc, f.pt]

end CrystallinePoints.Pd
