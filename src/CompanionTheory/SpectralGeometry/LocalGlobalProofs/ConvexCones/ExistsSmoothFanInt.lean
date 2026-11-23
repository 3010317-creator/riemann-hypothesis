module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.CmOrdIntId
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsIsPosDefOfBasis
public import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothPolyhedralFanRefinement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IntegerLatticeDominates
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.VoronoiFanIsPolyhedral
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
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt

@[expose] public section

set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan

theorem hasRedCover_int_proj (Y : Type) [AddCommGroup Y] [m : Module ℤ Y] [Module.Finite ℤ Y] [Module.Projective ℤ Y] :
    HasRedCover (id : ℤ → ℤ) Y := by
  obtain rfl : m = AddCommGroup.toIntModule Y := Subsingleton.elim _ _
  have : Module.Free ℤ Y := inferInstance
  exact hasRedCover_int Y

theorem dominates_int_proj (Y : Type) [AddCommGroup Y] [m : Module ℤ Y] [Module.Finite ℤ Y] [Module.Projective ℤ Y] :
    Dominates (id : ℤ → ℤ) Y := by
  obtain rfl : m = AddCommGroup.toIntModule Y := Subsingleton.elim _ _
  have : Module.Free ℤ Y := inferInstance
  exact _root_.GlobalTheory.CompanionTheory.Ar.Fan.dominates_int Y

theorem exists_smooth_fan_int : ∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan id g φ ∧ NoSelfInt id g φ := by
  intro g
  have hpoly : IsPolyFan (id : ℤ → ℤ) g (vorFun ℤ g) :=
    _root_.GlobalTheory.CompanionTheory.Ar.Fan.vorFun_isPolyFan ℤ id g g (fun Y _ _ _ _ => hasRedCover_int_proj Y) (by simp)
  have htw : IsTwG (0 : ℤ) (vorFun ℤ g) := fun σ _ n B => baseFun_twist _ _ _ σ n B
  obtain ⟨φ, h₁, h₂, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.SmoothRefinement.exists_smooth_refinement ℤ id 0 cmOrd_int_id g (vorFun ℤ g)
    (fun Y _ _ _ _ => dominates_int_proj Y) hpoly htw
  exact ⟨φ, h₁, h₂⟩

end GlobalTheory.CompanionTheory.Ar.Fan
