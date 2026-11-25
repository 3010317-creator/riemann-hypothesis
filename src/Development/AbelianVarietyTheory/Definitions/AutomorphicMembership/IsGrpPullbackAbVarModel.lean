module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicColimitOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Formalism.LocalToGlobal.ProjectiveLattices.DataAtPointN3
public import Formalism.LocalToGlobal.ProjectiveLattices.EmbKCoe
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.AbelianAt
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

@[expose] public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.TorusModel GlobalTheory.AdicColimit GlobalTheory.EigenSplit GlobalTheory.HTLat Formalism.L2.Pj
open Formalism.MainNotions.DIV.Cons (SCF intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLat

section Raynaud

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))}
  {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

def raynaud : Over (Sp R) := (exists_comparison U).choose

instance raynaudGrp : GrpObj (raynaud U) := (exists_comparison U).choose_spec.choose

instance raynaudComm : IsCommMonObj (raynaud U) := (exists_comparison U).choose_spec.choose_spec.choose

variable {Λ : Type} [CommRing Λ] [StarRing Λ] [Module Λ D.toPre.X] (ιD : D.toPre.OAct Λ)

end Raynaud

namespace Point

open OmegaRank

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O]
  [Algebra O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ)
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

end Point

end GlobalTheory.HTLat

namespace GlobalTheory.LocM

section Field

variable {p : ℕ} (C : SCF p)

abbrev fldVal : Valuation ↥C.S ℝ≥0 := NormedField.valuation (K := ↥C.S)

theorem integers_intO : (fldVal C).Integers ↥(intO ↥C.S) :=
  Valuation.integer.integers (fldVal C)

variable [Fact p.Prime]

theorem norm_p_lt_one : ‖algebraMap ↥(intO ↥C.S) ↥C.S (p : ↥(intO ↥C.S))‖ < 1 := by
  rw [map_natCast, C.norm_p]
  exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)

instance factNotIsUnitIntO : Fact ¬IsUnit (p : ↥(intO ↥C.S)) :=
  ⟨fun h => (norm_p_lt_one C).ne ((NormIntegers.isUnit_iff_norm_eq_one (integers_intO C)).1 h)⟩

instance isAdicCompleteIntO : IsAdicComplete (Ideal.span {(p : ↥(intO ↥C.S))}) ↥(intO ↥C.S) :=
  NormIntegers.isAdicComplete_span_singleton (integers_intO C) (norm_p_lt_one C)

def padicEmb : ℚ_[p] →+* ↥C.S := (exists_padic_isometry p C.norm_p).choose

theorem norm_padicEmb (x : ℚ_[p]) : ‖padicEmb C x‖ = ‖x‖ := (exists_padic_isometry p C.norm_p).choose_spec x

instance padicIntAlgebra : Algebra ℤ_[p] ↥C.S := ((padicEmb C).comp PadicInt.Coe.ringHom).toAlgebra

instance padicIntAlgebraIntO : Algebra ℤ_[p] ↥(intO ↥C.S) :=
  ((algebraMap ℤ_[p] ↥C.S).codRestrict (intO ↥C.S) fun x => (norm_padicEmb C x).trans_le x.2).toAlgebra

instance padicIntTower : IsScalarTower ℤ_[p] ↥(intO ↥C.S) ↥C.S := IsScalarTower.of_algebraMap_eq fun _ => rfl

end Field

section Roots

variable {p : ℕ} [Fact p.Prime] {F : IntermediateField ℚ ℂ} {C : Type} [Field C] [IsAlgClosed C]

theorem exists_eps_of_hom (f : F →+* C) : ∃ ε : Eps p C, ∀ (n : ℕ) (h : zeta (p ^ n) ∈ F),
    (ε.1.lev n : C) = f ⟨zeta (p ^ n), h⟩ := by
  have hp : p.Prime := Fact.out
  letI : Algebra F C := f.toAlgebra
  have key : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [Algebra K C],
      Nonempty (algebraicClosure K L →ₐ[K] C) := fun _ _ _ _ _ _ => ⟨IsAlgClosed.lift⟩
  obtain ⟨g⟩ := key F ℂ
  have hz : ∀ n, IsPrimitiveRoot (zeta (p ^ n)) (p ^ n) := fun n =>
    Complex.isPrimitiveRoot_exp _ (pow_ne_zero _ hp.ne_zero)
  have hm : ∀ n, zeta (p ^ n) ∈ algebraicClosure F ℂ := fun n =>
    mem_algebraicClosure_iff'.2 ((hz n).isIntegral (pow_pos hp.pos n)).tower_top
  have hz' : ∀ n, IsPrimitiveRoot (g ⟨_, hm n⟩) (p ^ n) := fun n =>
    (IsPrimitiveRoot.of_map_of_injective (f := (algebraicClosure F ℂ).val) (hz n)
      Subtype.val_injective).map_of_injective g.injective
  let s : ℕ → Cˣ := fun n => ((hz' n).isUnit (pow_ne_zero _ hp.ne_zero)).unit
  have hs : ∀ n, (s n : C) = g ⟨_, hm n⟩ := fun _ => rfl
  refine ⟨⟨Tate.mk s fun n => ⟨Units.ext (hz' n).pow_eq_one, Units.ext ?_⟩, ?_⟩, fun n h => g.commutes ⟨_, h⟩⟩
  · rw [Units.val_pow_eq_pow_val, hs, hs, ← map_pow]
    refine congrArg g (Subtype.ext ?_)
    have h0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    change zeta (p ^ (n + 1)) ^ p = zeta (p ^ n)
    rw [zeta, zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    field_simp
    ring
  · exact IsPrimitiveRoot.coe_units_iff.1 ((congrArg (IsPrimitiveRoot (g ⟨_, hm 1⟩)) (pow_one p)).mp (hz' 1))

end Roots

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {p : ℕ} {C : SCF p}

section Fibre

variable (P : PointsOfFlagModel.PtC Y C)

def abVar : PolAV (Sp ↥C.S) := StrictPull.polPull (Obj.toPolAV Y.oF) P.y

variable [Fact p.Prime]

def epsAt : Eps p ↥C.S := (exists_eps_of_hom P.fK).choose

end Fibre

variable {P : PointsOfFlagModel.PtC Y C} (A : DatAt Y P)

variable [Fact p.Prime]

end GlobalTheory.LocM
