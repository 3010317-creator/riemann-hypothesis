module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ClosureSpanCoefficients
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

namespace UpperTheory.Reformulated.B.OrthogonalGroupLemmas

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.ThK
  IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField

theorem aux1 (F : Type) [Field F] [NumberField F] {a b : AF F}
    (ha : a ∈ {a : AF F | evI F a = 0 ∧
      ∀ v : HeightOneSpectrum (RingOfIntegers F), evFin F v a ∈ adicCompletionIntegers F v})
    (hb : b ∈ {a : AF F | evI F a = 0 ∧
      ∀ v : HeightOneSpectrum (RingOfIntegers F), evFin F v a ∈ adicCompletionIntegers F v}) :
    evI F (a + b) = 0 ∧
      ∀ v : HeightOneSpectrum (RingOfIntegers F),
        evFin F v (a + b) ∈ adicCompletionIntegers F v := by
  refine ⟨?_, fun v => ?_⟩
  · have h : evI F (a + b) = evI F a + evI F b :=
      map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1
    rw [h, ha.1, hb.1, add_zero]
  · rw [map_add (f := _)]
    exact add_mem (ha.2 v) (hb.2 v)

theorem aux2 (F : Type) [Field F] [NumberField F] :
    evI F (0 : AF F) = 0 ∧
      ∀ v : HeightOneSpectrum (RingOfIntegers F),
        evFin F v (0 : AF F) ∈ adicCompletionIntegers F v := by
  refine ⟨map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F), fun v => ?_⟩
  rw [map_zero]
  exact zero_mem _

theorem aux3 (F : Type) [Field F] [NumberField F] {a : AF F}
    (ha : a ∈ {a : AF F | evI F a = 0 ∧
      ∀ v : HeightOneSpectrum (RingOfIntegers F), evFin F v a ∈ adicCompletionIntegers F v}) :
    evI F (-a) = 0 ∧
      ∀ v : HeightOneSpectrum (RingOfIntegers F), evFin F v (-a) ∈ adicCompletionIntegers F v := by
  refine ⟨?_, fun v => ?_⟩
  · have h : evI F (-a) = -evI F a :=
      map_neg (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1
    rw [h, ha.1, neg_zero]
  · rw [map_neg]
    exact neg_mem (ha.2 v)

noncomputable def Oh (F : Type) [Field F] [NumberField F] : AddSubgroup (AF F) :=
  { carrier := {a : AF F | evI F a = 0 ∧
      ∀ v : HeightOneSpectrum (RingOfIntegers F), evFin F v a ∈ adicCompletionIntegers F v}
    add_mem' := @aux1 F _ _
    zero_mem' := aux2 F
    neg_mem' := @aux3 F _ _ : AddSubgroup (AF F) }

theorem lat_gen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {n : ℕ} {Y : Spc F E n} (hL : Submodule.IsLattice E Y.L) :
    ∃ (m : ℕ) (x : Fin m → Y.L), Submodule.span ℤ (Set.range x) = ⊤ ∧
      ∀ z : Fin n → AE (F := F) (E := E), z ∈ latHat Y ↔
        ∃ a : Fin m → AF F, (∀ i, a i ∈ Oh F) ∧
          ∑ i : Fin m, a i • incV F (x i : Fin n → E) = z := by
  have h1 : Module.Finite (RingOfIntegers E) Y.L := Module.Finite.iff_fg.2 hL.fg
  have h2 : Module.Finite ℤ Y.L := Module.Finite.trans (RingOfIntegers E) Y.L
  obtain ⟨m, x, hx⟩ := Module.Finite.exists_fin (R := ℤ) (M := Y.L)
  refine ⟨m, x, hx, fun z => ?_⟩
  let f : Y.L →+ (Fin n → AE (F := F) (E := E)) :=
    { toFun := fun l => incV F (l : Fin n → E)
      map_zero' := funext fun _ => map_zero (inclR (F := F) (E := E) (AF F))
      map_add' := fun a b => funext fun i =>
        map_add (inclR (F := F) (E := E) (AF F)) (a.1 i) (b.1 i) }
  have hs : latHat Y = AddSubgroup.closure {z | ∃ a ∈ Oh F, ∃ l : Y.L, z = a • f l} := by
    unfold latHat
    congr 1
    ext w
    constructor
    · rintro ⟨a, h0, hv, y, hy, rfl⟩
      exact ⟨a, ⟨h0, hv⟩, ⟨y, hy⟩, rfl⟩
    · rintro ⟨a, ⟨h0, hv⟩, y, rfl⟩
      exact ⟨a, h0, hv, y.1, y.2, rfl⟩
  rw [hs]
  exact UpperTheory.closure_span_coefficients (Oh F) f x hx z

end UpperTheory.Reformulated.B.OrthogonalGroupLemmas
