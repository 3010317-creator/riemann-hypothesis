module

public import Mathlib.NumberTheory.LocalField.Basic
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Instances.Matrix
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

namespace UpperTheory.Reformulated.B.BlockHomomorphism

noncomputable def IsSmooth {k G V : Type} [Field k] [Group G] [AddCommGroup V] [Module k V]
    [TopologicalSpace G] (ρ : Representation k G V) : Prop :=
  ∀ v : V, IsOpen {g : G | ρ g v = v}

noncomputable def glCongr (k : Type) [Field k] {a b : ℕ} (h : a = b) :
    GL (Fin a) k →* GL (Fin b) k :=
  Units.map (Matrix.reindexAlgEquiv k k (finCongr h)).toMulEquiv.toMonoidHom

theorem aux3 (k : Type) [Field k] (n r : ℕ) :
    Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) k) 0 0 (1 : Matrix (Fin r) (Fin r) k) = 1 :=
  Matrix.fromBlocks_one

theorem aux4 (k : Type) [Field k] (n r : ℕ) (A B : Matrix (Fin n) (Fin n) k) :
    Matrix.fromBlocks (A * B) 0 0 (1 : Matrix (Fin r) (Fin r) k) =
      Matrix.fromBlocks A 0 0 1 * Matrix.fromBlocks B 0 0 1 := by
  simp [Matrix.fromBlocks_multiply]

noncomputable def blkHom (k : Type) [Field k] (n r : ℕ) :
    Matrix (Fin n) (Fin n) k →* Matrix (Fin n ⊕ Fin r) (Fin n ⊕ Fin r) k where
  toFun A := Matrix.fromBlocks A 0 0 1
  map_one' := aux3 k n r
  map_mul' := aux4 k n r

noncomputable def blkGL (k : Type) [Field k] (n r : ℕ) :
    GL (Fin n) k →* GL (Fin (n + r)) k :=
  Units.map ((Matrix.reindexAlgEquiv k k finSumFinEquiv).toMulEquiv.toMonoidHom.comp
    (blkHom k n r))

noncomputable def blkAt (k : Type) [Field k] (n N : ℕ) (h : n ≤ N) :
    GL (Fin n) k →* GL (Fin N) k :=
  (glCongr k (Nat.add_sub_cancel' h)).comp (blkGL k n (N - n))

noncomputable def FixK {k : Type} [Field k] {m N : ℕ} (h : m + 1 ≤ N) {V : Type}
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (K : Subgroup (GL (Fin (m + 1)) k)) (v : V) : Prop :=
  ∀ g ∈ K, π (blkAt k (m + 1) N h g) v = v

theorem aux9 {m N : ℕ} {h : m + 2 ≤ N} : ¬ m + 1 ≤ N → False := by
  omega

private theorem continuous_blkAt {k : Type} [Field k] [TopologicalSpace k]
    (n N : ℕ) (h : n ≤ N) : Continuous (blkAt k n N h) := by
  have h1 : Continuous (blkGL k n (N - n)) := by
    unfold blkGL
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin n) (Fin n) k =>
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks A 0 0 (1 : Matrix (Fin (N - n)) (Fin (N - n)) k))
    exact (Continuous.matrix_fromBlocks continuous_id continuous_const continuous_const
      continuous_const).matrix_reindex _ _
  have h2 : ∀ {a b : ℕ} (e : a = b), Continuous (glCongr k e) := by
    intro a b e
    unfold glCongr
    apply Continuous.units_map
    change Continuous fun A : Matrix (Fin a) (Fin a) k =>
      Matrix.reindex (finCongr e) (finCongr e) A
    exact continuous_id.matrix_reindex _ _
  exact (h2 _).comp h1

private def fixer {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V) (v : V) : Subgroup G where
  carrier := {g | π g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change π (a * b) v = v
    rw [map_mul, mul_apply_eq_comp, hb, ha]
  inv_mem' := by
    intro a ha
    change π a⁻¹ v = v
    calc
      π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha]
      _ = v := by rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]

theorem exists_fixK {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {m N : ℕ} {h : m + 2 ≤ N} {V : Type}
    [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin N) k) V}
    (hπ : IsSmooth π) (v w : V) :
    ∃ K : Subgroup (GL (Fin (m + 1)) k),
      IsOpen (K : Set (GL (Fin (m + 1)) k)) ∧ FixK (by omega) π K v ∧ FixK (by omega) π K w := by
  have hle : m + 1 ≤ N := by omega
  refine ⟨(fixer π v ⊓ fixer π w).comap (blkAt k (m + 1) N hle), ?_,
    fun g hg => hg.1, fun g hg => hg.2⟩
  exact ((hπ v).inter (hπ w)).preimage (continuous_blkAt (m + 1) N hle)

end UpperTheory.Reformulated.B.BlockHomomorphism
