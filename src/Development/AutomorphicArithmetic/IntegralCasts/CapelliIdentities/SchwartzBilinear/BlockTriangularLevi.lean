module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.LocallyConstant.Basic
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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

namespace UpperTheory.Reformulated.B.P6.BlockTriangularLevi

open scoped Sigma DFunLike EquivLike Equiv Matrix CommSemiring CommRing Membership Set Preorder PartialOrder SemilatticeInf Lattice DistribLattice MulZeroClass Units Semiring HMul MulOne MulOneClass Monoid DivInvMonoid Group OfNat One Inv InvOneClass DivInvOneMonoid DivisionMonoid Subgroup Submonoid Subsemigroup Subtype SetLike MulZeroOneClass MonoidHom OneHom Pi PUnit Fin Finset HAdd AddMonoidWithOne AddGroupWithOne Ring DivisionRing Field CommGroup Circle DivisionSemiring Semifield Complex SeminormedRing SeminormedCommRing NormedCommRing NormedField AddChar Zero HSub

namespace GlobalTheory.SmGL

noncomputable def blk {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (i : n) : α :=
  (e.symm i).1

end GlobalTheory.SmGL

theorem blockIndex_sigma_equiv {α n : Type} {m : α → Type} (e : (a : α) × m a ≃ n) (a : α) (i : m a) :
    GlobalTheory.SmGL.blk (m := m) e (e ⟨a, i⟩) = a := by
  show (e.symm (e ⟨a, i⟩)).1 = a
  rw [Equiv.symm_apply_apply]

theorem blockTriangular_mul_submatrix {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [Fintype n] (e : (a : α) × m a ≃ n) (a : α) (X Y : Matrix n n R)
    (hX : X.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e))
    (hY : Y.BlockTriangular (GlobalTheory.SmGL.blk (m := m) e)) :
    (X * Y).submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩)
      = X.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩)
        * Y.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩) := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  rw [← e.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single a]
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro l _
    rcases lt_or_gt_of_ne hb with h | h
    · have h' : GlobalTheory.SmGL.blk (m := m) e (e ⟨b, l⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨a, i⟩) := by
        rw [blockIndex_sigma_equiv, blockIndex_sigma_equiv]; exact h
      rw [hX h', zero_mul]
    · have h' : GlobalTheory.SmGL.blk (m := m) e (e ⟨a, j⟩) < GlobalTheory.SmGL.blk (m := m) e (e ⟨b, l⟩) := by
        rw [blockIndex_sigma_equiv, blockIndex_sigma_equiv]; exact h
      rw [hY h', mul_zero]
  · intro h
    exact absurd (Finset.mem_univ a) h

namespace GlobalTheory.SmGL

theorem parab_obl_1 (R : Type) [CommRing R] {α n : Type} {m : α → Type} [LinearOrder α] [Fintype n]
    [DecidableEq n] (e : (a : α) × m a ≃ n) {x y : GL n R}
    (hx : x ∈ {g : GL n R | g.val.BlockTriangular (blk (m := m) e)})
    (hy : y ∈ {g : GL n R | g.val.BlockTriangular (blk (m := m) e)}) :
    x * y ∈ {g : GL n R | g.val.BlockTriangular (blk (m := m) e)} := by
  show ((x * y : GL n R) : Matrix n n R).BlockTriangular _
  rw [Units.val_mul]
  exact Matrix.BlockTriangular.mul hx hy

theorem parab_obl_2 (R : Type) [CommRing R] {α n : Type} {m : α → Type} [LinearOrder α] [Fintype n]
    [DecidableEq n] (e : (a : α) × m a ≃ n) :
    (1 : GL n R) ∈ {g : GL n R | g.val.BlockTriangular (blk (m := m) e)} := by
  show ((1 : GL n R) : Matrix n n R).BlockTriangular _
  rw [Units.val_one]
  exact Matrix.blockTriangular_one

theorem parab_obl_3 (R : Type) [CommRing R] {α n : Type} {m : α → Type} [LinearOrder α] [Fintype n]
    [DecidableEq n] (e : (a : α) × m a ≃ n) {x : GL n R}
    (hx : x ∈ {g : GL n R | g.val.BlockTriangular (blk (m := m) e)}) :
    x⁻¹ ∈ {g : GL n R | g.val.BlockTriangular (blk (m := m) e)} := by
  show ((x⁻¹ : GL n R) : Matrix n n R).BlockTriangular _
  rw [Matrix.coe_units_inv]
  have : Invertible (x : Matrix n n R) := x.invertible
  exact Matrix.blockTriangular_inv_of_blockTriangular hx

noncomputable def parab (R : Type) [CommRing R] {α n : Type} {m : α → Type} [LinearOrder α]
    [Fintype n] [DecidableEq n] (e : (a : α) × m a ≃ n) : Subgroup (GL n R) :=
  { carrier := {g : GL n R | g.val.BlockTriangular (blk (m := m) e)}
    mul_mem' := @parab_obl_1 R _ α n m _ _ _ e
    one_mem' := parab_obl_2 R (m := m) e
    inv_mem' := @parab_obl_3 R _ α n m _ _ _ e }

@[reducible] noncomputable def Levi (R : Type) [CommRing R] {α : Type} (m : α → Type)
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] : Type :=
  (a : α) → GL (m a) R

/- `Units.val (Subtype.val …)` keeps the original statement's terms: there `Subtype.val` takes
its type from `Units.val`, not from the subgroup, which `(1 : parab R e).val.val` would not
reproduce. -/
theorem diagBlock_obl_1 (R : Type) [CommRing R] {α n : Type} {m : α → Type} [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (a : α) × m a ≃ n) (a : α) :
    (Units.val (Subtype.val (p := fun x : GL n R => x ∈ parab R (m := m) e) 1)).submatrix
        (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩) = (1 : Matrix (m a) (m a) R) := by
  show ((1 : GL n R) : Matrix n n R).submatrix _ _ = 1
  rw [Units.val_one]
  exact Matrix.submatrix_one _ (e.injective.comp sigma_mk_injective)

theorem diagBlock_obl_2 (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α]
    [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (a : α) × m a ≃ n) (a : α) (x y : parab R (m := m) e) :
    (x * y).val.val.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩) =
      x.val.val.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩) *
        y.val.val.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩) := by
  have hx : ((x : GL n R) : Matrix n n R).BlockTriangular (blk (m := m) e) := x.2
  have hy : ((y : GL n R) : Matrix n n R).BlockTriangular (blk (m := m) e) := y.2
  have key := blockTriangular_mul_submatrix e a _ _ hx hy
  exact key

/- The value binds the instance arguments as implicit (`{_}`), as the original did: those binders
become the binders of the auxiliary proof `diagBlock._proof_1`. -/
noncomputable def diagBlock :
    (R : Type) → [CommRing R] → {α n : Type} → {m : α → Type} → [Fintype α] → [LinearOrder α] →
      [∀ a, Fintype (m a)] → [∀ a, DecidableEq (m a)] → [Fintype n] → [DecidableEq n] →
      (e : (a : α) × m a ≃ n) → (a : α) → parab R (m := m) e →* Matrix (m a) (m a) R :=
  fun R {_} {_ _} {m} {_ _ _ _ _ _} e a ↦
    { toFun := fun p => p.val.val.submatrix (fun i : m a => e ⟨a, i⟩) (fun i : m a => e ⟨a, i⟩)
      map_one' := diagBlock_obl_1 R (m := m) e a
      map_mul' := diagBlock_obl_2 R (m := m) e a }

noncomputable def leviProj (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α]
    [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (a : α) × m a ≃ n) : parab R (m := m) e →* Levi R m :=
  MonoidHom.pi fun a => (diagBlock R (m := m) e a).toHomUnits

noncomputable def unipRad (R : Type) [CommRing R] {α n : Type} {m : α → Type} [Fintype α]
    [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    (e : (a : α) × m a ≃ n) : Subgroup (GL n R) :=
  (leviProj R (m := m) e).ker.map (parab R (m := m) e).subtype

noncomputable def points (n : Type) : (_ : n) × Unit ≃ n :=
  Equiv.sigmaUnique n fun _ => Unit

noncomputable def unipB (R : Type) [CommRing R] (n : Type) [Fintype n] [DecidableEq n]
    [LinearOrder n] : Subgroup (GL n R) :=
  unipRad R (m := fun _ : n => Unit) (points n)

end GlobalTheory.SmGL

noncomputable def GlobalTheory.Whittaker.superDiag {R : Type} [CommRing R] {n : ℕ}
    (g : GL (Fin n) R) : R :=
  ∑ i : Fin n, ∑ j : Fin n with j.val = i.val + 1, g.val i j

namespace DiscreteGroups.sglob.LConv

open GlobalTheory.SmGL GlobalTheory.Whittaker

/- The memberships in `unipB` and `Submonoid.unitSphere ℂ` name their carrier types explicitly,
as the original statement did; left to unification they are elaborated with different instance
paths. -/
noncomputable def IsWhitTest {k : Type} [Field k] [TopologicalSpace k] {m : ℕ}
    (ψ : AddChar k Circle) (f : GL (Fin m) k → ℂ) : Prop :=
  (∀ u : GL (Fin m) k, Membership.mem (γ := Subgroup (GL (Fin m) k)) (unipB k (Fin m)) u →
      ∀ g : GL (Fin m) k,
        f (u * g) = Subtype.val (p := fun x : ℂ =>
          Membership.mem (γ := Submonoid ℂ) (Submonoid.unitSphere ℂ) x) (ψ (superDiag u)) * f g) ∧
    IsLocallyConstant f ∧
    ∃ C : Set (GL (Fin m) k), IsCompact C ∧
      ∀ g : GL (Fin m) k, f g ≠ 0 →
        ∃ u : GL (Fin m) k, Membership.mem (γ := Subgroup (GL (Fin m) k)) (unipB k (Fin m)) u ∧
          ∃ c ∈ C, g = u * c

theorem IsWhitTest.sub {k : Type} [Field k] [TopologicalSpace k] {m : ℕ} {ψ : AddChar k Circle}
    {f f' : GL (Fin m) k → ℂ} (hf : IsWhitTest ψ f) (hf' : IsWhitTest ψ f') :
    IsWhitTest (m := m) ψ fun g => f g - f' g := by
  unfold IsWhitTest at hf hf' ⊢
  obtain ⟨h1, h2, C, hC, h3⟩ := hf
  obtain ⟨h1', h2', C', hC', h3'⟩ := hf'
  refine ⟨?_, h2.sub h2', C ∪ C', hC.union hC', ?_⟩
  · intro u hu g
    beta_reduce
    rw [h1 u hu g, h1' u hu g, mul_sub]
  · intro g hg
    beta_reduce at hg
    by_cases hfg : f g = 0
    · have hfg' : f' g ≠ 0 := by
        intro h
        apply hg
        rw [hfg, h, sub_zero]
      obtain ⟨u, hu, c, hc, rfl⟩ := h3' g hfg'
      exact ⟨u, hu, c, Set.mem_union_right _ hc, rfl⟩
    · obtain ⟨u, hu, c, hc, rfl⟩ := h3 g hfg
      exact ⟨u, hu, c, Set.mem_union_left _ hc, rfl⟩

end DiscreteGroups.sglob.LConv

end UpperTheory.Reformulated.B.P6.BlockTriangularLevi
