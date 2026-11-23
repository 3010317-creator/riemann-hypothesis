module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AbelianVarietyAutomorphismShiftsJacobianOrder
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsModelMapDefinedWeakNeronFamily
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueModelHasJacobianOrder
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsVectorFieldFrameSmoothCommGrpScheme
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.JacobianOrderMonotoneSemistableModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelMapGenericallyOpenImmersionCalculus
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ProdIrrAndWeakNeron
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.VectorFieldOrderAddOfProdStrictHenselian
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem Model.twist_twist_symm {R K : Type} [CommRing R] [Field K] [Algebra R K] {A A' : Over (Sp K)}
    (M : Model R A) (f : A ≅ A') : (M.twist f).twist f.symm = M := by
  obtain ⟨Y, e, h₁, h₂, h₃⟩ := M
  simp [Model.twist]

theorem isIntegral_of_abelian {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A) :
    IsIntegral A.left := by
  have := hA.smooth
  have := hA.geomConnected
  exact GlobalTheory.isIntegral_of_smooth_of_geometricallyConnected A.hom

theorem exists_genIso_of_max_ord (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    (hSH : SH R K) (π : R) (hπ : Irreducible π) (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (I : Type) [Fintype I] [DecidableEq I] (D : I → VF A) (hD : IsFrame D)
    (J : Type) (M : J → Model R A) (hI : ∀ j, (M j).Irr) (hW : WeakNeron M) (o : J → ℤ)
    (ho : ∀ j, HasOrd (M j) D π (o j)) (ρ : ℤ) (hρ : ∀ j, o j ≤ ρ) (f : A ≅ A) (i : J) (hi : o i = ρ) :
    ∃ i', o i' = ρ ∧ GenIso (M i) (M i') f.hom := by
  have hint := isIntegral_of_abelian A hA
  obtain ⟨-, -, h3, -⟩ := _root_.GlobalTheory.SS.GI.genIso_calculus R K hSH
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  have bound : ∀ (N : Model R A) (m : ℤ), N.Irr → HasOrd N D π m →
      m ≤ ρ ∧ (m = ρ → ∃ i', o i' = ρ ∧ GenIso N (M i') (𝟙 A)) := by
    intro N m hN hm
    obtain ⟨j, hj⟩ := _root_.GlobalTheory.SS.exists_defAt_of_weakNeron R K A J M hW N hN
    obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.SS.OrdMono.ord_mono R K π hπ A I D hD N (M j) m (o j) hN (hI j) hm (ho j) hj
    have := hρ j
    exact ⟨h₁.trans this, fun e => ⟨j, by omega, h₂ (by omega)⟩⟩
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.SS.OrdTwist.main R K π hπ A hA I D hD f
  obtain ⟨c', hc'⟩ := _root_.GlobalTheory.SS.OrdTwist.main R K π hπ A hA I D hD f.symm
  have t₁ := hc _ _ (ho i)
  have t₂ := hc' _ _ (ho i)
  have t₃ := hc' _ _ t₁
  rw [Model.twist_twist_symm] at t₃
  have e₃ := (_root_.GlobalTheory.SS.Ord.existsUnique_hasOrd R K π hπ A I D hD (M i) (hI i)).unique t₃ (ho i)
  have i₁ : ((M i).twist f).Irr := hI i
  have i₂ : ((M i).twist f.symm).Irr := hI i
  obtain ⟨b₁, b₁'⟩ := bound _ _ i₁ t₁
  obtain ⟨b₂, -⟩ := bound _ _ i₂ t₂
  obtain ⟨i', hi', hg⟩ := b₁' (by omega)
  exact ⟨i', hi', (h3 A A (M i) (M i') f).2.1.2 hg⟩

theorem WeakNeron.nonempty {R K : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K]
    (hSH : SH R K) {A : Over (Sp K)} [GrpObj A] {J : Type} {M : J → Model R A} (hW : WeakNeron M) :
    Nonempty J := by
  obtain ⟨hdvr, -, -, hfr⟩ := hSH
  obtain ⟨i, -⟩ := hW R K (by simp) (η[A]).left (by
    rw [← Category.assoc, Over.w]
    simp)
  exact ⟨i⟩

theorem exists_permuted_members : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ S : Finset (Fin n), S.Nonempty ∧ (∀ (f : A ≅ A), ∀ i ∈ S, ∃ i' ∈ S, GenIso (M i) (M i') f.hom) ∧ ∀ (Θ : A ⊗ A ≅ A ⊗ A), ∀ i ∈ S, ∀ j ∈ S, ∃ i' ∈ S, ∃ j' ∈ S, GenIso ((M i).prod (M j)) ((M i').prod (M j')) Θ.hom := by
  intro R K _ _ _ _ _ hSH A _ _ hA n M hI hW
  have hne := hW.nonempty hSH
  have hdvr := hSH.1
  have hfr := hSH.2.2.2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim K A hA
  obtain ⟨D, hD⟩ := _root_.GlobalTheory.SS.exists_isFrame K A g hg
  choose o ho using fun i => (_root_.GlobalTheory.SS.Ord.existsUnique_hasOrd R K π hπ A (Fin g) D hD (M i) (hI i)).exists
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max o
  refine ⟨Finset.univ.filter fun i => o i = o i₀, ⟨i₀, by simp⟩, ?_, ?_⟩
  · intro f i hi
    obtain ⟨i', hi', h⟩ := exists_genIso_of_max_ord R K hSH π hπ A hA _ D hD _ M hI hW o ho (o i₀) hi₀ f i
      (by simpa using hi)
    exact ⟨i', by simpa using hi', h⟩
  · intro Θ i hi j hj
    have hi : o i = o i₀ := by simpa using hi
    have hj : o j = o i₀ := by simpa using hj
    obtain ⟨D₂, hD₂, hp⟩ := _root_.GlobalTheory.SS.OrdProd.ord_prod R K hSH π hπ A A _ _ D D hD hD
    obtain ⟨p₁, p₂⟩ := _root_.GlobalTheory.SS.prod_irr_and_weakNeron R K hSH A A
    obtain ⟨⟨i', j'⟩, h', h⟩ := exists_genIso_of_max_ord R K hSH π hπ (A ⊗ A)
      (AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA) _ D₂ hD₂ (Fin n × Fin n)
      (fun p => (M p.1).prod (M p.2)) (fun p => p₁ _ _ (hI _) (hI _)) (p₂ _ _ M M hW hW)
      (fun p => o p.1 + o p.2) (fun p => hp _ _ _ _ (hI _) (hI _) (ho _) (ho _)) (o i₀ + o i₀)
      (fun p => add_le_add (hi₀ _) (hi₀ _)) Θ (i, j) (by simp [hi, hj])
    have a₁ := hi₀ i'
    have a₂ := hi₀ j'
    have h' : o i' + o j' = o i₀ + o i₀ := h'
    exact ⟨i', by simp; omega, j', by simp; omega, h⟩

end GlobalTheory.SS
