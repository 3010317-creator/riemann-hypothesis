module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.AdmCpt
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
import Mathlib.Tactic.Basify
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
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory.PureFinite

open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport GlobalTheory.GaugeEx Set

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {d : ℕ} (b : Module.Basis (Fin d) F E) {n M : ℕ}

include b in
theorem continuous_projV_fin (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (fun X : Fin n → Fin M → Af F ⊗[F] E => projV v X) := by
  have h : Continuous (evalV F v) :=
    RestrictedProduct.continuous_eval (R := fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F) v
  haveI : IsTopologicalRing (Af F) := inferInstance
  have h2 : Continuous (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)) :=
    continuous_map_tens b (evalV F v) h
  exact continuous_pi fun a => continuous_pi fun i =>
    h2.comp ((continuous_apply i).comp (continuous_apply a))

theorem projV_add (v : HeightOneSpectrum (𝓞 F)) (X Y : Fin n → Fin M → Af F ⊗[F] E) :
    projV v (X + Y) = projV v X + projV v Y := by
  funext a i
  simp [projV, map_add (f := _)]

theorem latV_add (v : HeightOneSpectrum (𝓞 F)) {Y Z : Fin n → Fin M → Fv F v ⊗[F] E}
    (hY : Y ∈ latV b v) (hZ : Z ∈ latV b v) : Y + Z ∈ latV b v := by
  intro a i k
  simpa only [Pi.add_apply, map_add (f := _), Finsupp.add_apply] using add_mem (hY a i k) (hZ a i k)

variable (Φv : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ)

theorem hasCompactSupport_finprod (hSB : ∀ v, IsSB (Φv v))
    (hae : ∀ᶠ v in Filter.cofinite, Φv v = (latV b v).indicator 1) :
    HasCompactSupport (fun X : Fin n → Fin M → Af F ⊗[F] E => ∏ᶠ v, Φv v (projV v X)) := by
  classical
  let D : Fin n → Fin M → Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) :=
    fun i j k v =>
      ((fun Z : Fin n → Fin M → Fv F v ⊗[F] E => crd b (Fv F v) (Z i j) k) '' tsupport (Φv v)) ∪
        (v.adicCompletionIntegers F : Set (Fv F v))
  have hD : ∀ i j k v, IsCompact (D i j k v) := fun i j k v =>
    ((hSB v).2.isCompact.image ((continuous_crd b (Fv F v) k).comp
      ((continuous_apply j).comp (continuous_apply i)))).union
      (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
  have hDe : ∀ i j k, ∀ᶠ v in Filter.cofinite,
      D i j k v = (v.adicCompletionIntegers F : Set (Fv F v)) := by
    intro i j k
    filter_upwards [hae] with v hv
    refine Set.union_eq_right.2 ?_
    rintro _ ⟨Z, hZ, rfl⟩
    have hsub : tsupport (Φv v) ⊆ latV b v := by
      rw [hv]
      exact closure_minimal Set.support_indicator_subset (isClopen_latV b v n M).isClosed
    exact hsub hZ i j k
  let Bf : Fin n → Fin M → Fin d → Set (Af F) := fun i j k => {x | ∀ v, x v ∈ D i j k v}
  have hBf : ∀ i j k, IsCompact (Bf i j k) := fun i j k => isCompact_finBox (hD i j k) (hDe i j k)
  let Box : Set (Fin n → Fin M → Fin d → Af F) :=
    Set.pi univ fun i => Set.pi univ fun j => Set.pi univ fun k => Bf i j k
  have hbox : IsCompact Box := isCompact_univ_pi fun i => isCompact_univ_pi fun j =>
    isCompact_univ_pi fun k => hBf i j k
  let L : (Fin n → Fin M → Fin d → Af F) → (Fin n → Fin M → Af F ⊗[F] E) :=
    fun c x i => ∑ k, c x i k • ((1 : Af F) ⊗ₜ[F] b k)
  have hL : Continuous L := by
    refine continuous_pi fun x => continuous_pi fun i => continuous_finsetSum _ fun k _ => ?_
    exact continuous_smul.comp
      (((continuous_apply k).comp ((continuous_apply i).comp (continuous_apply x))).prodMk
        continuous_const)
  refine HasCompactSupport.intro (hbox.image hL) fun X hX => ?_
  by_contra h
  apply hX
  have hv := factor_ne_zero b Φv hae X h
  refine ⟨fun i j k => crd b (Af F) (X i j) k, ?_, ?_⟩
  · simp only [Box, Set.mem_pi, Set.mem_univ, true_implies]
    exact fun i j k v => Or.inl ⟨projV v X, subset_tsupport _ (hv v), crd_projV b X v i j k⟩
  · funext i j
    exact (eq_sum_crd b (Af F) (X i j)).symm

end GlobalTheory.PureFinite

namespace GlobalTheory

end GlobalTheory
