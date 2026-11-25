module

import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.PointsIntegralSmallLimit
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import Mathlib.Topology.OpenPartialHomeomorph.Composition
import Std.Tactic.BVDecide.Normalize.Prop
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_unif

section Gen

variable {e e' : ℕ} {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_inv [CompactSpace Y] [T2Space X] (A : FinHolAtlas e X) (B : FinHolAtlas e Y) (π : Y → X)
    (hπ : HoloMap B A π) (hd : IsDegreeOff A B π 1 ∅) (hb : Function.Bijective π) :
    ∃ σ : X → Y, (∀ x, π (σ x) = x) ∧ (∀ y, σ (π y) = y) ∧ HoloMap A B σ ∧
      ∀ x k j, x ∈ (A.chart k).source → σ x ∈ (B.chart j).source →
        Function.Injective (fderiv ℂ (B.chart j ∘ σ ∘ (A.chart k).symm) (A.chart k x)) := by
  obtain ⟨hπc, hπa⟩ := hπ
  obtain ⟨-, -, -, -, -, hdd⟩ := hd
  let Φ : Y ≃ₜ X := (show Continuous (Equiv.ofBijective π hb) from hπc).homeoOfEquivCompactToT2
  let Ψ : Fin A.n → Fin B.n → OpenPartialHomeomorph (Fin e → ℂ) (Fin e → ℂ) :=
    fun i j => (B.chart j).symm.trans (Φ.toOpenPartialHomeomorph.trans (A.chart i))
  have key : ∀ i j z, z ∈ (Ψ i j).target →
      AnalyticAt ℂ (Ψ i j).symm z ∧ Function.Injective (fderiv ℂ (Ψ i j).symm z) := by
    intro i j z hz
    have hw : (Ψ i j).symm z ∈ (Ψ i j).source := (Ψ i j).map_target hz
    have han : AnalyticAt ℂ (Ψ i j) ((Ψ i j).symm z) := hπa j i _ ⟨hw.1, hw.2.2⟩
    have hdet : LinearMap.det (fderiv ℂ (Ψ i j) ((Ψ i j).symm z) : (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 :=
      hdd j i _ hw.1 (by simp) hw.2.2
    let L : (Fin e → ℂ) ≃L[ℂ] (Fin e → ℂ) :=
      (LinearMap.equivOfDetNeZero _ hdet).toContinuousLinearEquiv
    have hL : fderiv ℂ (Ψ i j) ((Ψ i j).symm z) = (L : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) :=
      ContinuousLinearMap.ext fun v => rfl
    have hsymm : AnalyticAt ℂ (Ψ i j).symm z := (Ψ i j).analyticAt_symm hz han hL
    have hder : HasFDerivAt (Ψ i j).symm (L.symm : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ)) z :=
      (Ψ i j).hasFDerivAt_symm hz (hL ▸ han.differentiableAt.hasFDerivAt)
    refine ⟨hsymm, ?_⟩
    rw [hder.fderiv]
    exact L.symm.injective
  refine ⟨⇑Φ.symm, fun x => Φ.apply_symm_apply x, fun y => Φ.symm_apply_apply y,
    ⟨Φ.symm.continuous, ?_⟩, ?_⟩
  · intro i j z hz
    exact (key i j z ⟨⟨hz.1, Set.mem_univ _⟩, hz.2⟩).1
  · intro x k j hxk hxj
    have hz : A.chart k x ∈ (Ψ k j).target := by
      refine ⟨⟨(A.chart k).map_source hxk, Set.mem_univ _⟩, ?_⟩
      show Φ.symm ((A.chart k).symm (A.chart k x)) ∈ (B.chart j).source
      rw [(A.chart k).left_inv hxk]
      exact hxj
    exact (key k j _ hz).2

theorem holoOn_comp {A : FinHolAtlas e X} {B : FinHolAtlas e' Y} {h : Y → X} (hh : HoloMap B A h) {W : Set X}
    {f : X → ℂ} (hf : A.HoloOn W f) : B.HoloOn (h ⁻¹' W) (fun y => f (h y)) := by
  apply PositivityTheory.Xgn.SmallPotentialLimit.holoOn_comp <;> assumption

theorem holoOn_mono {A : FinHolAtlas e X} {W W' : Set X} {f : X → ℂ} (h : A.HoloOn W f) (s : W' ⊆ W) :
    A.HoloOn W' f := by
  intro j
  exact (h j).mono (fun z hz => ⟨hz.1, s hz.2⟩)

theorem holoOn_at {A : FinHolAtlas e X} {W : Set X} {f : X → ℂ} (h : A.HoloOn W f) {x : X} (hx : x ∈ W) {k : Fin A.n}
    (hk : x ∈ (A.chart k).source) : AnalyticAt ℂ (fun w => f ((A.chart k).symm w)) (A.chart k x) := by
  have := h k (A.chart k x) ⟨(A.chart k).map_source hk, by
    show (A.chart k).symm (A.chart k x) ∈ W
    rw [(A.chart k).left_inv hk]
    exact hx⟩
  exact this

theorem exists_holoOn_of_germ (A : FinHolAtlas e X) {x : X} {k : Fin A.n} (hk : x ∈ (A.chart k).source)
    {f : X → ℝ} {H : (Fin e → ℂ) → ℂ} (hH : AnalyticAt ℂ H (A.chart k x))
    (hf : ∀ᶠ w in 𝓝 (A.chart k x), f ((A.chart k).symm w) = (H w).re) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ ∃ G : X → ℂ, A.HoloOn V G ∧ ∀ y ∈ V, f y = (G y).re := by
  have hev : ∀ᶠ w in 𝓝 (A.chart k x), AnalyticAt ℂ H w ∧ f ((A.chart k).symm w) = (H w).re :=
    hH.eventually_analyticAt.and hf
  obtain ⟨U, hU, hUo, hxU⟩ := eventually_nhds_iff.mp hev
  refine ⟨(A.chart k).source ∩ (A.chart k) ⁻¹' U, (A.chart k).isOpen_inter_preimage hUo, ⟨hk, hxU⟩,
    fun y => H (A.chart k y), ?_, ?_⟩
  · intro j z hz
    obtain ⟨hzt, hzs, hzU⟩ := hz
    have hin : AnalyticAt ℂ ((A.chart k) ∘ (A.chart j).symm) z := A.holo j k z ⟨hzt, hzs⟩
    have hout : AnalyticAt ℂ H (((A.chart k) ∘ (A.chart j).symm) z) := (hU _ hzU).1
    exact hout.comp hin
  · rintro y ⟨hy, hyU⟩
    have := (hU _ hyU).2
    rwa [(A.chart k).left_inv hy] at this

theorem isOpen_ne {A : FinHolAtlas e X} {W : Set X} (hW : IsOpen W) {T : Type} [Finite T] {f : T → X → ℂ}
    (hf : ∀ t, A.HoloOn W (f t)) : IsOpen {y | y ∈ W ∧ ∀ t, f t y ≠ 0} := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyW, hy⟩
  obtain ⟨k, hk⟩ := A.cover y
  have hcont : ∀ t, ContinuousAt (f t) y := by
    intro t
    have han : AnalyticAt ℂ (f t ∘ (A.chart k).symm) (A.chart k y) :=
      hf t k (A.chart k y) ⟨(A.chart k).map_source hk, by
        show (A.chart k).symm (A.chart k y) ∈ W
        rw [(A.chart k).left_inv hk]
        exact hyW⟩
    exact ((A.chart k).symm.continuousAt_iff_continuousAt_comp_right hk).2 han.continuousAt
  have hev : ∀ᶠ z in 𝓝 y, ∀ t, f t z ≠ 0 := by
    rw [Filter.eventually_all]
    intro t
    exact (hcont t).eventually_ne (hy t)
  filter_upwards [hW.mem_nhds hyW, hev] with z hz1 hz2
  exact ⟨hz1, hz2⟩

end Gen

section Mat

variable {N j : ℕ}

theorem lower_left_zero {H X D : Matrix (Fin N) (Fin N) ℂ} (hH : IsBlockDiag j H) (hd : H.det ≠ 0)
    (hD : IsBlockDiag j D) (ht : (H⁻¹ * (X * H + D)).BlockTriangular id) (a b : Fin N) (ha : N - j ≤ (a : ℕ))
    (hb : (b : ℕ) < N - j) : X a b = 0 := by
  classical
  have hunit : IsUnit H.det := isUnit_iff_ne_zero.mpr hd
  let _ : Invertible H := Matrix.invertibleOfIsUnitDet _ hunit
  let block (i : Fin N) : Bool := decide (N - j ≤ (i : ℕ))
  have cross {r s : Fin N} (h : block s < block r) :
      ¬ (r : ℕ) < N - j ∧ (s : ℕ) < N - j := by
    exact ⟨not_lt_of_ge (of_decide_eq_true (Bool.lt_iff.mp h).2),
      lt_of_not_ge (of_decide_eq_false (Bool.lt_iff.mp h).1)⟩
  have triangular {M : Matrix (Fin N) (Fin N) ℂ} (hM : IsBlockDiag j M) :
      M.BlockTriangular block := by
    intro r s hrs
    exact hM r s fun h => (cross hrs).1 (h.mpr (cross hrs).2)
  have ht' : (H⁻¹ * (X * H + D)).BlockTriangular block := by
    intro r s hrs
    obtain ⟨hr, hs⟩ := cross hrs
    exact ht (show s < r from hs.trans_le (le_of_not_gt hr))
  have hsum := (triangular hH).mul ht'
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.one_mul] at hsum
  have hX := ((triangular hD).add_iff_left.mp hsum).mul
    (Matrix.blockTriangular_inv_of_blockTriangular (triangular hH))
  rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit, Matrix.mul_one] at hX
  exact hX (Bool.lt_iff.mpr ⟨decide_eq_false hb.not_ge, decide_eq_true ha⟩)

theorem eq_zero_of_lower {L D : Matrix (Fin N) (Fin N) ℂ} (hL : IsLowerUni L) (hD : ∀ a b, a ≤ b → D a b = 0)
    (ht : (L⁻¹ * D).BlockTriangular id) : D = 0 := by
  classical
  obtain ⟨hL1, hL2⟩ := hL
  have hlow : L.BlockTriangular OrderDual.toDual :=
    fun i j hij => hL2 i j (OrderDual.toDual_lt_toDual.mp hij)
  have hunit : IsUnit L.det := by
    rw [Matrix.det_of_isLowerTriangular L hlow]
    simp [hL1]
  letI : Invertible L := Matrix.invertibleOfIsUnitDet _ hunit
  have hlow' : L⁻¹.BlockTriangular OrderDual.toDual :=
    Matrix.blockTriangular_inv_of_blockTriangular hlow
  have hM : L⁻¹ * D = 0 := by
    ext a b
    rw [Matrix.zero_apply]
    rcases lt_or_ge b a with hba | hab
    · exact ht hba
    · rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero (fun c _ => ?_)
      rcases lt_or_ge a c with hac | hca
      · rw [hlow' (OrderDual.toDual_lt_toDual.mpr hac), zero_mul]
      · rw [hD c b (hca.trans hab), mul_zero]
  have h2 := congrArg (fun M => L * M) hM
  simpa [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hunit] using h2

theorem fderiv_mul_of {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {P Q : E → Matrix (Fin N) (Fin N) ℂ}
    {w : E} (hP : ∀ a b, DifferentiableAt ℂ (fun u => P u a b) w) (hQ : ∀ a b, DifferentiableAt ℂ (fun u => Q u a b) w)
    (v : E) : (Matrix.of fun a b => fderiv ℂ (fun u => (P u * Q u) a b) w v) =
      (Matrix.of fun a b => fderiv ℂ (fun u => P u a b) w v) * Q w +
        P w * Matrix.of fun a b => fderiv ℂ (fun u => Q u a b) w v := by
  ext a b
  have h1 : HasFDerivAt (fun u => ∑ c, P u a c * Q u c b)
      (∑ c, (P w a c • fderiv ℂ (fun u => Q u c b) w + Q w c b • fderiv ℂ (fun u => P u a c) w)) w :=
    HasFDerivAt.fun_sum fun c _ => (hP a c).hasFDerivAt.fun_mul (hQ c b).hasFDerivAt
  simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.add_apply]
  rw [h1.fderiv, ← Finset.sum_add_distrib]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

end Mat

end PositivityTheory.Xgp.c_unif
