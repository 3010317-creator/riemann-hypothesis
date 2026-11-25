module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsTopNMixed
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsMuRegSmooth
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombExpand
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PTopNPoly
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PVertFactorPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB

@[expose] public section

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem TopNMixedExpand.proof (hIso : HilbertSamuel.IsomInvariance.Statement) (hS : MuRegSmooth.Statement) :
    TopNMixedExpand.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X B p q hII hp hpq
  have hP : IsArithVar (mCoordIdeal D.y) (D.n + 1) := D.arith
  have hA : IsSmoothHerm D.A' := D.A'_pos.1
  filter_upwards [hS II Ψ K ι Ω E D O Lt X B] with t ht
  have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  set Z := HilbertSamuel.HermLine.zcomb (muReg X.H X.S B t) D.A' (q : ℤ) (p : ℤ) with hZdef
  have hZ : IsSmoothHerm Z := HilbertSamuel.ZCombLimit.isSmoothHerm_zcomb_int ht hA _ _
  have hagree : ∀ z ∈ mcPts (mCoordIdeal D.y), Z.h z = (X.NbarQ B p q t).h z := by
    intro z hz
    rw [TopNPoly.NbarQ_h_eq VertFactorPos.proof X B p q t hz]
    show (muReg X.H X.S B t).h z ^ (q : ℤ) * D.A'.h z ^ (p : ℤ) = _
    simp
  have hdeg : Z.a = (X.NbarQ B p q t).a := by
    unfold ComponentSetting.NbarQ
    rw [smoothRep_a]
    show (q : ℤ) • (muReg X.H X.S B t).a + (p : ℤ) • D.A'.a = _
    rw [muReg, smoothRep_a, D.A'_deg]
    rfl
  have hN : IsSmoothHerm (X.NbarQ B p q t) := by
    unfold ComponentSetting.NbarQ
    refine TopNPoly.smoothRep_smooth_of (Z := Z) ?_ hZ fun z hz => ?_
    · rw [hdeg]; unfold ComponentSetting.NbarQ; rw [smoothRep_a]
    · rw [hagree z hz]; unfold ComponentSetting.NbarQ; rw [smoothRep_h _ hz]
  have hne : (1 : MRing ι) ∉ mCoordIdeal D.y := fun h =>
    hP.2.1.1.ne_top ((Ideal.eq_top_iff_one _).2 h)
  have hiso : ∀ j : Fin (D.n + 1), HilbertSamuel.IsIsometricOn (mCoordIdeal D.y)
      ((fun _ => X.NbarQ B p q t) j) ((fun _ => Z) j) := fun _ =>
    ⟨1, 1, 0, 0, by simpa using isMultiHomog_C_zero (ι := ι) 1, by simpa using isMultiHomog_C_zero (ι := ι) 1,
      hne, hne, fun k => by simp [hdeg], rfl, fun z hz => by simp [hagree z hz]⟩
  have hI := hIso K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B p q t) (fun _ => Z) hP
    (fun _ => hN) (fun _ => hZ) hiso
  have hE := (HilbertSamuel.ZCombExpand.proof K ι (II K ι) (hII K ι) (mCoordIdeal D.y) (D.n + 1)
    (muReg X.H X.S B t) D.A' q p hP ht hA).1
  show II K ι (mCoordIdeal D.y) (D.n + 1) (fun _ => X.NbarQ B p q t) / (q : ℝ) ^ (D.n + 1) = _
  rw [hI, hE, Finset.sum_div, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ D.n + 1 := by have := Finset.mem_range.1 hk; omega
  have hi : D.n + 1 + 1 - 1 - k = D.n + 1 - k := by omega
  rw [hi, Nat.sub_sub_self hk', Nat.choose_symm hk']
  unfold ComponentSetting.mixN
  have hpow : (q : ℝ) ^ (D.n + 1) = (q : ℝ) ^ k * (q : ℝ) ^ (D.n + 1 - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk']
  rw [div_pow, hpow]
  field_simp

end GroundTheory.Heights₂.Heights.LowerBoundFree
