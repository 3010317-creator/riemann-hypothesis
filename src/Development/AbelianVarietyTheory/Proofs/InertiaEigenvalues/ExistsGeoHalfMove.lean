module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
public import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftSubTranslate
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbeddingStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreConstantsBaseSolutionEquivariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfRealisationGeometricAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointIntertwines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOneOfSerOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenReadsOfUnitAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel
import Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRangeObj, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramePinSmul, Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeoHalfMove

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRangeObj =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRangeObj", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRange\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRangeObj =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramePinSmul =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramePinSmul", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ShiftSubTranslate\npublic import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointIntertwines\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCcIsEquivAtSerOfOneMapRowOfFive\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOneOfSerOf\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PureTensorOSmul\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenReadsOfUnitAt\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultValueLeftContLevel\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSpanAndGoodRangeObj\nimport Formalism.LocalToGlobal.ProjectiveLattices.SpMapAlgHomId\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.Unframe

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Lev ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeSup GlobalTheory.RealGeo

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Shift

variable {C : Formalism.L2.Pj.Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}
  (O : OMDat C R i Unit (fun _ => A.μ0)) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (C.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}
  {cE c0 : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ}



theorem phi_smul (s : ℂ) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (f : C.R ((i : ℕ) + 1)) (h : GA D (Wc D i)) :
    O.phi (s • cc) f h = s * O.phi cc f h := by
  rw [phi_apply, phi_apply, Pi.smul_apply, smul_eq_mul]
  ring



theorem oneMapOf_smul {ph ze : ℂ} (h : O.OneMapOf κ v₀ c0 ph) (hL : ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange)
    {m : ℕ} (hm : 0 < m) (hze : ze ^ m = 1) : O.OneMapOf κ v₀ (ze⁻¹ • c0) ph := by
  have hn : ‖ze‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hze hm.ne'
  have h0 : ze ≠ 0 := fun e => by simp [e] at hn
  obtain ⟨hE, ⟨h1, h2, h3, h4, h5, z, hz, h6⟩, h7⟩ := h
  refine ⟨fun g k hk f hf => ⟨(hE g k hk f hf).1, fun x => ?_⟩, ⟨h1, h2, h3, fun k => ?_, h5, z, hz, fun t => ?_⟩, fun x => ?_⟩
  · rw [phi_smul, phi_smul, (hE g k hk f hf).2 x, mul_left_comm]
  · have := h4 k
    show ‖ze⁻¹ * c0 k‖ = 1
    rw [norm_mul, norm_inv, hn, inv_one, one_mul]
    exact this
  · obtain ⟨y, hy, ⟨n, hn0, hyn⟩, h8⟩ := h6 t
    refine ⟨y * ze, mul_mem hy hL, ⟨n * m, Nat.mul_pos hn0 hm, ?_⟩, fun x hx => ⟨(h8 x hx).1, fun f hf hc q => ?_⟩⟩
    · rw [mul_pow, pow_mul, hyn, one_pow, mul_comm n, pow_mul, hze, one_pow, one_mul]
    · refine ((h8 x hx).2 f hf hc q).trans ?_
      have e : ∀ a : ℂ, y * a = y * ze * (ze⁻¹ * a) := fun a => by field_simp
      exact congrArg (fun u => u * _ * _) (e _)
  · obtain ⟨n, a, f, hf⟩ := h7 x
    obtain ⟨y, hy⟩ := hL
    have hy' : D.what₂.embLL y = ze := hy
    refine ⟨n, fun k => a k * y, f, fun g => (hf g).trans (Finset.sum_congr rfl fun k _ => ?_)⟩
    rw [phi_smul, map_mul, hy']
    field_simp

end Shift

section Frame

variable {T : CoreJ D} [iA : Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}

omit iA in
theorem lawsJ_setCE (hL : LawsJ T) {c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ}
    (h : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CUnit (c' j σ)) : LawsJ (setCE T c') :=
  ⟨hL.toLawsM, h, hL.muVal, hL.muConj, hL.intAll, hL.modelW, hL.familyUniformisationBasePointOrthogonal, hL.kfHalf, hL.adPin⟩



theorem framePin_smul {c' c'' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ} {i : Fin D.R.m} {σ : T.Q.c.F →+* ℂ}
    {hV : T.V ((i : ℕ) + 1) σ = Wc D i} {s : ℂ} (hs : ‖s‖ = 1) (e : c'' ((i : ℕ) + 1) σ = s • c' ((i : ℕ) + 1) σ)
    (h : @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c') iA R i σ hV) :
    @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c'') iA R i σ hV := by
  have h0 : s ≠ 0 := fun e => by simp [e] at hs
  obtain ⟨ph, b, h1, h2, h3⟩ := h
  refine ⟨ph / s, b, by rw [norm_div, h1, hs, div_one], h2, fun g γ hγ hf hx Wt Y X z hz => ?_⟩
  refine (h3 g γ hγ hf hx Wt Y X z hz).trans ?_
  have e1 : ∀ k (a : ℂ), ph * (c' ((i : ℕ) + 1) σ k * a) = ph / s * (c'' ((i : ℕ) + 1) σ k * a) := fun k a => by
    rw [e, Pi.smul_apply, smul_eq_mul]
    field_simp
  exact congrArg (· * _) (e1 _ _)



theorem exists_shift (hP : GlobalTheory.Published.CuspRapidDecay) (hsz : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) {F : Face D A} (hC : GlobalTheory.Core5 R F)
    (B : GeoHalf T R fun _ => 1) (hU : R.LUnif) (hJ : JEvExists T R B.κ B.v₀) (i : Fin D.R.m) :
    ∃ (c1 : (T.U ((i : ℕ) + 1) T.σ₀).Comp → ℂ) (z : G), z ∈ Subgroup.center G ∧
      (B.O i).OneMapOf (B.κ i) (B.v₀ i (sg0 D A)) c1 1 ∧
      (∀ c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ, c' ((i : ℕ) + 1) T.σ₀ = c1 → ∀ hV,
        @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c') iA R i T.σ₀ hV) ∧
      ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (B.κ i)) (B.κ i).n, ∀ h,
        (B.O i).phi c1 f h = (B.O i).phi (T.cE ((i : ℕ) + 1) (B.O i).s0) (actLev T.Q.c (B.O i).lev2 z f) h := by
  obtain ⟨κ, v₀, fw, bar, O, pins, rho, eqa, ct, phase⟩ := B
  dsimp only at hJ ⊢
  have ht : TieIn T R κ v₀ := ⟨fw.laws, fw.alg_eq, fw.kap, fw.hv₀, fw.chiR, fw.x0⟩
  have hio : IoExt R := GlobalTheory.IoExtremal.ioExt D G Pl0 T0 A _ R hC.lev hC.fam hC.models hC.thP
  obtain ⟨cc, hcc, u, hu, hE0, hS, -⟩ := GlobalTheory.AdTh.exists_ccIs_equivAt_serOf_oneMapRow_ofFive GlobalTheory.ChartFree.chartIndep
    D G Pl0 T0 A T R F κ v₀ hC ht hio i _ _ (O i) (pins i).2
  have h1 : (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (u • cc) 1 :=
    GlobalTheory.OneMapPhaseOne.oneMapOf_one_of_serOf D G Pl0 T0 A T R F κ v₀ hC.grp hC.thP ht O i (pins i) (u • cc) hS
      (GlobalTheory.ClassSumRule.exists_cusp_isThClsD_ofFive GlobalTheory.ChartFree.chartIndep D G Pl0 T0 A T R F κ v₀ hC ht i _ _ (O i) (pins i).2 ())
      hE0
  have hrow := phase i hU ⟨_, _, h1⟩
  have hσ : res T (sg0 D A) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T fw.alg_eq fw.laws.pins.2.2.1]
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := (O i).hV
  have hg := base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1
  have hV₁ : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i := fw.laws.spaceW _ (inR i) _ hg
  have hev : ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n, ∃ y : (R.HW i (sg0 D A)).H,
      (R.HW i (sg0 D A)).e y (v₀ i (sg0 D A)) = phiC T hV (wtA (κ i)) f := fun f hf =>
    ⟨_, (baseEmbedding_reading_eval_adelicFunction fw hV₁ (hJ i _ hg hV₁) ⟨f, hf⟩).trans (phiC_congr hσ hV₁ hV _ _)⟩
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank _ (Nat.le_add_left _ _) i.2).symm
  have hphi : ∀ f h, phiC T hV (wtA (κ i)) f h =
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) f h :=
    fun f h => phiC_apply hV _ f h
  obtain ⟨z, ze, hz, hzL, ⟨m, hm, hze⟩, ⟨k, hk⟩, hs⟩ := shift_central (O i) (pins i).2 hn hC.models.HV hC.models.jV hC.thP.thF_mem
    (GlobalTheory.AdSpan.spanAt R hP hsz hC.lev hC.fam hC.models hC.thP i A.μ0) hrow hE0 hS fun f hf => by
      obtain ⟨y, hy⟩ := hev f hf
      exact ⟨_, (hC.models.HW i _).2.1.le (LinearMap.mem_range_self _ y), fun h => (congrFun hy h).trans (hphi f h)⟩
  have hzn : ‖ze‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hze hm.ne'
  have h0 : ze ≠ 0 := fun e => by simp [e] at hzn
  refine ⟨ze⁻¹ • u • cc, z, hz, oneMapOf_smul (O i) h1 hzL hm hze, fun c'' hc'' hV' => ?_, fun f hf h => ?_⟩
  · obtain ⟨c', hc', hL'⟩ := exists_withConst fw.laws ((i : ℕ) + 1) T.σ₀ cc hcc.1
    have hx0 : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hσ ▸ fw.x0 i (sg0 D A) hg
    have hpin := @GlobalTheory.FrameConst.framePin_of_ccIs D G _ _ Pl0 T0 A (withConst T c') iA R i T.σ₀ hV rfl hL' hC.models.inf
      (pins i).2.lift.std hx0 (by subst hc'; exact hcc)
    refine framePin_smul (c' := c') (s := ze⁻¹ * u) (by rw [norm_mul, norm_inv, hzn, hu, inv_one, one_mul]) ?_ hpin
    rw [hc'', hc']
    exact funext fun _ => (mul_assoc _ _ _).symm
  · have h2 := hs k hk f hf h
    have h3 := (hrow.1 z k hk f hf).2 h
    rw [← chiC_coe] at h3
    rw [phi_smul, h2, h3]
    field_simp

end Frame

end GlobalTheory.Unframe
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramePinSmul =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeoHalfMove =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeoHalfMove", "h": "module\n\npublic import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints\npublic import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.OfCore\npublic import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivariantUnitConstantsGoodEmbeddingStatement\nimport Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHalfOfBasePins\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramePinSmul\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoreConstantsBaseSolutionEquivariant\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGeometricHalfRealisationGeometricAction\nimport Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.Unframe

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
  Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Lev ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.HeckeSup GlobalTheory.RealGeo

abbrev moveForms {LL Ks WL G : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
    [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] {W : (LL →+* ℂ) → Type}
    [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G]
    (B : Arith.FormsL LL Ks WL W G) (w : (LL →+* ℂ) → G) : Arith.FormsL LL Ks WL W G :=
  { B with j := fun σ => (B.j σ).comp (B.ρ (w σ)) }

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

abbrev moveR {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G) : RealDat D A Ks :=
  updFW R R.nW fun i => moveForms (R.FW i) (w i)

variable {T : CoreJ D} [iA : Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}


open Classical in
variable (T) in
def overEmb (w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ) : G :=
  if GoodEmb T.Q.c (res T σ) then w i (res T σ) else w i (resC T σ)

section Half

variable (B : GeoHalf T R fun _ => 1) (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ)
  (w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G)

def Moves : Prop :=
  ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∀ f ∈ T.cuspA ((i : ℕ) + 1) (wtA (B.κ i)) (B.κ i).n,
      phiC (setCE T c') hV (wtA (B.κ i)) f = phiC T hV (wtA (B.κ i)) (actLev T.Q.c (B.O i).lev2 (w i σ) f)

variable {B c' w}

theorem rho_e (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (i : Fin D.R.m) (g : G) (f : Cu T B.κ i) :
    (R.FW i).ρ g ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) =
      (B.fw.e i ⟨actLev T.Q.c (B.O i).lev2 g f, hK i g f f.2⟩ : (R.FW i).WK) :=
  (((B.rhoGeo i).1 (hK i) g f).choose_spec).symm


theorem ev_move (hJ : JEvExists T R B.κ B.v₀) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (f : Cu T B.κ i) :
    (R.HW i σ).e ((R.FW i).j σ ((R.FW i).ρ (overEmb T w i σ) ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL)))
      (B.v₀ i σ) = phiC (setCE T c') hV (wtA (B.κ i)) (f : T.R ((i : ℕ) + 1)) := by
  rw [overEmb, ite_eq_left hσ, rho_e hK, hM i _ hσ hV f f.2]
  exact B.fw.evaluates hJ i σ hσ hV ⟨_, hK i _ f f.2⟩


theorem bar_move (hJ : JEvBar T R B.κ) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) (i : Fin D.R.m)
    (σ : D.what₂.LL →+* ℂ) (hσ : ¬ GoodEmb T.Q.c (res T σ)) (hV : T.V ((i : ℕ) + 1) (resC T σ) = Wc D i) :
    ∃ v : (R.MW i σ).Vec, IsUnitV v ∧ ∀ f : Cu T B.κ i,
      (R.HW i σ).e ((R.FW i).j σ ((R.FW i).ρ (overEmb T w i σ) ((B.fw.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL))) v =
        fun g => starRingEnd ℂ (phiC (setCE T c') hV (wtA (B.κ i)) (f : T.R ((i : ℕ) + 1)) g) := by
  obtain ⟨v, hv, h⟩ := (B.bar i σ hσ hV).1 (hJ i σ hσ hV)
  refine ⟨v, hv, fun f => ?_⟩
  rw [overEmb, ite_eq_right hσ, rho_e hK, hM i _ (good_resC T hσ) hV f f.2]
  exact h ⟨_, hK i _ f f.2⟩



def tieMove (hL : LawsJ (setCE T c')) (hJ : JEvExists T R B.κ B.v₀) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w) :
    @FWTie D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) B.κ B.v₀ :=
  @FWTie.mk D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) B.κ B.v₀ B.fw.alg_eq B.fw.e B.fw.ks B.fw.kap B.fw.pt
    B.fw.nrm_eq hL B.fw.chiR B.fw.hv₀ B.fw.x0
    (fun i σ hσ hV h => absurd ⟨((R.FW i).j σ).comp ((R.FW i).ρ (overEmb T w i σ)), ev_move hJ hK hM i σ hσ hV⟩ h)
    (fun i σ hσ hV _ => ev_move hJ hK hM i σ hσ hV)



theorem exists_geoHalf_move (hL : LawsJ (setCE T c')) (hI : InGeo B) (hK : ∀ i, ActKeeps (κ := B.κ) B.O i) (hM : Moves B c' w)
    (hF : @Fired D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ B.O fun _ => 1) :
    ∃ B' : @GeoHalf D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) fun _ => 1,
      @GeoHalf.v₀ D G _ _ Pl0 T0 A (setCE T c') iA _ _ B' = B.v₀ := by
  have hF' := @Half.fired_upd D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ R.nW (fun i => moveForms (R.FW i) (overEmb T w i)) B.O _ hF
  refine ⟨@GeoHalf.mk D G _ _ Pl0 T0 A (setCE T c') iA (moveR R (overEmb T w)) _ B.κ B.v₀ (tieMove hL hI.jEvExists hK hM)
    (fun i σ hσ hV => ?_) (fun i => @Half.updO D G _ _ Pl0 T0 A (setCE T c') iA R _ _ _ _ _ (B.O i))
    (fun i => @Half.omPins_upd D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ _ _ B.O i (B.pins i)) B.rhoGeo
    (fun i σ hσ hV _ => hF'.2 i σ hσ hV) (fun i _ => ⟨1, hF'.1 i⟩) (fun i _ _ => hF'.1 i), rfl⟩
  obtain ⟨v, hv, h⟩ := bar_move hI.jEvBar hK hM i σ hσ hV
  exact ⟨fun _ => ⟨v, hv, h⟩, fun h' => absurd ⟨v, hv, (tieMove hL hI.jEvExists hK hM).jK i σ, h⟩ h'⟩

end Half

omit iA in
theorem phiC_setCE_of_eq {c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ} {j : ℕ} {σ : T.Q.c.F →+* ℂ} {W : HSp D}
    (hV : T.V j σ = W) (e : c' j σ = T.cE j σ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) :
    phiC (setCE T c') hV a f = phiC T hV a f := by
  funext h
  rw [phiC_apply, phiC_apply]
  exact congrArg (fun c => (lieFac (T.Q.Dw j) (xiR D) a : ℂ) * adel W (castDict hV (T.dict j σ))
      (muPin W (castDict hV (T.dict j σ)) (castDict hV (T.mu j σ)) c) (rdU (T.U j σ) f) h) e



theorem exists_framed_half (hP : GlobalTheory.Published.CuspRapidDecay) (hsz : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) {F : Face D A}
    (hC : GlobalTheory.Core5 R F) (B : GeoHalf T R fun _ => 1) (hU : R.LUnif) (hI : InGeo B) :
    ∃ (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ) (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → G),
      (∀ i σ, w i σ ∈ Subgroup.center G) ∧
      (∀ (i : Fin D.R.m) hV, @GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin D G _ _ Pl0 T0 A (setCE T c') iA R i T.σ₀ hV) ∧
      ∃ B' : @GeoHalf D G _ _ Pl0 T0 A (setCE T c') iA (moveR R w) fun _ => 1,
        @GeoHalf.v₀ D G _ _ Pl0 T0 A (setCE T c') iA _ _ B' = B.v₀ := by
  classical
  choose c1 z hz hO hfr hs using exists_shift hP hsz hC B hU hI.jEvExists
  have ht : TieIn T R B.κ B.v₀ := ⟨B.fw.laws, B.fw.alg_eq, B.fw.kap, B.fw.hv₀, B.fw.chiR, B.fw.x0⟩
  have hpb : T.pb = R.C.P.pb :=
    GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore R B.fw.laws.toLawsM hC.lev ((B.pins ⟨0, by have := D.R.two_le_m; omega⟩).2.tuple ()).half
  have hx := _root_.GlobalTheory.EquivConst.exists_equivariant_constants T R B.κ B.v₀ B.O hC.lev ht hpb B.pins
  have H : ∀ (n : ℕ) (σ : T.Q.c.F →+* ℂ), ∃ c : (T.U (n + 1) σ).Comp → ℂ, ∀ hn : n < D.R.m,
      (σ = T.σ₀ → HEq c (c1 ⟨n, hn⟩)) ∧ (σ ≠ T.σ₀ → c = T.cE (n + 1) σ) := by
    intro n σ
    by_cases hσ : σ = T.σ₀
    · subst hσ
      by_cases hn : n < D.R.m
      · exact ⟨c1 ⟨n, hn⟩, fun _ => ⟨fun _ => HEq.rfl, fun h => absurd rfl h⟩⟩
      · exact ⟨fun _ => 1, fun h => absurd h hn⟩
    · exact ⟨T.cE (n + 1) σ, fun _ => ⟨fun h => absurd h hσ, fun _ => rfl⟩⟩
  choose c hc using H
  have h0 : ∀ i : Fin D.R.m, c i T.σ₀ = c1 i := fun i => eq_of_heq ((hc i T.σ₀ i.2).1 rfl)
  have h1 : ∀ (i : Fin D.R.m) σ, σ ≠ T.σ₀ → c i σ = T.cE ((i : ℕ) + 1) σ := fun i σ => (hc i σ i.2).2
  let c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ :=
    fun j => Nat.casesOn (motive := fun j => ∀ σ : T.Q.c.F →+* ℂ, (T.U j σ).Comp → ℂ) j (fun _ _ => 1) c
  let w : Fin D.R.m → (T.Q.c.F →+* ℂ) → G := fun i σ => if σ = T.σ₀ then z i else 1
  have hK : ∀ i, ActKeeps (κ := B.κ) B.O i := fun i g f hf => by
    obtain ⟨k, hk, -⟩ := (B.pins i).2.lift.lev g
    exact ((hO i).1 g k hk f hf).1
  have hL : LawsJ (setCE T c') := lawsJ_setCE B.fw.laws fun j hj σ hσ => by
    cases j with
    | zero => exact fun _ => norm_one
    | succ n =>
      by_cases e : σ = T.σ₀
      · subst e
        have h : CUnit (c1 ⟨n, hj.2⟩) := (hO ⟨n, hj.2⟩).2.1.2.2.2.1
        rw [← h0 ⟨n, hj.2⟩] at h
        exact h
      · have h := B.fw.laws.cUnit _ hj σ hσ
        have e2 : c n σ = T.cE (n + 1) σ := h1 ⟨n, hj.2⟩ σ e
        rw [← e2] at h
        exact h
  have hM : Moves B c' w := fun i σ hσ hV f hf => by
    by_cases e : σ = T.σ₀
    · subst e
      rw [show w i T.σ₀ = z i from ite_eq_left rfl]
      funext h
      rw [phiC_apply, phiC_apply]
      have h2 := hs i f hf h
      rw [← h0 i] at h2
      exact congrArg (_ * ·) h2
    · rw [show w i σ = 1 from ite_eq_right e, phiC_setCE_of_eq hV (h1 i σ e)]
      have h2 := rho_e hK i 1 ⟨f, hf⟩
      rw [map_one] at h2
      have h3 := congrArg Subtype.val ((B.fw.e i).injective (Subtype.ext h2))
      exact congrArg _ h3
  have hF : @Fired D G _ _ Pl0 T0 A (setCE T c') iA R B.κ B.v₀ B.O fun _ => 1 := by
    refine ⟨fun i => ?_, fun i σ hσ hV => ?_⟩
    · have h := hO i
      rw [← h0 i] at h
      exact h
    · by_cases e : σ = T.σ₀
      · subst e
        have h := GlobalTheory.RealGeoConst.eqAt_base T R B.κ B.v₀ hC.lev ht i (B.O i) (c1 i) (hO i).1 hV
        rw [← h0 i] at h
        exact h
      · have h := B.equivAll i σ hσ hV (hx i σ hσ hV)
        rw [← h1 i σ e] at h
        exact h
  refine ⟨c', overEmb T w, fun i σ => ?_, fun i hV => hfr i c' (h0 i) hV, exists_geoHalf_move hL hI hK hM hF⟩
  have key : ∀ s, w i s ∈ Subgroup.center G := fun s => by
    by_cases e : s = T.σ₀
    · rw [show w i s = z i from ite_eq_left e]
      exact hz i
    · rw [show w i s = 1 from ite_eq_right e]
      exact one_mem _
  unfold overEmb
  split_ifs
  · exact key _
  · exact key _

end GlobalTheory.Unframe
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGeoHalfMove =====
