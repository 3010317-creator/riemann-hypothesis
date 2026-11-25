module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.GlobalFields.LocalAtPlace
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Algebra.Order.Archimedean.Submonoid
import Mathlib.Tactic.Linter.Style

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.locDual :
    UpperTheory.V.Af.Smo.LocDual := by
  intro E _ _ w ψ hψ V hV
  obtain ⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by
    by_contra! h
    exact hψ (AddChar.ext _ _ fun x => by simpa using h x)
  have ha0 : a ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hV
  obtain ⟨C, hC, hC0⟩ := exists_compact_mem_nhds (0 : HeightOneSpectrum.adicCompletion E w)
  obtain ⟨γ₁, hγ₁⟩ := Valued.mem_nhds_zero.mp hC0
  obtain ⟨π₀, hπ₀⟩ := HeightOneSpectrum.valuation_exists_uniformizer E w
  have hvπ : Valued.v (π₀ : HeightOneSpectrum.adicCompletion E w) = WithZero.exp (-1 : ℤ) := by
    simp [hπ₀]
  have hπ0 : (π₀ : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    intro h
    rw [h, map_zero] at hvπ
    exact WithZero.zero_ne_coe hvπ
  have hπ1 : Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w) < 1 := by
    rw [Valuation.restrict_lt_one_iff, hvπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have hπn : Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w) ≠ 0 := by
    rw [Ne, Valuation.restrict_eq_zero_iff, hvπ]
    exact WithZero.exp_ne_zero
  have hua : Valued.v.restrict a ≠ 0 := by simp [ha0]
  set R := Units.mk0 (Valued.v.restrict a * (γ : _)⁻¹ *
    (Valued.v.restrict (π₀ : HeightOneSpectrum.adicCompletion E w))⁻¹)
    (mul_ne_zero (mul_ne_zero hua γ⁻¹.ne_zero) (inv_ne_zero hπn)) with hR
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hπ1 (γ₁ * R⁻¹)
  refine ⟨Valued.v.restrict.ltAddSubgroup R, ?_, ?_, ?_⟩
  · rw [Valuation.coe_ltAddSubgroup]
    exact Valued.isOpen_ball _ _
  · rw [Valuation.coe_ltAddSubgroup]
    refine IsCompact.of_isClosed_subset
      (hC.image (continuous_const.mul continuous_id :
        Continuous fun z : HeightOneSpectrum.adicCompletion E w =>
          ((π₀ : HeightOneSpectrum.adicCompletion E w) ^ n)⁻¹ * z))
      (Valued.isClosed_ball _ _) ?_
    intro y hy
    refine ⟨(π₀ : HeightOneSpectrum.adicCompletion E w) ^ n * y, hγ₁ ?_, ?_⟩
    · show Valued.v.restrict ((π₀ : HeightOneSpectrum.adicCompletion E w) ^ n * y) < γ₁
      rw [map_mul, map_pow]
      exact (mul_le_mul_of_nonneg_left hy.le zero_le).trans_lt
        ((lt_mul_inv_iff₀ (zero_lt_iff.mpr R.ne_zero)).1 (by simpa using hn))
    · exact inv_mul_cancel_left₀ (pow_ne_zero n hπ0) y
  · intro x hx
    by_contra hxV
    have hxg : (γ : _) ≤ Valued.v.restrict x := by
      by_contra! h
      exact hxV (hγ h)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hxg
      exact γ.ne_zero (le_antisymm hxg zero_le')
    have hy : a * x⁻¹ ∈ Valued.v.restrict.ltAddSubgroup R := by
      rw [← SetLike.mem_coe, Valuation.coe_ltAddSubgroup]
      show Valued.v.restrict (a * x⁻¹) < R
      rw [map_mul, map_inv₀, hR, Units.val_mk0, Units.val_inv_eq_inv_val]
      exact (mul_le_mul_of_nonneg_left (inv_anti₀ (zero_lt_iff.mpr γ.ne_zero) hxg)
        zero_le).trans_lt (lt_mul_of_one_lt_right
        (zero_lt_iff.mpr (mul_ne_zero hua (inv_ne_zero γ.ne_zero)))
        ((one_lt_inv₀ (zero_lt_iff.mpr hπn)).2 hπ1))
    have h1 := hx _ hy
    rw [mul_comm a, ← mul_assoc, mul_inv_cancel₀ hx0, one_mul] at h1
    exact ha h1
