module

public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Ring.Ultra
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

@[expose] public section

universe u_1

namespace Bl.general_b_fact_left_ter

/-- A root of a monic polynomial lies in the closed unit ball if its lower coefficients do. -/
theorem norm_le_one_of_eval₂_eq_zero {R F : Type*} [CommSemiring R]
    [NormedField F] [IsUltrametricDist F] (f : R →+* F) {y : F} (p : Polynomial R)
    (hp : p.Monic) (hcoeff : ∀ i < p.natDegree, ‖f (p.coeff i)‖ ≤ 1)
    (h : p.eval₂ f y = 0) : ‖y‖ ≤ 1 := by
  by_contra hy0
  have hy : 1 < ‖y‖ := not_le.mp hy0
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at h
  have hsum : ‖∑ i ∈ Finset.range p.natDegree, f (p.coeff i) * y ^ i‖
      < ‖y‖ ^ p.natDegree := by
    rcases (Finset.range p.natDegree).eq_empty_or_nonempty with he | hne
    · rw [he, Finset.sum_empty, norm_zero]
      exact pow_pos (zero_lt_one.trans hy) _
    · obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hne
        (fun i => f (p.coeff i) * y ^ i)
      refine hle.trans_lt ?_
      rw [norm_mul, norm_pow]
      exact (mul_le_of_le_one_left (pow_nonneg (norm_nonneg y) _)
          (hcoeff i (Finset.mem_range.mp hi))).trans_lt
        (pow_lt_pow_right₀ hy (Finset.mem_range.mp hi))
  rw [eq_neg_of_add_eq_zero_left h, norm_neg, norm_pow] at hsum
  exact lt_irrefl _ hsum

/-- An element integral over a coefficient algebra in the closed unit ball also lies there. -/
theorem norm_le_one_of_isIntegral {R F : Type*} [CommRing R] [NormedField F]
    [IsUltrametricDist F] [Algebra R F]
    (hR : ∀ r : R, ‖algebraMap R F r‖ ≤ 1) {y : F} (hy : IsIntegral R y) : ‖y‖ ≤ 1 := by
  obtain ⟨p, hp, hy⟩ := hy
  exact norm_le_one_of_eval₂_eq_zero (algebraMap R F) p hp (fun i _ => hR _) hy

theorem goal1 :
  ∀ {F : Type u_1} [inst : NormedField.{u_1} F] [IsUltrametricDist.{u_1} F] {y : F} (p : Polynomial.{0} Int),
  Polynomial.Monic.{0} p →
    Eq.{u_1 + 1} (Polynomial.eval₂.{0, u_1} (Int.castRingHom.{u_1} F) y p) 0 → LE.le.{0} (Norm.norm.{u_1} y) 1 := by
  intro F _ _ y p hp h
  exact norm_le_one_of_eval₂_eq_zero (Int.castRingHom F) p hp
    (fun i _ => IsUltrametricDist.norm_intCast_le_one F (p.coeff i)) h

end Bl.general_b_fact_left_ter
