module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Formalism.SharpRestriction.ElevenLe
public import Formalism.LocalRingCardinality.DataParams
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.LogQdLeRd
public import Formalism.LocalRingCardinality.HostCls
import Formalism.LocalRingCardinality.FourthPowerRankLeNF
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.I2

variable {D : D7}

theorem hostSize_finrank (D : D7) : Module.finrank ℚ D.host.E = 2 * D.R.f := by
  rw [D.host.der.finrank_E, Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)]
  first
  | ring

theorem hostSize_f (D : D7) : PT.f D.host.E = D.R.f := by
  simp only [ReciprocityTheory.ChartRestriction.G.I2.PT.f, hostSize_finrank D]
  omega

theorem hostSize_rd (D : D7) : PT.rd D.host.E = D.host.rdE := rfl

theorem hostSize_n_sqrt_le (D : D7) :
    Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
  (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1

theorem hostSize_sqrt_gt {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) :
    ((D.R.f : ℝ) + 6) ^ 2 < Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hf : D.R.f = 2 * D.R.ord := Formalism.BasicNotions.Ranks.f_eq_ord (R := D.R)
  have hfk := D.R.f_le_k
  have hm := D.R.two_le_m
  have hmf := D.R.m_le_f
  have ht := D.R.rank_add_five_le
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have h1 : D.R.f + 6 ≤ D.R.t := by omega
  have h2 : D.R.f + 6 ≤ 4 * D.R.r := by omega
  have key : (D.R.f + 6) ^ 2 < 4 * D.R.t * D.R.r + 1 := by
    have := Nat.mul_le_mul h1 h2
    nlinarith
  have keyR : ((D.R.f : ℝ) + 6) ^ 2 < ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) := by exact_mod_cast key
  have hA : (0 : ℝ) ≤ ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hqR : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < (D.host.q : ℝ) := by exact_mod_cast hq
  have hdR : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < (D.host.d : ℝ) := by exact_mod_cast hd
  have hsq : ((4 * D.R.t * D.R.r + 1 : ℕ) : ℝ) < Real.sqrt ((D.host.q : ℝ) * D.host.d) := by
    rw [Real.lt_sqrt hA]
    nlinarith
  linarith

theorem host_f_sq_le_rd {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) : (PT.f D.host.E : ℝ) ^ 2 ≤ PT.rd D.host.E := by
  have h1 := hostSize_sqrt_gt P
  have h2 := hostSize_n_sqrt_le D
  rw [hostSize_f D, hostSize_rd D]
  have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem host_rd_ge_sixteen {large₂ : SizeData₂ D} (P : ParameterChoice' D large₂) : 16 ≤ PT.rd D.host.E := by
  have h1 := hostSize_sqrt_gt P
  have h2 := hostSize_n_sqrt_le D
  rw [hostSize_rd D]
  have h0 : (0 : ℝ) ≤ (D.R.f : ℝ) := Nat.cast_nonneg _
  nlinarith

theorem host_m_pow_four_le_f {large₂ : SizeData₂ D} (hS : SizesAt large₂) : D.R.m ^ 4 ≤ PT.f D.host.E := by
  rw [hostSize_f D]
  exact m_pow_four_le_f large₂ hS.1 hS.2.1

end Formalism.L2.Pj
