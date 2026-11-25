module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Formalism.LocalToGlobal.TorsionIntegrality.CMGoodModels.Statement
import ReciprocityTheory.NeutralLocalFields.HilbertClassField

@[expose] public section

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem mem_Aio {d l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (x : Om d) : x ∈ Aio d l ι ↔ ‖ι (x : ℂ)‖ ≤ 1 := by
  rw [Aio, ValuationSubring.mem_comap, Valuation.mem_valuationSubring_iff, NormedField.valuation_apply,
    ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  try exact Iff.rfl

theorem mem_nonunits_Aio {d l : ℕ} [Fact l.Prime] (ι : ℂ ≃+* ℂ_[l]) (x : Om d) :
    x ∈ (Aio d l ι).nonunits ↔ ‖ι (x : ℂ)‖ < 1 := by
  rw [ValuationSubring.mem_nonunits_iff_or, mem_Aio, IntermediateField.coe_inv, map_inv₀,
    norm_inv, not_le, one_lt_inv_iff₀]
  exact ⟨fun h => h.elim (fun hx => by subst hx; simp) And.right, fun h =>
    (eq_or_ne x 0).imp_right fun hx => ⟨norm_pos_iff.2 ((map_ne_zero ι).2
      (fun e => hx (Subtype.ext e))), h⟩⟩

theorem mem_of_isIntegral {Ω : Type*} [Field Ω] (A : ValuationSubring Ω) {x : Ω} (hx : IsIntegral ℤ x) : x ∈ A := by
  have h2 : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h2
  rw [← hy]
  exact y.2

theorem exists_Om (d : ℕ) {z : ℂ} (hz : IsIntegral ℤ z) : ∃ x : Om d, (x : ℂ) = z ∧ IsIntegral ℤ x := by
  have hzK : IsIntegral (KQ d) z := hz.tower_top
  have hmem : z ∈ Om d := hzK
  refine ⟨⟨z, hmem⟩, rfl, ?_⟩
  exact (isIntegral_algHom_iff (x := (⟨z, hmem⟩ : Om d)) (algebraMap (Om d) ℂ).toIntAlgHom
    (algebraMap (Om d) ℂ).injective).mp hz

theorem Om_isAlgebraic (d : ℕ) (x : Om d) : IsAlgebraic ℚ (x : ℂ) := by
  have hx : IsIntegral (KQ d) (x : ℂ) := x.2
  exact (isIntegral_trans (R := ℚ) _ hx).isAlgebraic

end ReciprocityTheory.ChartRestriction.L1
