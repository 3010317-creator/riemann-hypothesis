module

public import Formalism.FrobeniusBaseCase.Statement
public import Formalism.LocalToGlobal.CharacterGerms.Interface
public import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin

@[expose] public section

noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (OrdGE)

variable {C : Type} [Field C] {σ τ : Type}

theorem coeff_mvExp_partial {h : MvPowerSeries σ C} (hh : OrdGE 1 h) (N : ℕ) (m : σ →₀ ℕ)
    (hm : m.degree ≤ N) :
    coeff m (mvExp h) = coeff m (∑ k ∈ Finset.range (N + 1), ((k.factorial : C)⁻¹) • h ^ k) := by
  have hpow : ∀ k, OrdGE k (h ^ k) := by
    intro k
    have := ordGE_finset_prod (Finset.range k) (fun _ => 1) (fun _ => h) (fun _ _ => hh)
    simpa [Finset.prod_const, Finset.card_range] using this
  show (∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C)) = _

  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_subset (Finset.range_mono (by omega : m.degree + 1 ≤ N + 1)) ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [div_eq_inv_mul]
  · intro k hk hk'
    rw [Finset.mem_range] at hk hk'
    rw [hpow k m (by omega), zero_div]

theorem subst_mvExp [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {h : MvPowerSeries σ C} (hh : OrdGE 1 h) : subst a (mvExp h) = mvExp (subst a h) := by
  ext e
  have hsh : OrdGE 1 (subst a h) := ordGE_subst ha hh
  rw [coeff_subst_congr ha (F := mvExp h)
      (G := ∑ k ∈ Finset.range (e.degree + 1), ((k.factorial : C)⁻¹) • h ^ k) (N := e.degree)
      (fun d hd => coeff_mvExp_partial hh e.degree d hd) e le_rfl,
    coeff_mvExp_partial hsh e.degree e le_rfl]
  congr 1

  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_of_ordGE ha), map_sum]
  simp only [map_smul, map_pow]

end Formalism.L2.FormalSeriesBounds
