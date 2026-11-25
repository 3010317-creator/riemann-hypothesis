module

public import Development.AutomorphicArithmetic.PrimitiveCosets.RecH
import Mathlib.Tactic.Linter.Style

@[expose] public section

open UpperTheory.Comparison₂ Formalism Formalism.HC Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LHost

private theorem UpperTheory.Comparison₂.sign_character_bijective : Function.Bijective Formalism.LFunctionChainParameters.LHost.sgn2 := by
  constructor
  · intro a b h
    have h' := congrArg Multiplicative.toAdd h
    rcases Int.units_eq_one_or a with rfl | rfl <;> rcases Int.units_eq_one_or b with rfl | rfl
    · rfl
    · exact absurd h' (by decide)
    · exact absurd h' (by decide)
    · rfl
  · intro y
    by_cases hy : Multiplicative.toAdd y = 0
    · refine ⟨1, Multiplicative.toAdd.injective ?_⟩
      rw [hy]
      decide
    · refine ⟨-1, Multiplicative.toAdd.injective ?_⟩
      have h1 : Multiplicative.toAdd y = 1 := by
        generalize Multiplicative.toAdd y = z at hy ⊢
        revert z
        decide
      rw [h1]
      decide

private theorem UpperTheory.Comparison₂.sign_character_one : Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 1) = 0 := by decide

private theorem UpperTheory.Comparison₂.sign_character_neg_one : Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 (-1)) = 1 := by decide

private theorem UpperTheory.Comparison₂.sign_character_zero_iff : ∀ u : ℤˣ, u = 1 ↔ Multiplicative.toAdd (Formalism.LFunctionChainParameters.LHost.sgn2 u) = 0 := by
  intro u
  rcases Int.units_eq_one_or u with rfl | rfl <;> decide

theorem UpperTheory.Comparison₂.toE_bij :
    ∀ φ : Frame, Function.Bijective (toE φ) ∧ toE φ φ.iod = Multiplicative.ofAdd sgc0 ∧ toE φ φ.cc = Multiplicative.ofAdd cconj ∧
      (∀ t, toE φ (φ.tau1 t) = Multiplicative.ofAdd ((0 : E0), t)) ∧ ∀ g : φ.GG, g ∈ φ.Psi ↔ InPhi (Multiplicative.toAdd (toE φ g)) := by
  intro φ
  let sign : ℤˣ ≃ ZMod 2 :=
    Equiv.ofBijective (fun u => (LFunctionChainParameters.LHost.sgn2 u).toAdd)
      (Multiplicative.toAdd.bijective.comp sign_character_bijective)
  let signs := (Equiv.prodComm ℤˣ ℤˣ).trans (sign.prodCongr sign)
  refine ⟨(signs.prodCongr (Equiv.refl φ.A)).bijective, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · intro t
    rfl
  · exact fun g => sign_character_zero_iff g.1.2
