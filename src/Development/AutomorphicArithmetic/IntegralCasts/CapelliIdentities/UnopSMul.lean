module

public import Mathlib

@[expose] public section

namespace UpperTheory.Reformulated.B.Qk3

open scoped TensorProduct

theorem aux1 {A : Type} [CommRing A] :
    RingHomInvPair (RingHom.id A) (RingHom.id A) :=
  RingHomInvPair.ids

noncomputable def unopS (A E S : Type) [CommRing A] [Ring E] [Algebra A E]
    [CommRing S] [Algebra A S] : (S ⊗[A] Eᵐᵒᵖ) →ₗ[S] (S ⊗[A] E) :=
  LinearMap.baseChange S (MulOpposite.opLinearEquiv A).symm.toLinearMap

theorem unopS_mul {A E : Type} [CommRing A] [Ring E] [Algebra A E]
    (S : Type) [CommRing S] [Algebra A S] (x y : S ⊗[A] Eᵐᵒᵖ) :
    unopS A E S (x * y) = unopS A E S y * unopS A E S x := by
  induction x using TensorProduct.inductionOn with
  | add x₁ x₂ h₁ h₂ => rw [add_mul, map_add (f := _), map_add (f := _), h₁, h₂, mul_add]
  | tmul s e =>
    induction y using TensorProduct.inductionOn with
    | add y₁ y₂ h₁ h₂ => rw [mul_add, map_add (f := _), map_add (f := _), h₁, h₂, add_mul]
    | tmul t f =>
      simp [unopS, Algebra.TensorProduct.tmul_mul_tmul, mul_comm s t]

end UpperTheory.Reformulated.B.Qk3
