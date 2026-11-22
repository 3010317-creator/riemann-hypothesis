module

public import Mathlib.Algebra.Module.Lattice.Full

/-!
# The historical finitely generated spanning-lattice contract

This project-local predicate preserves the original generic lattice data: finite generation and
full scalar span. Mathlib's `Submodule.IsFullLattice` additionally requires that independent
subsets remain independent after extending scalars. That condition follows over a fraction field,
but is not part of this generic contract.
-/

@[expose] public section

namespace RHCompat

variable {R : Type*} [CommRing R]

/-- The finite-generation and full-span conditions used by the project's original lattice API. -/
class SpanningLattice (A : outParam Type*) [CommRing A] [Algebra R A] {V : Type*} [AddCommMonoid V]
    [Module R V] [Module A V] [IsScalarTower R A V] (M : Submodule R V) : Prop where
  fg : M.FG
  span_eq_top : Submodule.span A (M : Set V) = ⊤

namespace SpanningLattice

variable {A : Type*} [CommRing A] [Algebra R A] {V : Type*} [AddCommMonoid V]
  [Module R V] [Module A V] [IsScalarTower R A V] {M : Submodule R V}

/-- This is exactly the original predicate, expressed without any independence condition. -/
theorem iff_fg_and_span_eq_top :
    SpanningLattice A M ↔ M.FG ∧ Submodule.span A (M : Set V) = ⊤ :=
  ⟨fun h => ⟨h.fg, h.span_eq_top⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Forget the additional independence condition of a Mathlib full lattice. -/
theorem ofFull {W : Type*} [AddCommGroup W] [Module R W] [Module A W]
    [IsScalarTower R A W] {L : Submodule R W}
    (h : Submodule.IsFullLattice A L) : SpanningLattice A L :=
  ⟨h.fg, h.span_eq_top⟩

/-- Over the fraction field, independence follows from finite generation. -/
theorem toIsFullLattice {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {W : Type*} [AddCommGroup W] [Module R W] [Module K W] [IsScalarTower R K W]
    {L : Submodule R W} (h : SpanningLattice K L) : Submodule.IsFullLattice K L :=
  { toIsLattice := Submodule.IsLattice.of_fg K h.fg, span_eq_top := h.span_eq_top }

end SpanningLattice

end RHCompat
