module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.Tactic.TypeStar
import Formalism.SharpRestriction.GrowthBounds.CovariantDegrees

@[expose] public section

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

section v2dpAbs

variable {R : Type*} [CommRing R] {σ ι : Type*} [DecidableEq ι]

def dividedPowerExponent (src dst : ι → σ) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : σ →₀ ℕ :=
  (m - Finsupp.mapDomain src f) + Finsupp.mapDomain dst f

def dividedPowerCoefficient (sg : ι → R) (src : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : R :=
  ∏ l ∈ s, sg l ^ (f l) * ((m (src l)).choose (f l) : R)

def dividedPowerMonomialTerm (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (m : σ →₀ ℕ) (f : ι →₀ ℕ) : MvPolynomial σ R :=
  monomial (dividedPowerExponent src dst m f) (dividedPowerCoefficient sg src s m f)

def dividedPowerMonomialSum (sg : ι → R) (src dst : ι → σ) (s : Finset ι) (k : ℕ) (m : σ →₀ ℕ) : MvPolynomial σ R :=
  ∑ f ∈ Finset.finsuppAntidiag s k, dividedPowerMonomialTerm sg src dst s m f

def polarizationDerivation (sg : ι → R) (src dst : ι → σ) (l : ι) : MvPolynomial σ R →ₗ[R] MvPolynomial σ R :=
  sg l • ((LinearMap.mulLeft R (X (dst l))) ∘ₗ (pderiv (src l)).toLinearMap)

theorem finsuppAntidiag_succ_reindex {N : Type*} [AddCommMonoid N] (s : Finset ι) (k : ℕ) (l : ι) (hl : l ∈ s)
    (F : (ι →₀ ℕ) → N) :
    ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • F g =
      ∑ f ∈ Finset.finsuppAntidiag s k, (f l + 1) • F (f + Finsupp.single l 1) := by
  have hL : ∑ g ∈ Finset.finsuppAntidiag s (k + 1), (g l) • F g =
      ∑ g ∈ (Finset.finsuppAntidiag s (k + 1)).filter (fun g => g l ≠ 0), (g l) • F g := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro g _ h h0
    apply h
    simp [h0]
  rw [hL]
  symm
  apply Finset.sum_nbij' (fun f => f + Finsupp.single l 1) (fun g => g - Finsupp.single l 1)
  · intro f hf
    simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag] at hf ⊢
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [← hf.1]
      simp [Finset.sum_add_distrib, Finsupp.single_apply, hl]
    · intro x hx
      rcases Finset.mem_union.1 (Finsupp.support_add hx) with h | h
      · exact hf.2 h
      · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
        exact hl
    · simp
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag] at hg ⊢
    have hle : Finsupp.single l 1 ≤ g := Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hg.2)
    have hg' : g - Finsupp.single l 1 + Finsupp.single l 1 = g := tsub_add_cancel_of_le hle
    refine ⟨?_, ?_⟩
    · have hsum : ∑ x ∈ s, (g - Finsupp.single l 1 : ι →₀ ℕ) x + ∑ x ∈ s, (Finsupp.single l 1 : ι →₀ ℕ) x =
          ∑ x ∈ s, g x := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun x _ => by rw [← Finsupp.add_apply, hg'])
      have h1 : ∑ x ∈ s, (Finsupp.single l 1 : ι →₀ ℕ) x = 1 := by
        simp [Finsupp.single_apply, hl]
      have h2 : ∑ x ∈ s, g x = k + 1 := hg.1.1
      have h3 : ∑ x ∈ s, (g - Finsupp.single l 1 : ι →₀ ℕ) x = k := by omega
      exact h3
    · intro x hx
      apply hg.1.2
      rw [Finsupp.mem_support_iff] at hx ⊢
      intro h0
      apply hx
      simp [h0]
  · intro f _
    simp
  · intro g hg
    simp only [Finset.mem_filter, Finset.mem_finsuppAntidiag] at hg
    exact tsub_add_cancel_of_le (Finsupp.single_le_iff.2 (Nat.one_le_iff_ne_zero.2 hg.2))
  · intro f _
    simp

end v2dpAbs

end Formalism.MainNotions.G.GLWeightTheory
