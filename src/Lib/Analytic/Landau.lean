import Lib.Analytic.EntireLFunction
import TauCeti.Analysis.LaplaceTransform.Meromorphic

/-!
# Landau's lemma

This part applies Landau's lemma, that the Laplace transform of a function of one sign is not
analytic at its abscissa of convergence, to transforms satisfying `New.IsPolar`. Assume a one-sided
bound on the error term `E`, and assume that the residues `r x` at real `x > β` have non-negative
real part. Then there is no pole to the right of `β`. Together with `Lib.Analytic.EntireLFunction`,
these are the analytic tools for passing from a one-sided bound on an error term to the absence of
zeros of L-functions.

Landau's lemma in the one-sided form used here is Tau Ceti's
`TauCeti.hasLaplace_toMeromorphicNFOn_of_ae_le_exp`, stated with meromorphic orders and trailing
coefficients; this file translates residues to trailing coefficients.

## Main results

* `New.IsPolar.landau`: let `β > 0`. If `E v ≤ A e^{(β-1)v}` for all large `v` and `re (r x) ≥ 0`
  for real `x > β`, then `r ρ = 0` for `re ρ > β`.

Notions from other files:
* `New.IsPolar` (from `Lib.Analytic.EntireLFunction`): `E` is measurable, `|E v| ≤ C e^v` for
  `v ≥ 0`, and `∫₀^∞ E(v) e^{(1-s)v} dv` continues meromorphically with at most simple poles of
  residue `r ρ` in `re ρ > 0`.

## Relation to the literature

Known result: Landau's lemma on Dirichlet integrals of one sign. It is applied to transforms with
simple poles whose residues at real points have non-negative real part: no pole lies to the right
of the abscissa given by the one-sided bound. Source: Montgomery and Vaughan, Multiplicative
Number Theory I, 2007, Lemma 15.1 (Widder, The Laplace Transform, 1941, II Thm 5b).
-/

open Complex Set Filter MeasureTheory Topology

namespace New

variable {E : ℝ → ℝ}

/-- At a pole `x` of a meromorphic `Φ`, if `(z - x) Φ(z) → c` then the pole is simple and its
trailing coefficient is the residue `c`. -/
lemma meromorphicTrailingCoeffAt_eq_of_tendsto {Φ : ℂ → ℂ} {x c : ℂ} (hΦ : MeromorphicAt Φ x)
    (h_neg : meromorphicOrderAt Φ x < 0)
    (h_lim : Tendsto (fun z ↦ (z - x) * Φ z) (𝓝[≠] x) (𝓝 c)) :
    meromorphicTrailingCoeffAt Φ x = c := by
  have hm : MeromorphicAt (· - x) x := by fun_prop
  have h_nonneg : 0 ≤ meromorphicOrderAt ((· - x) • Φ) x :=
    (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hm.smul hΦ)).1 ⟨c, h_lim⟩
  rw [meromorphicOrderAt_smul hm hΦ, meromorphicOrderAt_id_sub_const] at h_nonneg
  obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.1 h_neg.ne_top
  rw [← hn] at h_neg h_nonneg
  have h_one : n = -1 := by norm_cast at h_neg h_nonneg; omega
  have h := hΦ.tendsto_nhds_meromorphicTrailingCoeffAt
  rw [← hn, h_one] at h
  exact tendsto_nhds_unique (h.congr fun z ↦ by simp) h_lim

/-- **No pole to the right of `β`**, by Landau's lemma and the sign of the residues at real points.
Suppose `IsPolar E r`: `|E v| ≤ C e^v` for `v ≥ 0` and the transform
`∫₀^∞ E(v) e^{(1-s)v} dv` has a meromorphic continuation with at most simple poles of residue `r ρ`
in `re ρ > 0`. Let `β > 0`. If `E(v) ≤ A e^{(β-1)v}` for all large `v` and the residues at real points
right of `β` have real part `≥ 0`, then there is no pole in `re s > β`, that is, `r ρ = 0`. -/
lemma IsPolar.landau {r : ℂ → ℂ} (h : IsPolar E r) {A β : ℝ} (hβ : 0 < β)
    (hr : ∀ x : ℝ, β < x → 0 ≤ (r x).re) (hE_le : ∀ᶠ v : ℝ in atTop, E v ≤ A * Real.exp ((β - 1) * v))
    {ρ : ℂ} (hρ : β < ρ.re) :
    r ρ = 0 := by
  -- `Φ` is the Laplace transform of `g(v) = E(v) e^v`, and `g(v) ≤ A e^{βv}` for large `v`.
  obtain ⟨hE, C, Φ, hΦ, hE_growth, Φ_eq, Φ_res⟩ := h
  obtain ⟨u₀, hu₀⟩ := hE_le.exists_forall_of_atTop
  have hg : ∀ᵐ u ∂volume.restrict (Ioi u₀), E u * Real.exp u ≤ A * Real.exp (β * u) :=
    ae_restrict_of_forall_mem measurableSet_Ioi fun u (hu : u₀ < u) ↦
      calc E u * Real.exp u ≤ A * Real.exp ((β - 1) * u) * Real.exp u := by grw [hu₀ u hu.le]
        _ = A * Real.exp (β * u) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
  have h_integrand (s : ℂ) (u : ℝ) :
      cexp (-s * u) • ((E u * Real.exp u : ℝ) : ℂ) = E u * cexp ((1 - s) * u) := by
    push_cast
    rw [smul_eq_mul, show (1 - s) * u = -s * u + u by ring, Complex.exp_add]
    ring
  have hL (s : ℂ) (hs : 2 < s.re) :
      TauCeti.HasLaplace (fun u ↦ ((E u * Real.exp u : ℝ) : ℂ)) s (Φ s) := by
    refine ⟨?_, ?_⟩ <;> simp only [h_integrand]
    exacts [integrableOn_laplace_of_abs_le hE hE_growth hs, (Φ_eq s hs).symm]
  -- At a real pole the trailing coefficient is the residue, whose real part is `≥ 0`.
  have h_sign (x : ℝ) (hx : x ∈ Ioc β 2) (h_neg : meromorphicOrderAt Φ x < 0) :
      0 ≤ (meromorphicTrailingCoeffAt Φ x).re := by
    rw [meromorphicTrailingCoeffAt_eq_of_tendsto (hΦ x) h_neg
      (Φ_res x (by simpa using hβ.trans hx.1))]
    exact hr x hx.1
  -- So `Φ` has no pole in `re s > β`, and its residue `r ρ` is `0`.
  obtain ⟨h_order, -⟩ :=
    TauCeti.hasLaplace_toMeromorphicNFOn_of_ae_le_exp hg (fun z _ ↦ hΦ z) hL h_sign
  obtain ⟨L, hL⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg (hΦ ρ) (h_order ρ hρ)
  have h_zero : Tendsto (fun z ↦ (z - ρ) * Φ z) (𝓝[≠] ρ) (𝓝 0) := by
    simpa using ((((continuous_sub_right ρ).tendsto ρ).mono_left nhdsWithin_le_nhds).mul hL)
  exact tendsto_nhds_unique (Φ_res ρ (hβ.trans hρ)) h_zero

end New
