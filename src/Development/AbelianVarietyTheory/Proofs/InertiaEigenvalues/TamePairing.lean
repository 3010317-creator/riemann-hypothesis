module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.GaloisValuations.GlobalA

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.TamePairing

open GlobalTheory.TameQuot

theorem eq_zero_of_isProGen {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {l : ℕ} [hl : Fact l.Prime] {n : ℕ} {A : ValuationSubring Ω} {γ₀ : Dec (F := F) A}
    (hγ : IsProGen F A l (γ₀ : G F Ω)) (f : Dec (F := F) A → ZMod (l ^ n)) (hf : Continuous f)
    (hadd : ∀ g h, f (g * h) = f g + f h) (h0 : f γ₀ = 0) (σ : Dec (F := F) A)
    (hσ : (σ : G F Ω) ∈ Ine (F := F) A) : f σ = 0 := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ hl.out.ne_zero⟩
  let φ : Dec (F := F) A →* Multiplicative (ZMod (l ^ n)) :=
    MonoidHom.mk' (fun g => Multiplicative.ofAdd (f g)) (fun g h => by rw [hadd, ofAdd_add])
  let ψ : Ine (F := F) A →* Multiplicative (ZMod (l ^ n)) :=
    φ.comp (Subgroup.inclusion (Ine_le_Dec A))
  have hc : Continuous fun g : Ine (F := F) A => f (Subgroup.inclusion (Ine_le_Dec A) g) :=
    hf.comp (continuous_induced_rng.2 continuous_subtype_val)
  have hker : (ψ.ker : Set (Ine (F := F) A)) =
      (fun g : Ine (F := F) A => f (Subgroup.inclusion (Ine_le_Dec A) g)) ⁻¹' {0} := by
    ext g; rfl
  have hopen : IsOpen (ψ.ker : Set (Ine (F := F) A)) := by
    rw [hker]; exact (isOpen_discrete _).preimage hc
  have hclosed : IsClosed (ψ.ker : Set (Ine (F := F) A)) := by
    rw [hker]; exact (isClosed_discrete _).preimage hc
  have hidx : ∃ m : ℕ, ψ.ker.index = l ^ m := by
    have h1 : ψ.ker.index ∣ l ^ n := by
      rw [Subgroup.index_ker]
      have := Subgroup.card_subgroup_dvd_card ψ.range
      simpa using this
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hl.out).1 h1
    exact ⟨m, hm⟩
  have hle : Subgroup.zpowers (γ₀ : G F Ω) ⊔ ineKer F A l ≤
      ψ.ker.map (Ine (F := F) A).subtype := by
    refine sup_le ?_ (Subgroup.map_mono fun x hx => mem_proKer.1 hx _ inferInstance hopen hidx)
    rw [Subgroup.zpowers_le]
    refine ⟨⟨γ₀, hγ.1⟩, ?_, rfl⟩
    rw [hker]; exact h0
  have h2 : (σ : G F Ω) ∈ closure ((↑) '' (ψ.ker : Set (Ine (F := F) A)) : Set (G F Ω)) :=
    closure_mono (s := ((Subgroup.zpowers (γ₀ : G F Ω) ⊔ ineKer F A l : Subgroup (G F Ω)) :
      Set (G F Ω))) hle (hγ.2 hσ)
  have h3 : (⟨σ, hσ⟩ : Ine (F := F) A) ∈ closure (ψ.ker : Set (Ine (F := F) A)) :=
    closure_subtype.2 h2
  rw [hclosed.closure_eq, hker] at h3
  exact h3

open NumberField IsDedekindDomain in
open scoped Pointwise in
private theorem ne_zero_of_isUnifRoot {F Ω : Type} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] {v : HeightOneSpectrum (𝓞 F)} {N : ℕ} [NeZero N] {x : Ω}
    (hx : _root_.GlobalTheory.TameQuot.IsUnifRoot v N x) : x ≠ 0 := by
  obtain ⟨ϖ, -, hϖ2, hxN⟩ := hx
  have hϖ : (ϖ : F) ≠ 0 := by
    intro h
    apply hϖ2
    have : ϖ = 0 := by exact_mod_cast h
    rw [this]
    exact Submodule.zero_mem _
  rintro rfl
  rw [zero_pow (NeZero.ne N), eq_comm] at hxN
  exact hϖ ((map_eq_zero_iff _ (algebraMap F Ω).injective).1 hxN)


open NumberField IsDedekindDomain in
open scoped Pointwise in
theorem _root_.GlobalTheory.TamePairing.exists_apply_eq_pow_mul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {v : HeightOneSpectrum (𝓞 F)} {N : ℕ} [NeZero N] {ζ x : Ω} (hζ : IsPrimitiveRoot ζ N)
    (hx : _root_.GlobalTheory.TameQuot.IsUnifRoot v N x) (g : _root_.Formalism.ConjugateSelfDual.G F Ω) : ∃ c : ZMod N, g x = ζ ^ c.val * x := by
  have hx0 := ne_zero_of_isUnifRoot hx
  obtain ⟨ϖ, -, -, hxN⟩ := hx
  have hpow : (g x / x) ^ N = 1 := by
    rw [div_pow, ← map_pow, hxN, AlgEquiv.commutes, div_self]
    rw [← hxN]
    exact pow_ne_zero _ hx0
  obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one hpow
  refine ⟨(i : ZMod N), ?_⟩
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi, hi', div_mul_cancel₀ _ hx0]


end GlobalTheory.TamePairing
