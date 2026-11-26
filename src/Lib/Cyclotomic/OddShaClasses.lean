module

public import Lib.ClassField.GaloisCohomology.Cohomology
public import Lib.Cyclotomic.OddSha

/-!
# The model of the odd part of Ш as a group of cohomology classes

`New.Selmer.shaOdd l E O e n` is a module of cocycles `Gal(Ω/E) → O / lⁿ(-e)`: locally constant,
unramified outside `l`, vanishing on `New.Selmer.shaLocalSet l E e` and, for `e ≠ 0`, odd under
`New.conjGal`, `z (c g c) = -z g`. This file compares it with cohomology classes. The cocycles
`New.Selmer.shaCocycles` cut out by the same conditions without oddness contain the coboundaries
`B¹`. A coboundary `g ↦ g b - b` is even under `conjGal`, since the cyclotomic character is, so an
odd coboundary is killed by `2`. Hence for `e = 0` or `2` a unit of `O` (that is, `l` odd),
`shaOdd` meets `B¹` only in `0` and maps isomorphically onto its classes, and these are the classes
of `shaCocycles` that are odd under `conjGal` (`New.Selmer.mem_shaOddClasses_iff`). For `l = 2` and
`e ≠ 0` the intersection with `B¹` can be non-zero, and only the image of `shaOdd` is considered.

* `New.Selmer.shaModule`: the discrete Galois module `O / lⁿ(-e)`.
* `New.Selmer.shaCocycles`, `New.Selmer.shaOddClasses`: the cocycles without oddness, and the
  classes of `shaOdd` in `H¹(Gal(Ω/E), O / lⁿ(-e))`.
* `New.Selmer.shaOdd_inf_B1_eq_bot`, `New.Selmer.length_shaOdd_eq_length_classes`,
  `New.Selmer.card_shaOdd_eq_card_classes`, `New.Selmer.mem_shaOddClasses_iff`: for `e = 0` or `2`
  a unit, `shaOdd` is isomorphic to its classes, which are the odd classes of `shaCocycles`.
* `New.length_shaOddClasses_zero_le_addVal_classNumber`,
  `New.OddPart.nsmul_shaOddClasses_eq_zero_of_isStickelbergerBound`,
  `New.OddPart.length_shaOddClasses_le_addVal_pow`, `New.OddPart.length_shaOddClasses_le_of_le_sq`,
  `New.OddPart.length_shaOddClasses_le_of_sq_lt`, `New.exists_length_shaOddClasses_le`: the bounds
  of `Lib.Cyclotomic.OddSha` for the classes.

Notions from other files:
* `New.Z1`, `New.B1`: continuous 1-cocycles and coboundaries.
* `New.DiscreteModule.π₁`: the `O`-linear class map from `Z¹` onto `H¹`, with kernel `B¹`.

## Relation to the literature

Known: for `l` odd the odd part of `H¹` under complex conjugation is computed by odd cocycles. See
B. Mazur, A. Wiles, Class fields of abelian extensions of Q, Invent. Math. 76 (1984).
-/

@[expose] public section

noncomputable section

namespace New.Selmer

open Module Matrix.Module

variable {l : ℕ} [ThePrime l] {E : Type} [Field E] [EmbeddedNumberField E]
  [NumberField.IsCMField E] {O : Type} [CommRing O] [PadicIntegerRing O l] {e n : ℕ}

omit [NumberField.IsCMField E] in
/-- An element of `Gal(Ω/E)` that fixes the `l ^ n`-th roots of unity acts trivially on
`O / lⁿ(-e)`. -/
lemma tateTwist_smul_eq_self_of_cyclotomicCharMod {h : Gal(Ω/E)}
    (hh : cyclotomicCharMod Ω (l ^ n) h = 1) (a : Unit → QuotSpan (l ^ n : O)) :
    tateTwist l E O e h • a = a := by
  set x : Gal(Ω/ℚ) := h.restrictScalars ℚ
  have h_char : cyclotomicChar Ω l h = cyclotomicChar Ω l x := rfl
  have hx0 : x ∈ cycloGalGroup (l ^ n) := MonoidHom.mem_ker.2 hh
  have hx : x⁻¹ ∈ cycloGalGroup (1 * l ^ n) :=
    cyclotomicCharMod_eq_one_of_dvd (one_mul (l ^ n)).dvd (inv_mem hx0)
  have ha : l ^ n • a = 0 := funext fun _ ↦ nsmul_quot_eq_zero dvd_rfl _
  have h_fix := (OddPart.cyclotomicPowDirichlet_smul_eq_self (O := O) (e := e) (l := l)
    (ψ := (1 : DirichletCharacter O 1)) hx ha).left
  -- The twist at `h` is the value of `cyc ^ e` at `x⁻¹`.
  simpa [cyclotomicPowDirichlet, tateTwist, cyclotomicInv, h_char,
    map_inv (cyclotomicChar Ω l), -map_inv] using h_fix

omit [NumberField.IsCMField E] in
lemma tateTwist_eq_one_of_cyclotomicChar_eq_one' {g : Gal(Ω/E)}
    (hg : cyclotomicChar Ω l g = 1) : tateTwist l E O e g = 1 := by
  simp [tateTwist, cyclotomicInv, hg]

lemma tateTwist_conjGal (g : Gal(Ω/E)) : tateTwist l E O e (conjGal g) = tateTwist l E O e g := by
  simp [tateTwist, cyclotomicInv, cyclotomicChar_conjGal]

variable (l E O e n) in
/-- The discrete Galois module `O / lⁿ(-e)`: `g` acts by `cyc(g) ^ (-e)`. -/
abbrev shaModule : DiscreteModule O Gal(Ω/E) :=
  letI : TopologicalSpace (QuotSpan (l ^ n : O)) := ⊥
  haveI : DiscreteTopology (QuotSpan (l ^ n : O)) := ⟨rfl⟩
  letI : MulAction Gal(Ω/E) (Unit → QuotSpan (l ^ n : O)) := .compHom _ (tateTwist l E O e)
  .of (actionRep O (Unit → QuotSpan (l ^ n : O)) (tateTwist l E O e))
    (continuousSMul_iff_stabilizer_isOpen.2 fun a ↦ Subgroup.isOpen_mono
      (fun _ hg ↦ MulAction.mem_stabilizer_iff.2
        (tateTwist_smul_eq_self_of_cyclotomicCharMod (E := E) (O := O) (e := e) hg a))
      isOpen_ker_cyclotomicCharMod.out).1

/-- The discrete topology on `O / b`, the one used by `New.Selmer.shaModule`. -/
local instance (b : O) : TopologicalSpace (QuotSpan b) := ⊥

local instance (b : O) : DiscreteTopology (QuotSpan b) := ⟨rfl⟩

omit [NumberField.IsCMField E] in
lemma shaModule_ρ_apply (g : Gal(Ω/E)) (a : Unit → QuotSpan (l ^ n : O)) :
    (shaModule l E O e n).ρ g a = tateTwist l E O e g • a :=
  rfl

variable (l E O e n) in
/-- `New.Selmer.shaOdd` without the oddness condition: the locally constant cocycles for `O(-e)`
with values in `O / lⁿ`, unramified outside `l`, that vanish on `shaLocalSet l E e`. -/
def shaCocycles : Submodule O (Gal(Ω/E) → Unit → QuotSpan (l ^ n : O)) where
  carrier := {z | (∀ g ∈ shaLocalSet l E e, z g = 0) ∧
    z ∈ selmerModule (tateTwist l E O e) (placesDividing E l) ∅ (QuotSpan (l ^ n : O))}
  add_mem' := by
    rintro z z' ⟨hz_local, hz_sel⟩ ⟨hz'_local, hz'_sel⟩
    exact ⟨fun g hg ↦ by simp [hz_local g hg, hz'_local g hg], add_mem hz_sel hz'_sel⟩
  zero_mem' := ⟨fun _ _ ↦ rfl, zero_mem _⟩
  smul_mem' := by
    rintro c z ⟨hz_local, hz_sel⟩
    exact ⟨fun g hg ↦ by simp [hz_local g hg], Submodule.smul_mem _ c hz_sel⟩

lemma mem_shaOdd_iff_mem_shaCocycles {z : Gal(Ω/E) → Unit → QuotSpan (l ^ n : O)} :
    z ∈ shaOdd l E O e n ↔
      z ∈ shaCocycles l E O e n ∧ (e ≠ 0 → ∀ g : Gal(Ω/E), z (conjGal g) = -z g) := by
  rw [mem_shaOdd]
  exact ⟨fun ⟨h₁, h₂, h₃⟩ ↦ ⟨⟨h₁, h₃⟩, h₂⟩, fun ⟨⟨h₁, h₃⟩, h₂⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

omit [NumberField.IsCMField E] in
variable (l E O e n) in
lemma shaCocycles_le_Z1 : shaCocycles l E O e n ≤ Z1 (shaModule l E O e n).ρ := fun _ hz ↦
  have h := mem_selmerModule_iff.1 hz.2
  ⟨h.2.2.2.continuous, h.1⟩

variable (l E O e n) in
/-- `shaCocycles` as a module of continuous 1-cocycles of `shaModule`. -/
abbrev shaCocyclesZ1 : Submodule O (Z1 (shaModule l E O e n).ρ) :=
  (shaCocycles l E O e n).comap (Z1 (shaModule l E O e n).ρ).subtype

variable (l E O e n) in
/-- `shaOdd` as a module of continuous 1-cocycles of `shaModule`. -/
abbrev shaOddZ1 : Submodule O (Z1 (shaModule l E O e n).ρ) :=
  (shaOdd l E O e n).comap (Z1 (shaModule l E O e n).ρ).subtype

variable (l E O e n) in
/-- The classes of `shaOdd` in `H¹(Gal(Ω/E), O / lⁿ(-e))`. -/
abbrev shaOddClasses : Submodule O ((shaModule l E O e n).H 1) :=
  (shaOddZ1 l E O e n).map (shaModule l E O e n).π₁

variable (l E O e n) in
lemma shaOdd_le_Z1 : shaOdd l E O e n ≤ Z1 (shaModule l E O e n).ρ := fun _ hz ↦
  shaCocycles_le_Z1 l E O e n (mem_shaOdd_iff_mem_shaCocycles.1 hz).1

omit [NumberField.IsCMField E] in
variable (l E O e n) in
/-- The cocycles `shaCocycles` contain the coboundaries: the twist is trivial on inertia outside
`l` and on `shaLocalSet l E e`. -/
lemma B1_le_shaCocyclesZ1 : B1 (shaModule l E O e n).ρ ≤ shaCocyclesZ1 l E O e n := fun z hz ↦ by
  obtain ⟨b, hb⟩ := mem_B1_iff.1 hz
  have h_triv {g : Gal(Ω/E)} (hg : tateTwist l E O e g = 1) : z.1 g = 0 := by
    rw [← hb, shaModule_ρ_apply, hg, one_smul, sub_self]
  refine ⟨fun g hg ↦ h_triv ?_, mem_selmerModule_iff.2 ⟨z.2.2, fun g hg ↦ h_triv ?_,
    mem_obeying.2 fun _ hf ↦ hf.elim, (IsLocallyConstant.iff_continuous _).2 z.2.1⟩⟩
  · obtain ⟨A, -, hA⟩ := hg
    split_ifs at hA with he
    · simp [tateTwist, he]
    · exact tateTwist_eq_one_of_cyclotomicChar_eq_one' hA.2
  · obtain ⟨u, hu, B, hB, hgB⟩ := hg
    exact tateTwist_eq_one_of_cyclotomicChar_eq_one'
      (cyclotomicChar_eq_one_of_mem_inertiaGroup l hgB (hB.valuation_natCast_eq_one_iff.2 hu))

/-- A coboundary of `shaModule` is even under `conjGal`. -/
lemma B1_apply_conjGal {z : Z1 (shaModule l E O e n).ρ} (hz : z ∈ B1 (shaModule l E O e n).ρ)
    (g : Gal(Ω/E)) : z.1 (conjGal g) = z.1 g := by
  obtain ⟨b, hb⟩ := mem_B1_iff.1 hz
  rw [← hb, ← hb, shaModule_ρ_apply, shaModule_ρ_apply, tateTwist_conjGal]

/-- For `e = 0` or `2` a unit of `O`, `shaOdd` meets the coboundaries only in `0`: an odd
coboundary is killed by `2`, and for `e = 0` all coboundaries vanish. -/
theorem shaOdd_inf_B1_eq_bot (h : e = 0 ∨ IsUnit (2 : O)) :
    shaOddZ1 l E O e n ⊓ B1 (shaModule l E O e n).ρ = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun z hz ↦ ?_
  obtain ⟨hz_odd, hz_B⟩ := Submodule.mem_inf.1 hz
  obtain ⟨b, hb⟩ := mem_B1_iff.1 hz_B
  refine Subtype.ext (funext fun g ↦ ?_)
  show z.1 g = 0
  rcases eq_or_ne e 0 with rfl | he
  · rw [← hb, shaModule_ρ_apply]
    simp [tateTwist]
  have h_two : IsUnit (2 : O) := h.resolve_left he
  have h_odd : z.1 (conjGal g) = -z.1 g :=
    (mem_shaOdd_iff_mem_shaCocycles.1 hz_odd).2 he g
  rw [B1_apply_conjGal hz_B, eq_neg_iff_add_eq_zero, ← two_smul O] at h_odd
  exact h_two.smul_eq_zero.1 h_odd

/-- For `e = 0` or `2` a unit of `O`, `shaOdd` has the length of its module of classes in
`H¹(Gal(Ω/E), O / lⁿ(-e))`. -/
theorem length_shaOdd_eq_length_classes (h : e = 0 ∨ IsUnit (2 : O)) :
    length O (shaOdd l E O e n) = length O (shaOddClasses l E O e n) := by
  rw [← LinearEquiv.length_eq (R := O) (M := shaOddZ1 l E O e n) (N := shaOdd l E O e n)
    (Submodule.comapSubtypeEquivOfLe (shaOdd_le_Z1 l E O e n)),
    (shaModule l E O e n).length_eq_length_map_π₁_add_length_inf_B1, shaOdd_inf_B1_eq_bot h,
    length_eq_zero (M := ↥(⊥ : Submodule O (Z1 (shaModule l E O e n).ρ))), add_zero]

/-- For `e = 0` or `2` a unit of `O`, `shaOdd` has as many elements as its module of classes. -/
theorem card_shaOdd_eq_card_classes (h : e = 0 ∨ IsUnit (2 : O)) :
    Nat.card (shaOdd l E O e n) = Nat.card (shaOddClasses l E O e n) := by
  rw [← Nat.card_congr (Submodule.comapSubtypeEquivOfLe (shaOdd_le_Z1 l E O e n)).toEquiv,
    (shaModule l E O e n).card_eq_card_map_π₁_mul_card_inf_B1, shaOdd_inf_B1_eq_bot h]
  simp

/-- For `2` a unit of `O`, the classes of `shaOdd` are the classes of `shaCocycles` that are odd
under `conjGal` if `e ≠ 0`: those with a representative `z` such that `g ↦ z (c g c)` and `-z`
differ by a coboundary. -/
theorem mem_shaOddClasses_iff (h_two : IsUnit (2 : O)) {c : (shaModule l E O e n).H 1} :
    c ∈ shaOddClasses l E O e n ↔
      ∃ z ∈ shaCocyclesZ1 l E O e n, (shaModule l E O e n).π₁ z = c ∧
        (e ≠ 0 → ∃ b, ∀ g : Gal(Ω/E), z.1 (conjGal g) + z.1 g =
          (shaModule l E O e n).ρ g b - b) := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨hz_coc, hz_odd⟩ := mem_shaOdd_iff_mem_shaCocycles.1 hz
    exact ⟨z, hz_coc, rfl, fun he ↦ ⟨0, fun g ↦ by
      rw [map_zero, sub_zero]
      exact eq_neg_iff_add_eq_zero.1 (hz_odd he g)⟩⟩
  · rintro ⟨z, hz, rfl, hz_odd⟩
    rcases eq_or_ne e 0 with rfl | he
    · exact ⟨z, mem_shaOdd_iff_mem_shaCocycles.2 ⟨hz, fun h ↦ absurd rfl h⟩, rfl⟩
    obtain ⟨b, hb⟩ := hz_odd he
    -- Subtract the coboundary of `b / 2`, which is even under `conjGal`.
    set b' : Unit → QuotSpan (l ^ n : O) := h_two.unit⁻¹ • b
    have hb' : (2 : O) • b' = b := by
      rw [← h_two.unit_spec, ← Units.smul_def, smul_inv_smul]
    set δ : Z1 (shaModule l E O e n).ρ :=
      coboundaryZ1 (shaModule l E O e n).continuous_orbit b'
    have hδ : δ ∈ B1 (shaModule l E O e n).ρ :=
      range_coboundaryZ1 (shaModule l E O e n).continuous_orbit ▸ LinearMap.mem_range_self _ _
    refine ⟨z - δ, mem_shaOdd_iff_mem_shaCocycles.2 ⟨sub_mem hz
      (B1_le_shaCocyclesZ1 l E O e n hδ), fun _ g ↦ ?_⟩, ?_⟩
    · have h_sum : z.1 (conjGal g) + z.1 g =
          δ.1 g + δ.1 g := by
        rw [← two_smul O, hb g, coe_coboundaryZ1_apply, smul_sub, ← map_smul, hb']
      rw [eq_neg_iff_add_eq_zero]
      show (z - δ).1 (conjGal g) +
        (z - δ).1 g = 0
      simp only [Submodule.coe_sub, Pi.sub_apply]
      rw [B1_apply_conjGal hδ, sub_add_sub_comm, h_sum, sub_self]
    · have hπδ : (shaModule l E O e n).π₁ δ = 0 :=
        LinearMap.mem_ker.1 ((shaModule l E O e n).ker_π₁ ▸ hδ)
      rw [map_sub, hπδ, sub_zero]

end New.Selmer

/-! ## The bounds of `Lib.Cyclotomic.OddSha` for classes

The classes `shaOddClasses` are the image of `shaOdd`, so the bounds on its length pass to them. -/

section OddShaClassBounds

open Module IsDiscreteValuationRing New OddPart Selmer NumberField Nat

/-- The classes of `shaOdd` are no longer than `shaOdd`. -/
lemma New.Selmer.length_shaOddClasses_le {l : ℕ} [ThePrime l] {E : Type} [Field E]
    [EmbeddedNumberField E] [IsCMField E] {O : Type} [CommRing O] [PadicIntegerRing O l]
    {e n : ℕ} : length O (shaOddClasses l E O e n) ≤ length O (shaOdd l E O e n) := by
  rw [← LinearEquiv.length_eq (R := O) (M := shaOddZ1 l E O e n) (N := shaOdd l E O e n)
    (Submodule.comapSubtypeEquivOfLe (shaOdd_le_Z1 l E O e n))]
  exact length_le_of_surjective _ (LinearMap.submoduleMap_surjective _ _)

/-- `New.length_shaOdd_zero_le_addVal_classNumber` for classes: for `e = 0` the classes of
`shaOdd` in `H¹(Gal(Ω/E), O / lⁿ)`, the everywhere unramified homomorphisms, have length at most
`addVal O (classNumber E)`. -/
lemma New.length_shaOddClasses_zero_le_addVal_classNumber (E : Type) [Field E] [NumberField E]
    [IsCMField E] [Algebra E Ω] (l : ℕ) [ThePrime l] (O : Type) [CommRing O]
    [PadicIntegerRing O l] (n : ℕ) :
    length O (shaOddClasses l E O 0 n) ≤ addVal O (classNumber E) :=
  length_shaOddClasses_le.trans (length_shaOdd_zero_le_addVal_classNumber E l O n)

/-- `New.OddPart.nsmul_shaOdd_eq_zero_of_isStickelbergerBound` for classes: under the same
hypotheses, `4 φ(N) · 4 X²` kills the classes of `shaOdd` in `H¹(Gal(Ω/E), O / lⁿ(-e))`. -/
lemma New.OddPart.nsmul_shaOddClasses_eq_zero_of_isStickelbergerBound {N : ℕ} [NeZero N]
    {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra E Ω]
    (h_sub : ∀ x : E, algebraMap E Ω x ∈ cycloField N) (l : ℕ) [ThePrime l] (O : Type)
    [CommRing O] [PadicIntegerRing O l] [HasEnoughRootsOfUnity O (Monoid.exponent (ZMod N)ˣ)]
    {e : ℕ} (he : e ≠ 0) (n : ℕ) {X : ℕ} (h_stick : IsStickelbergerBound N e X) :
    ∀ c ∈ shaOddClasses l E O e n, (4 * φ N * (4 * X * X)) • c = 0 := by
  rintro _ ⟨z, hz, rfl⟩
  have h_zero : (4 * φ N * (4 * X * X)) • z = 0 :=
    Subtype.ext (nsmul_shaOdd_eq_zero_of_isStickelbergerBound h_sub l O he n h_stick z hz)
  rw [← map_nsmul, h_zero, map_zero]

/-- `New.OddPart.length_shaOdd_le_addVal_pow` for classes: if `m` kills `shaOdd` and only `0`
vanishes at the at most `k` points `p i`, the classes of `shaOdd` have length at most the
valuation of `m ^ k`. -/
lemma New.OddPart.length_shaOddClasses_le_addVal_pow {E : Type} [Field E] [NumberField E]
    [IsCMField E] [Algebra E Ω] {l : ℕ} [ThePrime l] {O : Type} [CommRing O]
    [PadicIntegerRing O l] {e n m k : ℕ} (h_kill : ∀ z ∈ shaOdd l E O e n, m • z = 0) {ι : Type}
    [Fintype ι] (p : ι → Gal(Ω/E)) (h_card : Fintype.card ι ≤ k)
    (h_detect : ∀ z ∈ shaOdd l E O e n, (∀ i : ι, z (p i) = 0) → z = 0) :
    length O (shaOddClasses l E O e n) ≤ addVal O (m ^ k : ℕ) :=
  length_shaOddClasses_le.trans (length_shaOdd_le_addVal_pow h_kill p h_card h_detect)

/-- `New.OddPart.length_shaOdd_le_of_le_sq` for classes: for `E ⊆ ℚ(μ_N)` CM, `N ≤ y` and
`l ≤ y ^ 2`, if `m` kills `shaOdd`, its classes have length at most the valuation of
`m ^ y ^ 20`. -/
lemma New.OddPart.length_shaOddClasses_le_of_le_sq {N : ℕ} [NeZero N] {E : Type} [Field E]
    [NumberField E] [IsCMField E] [Algebra E Ω] (h_sub : ∀ x : E, algebraMap E Ω x ∈ cycloField N)
    (l : ℕ) [ThePrime l] (O : Type) [CommRing O] [PadicIntegerRing O l] (e n : ℕ) {y : ℕ}
    (hN_le : N ≤ y) (hl_le : l ≤ y ^ 2) {m : ℕ}
    (h_kill : ∀ z ∈ shaOdd l E O e n, m • z = 0) :
    length O (shaOddClasses l E O e n) ≤ addVal O (m ^ y ^ 20 : ℕ) :=
  length_shaOddClasses_le.trans (length_shaOdd_le_of_le_sq h_sub l O e n hN_le hl_le h_kill)

/-- `New.OddPart.length_shaOdd_le_of_sq_lt` for classes: under the same hypotheses (so `l` is
odd), the classes of `shaOdd` in `H¹(Gal(Ω/E), O / lⁿ(-e))` have length at most the valuation of
`(4 φ(N) · 4 X²) ^ y ^ 20`. -/
lemma New.OddPart.length_shaOddClasses_le_of_sq_lt {N : ℕ} [NeZero N] {E : Type} [Field E]
    [NumberField E] [IsCMField E] [Algebra E Ω] (h_sub : ∀ x : E, algebraMap E Ω x ∈ cycloField N)
    (l : ℕ) [ThePrime l] (O : Type) [CommRing O] [PadicIntegerRing O l]
    [HasEnoughRootsOfUnity O (Monoid.exponent (ZMod N)ˣ)] {e : ℕ} (he : e ≠ 0) (n : ℕ) {y : ℕ}
    (h_le_y : N + e + 3 ≤ y) (hl_gt : y ^ 2 < l) {X : ℕ} (hX_ne : X ≠ 0) (hX_le : X ≤ 2 ^ y ^ 6)
    (h_stick : IsStickelbergerBound N e X) :
    length O (shaOddClasses l E O e n) ≤ addVal O ((4 * φ N * (4 * X * X)) ^ y ^ 20 : ℕ) :=
  length_shaOddClasses_le.trans
    (length_shaOdd_le_of_sq_lt h_sub l O he n h_le_y hl_gt hX_ne hX_le h_stick)

/-- `New.exists_length_shaOdd_le` for classes. For a CM field `E` inside `ℚ(μ_N)` and `t : ℕ` there
is an integer `X ≠ 0`, at most `2 ^ (4 (N + t + 3) ^ 27) · h_E`, such that for each prime `l`, each
`O` with `PadicIntegerRing O l` and enough roots of unity for the characters mod `N`, and each
`e < t` and `n`, the classes of `shaOdd l E O e n` in `H¹(Gal(Ω/E), O / lⁿ(-e))` have length at
most `addVal O X`. For `l` odd these are the classes of the cocycles unramified off `l` and
vanishing on `shaLocalSet l E e` that are odd under `conjGal` (`New.Selmer.mem_shaOddClasses_iff`).
-/
lemma New.exists_length_shaOddClasses_le (N t : ℕ) [NeZero N] (E : Type) [Field E] [NumberField E]
    [IsCMField E] [Algebra E Ω] (h_sub : ∀ x : E, algebraMap E Ω x ∈ cycloField N) :
    ∃ X : ℕ, X ≠ 0 ∧
      X ≤ 2 ^ (4 * (N + t + 3) ^ 27) * classNumber E ∧
      ∀ (l : ℕ) [ThePrime l] (O : Type) [CommRing O] [PadicIntegerRing O l],
        HasEnoughRootsOfUnity O (Monoid.exponent (ZMod N)ˣ) →
        ∀ e : ℕ, e < t → ∀ n : ℕ, length O (shaOddClasses l E O e n) ≤ addVal O X := by
  obtain ⟨X, hX_ne, hX_le, hX⟩ := exists_length_shaOdd_le N t E h_sub
  exact ⟨X, hX_ne, hX_le, fun l _ O _ _ hO e he n ↦
    length_shaOddClasses_le.trans (hX l O hO e he n)⟩

end OddShaClassBounds

end
