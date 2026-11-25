module

public import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeMapFractionField
public import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeRename
import Formalism.SharpRestriction.GrowthBounds.WittFrameLocaliserOrders
public import Lemmata.ComplementLifts.ComplLift
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Algebra.Order.Antidiag.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.Order.Interval.Finset.Box
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.TypeStar
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.SelectionLemmas.Pf
section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

structure Dat (n' r : ℕ) where
  F : Frames n' r
  deg : Fin n' → ℕ
  L₁ : ℕ
  N₁ : ℕ
  Ns : ℕ
  E₀ : ℕ
  mStar : ℕ
  E' : Fin n' → ℕ
  a : ℝ
  Y : ℝ
  Q : ℝ
  CLa : ℝ
  Ck : ℝ

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

structure Hyp : Prop where
  prime : p.Prime
  even : Even n'
  p13 : 13 ≤ p
  r2 : 2 ≤ r
  valid : X.F.Valid X.L₁ X.N₁
  degs : ∀ t ∈ X.F.TT, X.a ≤ (X.deg t : ℝ) ∧ (X.deg t : ℝ) ≤ 2 * X.a
  card : ∀ j : ℤ, (X.F.letters j).card ≤ X.Ns
  NsN₁ : X.Ns ≤ X.N₁
  NsN : X.Ns ≤ 2 * X.F.TT.card
  NsK : X.Ns + r ≤ K
  twist : ∀ j : ℤ, ∀ x ∈ X.F.letters j, (p : ℝ) ^ X.F.dist j x ≤ X.Q
  Y1 : 1 ≤ X.Y
  P1 : X.Ck * (X.Ns : ℝ) ^ 2 * Real.log X.a ≤ ((r + K : ℕ) : ℝ)
  P2 : 128 * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Y ^ 2 ≤ (p : ℝ) ^ ((X.L₁ : ℤ) - 1)
  E'le : ∀ t ∈ X.F.TT, X.E' t ≤ X.E₀
  P3 : 32 * (p : ℝ) * X.Y * ((r + K : ℕ) : ℝ) ^ 2 * (X.Ns : ℝ) * X.Q ^ 2 * ((X.E₀ : ℝ) + X.mStar + 1) ≤ X.a

def k : ℝ := ((r + K : ℕ) : ℝ)

def La : ℝ := X.CLa * (X.Ns : ℝ) ^ 2 * Real.log X.a

def Bo (j x : ℤ) : ℝ :=
  (X.deg (posOf n' (X.F.oldest j x)) : ℝ) / (p : ℝ) ^ X.F.dist j (X.F.oldest j x)

def sg (j x : ℤ) : ℕ := ⌊X.Bo p j x / (k (r := r) K ^ 2 * X.Y)⌋₊

def mg (j x : ℤ) : ℤ := (X.mStar : ℤ) + (X.sg p K j x : ℤ)

def th (j x : ℤ) : ℝ := X.Bo p j x / 2

def o (j x : ℤ) : ℝ :=
  X.La * X.a / ((p : ℝ) * k (r := r) K * (p : ℝ) ^ X.F.dist j x) +
    (if Even x then (10 : ℝ) else 1) * X.a * (p : ℝ) ^ (-((X.L₁ : ℤ) + (X.F.dist j x : ℤ)))

def d : Fin n' → ℕ := fun t => if t ∈ X.F.TT then X.deg t - X.E' t else 0

variable [NeZero r] [NeZero K]

def XXs (O : Type) [CommRing O] (j : ℤ) : Submodule O (SegRing O r K) :=
  XX' O r K X.F j (X.mg p K j) (X.th p j) (X.o p K j)

def gen (O : Type) [CommRing O] : Set (RRing O n' (r + K)) := Gen O p K X.F (X.XXs p K O) X.d

def NN (O : Type) [CommRing O] : Submodule O (RRing O n' (r + K)) := Submodule.span O (X.gen p K O)

omit [NeZero n'] [NeZero r] [NeZero K] in
def bound (Crk : ℝ) : ℝ := (1 - Crk * (X.F.TT.card : ℝ) * (r : ℝ) ^ 2 * k (r := r) K / X.Y) *
    ∏ t ∈ X.F.TT, ((Nat.choose (X.deg t + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)

def NNbar (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Submodule (FF O) (RRing (FF O) n' (r + K)) :=
  Submodule.span (FF O) (MvPolynomial.map (IsLocalRing.residue O) '' X.gen p K O)

end Dat

def RestDeg : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O],
    X.Hyp p K → 0 ≤ X.CLa →
    ∀ P ∈ X.NN p K O, ∀ mm ∈ P.support,
      (vsDeg mm : ℝ) ≤ 10 * (X.F.TT.card : ℝ) *
        (X.La * X.a / ((p : ℝ) * Dat.k (r := r) K) + X.a * (p : ℝ) ^ (-(X.L₁ : ℤ)) + Dat.k (r := r) K * X.Q)

def RestSel : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (σ : Type) (s : Set (σ →₀ ℕ)), s.Finite →
    ∀ G : Set (MvPolynomial σ O), (∀ g ∈ G, g ∈ restrictSupport O s) →
    ∃ Sg : Submodule O (MvPolynomial σ O), Sg ≤ Submodule.span O G ∧
      (∃ T : Submodule O (MvPolynomial σ O), IsCompl Sg T) ∧
      (∃ (ιb : Type) (b : Module.Basis ιb O Sg), ∀ i, (b i : MvPolynomial σ O) ∈ G) ∧
      Module.finrank O Sg =
        Module.finrank (FF O) (Submodule.span (FF O) (MvPolynomial.map (IsLocalRing.residue O) '' G))

def RestRank (C₀ Crk : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * X.bound K Crk ≤ (Module.finrank (FF O) (X.NNbar p K O) : ℝ)

theorem degSet_finite (n' k : ℕ) (d : Fin n' → ℕ) :
    {m : Fin n' × Fin k →₀ ℕ | ∀ t, ∑ c : Fin k, m (t, c) = d t}.Finite := by
  have hpi : (Set.pi Set.univ fun v : Fin n' × Fin k => Set.Iic (d v.1)).Finite :=
    Set.Finite.pi fun v => Set.finite_Iic _
  refine (Set.Finite.preimage
    (f := (Finsupp.equivFunOnFinite : (Fin n' × Fin k →₀ ℕ) → (Fin n' × Fin k → ℕ)))
    (fun a _ b _ hab => Finsupp.equivFunOnFinite.injective hab) hpi).subset ?_
  intro m hm
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Iic, Finsupp.equivFunOnFinite_apply]
  intro v
  simpa using (Finset.single_le_sum (f := fun c => m (v.1, c))
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)).trans_eq (hm v.1)

theorem nonempty_dvr_setting_of_standard {p n' : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
    {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {jW : W →+* O} {w : O} (h : UnramifiedQuadraticSetting p n' W Qq O Kf ι σ jW w) :
    Nonempty (UniformizedDVR p O) := by
  obtain ⟨hS, hw, -, -⟩ := h
  have hw0 : w ≠ 0 := hw.ne_zero
  have hwm : w ∈ IsLocalRing.maximalIdeal O := by
    rw [IsLocalRing.mem_maximalIdeal]; exact hw.not_isUnit
  refine ⟨⟨w, hw, ?_, ?_, hS.complete_O⟩⟩
  · rw [← hS.w_sq]; exact Ideal.pow_mem_of_mem _ hwm 2 (by norm_num)
  · rw [← hS.w_sq]; exact pow_ne_zero 2 hw0

theorem second_estimate_of_rank_bound (D : Formalism.BasicNotions.D7) (C₀ Crk : ℝ) (hC₀ : 0 < C₀) (hCrk : 0 < Crk)
    (hDeg : RestDeg) (hSel : RestSel) (hRank : AdmB D → RestRank C₀ Crk) : SecondPartClosed D := by
  intro hAdm
  refine ⟨C₀, hC₀, fun CLa Ck hCLa hCk => ⟨Crk, 10, hCrk, by norm_num, ?_⟩⟩
  intro p n' _ W Qq O Kf _ _ _ _ _ _ _ _ _ _ ι σ jW w hSet hp13 r K _ _ hr2 F deg L₁ N₁ Ns E₀ mStar E' a Y Q
    hV hdeg hcard hNsN₁ hNsN hNsK htw hY hP1 hP2 hE' hP3
  obtain ⟨S⟩ := nonempty_dvr_setting_of_standard hSet
  let X : Dat n' r := ⟨F, deg, L₁, N₁, Ns, E₀, mStar, E', a, Y, Q, CLa, Ck⟩
  have hX : X.Hyp p K :=
    ⟨hSet.1.prime, hSet.1.even, hp13, hr2, hV, hdeg, hcard, hNsN₁, hNsN, hNsK, htw, hY, hP1, hP2, hE', hP3⟩
  have hrk := hRank hAdm p n' r K X O S hX hCLa hCk
  have hdg := hDeg p n' r K X O hX (hC₀.le.trans hCLa)
  obtain ⟨Sg, hle, hT, hb, hfr⟩ := hSel O (Fin n' × Fin (r + K)) _ (degSet_finite n' (r + K) X.d) (X.gen p K O)
    (fun g hg => by obtain ⟨x, -, l, -, -, h⟩ := hg; exact h)
  have hrk' : ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * X.bound K Crk ≤ (Module.finrank O Sg : ℝ) := by
    rw [hfr]; exact hrk
  refine ⟨⟨Sg, hle, hT, hb, hrk', ?_⟩, hdg⟩
  intro FFq _ _ hcardF
  have h6 : Fintype.card FFq ^ (r * (r + K - r)) ≤ nPl FFq (r + K) r :=
    hAdm.2.2.2.2.2.1 FFq (r + K) r (Nat.le_add_right r K)
  rw [hcardF, Nat.add_sub_cancel_left] at h6
  have hq : (0 : ℝ) < ((p : ℝ) ^ n') ^ (r * K) := by
    have : (0 : ℝ) < p := by exact_mod_cast hSet.1.prime.pos
    positivity
  have h6' : ((p : ℝ) ^ n') ^ (r * K) ≤ (nPl FFq (r + K) r : ℝ) := by exact_mod_cast h6
  have hn : (0 : ℝ) < (nPl FFq (r + K) r : ℝ) := lt_of_lt_of_le hq h6'
  rcases le_or_gt (X.bound K Crk) 0 with hb0 | hb0
  · exact le_trans (div_nonpos_of_nonpos_of_nonneg hb0 hn.le) (Nat.cast_nonneg _)
  · refine le_trans ?_ hrk'
    rw [zpow_neg, zpow_natCast, div_eq_inv_mul]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hq h6') hb0.le

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

open Classical in
def toLate (j : ℤ) : Finset ℤ := (X.F.letters j).filter fun x => ¬ X.F.IsW j x

open Classical in
def row (j x : ℤ) (i : Fin r) : ℤ :=
  let l := ((X.F.letters j).filter fun z => Even z ∧ z < x).sort (· ≤ ·)
  l.getD (l.length - r + i.val) 0

def detPl (O : Type) [CommRing O] (j x : ℤ) : MvPolynomial (ℤ × Fin r) O :=
  Matrix.det (Matrix.of fun a b : Fin r => (MvPolynomial.X (X.row j x a, b) : MvPolynomial (ℤ × Fin r) O))

def DlSeg (O : Type) [CommRing O] (j : ℤ) : MvPolynomial (ℤ × Fin r) O :=
  ∏ x ∈ X.toLate j, X.detPl O j x ^ X.sg p K j x

def Dl (O : Type) [CommRing O] : RRing O n' (r + K) :=
  ∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (plEmb O r K (X.DlSeg p K O j))

def Et (t : Fin n') : ℕ :=
  ∑ j ∈ Finset.range X.F.J, ∑ x ∈ X.toLate j, X.sg p K j x *
    ∑ i : Fin r, if posOf n' (X.row j x i) = t then p ^ X.F.dist j (X.row j x i) else 0

def a' (t : Fin n') : ℕ := X.d t - X.Et p K t

def Rj (j : ℤ) : ℕ :=
  Nat.log p ⌊X.a / (8 * X.Y * k (r := r) K ^ 2 * (X.Ns : ℝ) * (p : ℝ) ^ X.F.dist j (X.F.fr (j - 1) 0))⌋₊

def Qc (j : ℤ) : ℕ :=
  p ^ (X.F.fr (j + 1) (r - 1) - X.F.fr j (r - 1) + (X.Rj p K (j + 1) : ℤ) - (X.Rj p K j : ℤ)).toNat

def m0 : ℕ := (r + K) * X.Ns + 1

def phc (O : Type) [CommRing O] (j : ℤ) : SegRing O r K →ₐ[O] RRing O n' (r + K) :=
  aeval fun v => MvPolynomial.X (posOf n' v.1, v.2) ^ (p ^ (X.F.dist j v.1 + X.Rj p K j))

def IsCLabel (l : Fin n' × Fin (r + K) →₀ ℕ) : Prop :=
  ∀ j : ℤ, ∀ x ∈ X.F.letters j, ¬ X.F.IsW j x → ∀ c, l (posOf n' x, c) < p ^ (X.F.dist j x + X.Rj p K j)

def resSet (j : ℤ) : Set (ℤ × Fin (r + K) →₀ ℕ) :=
  {m | ∀ i < r, ∀ c : Fin r, m (X.F.fr j i, Fin.castAdd K c) < X.Qc p K j}

def segDegSet (b : ℤ → ℕ) : Set (ℤ × Fin (r + K) →₀ ℕ) := {m | ∀ x, ∑ c : Fin (r + K), m (x, c) = b x}

def Bw (j y : ℤ) : ℤ :=
  ((X.a' p K (posOf n' y) / p ^ (X.F.dist j y + X.Rj p K j) : ℕ) : ℤ) - ((r + K + r + 1 : ℕ) : ℤ)

open Classical in
def thc (j : ℤ) (b : ℤ → ℕ) (x : ℤ) : ℝ :=
  (2 / 3) * (if X.F.IsW j (X.F.oldest j x) then ((X.Bw p K j (X.F.oldest j x) - (X.m0 K : ℤ) : ℤ) : ℝ)
    else (b (X.F.oldest j x) : ℝ))

def oc (j x : ℤ) : ℝ :=
  X.La * X.a / ((p : ℝ) * k (r := r) K * (p : ℝ) ^ (X.F.dist j x + X.Rj p K j)) +
    (if Even x then 4 * X.a * (p : ℝ) ^ (-((X.F.dist j (X.F.oldest j x) : ℤ) + (X.Rj p K j : ℤ))) else 0)

variable [NeZero r] [NeZero K]

def Mj (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ) : Submodule O (SegRing O r K) :=
  XX' O r K X.F j (fun _ => (X.m0 K : ℤ)) (X.thc p K j b) (X.oc p K j) ⊓
    restrictSupport O (segDegSet (r := r) K b) ⊓ restrictSupport O (X.resSet p K j)

def lamGen (O : Type) [CommRing O] : Set (RRing O n' (r + K)) :=
  {u | ∃ (b : ℤ → ℤ → ℕ) (y : ℤ → SegRing O r K) (l : Fin n' × Fin (r + K) →₀ ℕ),
      (∀ j, y j ∈ X.Mj p K O j (b j)) ∧ X.IsCLabel p K l ∧
      u = (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y j)) * monomial l 1 ∧
      u ∈ RRdeg O n' (r + K) (X.a' p K)}

def LamBar (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Submodule (FF O) (RRing (FF O) n' (r + K)) :=
  Submodule.span (FF O) (MvPolynomial.map (IsLocalRing.residue O) '' X.lamGen p K O)

end Dat

def DiscriminantNonzeroModUniformiser : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], X.Hyp p K →
    MvPolynomial.map (IsLocalRing.residue O) (X.Dl p K O) ≠ 0

def GeneratorModuloUniformiser (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ u ∈ X.lamGen p K O, ∃ g ∈ X.gen p K O,
      MvPolynomial.map (IsLocalRing.residue O) (X.Dl p K O * u) = MvPolynomial.map (IsLocalRing.residue O) g

def RestCount (C₀ Crk : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * X.bound K Crk ≤ (Module.finrank (FF O) (X.LamBar p K O) : ℝ)

theorem finite_restrictSupport (Fd : Type) [Field Fd] (σ : Type) (s : Set (σ →₀ ℕ)) (hs : s.Finite) :
    Module.Finite Fd (restrictSupport Fd s : Submodule Fd (MvPolynomial σ Fd)) := by
  have hle : (restrictSupport Fd s : Submodule Fd (MvPolynomial σ Fd)) ≤
      Submodule.span Fd ((fun m => (monomial m (1 : Fd) : MvPolynomial σ Fd)) '' s) := by
    intro P hP
    rw [MvPolynomial.mem_restrictSupport_iff] at hP
    rw [P.as_sum]
    refine Submodule.sum_mem _ fun m hm => ?_
    have : (monomial m (AddMonoidAlgebra.coeff P m) : MvPolynomial σ Fd) = AddMonoidAlgebra.coeff P m • monomial m (1 : Fd) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hP (by exact_mod_cast hm), rfl⟩)
  have : Module.Finite Fd (Submodule.span Fd ((fun m => (monomial m (1 : Fd) : MvPolynomial σ Fd)) '' s)) :=
    FiniteDimensional.span_of_finite Fd (hs.image _)
  exact Submodule.finiteDimensional_of_le hle

theorem map_mem_restrictSupport {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {σ : Type} (s : Set (σ →₀ ℕ))
    {P : MvPolynomial σ R} (hP : P ∈ restrictSupport R s) : MvPolynomial.map f P ∈ restrictSupport S s := by
  rw [MvPolynomial.mem_restrictSupport_iff] at hP ⊢
  intro m hm
  exact hP (by exact_mod_cast MvPolynomial.support_map_subset f P (by exact_mod_cast hm))

theorem restRank_of (C₀ Crk : ℝ) (h1 : DiscriminantNonzeroModUniformiser) (h5 : GeneratorModuloUniformiser C₀) (hc : RestCount C₀ Crk) : RestRank C₀ Crk := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk
  refine le_trans (hc p n' r K X O S hX hLa hk) ?_
  have hD := h1 p n' r K X O hX
  have h45 := h5 p n' r K X O S hX hLa hk
  set res := MvPolynomial.map (σ := Fin n' × Fin (r + K)) (IsLocalRing.residue O) with hres
  let f : RRing (FF O) n' (r + K) →ₗ[FF O] RRing (FF O) n' (r + K) := LinearMap.mulLeft (FF O) (res (X.Dl p K O))
  have hf : Function.Injective f := by
    intro a b hab
    exact mul_left_cancel₀ hD hab
  have hmap : (X.LamBar p K O).map f ≤ X.NNbar p K O := by
    unfold Dat.LamBar
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    obtain ⟨g, hg, hgu⟩ := h45 u hu
    have : f (res u) = res g := by
      rw [← hgu]; simp [f, hres]
    rw [this]
    exact Submodule.subset_span ⟨g, hg, rfl⟩
  have hfin : Module.Finite (FF O) (X.NNbar p K O) := by
    have := finite_restrictSupport (FF O) _ _ (degSet_finite n' (r + K) X.d)
    refine Submodule.finiteDimensional_of_le
      (S₂ := restrictSupport (FF O) {m : Fin n' × Fin (r + K) →₀ ℕ | ∀ t, ∑ c : Fin (r + K), m (t, c) = X.d t}) ?_
    unfold Dat.NNbar
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨x, -, l, -, -, h⟩ := hg
    exact map_mem_restrictSupport _ _ h
  have h1' : Module.finrank (FF O) ((X.LamBar p K O).map f) = Module.finrank (FF O) (X.LamBar p K O) :=
    (Submodule.equivMapOfInjective f hf (X.LamBar p K O)).finrank_eq.symm
  have h2 := Submodule.finrank_mono hmap
  rw [h1'] at h2
  exact_mod_cast h2

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def zSeg (O : Type) [CommRing O] (j : ℤ) (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ) : SegRing O r K :=
  plEmb O r K (X.DlSeg p K O j) * expand (p ^ X.Rj p K j) y * monomial e 1

def IsEll (j : ℤ) (e : ℤ × Fin (r + K) →₀ ℕ) : Prop :=
  (∀ v, e v ≠ 0 → v.1 ∈ X.toLate j) ∧ ∀ v, e v < p ^ X.Rj p K j

def Step2 (j : ℤ) (b : ℤ → ℕ) : Prop :=
  ∀ z ∈ X.F.LLset j,
    (X.a' p K (posOf n' z) : ℝ) / (p : ℝ) ^ (X.F.dist j z + X.Rj p K j) - k (r := r) K < (b z : ℝ)

end Dat

def CoarseLabelFactorisation : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O],
    X.Hyp p K → ∀ l, X.IsCLabel p K l →
    ∃ (l0 : Fin n' × Fin (r + K) →₀ ℕ) (e : ℤ → (ℤ × Fin (r + K) →₀ ℕ)), IsLabel p X.F l0 ∧
      (∀ j, X.IsEll p K j (e j)) ∧
      (monomial l 1 : RRing O n' (r + K)) =
        monomial l0 1 * ∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (monomial (e j) 1)

def TopDegreeComparison : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O],
    X.Hyp p K → ∀ (b : ℤ → ℤ → ℕ) (y : ℤ → SegRing O r K) (l : Fin n' × Fin (r + K) →₀ ℕ),
      (∀ j, y j ∈ X.Mj p K O j (b j)) → X.IsCLabel p K l →
      (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y j)) * monomial l 1 ∈ RRdeg O n' (r + K) (X.a' p K) →
      (∏ j ∈ Finset.range X.F.J, X.phc p K O (j : ℤ) (y j)) * monomial l 1 ≠ 0 →
      ∀ j ∈ Finset.range X.F.J, X.Step2 p K (j : ℤ) (b j)

def DiscriminantMultihomogeneous : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O],
    X.Dl p K O ∈ RRdeg O n' (r + K) (X.Et p K)

def DiscriminantNeZero : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], X.Hyp p K → X.Dl p K O ≠ 0

theorem discriminant_ne_zero_of_residue_ne_zero (h : DiscriminantNonzeroModUniformiser) : DiscriminantNeZero := by
  intro p n' r K _ _ _ X O _ _ _ hX h0
  exact h p n' r K X O hX (by rw [h0, map_zero])

def TopCountLowerBounds (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    (∀ t ∈ X.F.TT, (9 / 10 : ℝ) * (X.deg t : ℝ) ≤ (X.a' p K t : ℝ)) ∧ ∀ t, X.Et p K t ≤ X.d t

def SegmentReductionLiftsMultihomogeneous (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ) (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ),
      y ∈ X.Mj p K O j b → X.IsEll p K j e → X.Step2 p K j b →
      ∀ β : ℤ → ℕ, X.zSeg p K O j y e ∈ Pol O (r + K) β →
      ∃ x ∈ X.XXs p K O j, x ∈ Pol O (r + K) β ∧
        MvPolynomial.map (IsLocalRing.residue O) x = MvPolynomial.map (IsLocalRing.residue O) (X.zSeg p K O j y e)

def SegmentImageMultihomogeneous : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O]
    (j : ℤ) (b : ℤ → ℕ) (y : SegRing O r K) (e : ℤ × Fin (r + K) →₀ ℕ),
    y ∈ Pol O (r + K) b → ∃ β : ℤ → ℕ, X.zSeg p K O j y e ∈ Pol O (r + K) β

def SegmentProductDegreeDetermined : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] (F : Frames n' r) (O : Type) [CommRing O]
    (x z : ℤ → SegRing O r K) (β : ℤ → ℤ → ℕ) (l0 : Fin n' × Fin (r + K) →₀ ℕ) (d : Fin n' → ℕ),
    (∀ j, x j ∈ Pol O (r + K) (β j)) → (∀ j, z j ∈ Pol O (r + K) (β j)) →
    (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (z j)) * monomial l0 1 ∈ RRdeg O n' (r + K) d →
    (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (z j)) * monomial l0 1 ≠ 0 →
    (∏ j ∈ Finset.range F.J, phSeg O K p F (j : ℤ) (x j)) * monomial l0 1 ∈ RRdeg O n' (r + K) d

theorem RRdeg_eq_Pol (O : Type) [CommRing O] (n' k : ℕ) (d : Fin n' → ℕ) : RRdeg O n' k d = Pol O k d := rfl

theorem segDeg_eq_Pol (O : Type) [CommRing O] (r K : ℕ) (b : ℤ → ℕ) :
    restrictSupport O (Dat.segDegSet (r := r) K b) = Pol O (r + K) b := rfl

theorem map_phSeg {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (K p : ℕ) {n' r : ℕ} [NeZero n']
    (F : Frames n' r) (j : ℤ) (P : SegRing R r K) :
    MvPolynomial.map f (phSeg R K p F j P) = phSeg S K p F j (MvPolynomial.map f P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [phSeg]
  | add u v hu hv => simp only [map_add (f := _), hu, hv]
  | mul_X q v h =>
    simp only [map_mul, h, map_X]
    simp [phSeg]

theorem phc_eq {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) (O : Type) [CommRing O] (j : ℤ) (y : SegRing O r K) :
    X.phc p K O j y = phSeg O K p X.F j (expand (p ^ X.Rj p K j) y) := by
  have : X.phc p K O j = (phSeg O K p X.F j).comp (expand (p ^ X.Rj p K j)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp only [Dat.phc, phSeg, AlgHom.comp_apply, expand_X, aeval_X, map_pow]
    rw [← pow_mul, ← pow_add]
  rw [this]; rfl

theorem generator_of_segment_reductions (C₀ : ℝ) (hLab : CoarseLabelFactorisation) (hDeg2 : TopDegreeComparison) (hDlHom : DiscriminantMultihomogeneous) (hDlNe : DiscriminantNeZero)
    (h41b : TopCountLowerBounds C₀) (hSeg : SegmentReductionLiftsMultihomogeneous C₀) (hZ : SegmentImageMultihomogeneous) (hHom : SegmentProductDegreeDetermined) : GeneratorModuloUniformiser C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk u hu
  obtain ⟨b, y, l, hy, hl, hueq, hdeg⟩ := hu
  have hJ : 1 ≤ X.F.J := hX.valid.1
  have hp0 : 0 < p := hX.prime.pos
  by_cases hu0 : u = 0
  · refine ⟨0, ⟨fun _ => 0, fun _ => Submodule.zero_mem _, 0, ?_, ?_, Submodule.zero_mem _⟩, by simp [hu0]⟩
    · intro j x _ _ c
      simpa using Nat.pow_pos hp0
    · have h0 : (∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) ((fun _ : ℤ => (0 : SegRing O r K)) (j : ℤ))) = 0 :=
        Finset.prod_eq_zero (i := 0) (Finset.mem_range.mpr hJ) (map_zero _)
      rw [h0, zero_mul]
  obtain ⟨l0, e, hl0, he, hmon⟩ := hLab p n' r K X O hX l hl
  set z : ℤ → SegRing O r K := fun j => X.zSeg p K O j (y j) (e j) with hz
  have hDu : X.Dl p K O * u = (∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (z j)) * monomial l0 1 := by
    rw [hueq, hmon]
    simp only [hz, Dat.zSeg, Dat.Dl, map_mul, Finset.prod_mul_distrib, phc_eq]
    ring
  have hβ : ∀ j, ∃ β : ℤ → ℕ, z j ∈ Pol O (r + K) β := fun j =>
    hZ p n' r K X O j (b j) (y j) (e j) (by rw [← segDeg_eq_Pol]; exact (hy j).1.2)
  choose β hβ using hβ
  have h2 := hDeg2 p n' r K X O hX b y l hy hl (hueq ▸ hdeg) (hueq ▸ hu0)
  have hx : ∀ j : ℤ, ∃ x, x ∈ X.XXs p K O j ∧ x ∈ Pol O (r + K) (β j) ∧
      ((∃ i ∈ Finset.range X.F.J, (i : ℤ) = j) →
        MvPolynomial.map (IsLocalRing.residue O) x = MvPolynomial.map (IsLocalRing.residue O) (z j)) := by
    intro j
    by_cases hj : ∃ i ∈ Finset.range X.F.J, (i : ℤ) = j
    · obtain ⟨i, hi, rfl⟩ := hj
      obtain ⟨x, h1, h2', h3⟩ := hSeg p n' r K X O S hX hLa hk (i : ℤ) (b i) (y i) (e i) (hy i) (he i) (h2 i hi)
        (β i) (hβ i)
      exact ⟨x, h1, h2', fun _ => h3⟩
    · exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, fun h => absurd h hj⟩
  choose x hx1 hx2 hx3 using hx
  have hsum : X.Et p K + X.a' p K = X.d := by
    funext t
    have := (h41b p n' r K X hX hLa hk).2 t
    simp only [Pi.add_apply, Dat.a']
    omega
  have hDdeg : X.Dl p K O * u ∈ RRdeg O n' (r + K) X.d := by
    have h1 : X.Dl p K O ∈ Pol O (r + K) (X.Et p K) := by
      rw [← RRdeg_eq_Pol]; exact hDlHom p n' r K X O
    have h2 : u ∈ Pol O (r + K) (X.a' p K) := by
      rw [← RRdeg_eq_Pol]; exact hdeg
    have := hom_Pol_mul O h1 h2
    rw [hsum] at this
    rw [RRdeg_eq_Pol]
    exact this
  have hDne : X.Dl p K O * u ≠ 0 := mul_ne_zero (hDlNe p n' r K X O hX) hu0
  refine ⟨(∏ j ∈ Finset.range X.F.J, phSeg O K p X.F (j : ℤ) (x j)) * monomial l0 1,
    ⟨x, hx1, l0, hl0, rfl, ?_⟩, ?_⟩
  · exact hHom p n' r K X.F O x z β l0 X.d hx2 hβ (hDu ▸ hDdeg) (hDu ▸ hDne)
  · rw [hDu]
    simp only [map_mul, map_prod, map_phSeg]
    rw [Finset.prod_congr rfl fun i hi => by rw [← hx3 (i : ℤ) ⟨i, hi, rfl⟩]]

end

open Finset

theorem sum_card_tuples (k n : ℕ) (hk : 0 < k) :
    (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).card = (n + k - 1).choose (k - 1) := by
  have h1 : (Finset.piAntidiag (Finset.univ : Finset (Fin k)) n).card =
      ((Finset.univ : Finset (Fin k)).finsuppAntidiag n).card := by
    refine Finset.card_bij' (fun f _ => Finsupp.equivFunOnFinite.symm f) (fun f _ => ⇑f) ?_ ?_ ?_ ?_ <;>
      simp [Finset.mem_finsuppAntidiag]
  rw [h1, Finset.card_finsuppAntidiag_nat_eq_choose, Finset.card_univ, Fintype.card_fin]
  have h2 : k + n - 1 = n + (k - 1) := by omega
  have h3 : n + k - 1 = n + (k - 1) := by omega
  rw [h2, h3]
  exact Nat.choose_symm_add

theorem sum_digit_count (k n P : ℕ) (hk : 0 < k) (hP : 0 < P) (S : Finset (Fin k → ℕ))
    (hS : ∀ v : Fin k → ℕ, (∀ c, v c < P) → ∑ c, v c ≤ n → (∑ c, v c) % P = n % P → v ∈ S) :
    (n + k - 1).choose (k - 1) ≤ ∑ v ∈ S, ((n - ∑ c, v c) / P + k - 1).choose (k - 1) := by
  classical
  rw [← sum_card_tuples k n hk]
  have hdec : ∀ w : Fin k → ℕ, ∑ c, w c = P * ∑ c, w c / P + ∑ c, w c % P := by
    intro w
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => (Nat.div_add_mod (w c) P).symm
  have hmaps : ∀ w ∈ Finset.piAntidiag (Finset.univ : Finset (Fin k)) n, (fun c => w c % P) ∈ S := by
    intro w hw
    have hw' : ∑ c, w c = n := by simpa using hw
    have hd := hdec w
    refine hS _ (fun c => Nat.mod_lt _ hP) ?_ ?_
    · rw [← hw', hd]; exact Nat.le_add_left _ _
    · rw [← hw', hd, Nat.mul_add_mod]
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [← sum_card_tuples k _ hk]
  refine Finset.card_le_card_of_injOn (fun w c => w c / P) ?_ ?_
  · intro w hw
    have hw1 := Finset.mem_filter.mp (Finset.mem_coe.mp hw)
    have hw' : ∑ c, w c = n := by simpa using hw1.1
    have hv : (fun c => w c % P) = v := hw1.2
    have hd := hdec w
    have hv' : ∑ c, w c % P = ∑ c, v c := by rw [← hv]
    simp only [Finset.mem_coe, Finset.mem_piAntidiag, Finset.mem_univ, implies_true, and_true]
    rw [← hw', hd, hv', Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hP]
  · intro w hw w' hw' hww
    have hw1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hw)).2
    have hw2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hw')).2
    funext c
    have e1 := congrFun hww c
    have e2 := congrFun (hw1.trans hw2.symm) c
    simp only at e1 e2
    rw [← Nat.div_add_mod (w c) P, ← Nat.div_add_mod (w' c) P, e1, e2]

theorem sum_label_count (k n P : ℕ) (hk : 0 < k) (hP : 0 < P) (hn : k * P ≤ n) (S : Finset (Fin k → ℕ))
    (hS : ∀ v : Fin k → ℕ, (∀ c, v c < P) → ∑ c, v c ≤ n → (∑ c, v c) % P = n % P → v ∈ S) :
    P ^ (k - 1) ≤ S.card := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hc : (Finset.univ : Finset (Fin m → Fin P)).card = P ^ (m + 1 - 1) := by
    simp
  rw [← hc]
  let g : (Fin m → Fin P) → (Fin (m + 1) → ℕ) := fun u =>
    Fin.cons ((n + (P - 1) * ∑ i, (u i : ℕ)) % P) (fun i => (u i : ℕ))
  refine Finset.card_le_card_of_injOn g ?_ ?_
  · intro u _
    have hlt : ∀ c, g u c < P := by
      intro c
      refine Fin.cases ?_ (fun i => ?_) c
      · simp only [g, Fin.cons_zero]; exact Nat.mod_lt _ hP
      · simp only [g, Fin.cons_succ]; exact (u i).isLt
    refine Finset.mem_coe.mpr (hS _ hlt ?_ ?_)
    · calc ∑ c, g u c ≤ ∑ _c : Fin (m + 1), P := Finset.sum_le_sum fun c _ => (hlt c).le
        _ = (m + 1) * P := by simp
        _ ≤ n := hn
    · rw [Fin.sum_univ_succ]
      simp only [g, Fin.cons_zero, Fin.cons_succ]
      set s := ∑ i, (u i : ℕ)
      rw [Nat.mod_add_mod]
      have : n + (P - 1) * s + s = n + P * s := by
        obtain ⟨P', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hP.ne'
        simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
        ring
      rw [this, Nat.add_mul_mod_self_left]
  · intro u _ u' _ huu
    funext i
    have := congrFun huu i.succ
    simp only [g, Fin.cons_succ] at this
    exact Fin.ext this

theorem factorial_mul_choose_eq_prod_range (x M : ℕ) :
    ((M.factorial : ℕ) : ℝ) * (((x + M).choose M : ℕ) : ℝ) = ∏ l ∈ Finset.range M, ((x : ℝ) + 1 + l) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose x M
  rw [Nat.ascFactorial_eq_prod_range] at h
  have h' : ((∏ i ∈ Finset.range M, (x + 1 + i) : ℕ) : ℝ) = ((M.factorial * (x + M).choose M : ℕ) : ℝ) := by
    rw [h]
  push_cast at h'
  rw [← h']

theorem choose_add_mul_one_sub_le_pow_mul_choose_add (x y M : ℕ) (s θ : ℝ) (h1 : θ ≤ 1)
    (h : ∀ l < M, ((y : ℝ) + 1 + l) * (1 - θ) ≤ s * ((x : ℝ) + 1 + l)) :
    (((y + M).choose M : ℕ) : ℝ) * (1 - M * θ) ≤ s ^ M * (((x + M).choose M : ℕ) : ℝ) := by
  have hf : (0 : ℝ) < (M.factorial : ℝ) := by exact_mod_cast M.factorial_pos
  have hb : 1 - (M : ℝ) * θ ≤ (1 - θ) ^ M := by
    have := one_add_mul_le_pow (a := -θ) (by linarith) M
    calc 1 - (M : ℝ) * θ = 1 + (M : ℝ) * (-θ) := by ring
      _ ≤ (1 + -θ) ^ M := this
      _ = (1 - θ) ^ M := by ring_nf
  have hy : (0 : ℝ) ≤ (((y + M).choose M : ℕ) : ℝ) := Nat.cast_nonneg _
  refine le_trans (mul_le_mul_of_nonneg_left hb hy) ?_
  refine le_of_mul_le_mul_left ?_ hf
  have e1 : (M.factorial : ℝ) * ((((y + M).choose M : ℕ) : ℝ) * (1 - θ) ^ M) =
      ∏ l ∈ Finset.range M, (((y : ℝ) + 1 + l) * (1 - θ)) := by
    rw [← mul_assoc, factorial_mul_choose_eq_prod_range, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
  have e2 : (M.factorial : ℝ) * (s ^ M * (((x + M).choose M : ℕ) : ℝ)) =
      ∏ l ∈ Finset.range M, (s * ((x : ℝ) + 1 + l)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← factorial_mul_choose_eq_prod_range]
    ring
  rw [e1, e2]
  refine Finset.prod_le_prod₀ (fun l _ => ?_) fun l hl => h l (Finset.mem_range.mp hl)
  have : (0 : ℝ) ≤ (y : ℝ) + 1 + l := by positivity
  exact mul_nonneg this (by linarith)

theorem prod_range_shift_of_periodic (φ : ℤ → ℝ) (J : ℕ) (hJ : 1 ≤ J) (hφ : ∀ j, φ (j + J) = φ j) :
    ∏ j ∈ Finset.range J, φ ((j : ℤ) + 1) = ∏ j ∈ Finset.range J, φ (j : ℤ) := by
  obtain ⟨J', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : J ≠ 0)
  rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun j : ℕ => φ (j : ℤ))]
  have h := hφ 0
  push_cast at h ⊢
  rw [zero_add] at h
  rw [h]

end Formalism.MainNotions.SelectionLemmas.Pf

namespace Formalism.MainNotions.SelectionLemmas.Pf.TE

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Dict

variable {n' r : ℕ} [NeZero n'] [NeZero r] (F : Frames n' r) (j : ℤ) {L₁ N₁ : ℕ}

omit [NeZero r] in
theorem idx_card (i : Fin (segN F j)) : ((F.letters j).filter (· < segE F j i)).card = i.val := by
  classical
  have hIio : (Finset.univ.filter (· < i) : Finset (Fin (segN F j))) = Finset.Iio i := by
    ext k
    simp
  have hfe : (F.letters j).filter (· < segE F j i) =
      (Finset.univ.filter (· < i)).image
        (fun k : Fin (segN F j) => (((F.letters j).orderIsoOfFin rfl k : {x // x ∈ F.letters j}) : ℤ)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hx, hlt⟩
      refine ⟨((F.letters j).orderIsoOfFin rfl).symm ⟨x, hx⟩, ?_, by simp⟩
      exact (OrderIso.symm_apply_lt _).mpr hlt
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(((F.letters j).orderIsoOfFin rfl) k).2, ((F.letters j).orderIsoOfFin rfl).strictMono hk⟩
  have hinj : Function.Injective
      (fun k : Fin (segN F j) => (((F.letters j).orderIsoOfFin rfl k : {x // x ∈ F.letters j}) : ℤ)) :=
    fun a b h => (OrderIso.injective _) (Subtype.ext h)
  rw [hfe, Finset.card_image_of_injective _ hinj, hIio, Fin.card_Iio]

variable {F} {j}

omit [NeZero r] in
theorem fr_lt (hV : F.Valid L₁ N₁) (J : ℤ) : ∀ i i', i < i' → i' < r → F.fr J i < F.fr J i' := by
  apply _root_.Formalism.MainNotions.G.WittFrameLocaliserOrders.frame_entries_strictMono <;> assumption

omit [NeZero r] in
theorem fr_le (hV : F.Valid L₁ N₁) (J : ℤ) (i i' : ℕ) (h : i ≤ i') (hr : i' < r) : F.fr J i ≤ F.fr J i' := by
  rcases Nat.eq_or_lt_of_le h with rfl | h'
  · exact le_rfl
  · exact le_of_lt (fr_lt hV J i i' h' hr)

omit [NeZero r] in
theorem fr_inj (hV : F.Valid L₁ N₁) (J : ℤ) (i i' : ℕ) (hi : i < r) (hi' : i' < r) (h : F.fr J i = F.fr J i') :
    i = i' := by
  rcases lt_trichotomy i i' with h1 | h1 | h1
  · exact absurd h (ne_of_lt (fr_lt hV J i i' h1 hi'))
  · exact h1
  · exact absurd h (ne_of_gt (fr_lt hV J i' i h1 hi))

theorem fr_prev_lt (hV : F.Valid L₁ N₁) (j : ℤ) : F.fr (j - 1) (r - 1) < F.fr j 0 := by
  obtain ⟨_, _, _, hnext, _⟩ := id hV
  have := hnext (j - 1)
  rwa [sub_add_cancel] at this

theorem frj_mem (hV : F.Valid L₁ N₁) (j : ℤ) (i' : ℕ) (h : i' < r) : F.fr j i' ∈ F.letters j := by
  obtain ⟨_, _, _, _, hTT, _⟩ := id hV
  unfold Frames.letters
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, fr_le hV j i' (r - 1) (by omega) (by omega)⟩, (hTT j i' h).1⟩
  have h1 := fr_le hV (j - 1) 0 (r - 1) (by omega) (by omega)
  have h2 := fr_prev_lt hV j
  have h3 := fr_le hV j 0 i' (by omega) h
  linarith

theorem frp_mem (hV : F.Valid L₁ N₁) (j : ℤ) (i' : ℕ) (h : i' < r) : F.fr (j - 1) i' ∈ F.letters j := by
  obtain ⟨_, _, _, _, hTT, _⟩ := id hV
  unfold Frames.letters
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨fr_le hV (j - 1) 0 i' (by omega) h, ?_⟩, (hTT (j - 1) i' h).1⟩
  have h1 := fr_le hV (j - 1) i' (r - 1) (by omega) (by omega)
  have h2 := fr_prev_lt hV j
  have h3 := fr_le hV j 0 (r - 1) (by omega) (by omega)
  linarith

private theorem segE_lt_lemma_7 (J : ℤ) {a b : Fin (segN F J)} : segE F J a < segE F J b ↔ a < b := by
  unfold segE
  rw [Subtype.coe_lt_coe]
  exact OrderIso.lt_iff_lt _

private theorem segE_le_lemma_8 (J : ℤ) {a b : Fin (segN F J)} : segE F J a ≤ segE F J b ↔ a ≤ b := by
  unfold segE
  rw [Subtype.coe_le_coe]
  exact OrderIso.le_iff_le _

private theorem segE_surj_lemma_9 (J : ℤ) {x : ℤ} (hx : x ∈ F.letters J) : ∃ k : Fin (segN F J), segE F J k = x :=
  ⟨((F.letters J).orderIsoOfFin rfl).symm ⟨x, hx⟩, by unfold segE; simp⟩

private theorem segE_inj_lemma_10 (J : ℤ) : Function.Injective (segE F J) := by
  intro a b h
  rcases lt_trichotomy a b with h' | h' | h'
  · exact absurd h (ne_of_lt ((segE_lt_lemma_7 J).mpr h'))
  · exact h'
  · exact absurd h (ne_of_gt ((segE_lt_lemma_7 J).mpr h'))

private theorem gap_lemma_2 (hV : F.Valid L₁ N₁) (J : ℤ) : ∀ k, k < r → ∀ x, F.fr J 0 ≤ x → x < F.fr J k →
    posOf n' x ∈ F.TT → ∃ m < k, x = F.fr J m := by
  obtain ⟨_, _, _, _, _, hgap, _⟩ := id hV
  intro k
  induction k with
  | zero =>
    intro _ x h1 h2 _
    exact absurd h2 (not_lt.mpr h1)
  | succ k ih =>
    intro hk x h1 h2 hx
    rcases lt_trichotomy x (F.fr J k) with h3 | h3 | h3
    · obtain ⟨m, hm, hxm⟩ := ih (by omega) x h1 h3 hx
      exact ⟨m, by omega, hxm⟩
    · exact ⟨k, by omega, h3⟩
    · exact absurd hx (hgap J k x hk h3 h2)

private theorem countW_lemma_3 (hV : F.Valid L₁ N₁) (J : ℤ) (i' : ℕ) (hi' : i' < r) :
    ((F.letters J).filter (· < F.fr (J - 1) i')).card = i' := by
  have hfe : (F.letters J).filter (· < F.fr (J - 1) i') = (Finset.range i').image (F.fr (J - 1)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hx, hlt⟩
      unfold Frames.letters at hx
      rw [Finset.mem_filter, Finset.mem_Icc] at hx
      obtain ⟨m, hm, hxm⟩ := gap_lemma_2 hV (J - 1) i' hi' x hx.1.1 hlt hx.2
      exact ⟨m, hm, hxm.symm⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨frp_mem hV J m (by omega), fr_lt hV (J - 1) m i' hm hi'⟩
  rw [hfe, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  exact fr_inj hV (J - 1) a b (by omega) (by omega) hab

private theorem countT_lemma_4 (hV : F.Valid L₁ N₁) (J : ℤ) (i' : ℕ) (hi' : i' < r) :
    ((F.letters J).filter (F.fr J i' ≤ ·)).card = r - i' := by
  have hfe : (F.letters J).filter (F.fr J i' ≤ ·) = (Finset.Ico i' r).image (F.fr J) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨hx, hle⟩
      unfold Frames.letters at hx
      rw [Finset.mem_filter, Finset.mem_Icc] at hx
      rcases lt_or_eq_of_le hx.1.2 with hlt | heq
      · obtain ⟨m, hm, hxm⟩ := gap_lemma_2 hV J (r - 1) (by omega) x
          (le_trans (fr_le hV J 0 i' (Nat.zero_le _) hi') hle) hlt hx.2
        subst hxm
        refine ⟨m, ⟨?_, by omega⟩, rfl⟩
        by_contra hc
        exact absurd hle (not_le.mpr (fr_lt hV J m i' (by omega) hi'))
      · exact ⟨r - 1, ⟨by omega, by omega⟩, heq.symm⟩
    · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
      exact ⟨frj_mem hV J m hm2, fr_le hV J i' m hm1 hm2⟩
  rw [hfe, Finset.card_image_of_injOn, Nat.card_Ico]
  intro a ha b hb hab
  simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
  exact fr_inj hV J a b ha.2 hb.2 hab

private theorem countTlt_lemma_5 (hV : F.Valid L₁ N₁) (J : ℤ) (i' : ℕ) (hi' : i' < r) :
    ((F.letters J).filter (· < F.fr J i')).card + (r - i') = (F.letters J).card := by
  rw [← countT_lemma_4 hV J i' hi']
  have e := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset (F.fr J i' ≤ ·) (F.letters J))
  have hs : (F.letters J) \ (F.letters J).filter (F.fr J i' ≤ ·) = (F.letters J).filter (· < F.fr J i') := by
    ext y
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    constructor
    · rintro ⟨hy, h⟩
      exact ⟨hy, not_le.mp fun h' => h ⟨hy, h'⟩⟩
    · rintro ⟨hy, h⟩
      exact ⟨hy, fun h' => absurd h'.2 (not_le.mpr h)⟩
  rw [hs] at e
  exact e

theorem idx_w (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (i' : ℕ) (hi' : i' < r) (h : segE F j i = F.fr (j - 1) i') :
    i.val = i' := by
  have h1 := idx_card F j i
  rw [h, countW_lemma_3 hV j i' hi'] at h1
  exact h1.symm

theorem idx_tau (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (i' : ℕ) (hi' : i' < r) (h : segE F j i = F.fr j i') :
    i.val + (r - i') = segN F j := by
  have h1 := idx_card F j i
  rw [h] at h1
  have h2 := countTlt_lemma_5 hV j i' hi'
  rw [h1] at h2
  exact h2

theorem r_le_segN (hV : F.Valid L₁ N₁) (j : ℤ) : r ≤ segN F j := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := countT_lemma_4 hV j 0 hr0
  have h2 := Finset.card_filter_le (F.letters j) (F.fr j 0 ≤ ·)
  rw [h1] at h2
  unfold segN
  omega

theorem dict_tau (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (i' : Fin r) :
    segE F j i = F.fr j i'.val ↔ i.val = (segN F j - r) + i'.val := by
  have hr := r_le_segN hV j
  have hi' := i'.isLt
  constructor
  · intro h
    have := idx_tau hV i i'.val i'.isLt h
    omega
  · intro h
    obtain ⟨k, hk⟩ := segE_surj_lemma_9 j (frj_mem hV j i'.val i'.isLt)
    have := idx_tau hV k i'.val i'.isLt hk
    have hki : k = i := by
      apply Fin.ext
      omega
    subst hki
    exact hk

theorem dict_early (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) :
    segE F j i < F.fr j 0 ↔ i.val < segN F j - r := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  obtain ⟨k, hk⟩ := segE_surj_lemma_9 j (frj_mem hV j 0 hr0)
  have hkv := (dict_tau hV k ⟨0, hr0⟩).mp hk
  rw [← hk, segE_lt_lemma_7, Fin.lt_iff_val_lt_val, hkv]
  show i.val < segN F j - r + 0 ↔ i.val < segN F j - r
  omega

theorem dict_wE (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (h : i.val < r) : segE F j i = F.fr (j - 1) i.val := by
  obtain ⟨k, hk⟩ := segE_surj_lemma_9 j (frp_mem hV j i.val h)
  have hki : k = i := Fin.ext (idx_w hV k i.val h hk)
  subst hki
  exact hk

theorem dict_w (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) : F.IsW j (segE F j i) ↔ i.val < r := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hr := r_le_segN hV j
  have hw : segE F j ⟨r - 1, by omega⟩ = F.fr (j - 1) (r - 1) :=
    dict_wE hV _ (by show r - 1 < r; omega)
  unfold Frames.IsW
  rw [← hw, segE_le_lemma_8, Fin.le_iff_val_le_val]
  show i.val ≤ r - 1 ↔ i.val < r
  omega

theorem mem_LLset_iff (hV : F.Valid L₁ N₁) (x : ℤ) :
    x ∈ F.LLset j ↔ x ∈ F.letters j ∧ ¬ F.IsW j x ∧ x < F.fr j 0 := by
  have hr0 : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  have h1 := fr_le hV (j - 1) 0 (r - 1) (Nat.zero_le _) (by omega)
  have h2 := fr_le hV j 0 (r - 1) (Nat.zero_le _) (by omega)
  unfold Frames.LLset Frames.letters Frames.IsW
  simp only [Finset.mem_filter, Finset.mem_Ioo, Finset.mem_Icc, not_le]
  constructor
  · rintro ⟨⟨ha, hb⟩, hT⟩
    exact ⟨⟨⟨by linarith, by linarith⟩, hT⟩, ha, hb⟩
  · rintro ⟨⟨_, hT⟩, ha, hb⟩
    exact ⟨⟨ha, hb⟩, hT⟩

theorem dict_LL (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) :
    segE F j i ∈ F.LLset j ↔ r ≤ i.val ∧ i.val < segN F j - r := by
  rw [mem_LLset_iff hV, dict_w hV, dict_early hV]
  have hm := ((F.letters j).orderIsoOfFin rfl i).2
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨not_lt.mp h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨hm, not_lt.mpr h1, h2⟩

theorem LLset_eq_image (hV : F.Valid L₁ N₁) (j : ℤ) :
    F.LLset j = (Finset.univ.filter fun i : Fin (segN F j) => r ≤ i.val ∧ i.val < segN F j - r).image (segE F j) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hx
    have hxl := ((mem_LLset_iff hV x).mp hx).1
    obtain ⟨k, rfl⟩ := segE_surj_lemma_9 j hxl
    exact ⟨k, (dict_LL hV k).mp hx, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact (dict_LL hV k).mpr hk

omit [NeZero n'] [NeZero r] in
theorem card_fin_range (N a b : ℕ) (hb : b ≤ N) :
    (Finset.univ.filter fun i : Fin N => a ≤ i.val ∧ i.val < b).card = b - a := by
  have hm : (Finset.univ.filter fun i : Fin N => a ≤ i.val ∧ i.val < b).map Fin.valEmbedding = Finset.Ico a b := by
    ext y
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.valEmbedding_apply,
      Finset.mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hi
    · intro hy
      exact ⟨⟨y, by omega⟩, hy, rfl⟩
  rw [← Finset.card_map Fin.valEmbedding, hm, Nat.card_Ico]

theorem card_LLset (hV : F.Valid L₁ N₁) (j : ℤ) : (F.LLset j).card = segN F j - r - r := by
  rw [LLset_eq_image hV j, Finset.card_image_of_injective _ (segE_inj_lemma_10 j),
    card_fin_range _ _ _ (Nat.sub_le _ _)]

theorem two_r_le (hV : F.Valid L₁ N₁) (j : ℤ) : 2 * r ≤ segN F j - r := by
  obtain ⟨_, _, _, _, _, _, hLL, _⟩ := id hV
  have h1 := (hLL j).1
  rw [card_LLset hV j] at h1
  omega

theorem card_LLset_le (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (hi : r ≤ i.val) (hi2 : i.val < segN F j - r) :
    ((F.LLset j).filter (· ≤ segE F j i)).card = i.val + 1 - r := by
  rw [LLset_eq_image hV j]
  have hfe : ((Finset.univ.filter fun k : Fin (segN F j) => r ≤ k.val ∧ k.val < segN F j - r).image
      (segE F j)).filter (· ≤ segE F j i) =
      (Finset.univ.filter fun k : Fin (segN F j) => r ≤ k.val ∧ k.val < i.val + 1).image (segE F j) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨k, hk, rfl⟩, hle⟩
      rw [segE_le_lemma_8, Fin.le_iff_val_le_val] at hle
      exact ⟨k, ⟨hk.1, by omega⟩, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨k, ⟨hk.1, by omega⟩, rfl⟩, ?_⟩
      rw [segE_le_lemma_8, Fin.le_iff_val_le_val]
      omega
  rw [hfe, Finset.card_image_of_injective _ (segE_inj_lemma_10 j), card_fin_range _ _ _ (by omega)]

theorem dict_lateV (hV : F.Valid L₁ N₁) (i : Fin (segN F j)) (h : segN F j - r ≤ i.val + r) : Even (segE F j i) := by
  obtain ⟨_, _, _, _, hTT, _, hLL, _⟩ := id hV
  have hr := r_le_segN hV j
  have h2r := two_r_le hV j
  by_cases hi : segN F j - r ≤ i.val
  · have hi' : i.val - (segN F j - r) < r := by omega
    have he := (dict_tau hV i ⟨i.val - (segN F j - r), hi'⟩).mpr
      (by show i.val = segN F j - r + (i.val - (segN F j - r)); omega)
    rw [he]
    exact (hTT j _ hi').2
  · have hin : segE F j i ∈ F.LLset j := (dict_LL hV i).mpr ⟨by omega, by omega⟩
    have hcnt := card_LLset_le hV i (by omega) (by omega)
    have hcard := card_LLset hV j
    exact (((hLL j).2.1 _ hin) (Or.inr (by rw [hcnt, hcard]; omega))).1

end Dict

end Formalism.MainNotions.SelectionLemmas.Pf.TE

namespace Formalism.MainNotions.SelectionLemmas.Pf
section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

section Supp

variable {σ τ R : Type*} [CommRing R]

theorem supp_one {m : σ →₀ ℕ} (hm : m ∈ (1 : MvPolynomial σ R).support) : m = 0 := by
  classical
  by_contra h
  exact (MvPolynomial.mem_support_iff.mp hm) (by rw [MvPolynomial.coeff_one, ite_eq_right (fun h' => h h'.symm)])

theorem supp_prod_bound {ι : Type*} (w : (σ →₀ ℕ) →+ ℕ) (s : Finset ι) (f : ι → MvPolynomial σ R) (b : ι → ℝ)
    (h : ∀ j ∈ s, ∀ m ∈ (f j).support, (w m : ℝ) ≤ b j) :
    ∀ m ∈ (∏ j ∈ s, f j).support, (w m : ℝ) ≤ ∑ j ∈ s, b j := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _ m hm
    rw [Finset.prod_empty] at hm
    rw [supp_one hm]
    simp
  · intro a s ha ih h m hm
    rw [Finset.prod_insert ha] at hm
    have hm' := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_mul] at hm'
    obtain ⟨⟨m1, m2⟩, hmem, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm'
    have hmem' : m1 + m2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hmem
    have h1 : m1 ∈ (f a).support := MvPolynomial.mem_support_iff.mpr (left_ne_zero_of_mul hne)
    have h2 : m2 ∈ (∏ j ∈ s, f j).support := MvPolynomial.mem_support_iff.mpr (right_ne_zero_of_mul hne)
    rw [Finset.sum_insert ha, ← hmem', map_add (f := _), Nat.cast_add]
    exact add_le_add (h a (Finset.mem_insert_self a s) m1 h1)
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) m2 h2)

def imgMon (g : σ → τ) (e : σ → ℕ) (m : σ →₀ ℕ) : τ →₀ ℕ := m.sum fun v n => Finsupp.single (g v) (e v * n)

theorem aeval_pow_monomial (g : σ → τ) (e : σ → ℕ) (m : σ →₀ ℕ) (c : R) :
    aeval (fun v => (X (g v) : MvPolynomial τ R) ^ e v) (monomial m c) = monomial (imgMon g e m) c := by
  rw [MvPolynomial.aeval_monomial, imgMon, MvPolynomial.monomial_finsupp_sum_index, MvPolynomial.algebraMap_eq]
  congr 1
  apply Finsupp.prod_congr
  intro v _
  show (X (g v) ^ e v) ^ m v = _
  rw [← pow_mul, MvPolynomial.X_pow_eq_monomial]

theorem supp_aeval_pow (g : σ → τ) (e : σ → ℕ) (x : MvPolynomial σ R) {m' : τ →₀ ℕ}
    (hm' : m' ∈ (aeval (fun v => (X (g v) : MvPolynomial τ R) ^ e v) x).support) :
    ∃ m ∈ x.support, m' = imgMon g e m := by
  classical
  by_contra! hne
  apply MvPolynomial.mem_support_iff.mp hm'

  rw [x.as_sum, map_sum, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  rw [aeval_pow_monomial, MvPolynomial.coeff_monomial, ite_eq_right (fun h => hne m hm h.symm)]

end Supp

theorem posOf_val (n' : ℕ) [NeZero n'] (x : ℤ) : ((posOf n' x).val : ℤ) = x % (n' : ℤ) := by
  have h0 : 0 ≤ x % (n' : ℤ) := Int.emod_nonneg _ (by exact_mod_cast (NeZero.ne n'))
  have h1 : x % (n' : ℤ) < n' := Int.emod_lt_of_pos _ (by exact_mod_cast NeZero.pos n')
  show (((x % (n' : ℤ)).toNat % n' : ℕ) : ℤ) = _
  generalize x % (n' : ℤ) = y at *
  have h2 := Int.toNat_of_nonneg h0
  have h3 : y.toNat < n' := by omega
  rw [Nat.mod_eq_of_lt h3, h2]

theorem posOf_even {n' : ℕ} [NeZero n'] (he : Even n') (x : ℤ) : Even (posOf n' x).val ↔ Even x := by
  have hv := posOf_val n' x
  obtain ⟨k, hk⟩ := he
  have hn : (n' : ℤ) = k + k := by exact_mod_cast hk
  rw [hn] at hv
  have h2 : x % ((k : ℤ) + k) % 2 = x % 2 := Int.emod_emod_of_dvd x ⟨(k : ℤ), by ring⟩
  rw [Nat.even_iff, Int.even_iff]
  generalize x % ((k : ℤ) + k) = y at *
  generalize (posOf n' x).val = v at *
  omega

theorem posOf_natCast {n' : ℕ} [NeZero n'] (t : Fin n') : posOf n' (t.val : ℤ) = t := by
  apply Fin.ext
  have h := posOf_val n' (t.val : ℤ)
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast t.isLt)] at h
  exact_mod_cast h

theorem posOf_injOn {n' : ℕ} [NeZero n'] (a : ℤ) :
    Set.InjOn (posOf n') (Set.Ioc a (a + n')) := by
  intro x hx y hy hxy
  have h1 := posOf_val n' x
  have h2 := posOf_val n' y
  rw [hxy] at h1
  rw [Set.mem_Ioc] at hx hy
  have hmod : Int.ModEq n' y x := (h1.symm.trans h2).symm
  obtain ⟨c, hc⟩ := Int.ModEq.dvd hmod
  have hn : (0 : ℤ) < n' := by exact_mod_cast NeZero.pos n'
  have hc1 : c < 1 := by
    by_contra! h
    have : (n' : ℤ) * 1 ≤ n' * c := mul_le_mul_of_nonneg_left h hn.le
    omega
  have hc2 : -1 < c := by
    by_contra! h
    have : (n' : ℤ) * c ≤ n' * (-1) := mul_le_mul_of_nonneg_left h hn.le
    omega
  have : c = 0 := by omega
  subst this
  omega

section Wt

variable {n' r K : ℕ}

def wtVS (v : Fin n' × Fin (r + K)) : ℕ :=
  if Even v.1.val then (if r ≤ v.2.val then 1 else 0) else (if v.2.val < r then 1 else 0)

theorem sum_wtVS (f : Fin (r + K) → ℕ) (t : Fin n') :
    ∑ c : Fin (r + K), f c * wtVS (t, c) =
      if Even t.val then ∑ c : Fin K, f (Fin.natAdd r c) else ∑ c : Fin r, f (Fin.castAdd K c) := by
  have hi : ∀ i : Fin r, ¬ r ≤ (i : ℕ) := fun i => not_le.mpr i.isLt
  rw [Fin.sum_univ_add]
  split_ifs with h
  · simp [wtVS, h, hi]
  · simp [wtVS, h]

theorem vsDeg_eq (m : Fin n' × Fin (r + K) →₀ ℕ) : vsDeg m = Finsupp.linearCombination ℕ wtVS m := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
  unfold vsDeg
  refine Finset.sum_congr rfl fun t _ => ?_
  have := sum_wtVS (fun c => m (t, c)) t
  beta_reduce at this
  simp only [smul_eq_mul]
  rw [this]

end Wt

section Fr

variable {n' r : ℕ} [NeZero n'] (F : Frames n' r)

def eFr (j : ℤ) : ℤ := F.fr j (r - 1)

variable {F} {L₁ N₁ : ℕ}

theorem fr_zero_le (hV : F.Valid L₁ N₁) (j : ℤ) : ∀ i, i < r → F.fr j 0 ≤ F.fr j i := by
  intro i hi
  induction i with
  | zero => exact le_refl _
  | succ k ih => exact le_trans (ih (by omega)) (le_of_lt (hV.2.2.1 j k (by omega)))

theorem fr_zero_le_eFr [NeZero r] (hV : F.Valid L₁ N₁) (j : ℤ) : F.fr j 0 ≤ eFr F j := by
  exact fr_zero_le hV j (r - 1) (by have := NeZero.pos r; omega)

theorem eFr_strictMono [NeZero r] (hV : F.Valid L₁ N₁) : StrictMono (eFr F) := by
  exact strictMono_int_of_lt_succ fun j => lt_of_lt_of_le (hV.2.2.2.1 j) (fr_zero_le_eFr hV (j + 1))

theorem strictMono_int_exists (e : ℤ → ℤ) (he : StrictMono e) (x : ℤ) : ∃ j, e (j - 1) < x ∧ x ≤ e j :=
  by
    have hmono : Monotone (fun i => e i - i) := monotone_int_of_le_succ fun i => by
      have := he (lt_add_one i)
      omega
    have hbdd : ∃ b : ℤ, ∀ z, x ≤ e z → b ≤ z := by
      refine ⟨min 0 (x - e 0), fun z hz => ?_⟩
      by_cases h : z ≤ 0
      · have := hmono h
        dsimp only at this
        omega
      · omega
    have hinh : ∃ z, x ≤ e z := by
      let z := max 0 (x - e 0)
      have := hmono (show 0 ≤ z from le_max_left _ _)
      exact ⟨z, by dsimp only at this; dsimp [z] at this ⊢; omega⟩
    obtain ⟨j, hj, hmin⟩ := Int.exists_least_of_bdd hbdd hinh
    exact ⟨j, lt_of_not_ge fun h => by have := hmin (j - 1) h; omega, hj⟩

open Classical in
def nonW (F : Frames n' r) (j : ℤ) : Finset ℤ := (F.letters j).filter fun x => ¬ F.IsW j x

open Classical in
theorem nonW_eq [NeZero r] (hV : F.Valid L₁ N₁) (j : ℤ) :
    nonW F j = (Finset.Ioc (eFr F (j - 1)) (eFr F j)).filter fun x => posOf n' x ∈ F.TT := by
  ext x
  have h0 := fr_zero_le_eFr hV (j - 1)
  unfold eFr at h0 ⊢
  unfold nonW Frames.letters Frames.IsW
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨⟨by omega, h2⟩, h3⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨⟨by omega, h2⟩, h3⟩, by omega⟩

theorem exists_nonW [NeZero r] (hV : F.Valid L₁ N₁) (t : Fin n') (ht : t ∈ F.TT) :
    ∃ j : ℤ, ∃ x ∈ F.letters j, ¬ F.IsW j x ∧ posOf n' x = t := by
  classical
  obtain ⟨j, hj1, hj2⟩ := strictMono_int_exists (eFr F) (eFr_strictMono hV) (t.val : ℤ)
  have hx : (t.val : ℤ) ∈ nonW F j := by
    rw [nonW_eq hV j, Finset.mem_filter, Finset.mem_Ioc, posOf_natCast]
    exact ⟨⟨hj1, hj2⟩, ht⟩
  unfold nonW at hx
  rw [Finset.mem_filter] at hx
  exact ⟨j, (t.val : ℤ), hx.1, hx.2, posOf_natCast t⟩

theorem sum_card_Ioc (g : ℕ → ℤ) (hg : Monotone g) (P : ℤ → Prop) [DecidablePred P] (m : ℕ) :
    ∑ j ∈ Finset.range m, ((Finset.Ioc (g j) (g (j + 1))).filter P).card = ((Finset.Ioc (g 0) (g m)).filter P).card := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : g 0 ≤ g k := hg (Nat.zero_le k)
    have h2 : g k ≤ g (k + 1) := hg (Nat.le_succ k)
    rw [← Finset.Ioc_union_Ioc_eq_Ioc h1 h2, Finset.filter_union, Finset.card_union_of_disjoint]
    exact Finset.disjoint_left.mpr fun x hx1 hx2 => by
      simp only [Finset.mem_filter, Finset.mem_Ioc] at hx1 hx2
      omega

theorem sum_card_nonW [NeZero r] (hV : F.Valid L₁ N₁) :
    ∑ j ∈ Finset.range F.J, (nonW F (j : ℤ)).card ≤ F.TT.card := by
  classical
  have hmono : Monotone (fun i : ℕ => eFr F ((i : ℤ) - 1)) := fun a b hab =>
    (eFr_strictMono hV).monotone (by have : (a : ℤ) ≤ b := by exact_mod_cast hab
                                     omega)
  have h1 : ∀ j ∈ Finset.range F.J, (nonW F (j : ℤ)).card =
      ((Finset.Ioc ((fun i : ℕ => eFr F ((i : ℤ) - 1)) j) ((fun i : ℕ => eFr F ((i : ℤ) - 1)) (j + 1))).filter
        (fun x => posOf n' x ∈ F.TT)).card := by
    intro j _
    rw [nonW_eq hV]
    simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  rw [Finset.sum_congr rfl h1, sum_card_Ioc _ hmono]
  simp only [Nat.cast_zero, zero_sub]
  have hlen : eFr F ((F.J : ℤ) - 1) = eFr F (-1) + n' := by
    have := hV.2.1 (-1) (r - 1)
    unfold eFr
    rw [← this, show (F.J : ℤ) - 1 = -1 + F.J by ring]
  refine Finset.card_le_card_of_injOn (posOf n') ?_ ?_
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_filter] at hx
    simpa [Finset.mem_coe] using hx.2
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc] at hx hy
    refine posOf_injOn (eFr F (-1)) ?_ ?_ hxy
    · rw [Set.mem_Ioc]; constructor <;> omega
    · rw [Set.mem_Ioc]; constructor <;> omega

end Fr

section Seg

variable {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K]

def okVars (F : Frames n' r) (K : ℕ) (j : ℤ) : Set (ℤ × Fin (r + K)) :=
  {v | v.1 ∈ F.letters j ∧ (r ≤ v.2.val → ¬ F.IsW j v.1)}

theorem XX'_supported (O : Type) [CommRing O] (F : Frames n' r) (j : ℤ) (m : ℤ → ℤ) (th o : ℤ → ℝ)
    {x : SegRing O r K} (hx : x ∈ XX' O r K F j m th o) : x ∈ supported O (okVars F K j) := by
  classical
  unfold XX' at hx
  have hx1 := (Submodule.mem_inf.mp hx).1
  refine (Submodule.span_le (p := Subalgebra.toSubmodule (supported O (okVars F K j)))).mpr ?_ hx1
  rintro P ⟨A, G, M, hA, hG, -, rfl⟩
  rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule]
  refine Subalgebra.mul_mem _ ?_ ?_
  · rw [MvPolynomial.mem_supported] at hA ⊢
    unfold plEmb
    refine (Finset.coe_subset.mpr (MvPolynomial.vars_rename (fun v : ℤ × Fin r => (v.1, Fin.castAdd K v.2)) A)).trans ?_
    intro v hv
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have h1 : w.1 ∈ F.letters j := hA (Finset.mem_coe.mpr hw)
    simp only [okVars, Set.mem_setOf_eq]
    refine ⟨h1, fun h => ?_⟩
    exfalso
    have := w.2.isLt
    simp only [Fin.coe_castAdd] at h
    omega
  · rw [MvPolynomial.mem_supported] at hG ⊢
    unfold nmEmb
    refine (Finset.coe_subset.mpr (MvPolynomial.vars_rename (fun v : ℤ × Fin K => (v.1, Fin.natAdd r v.2)) G)).trans ?_
    intro v hv
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    have h1 : w.1 ∈ F.letters j ∧ ¬ F.IsW j w.1 := hG (Finset.mem_coe.mpr hw)
    simp only [okVars, Set.mem_setOf_eq]
    exact ⟨h1.1, fun _ => h1.2⟩

theorem ordDeg_eq (he : Even n') (m : ℤ × Fin (r + K) →₀ ℕ) (x : ℤ) :
    ordDeg m x = ∑ c : Fin (r + K), m (x, c) * wtVS (posOf n' x, c) := by
  have := sum_wtVS (fun c => m (x, c)) (posOf n' x)
  beta_reduce at this
  rw [this]
  unfold ordDeg
  simp only [posOf_even he]

private theorem even_of_isW {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) {j x : ℤ}
    (hx : x ∈ F.letters j) (hw : F.IsW j x) : Even x := by
  unfold Frames.letters at hx
  unfold Frames.IsW at hw
  simp only [Finset.mem_filter, Finset.mem_Icc] at hx
  obtain ⟨⟨hx0, -⟩, hT⟩ := hx
  have key : ∀ i, i < r → x ≤ F.fr (j - 1) i → ∃ i', i' < r ∧ x = F.fr (j - 1) i' := by
    intro i
    induction i with
    | zero => intro hi h; exact ⟨0, hi, le_antisymm h hx0⟩
    | succ k ih =>
      intro hi h
      by_cases hk : x ≤ F.fr (j - 1) k
      · exact ih (by omega) hk
      · by_cases he : x = F.fr (j - 1) (k + 1)
        · exact ⟨k + 1, hi, he⟩
        · exact absurd hT (hV.2.2.2.2.2.1 (j - 1) k x hi (by omega) (by omega))
  obtain ⟨i', hi', rfl⟩ := key (r - 1) (by have := NeZero.pos r; omega) hw
  exact (hV.2.2.2.2.1 (j - 1) i' hi').2

theorem vs_img_le (he : Even n') {F : Frames n' r} {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (p : ℕ) (j : ℤ)
    (m : ℤ × Fin (r + K) →₀ ℕ) (hm : ∀ v ∈ m.support, v ∈ okVars F K j) :
    vsDeg (imgMon (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2)) (fun v => p ^ F.dist j v.1) m) ≤
      ∑ x ∈ nonW F j, p ^ F.dist j x * ordDeg m x := by
  classical

  rw [vsDeg_eq, imgMon, Finsupp.sum, map_sum]
  simp only [Finsupp.linearCombination_single, smul_eq_mul]
  calc ∑ v ∈ m.support, p ^ F.dist j v.1 * m v * wtVS (posOf n' v.1, v.2)
      ≤ ∑ v ∈ nonW F j ×ˢ (Finset.univ : Finset (Fin (r + K))), p ^ F.dist j v.1 * m v * wtVS (posOf n' v.1, v.2) := by
        apply Finset.sum_le_sum_of_ne_zero
        intro v hv hne
        have hok := hm v hv
        simp only [okVars, Set.mem_setOf_eq] at hok
        rw [Finset.mem_product]
        refine ⟨?_, Finset.mem_univ _⟩
        simp only [nonW, Finset.mem_filter]
        refine ⟨hok.1, fun hw => hne ?_⟩
        have hev : Even v.1 := even_of_isW hV hok.1 hw
        have hlt : ¬ r ≤ (v.2 : ℕ) := fun h => hok.2 h hw
        have hpe : Even (posOf n' v.1).val := (posOf_even he v.1).mpr hev
        simp [wtVS, hpe, hlt]
    _ = ∑ x ∈ nonW F j, p ^ F.dist j x * ordDeg m x := by
        rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [ordDeg_eq he, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring

end Seg

section Num

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def B1 : ℝ := X.La * X.a / ((p : ℝ) * Dat.k (r := r) K) + 10 * X.a * (p : ℝ) ^ (-(X.L₁ : ℤ))

omit [NeZero n'] in
theorem k_pos (hr : 0 < r) : (0 : ℝ) < Dat.k (r := r) K := by
  unfold Dat.k
  exact_mod_cast (show 0 < r + K by omega)

theorem pow_mul_o_le (hp : 0 < p) (hr : 0 < r) (ha : 0 ≤ X.a) (j x : ℤ) :
    (p : ℝ) ^ X.F.dist j x * X.o p K j x ≤ B1 X p K := by
  unfold Dat.o B1
  have hp' : (0:ℝ) < p := by exact_mod_cast hp
  have hk := (k_pos K hr).ne'
  have hz : (p:ℝ) ^ X.F.dist j x * (p:ℝ) ^ (-((X.L₁:ℤ) + (X.F.dist j x : ℤ))) = (p:ℝ) ^ (-(X.L₁:ℤ)) := by
    rw [← zpow_natCast, ← zpow_add₀ hp'.ne']
    congr 1
    ring
  have h1 : (p:ℝ) ^ X.F.dist j x * (X.La * X.a / (↑p * Dat.k (r := r) K * ↑p ^ X.F.dist j x)) = X.La * X.a / (↑p * Dat.k (r := r) K) := by
    field_simp
  have hc : (if Even x then (10:ℝ) else 1) ≤ 10 := by split_ifs <;> norm_num
  have hpL : (0:ℝ) ≤ (p:ℝ) ^ (-(X.L₁:ℤ)) := by positivity
  rw [mul_add, h1]
  have h2 : (p:ℝ) ^ X.F.dist j x * ((if Even x then (10:ℝ) else 1) * X.a * (p:ℝ) ^ (-((X.L₁:ℤ) + (X.F.dist j x : ℤ)))) = (if Even x then (10:ℝ) else 1) * X.a * (p:ℝ) ^ (-(X.L₁:ℤ)) := by
    rw [← hz]
    ring
  rw [h2]
  have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc ha) hpL
  linarith

variable {X p K}

theorem eFr_mem_letters [NeZero r] (hX : X.Hyp p K) (j : ℤ) : eFr X.F j ∈ X.F.letters j := by
  have hV := hX.valid
  have hr : 0 < r := NeZero.pos r
  have h1 := fr_zero_le_eFr hV (j - 1)
  have h2 := eFr_strictMono hV (show j - 1 < j by omega)
  have h3 := (hV.2.2.2.2.1 j (r - 1) (by omega)).1
  unfold eFr at h1 h2 ⊢
  unfold Frames.letters
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨by omega, le_refl _⟩, h3⟩

theorem Q_one_le [NeZero r] (hX : X.Hyp p K) : 1 ≤ X.Q := by
  have h := hX.twist 0 (eFr X.F 0) (eFr_mem_letters hX 0)
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast hX.prime.one_lt.le
  exact le_trans (one_le_pow₀ hp) h

theorem Ns_one_le [NeZero r] (hX : X.Hyp p K) : 1 ≤ X.Ns := by
  have h1 := Finset.card_pos.mpr ⟨_, eFr_mem_letters hX 0⟩
  have h2 := hX.card 0
  omega

theorem a_one_le [NeZero r] (hX : X.Hyp p K) : 1 ≤ X.a := by
  refine le_trans ?_ hX.P3
  refine one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) ?_) ?_) ?_) ?_) ?_) ?_
  · exact_mod_cast hX.prime.one_lt.le
  · exact hX.Y1
  · exact one_le_pow₀ (by exact_mod_cast (show 1 ≤ r + K by have := NeZero.pos r; omega))
  · exact_mod_cast Ns_one_le hX
  · exact one_le_pow₀ (Q_one_le hX)
  · norm_cast
    omega

end Num

section Main

variable {n' r K : ℕ} [NeZero n'] [NeZero r] [NeZero K] {X : Dat n' r} {p : ℕ}

theorem seg_bound (O : Type) [CommRing O] (hX : X.Hyp p K) (j : ℤ) {x : SegRing O r K} (hx : x ∈ X.XXs p K O j)
    {m' : Fin n' × Fin (r + K) →₀ ℕ} (hm' : m' ∈ (phSeg O K p X.F j x).support) :
    (vsDeg m' : ℝ) ≤ ((nonW X.F j).card : ℝ) * B1 X p K := by
  classical
  unfold Dat.XXs at hx
  have hV := hX.valid
  have hsupp := XX'_supported O X.F j (X.mg p K j) (X.th p j) (X.o p K j) hx
  unfold XX' at hx
  have hres0 := (Submodule.mem_inf.mp hx).2
  rw [MvPolynomial.mem_restrictSupport_iff] at hres0
  unfold phSeg at hm'
  obtain ⟨mm, hmm, rfl⟩ := supp_aeval_pow (fun v : ℤ × Fin (r + K) => (posOf n' v.1, v.2)) (fun v => p ^ X.F.dist j v.1) x hm'
  have hres : ∀ y ∈ X.F.letters j, ¬ X.F.IsW j y → (ordDeg mm y : ℝ) ≤ X.o p K j y :=
    hres0 (Finset.mem_coe.mpr hmm)
  have hsupp' := MvPolynomial.mem_supported.mp hsupp
  have hm : ∀ v ∈ mm.support, v ∈ okVars X.F K j := fun v hv =>
    hsupp' (Finset.mem_coe.mpr ((MvPolynomial.mem_vars_iff_mem_support v).mpr ⟨mm, hmm, hv⟩))
  have hmain := vs_img_le hX.even hV p j mm hm
  have hmain' := (Nat.cast_le (α := ℝ)).mpr hmain
  have hp : 0 < p := hX.prime.pos
  have hr : 0 < r := NeZero.pos r
  have ha : 0 ≤ X.a := le_trans zero_le_one (a_one_le hX)
  have hsum : ((∑ y ∈ nonW X.F j, p ^ X.F.dist j y * ordDeg mm y : ℕ) : ℝ) ≤ ∑ y ∈ nonW X.F j, B1 X p K := by
    push_cast
    refine Finset.sum_le_sum fun y hy => ?_
    have hy' : y ∈ X.F.letters j ∧ ¬ X.F.IsW j y := by simpa [nonW] using hy
    have h1 : (ordDeg mm y : ℝ) ≤ X.o p K j y := hres y hy'.1 hy'.2
    have h2 := pow_mul_o_le X p K hp hr ha j y
    have h3 : (0:ℝ) ≤ (p:ℝ) ^ X.F.dist j y := by positivity
    calc (p:ℝ) ^ X.F.dist j y * (ordDeg mm y : ℝ) ≤ (p:ℝ) ^ X.F.dist j y * X.o p K j y :=
          mul_le_mul_of_nonneg_left h1 h3
      _ ≤ B1 X p K := h2
  rw [Finset.sum_const, nsmul_eq_mul] at hsum
  exact le_trans hmain' hsum

theorem vsDeg_sum (m : Fin n' × Fin (r + K) →₀ ℕ) :
    vsDeg m = ∑ t : Fin n', ∑ c : Fin (r + K), m (t, c) * wtVS (t, c) := by
  unfold vsDeg
  refine Finset.sum_congr rfl fun t _ => ?_
  have := sum_wtVS (fun c => m (t, c)) t
  beta_reduce at this
  exact this.symm

theorem label_bound (hX : X.Hyp p K) (l : Fin n' × Fin (r + K) →₀ ℕ) (hl : IsLabel p X.F l)
    (h0 : ∀ t, t ∉ X.F.TT → ∀ c, l (t, c) = 0) :
    (vsDeg l : ℝ) ≤ (X.F.TT.card : ℝ) * (Dat.k (r := r) K * X.Q) := by
  have hV := hX.valid
  have hc : ∀ t ∈ X.F.TT, ∀ c, (l (t, c) : ℝ) ≤ X.Q := by
    intro t ht c
    obtain ⟨j, x, hx, hw, rfl⟩ := exists_nonW hV t ht
    have h1 := hl j x hx hw c
    have h2 := hX.twist j x hx
    have h3 : ((l (posOf n' x, c) : ℕ) : ℝ) < (p : ℝ) ^ X.F.dist j x := by exact_mod_cast h1
    linarith
  have hterm : ∀ t : Fin n', (∑ c : Fin (r + K), (l (t, c) : ℝ) * (wtVS (t, c) : ℝ)) ≤
      if t ∈ X.F.TT then Dat.k (r := r) K * X.Q else 0 := by
    intro t
    split_ifs with ht
    · calc (∑ c : Fin (r + K), (l (t, c) : ℝ) * (wtVS (t, c) : ℝ)) ≤ ∑ c : Fin (r + K), X.Q := by
            refine Finset.sum_le_sum fun c _ => ?_
            have hw : (wtVS (t, c) : ℝ) ≤ 1 := by
              unfold wtVS
              split_ifs <;> norm_num
            nlinarith [hc t ht c]
        _ = Dat.k (r := r) K * X.Q := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            rfl
    · have : ∀ c, l (t, c) = 0 := h0 t ht
      simp [this]
  rw [vsDeg_sum]
  push_cast
  calc (∑ t : Fin n', ∑ c : Fin (r + K), (l (t, c) : ℝ) * (wtVS (t, c) : ℝ))
      ≤ ∑ t : Fin n', (if t ∈ X.F.TT then Dat.k (r := r) K * X.Q else 0) := Finset.sum_le_sum fun t _ => hterm t
    _ = (X.F.TT.card : ℝ) * (Dat.k (r := r) K * X.Q) := by
        rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

theorem gen_bound (O : Type) [CommRing O] (hX : X.Hyp p K) (hC : 0 ≤ X.CLa) {P : RRing O n' (r + K)}
    (hP : P ∈ X.gen p K O) {mm : Fin n' × Fin (r + K) →₀ ℕ} (hmm : mm ∈ P.support) :
    (vsDeg mm : ℝ) ≤ 10 * (X.F.TT.card : ℝ) *
        (X.La * X.a / ((p : ℝ) * Dat.k (r := r) K) + X.a * (p : ℝ) ^ (-(X.L₁ : ℤ)) + Dat.k (r := r) K * X.Q) := by
  classical
  obtain ⟨x, hx, l, hl, rfl, hdeg⟩ := hP
  by_cases hle : l ≤ mm
  swap
  · exfalso
    apply MvPolynomial.mem_support_iff.mp hmm
    rw [MvPolynomial.coeff_mul_monomial', ite_eq_right hle]
  have hm'' : mm - l ∈ (∏ j ∈ Finset.range X.F.J, (phSeg O K p X.F (j : ℤ)) (x j)).support := by
    have hcoef := MvPolynomial.mem_support_iff.mp hmm
    rw [MvPolynomial.coeff_mul_monomial', ite_eq_left hle, mul_one] at hcoef
    exact MvPolynomial.mem_support_iff.mpr hcoef
  have hadd : vsDeg mm = vsDeg (mm - l) + vsDeg l := by
    conv_lhs => rw [← tsub_add_cancel_of_le hle]
    rw [vsDeg_eq, vsDeg_eq, vsDeg_eq, map_add (f := _)]
  unfold RRdeg Dat.d at hdeg
  rw [MvPolynomial.mem_restrictSupport_iff] at hdeg
  have hrow := hdeg (Finset.mem_coe.mpr hmm)
  simp only [Set.mem_setOf_eq] at hrow
  have h0 : ∀ t, t ∉ X.F.TT → ∀ c, l (t, c) = 0 := by
    intro t ht c
    have h1 : ∑ c, mm (t, c) = 0 := by
      have := hrow t
      simpa [ht] using this
    have h2 : mm (t, c) = 0 := (Finset.sum_eq_zero_iff.mp h1) c (Finset.mem_univ _)
    have h3 : l (t, c) ≤ mm (t, c) := (Finsupp.le_def.mp hle) (t, c)
    omega
  have hL := label_bound hX l hl h0
  have hT : (0:ℝ) ≤ X.F.TT.card := Nat.cast_nonneg _
  have ha := a_one_le hX
  have hp' : (0:ℝ) < p := by exact_mod_cast hX.prime.pos
  have hk := k_pos K (NeZero.pos r)
  have hLa : 0 ≤ X.La := by
    unfold Dat.La
    have : 0 ≤ Real.log X.a := Real.log_nonneg ha
    exact mul_nonneg (mul_nonneg hC (by positivity)) this
  have hA : 0 ≤ X.La * X.a / (↑p * Dat.k (r := r) K) :=
    div_nonneg (mul_nonneg hLa (by linarith)) (mul_pos hp' hk).le
  have hPq : 0 ≤ X.a * (p:ℝ) ^ (-(X.L₁ : ℤ)) := mul_nonneg (by linarith) (by positivity)
  have hC' : 0 ≤ Dat.k (r := r) K * X.Q := mul_nonneg hk.le (le_trans zero_le_one (Q_one_le hX))
  have hB1 : 0 ≤ B1 X p K := by
    unfold B1
    exact add_nonneg hA (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by positivity))
  have hprod := supp_prod_bound (Finsupp.linearCombination ℕ (wtVS (n' := n') (r := r) (K := K))).toAddMonoidHom
    (Finset.range X.F.J) (fun j : ℕ => (phSeg O K p X.F (j : ℤ)) (x j))
    (fun j : ℕ => ((nonW X.F (j : ℤ)).card : ℝ) * B1 X p K) (fun j _ m hm => by
      have := seg_bound O hX (j : ℤ) (hx j) hm
      rw [vsDeg_eq] at this
      exact this) (mm - l) hm''
  have hsumc := sum_card_nonW hX.valid
  have hsumc' : (∑ j ∈ Finset.range X.F.J, ((nonW X.F (j : ℤ)).card : ℝ)) ≤ X.F.TT.card := by
    exact_mod_cast hsumc
  have hQ' : (vsDeg (mm - l) : ℝ) ≤ X.F.TT.card * B1 X p K := by
    rw [vsDeg_eq]
    refine le_trans hprod ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right hsumc' hB1
  have hB1' : B1 X p K = X.La * X.a / (↑p * Dat.k (r := r) K) + 10 * X.a * (p:ℝ) ^ (-(X.L₁ : ℤ)) := rfl
  rw [hB1'] at hQ'
  rw [hadd, Nat.cast_add]
  nlinarith [mul_nonneg hT hA, mul_nonneg hT hC', mul_nonneg hT hPq, hQ', hL]

theorem restDeg : RestDeg := by
  unfold RestDeg
  intro p n' r K _ _ _ X O _ _ hX hC P hP mm hmm
  unfold Dat.NN at hP
  revert hmm
  induction hP using Submodule.span_induction with
  | mem Q hQ => exact fun h => gen_bound O hX hC hQ h
  | zero => intro h; simp at h
  | add Q1 Q2 _ _ ih1 ih2 =>
    intro h
    classical
    rcases Finset.mem_union.mp (MvPolynomial.support_add h) with h' | h'
    · exact ih1 h'
    · exact ih2 h'
  | smul a Q _ ih => exact fun h => ih (MvPolynomial.support_smul h)

end Main

end

section
open MvPolynomial

open Formalism.MainNotions.G

theorem sel_isCompl_restrictSupport (R : Type*) [CommRing R] {σ : Type*} (s : Set (σ →₀ ℕ)) :
    IsCompl (restrictSupport R s) (restrictSupport R sᶜ) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    rw [mem_restrictSupport_iff] at hx hx'
    rw [← support_eq_empty]
    ext m
    simp only [Finset.notMem_empty, iff_false]
    intro hm
    exact hx' (Finset.mem_coe.mpr hm) (hx (Finset.mem_coe.mpr hm))
  · rw [codisjoint_iff, restrictSupport_eq_span, restrictSupport_eq_span, ← Submodule.span_union, ← Set.image_union,
      Set.union_compl_self, ← restrictSupport_eq_span, restrictSupport_univ]

section DVR

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {σ : Type}

theorem sel_red_sum {ι : Type} [Fintype ι] (c : ι → O) (v : ι → MvPolynomial σ O) :
    MvPolynomial.map (IsLocalRing.residue O) (∑ i, c i • v i) =
      ∑ i, IsLocalRing.residue O (c i) • MvPolynomial.map (IsLocalRing.residue O) (v i) := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]

theorem sel_key {ι : Type} [Fintype ι] (v : ι → MvPolynomial σ O)
    (hv : LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (v i))
    {ϖ : O} (hϖ : Irreducible ϖ) (c : ι → O) (x : MvPolynomial σ O) (h : ∑ i, c i • v i = ϖ • x) :
    ∃ c' : ι → O, (∀ i, c i = ϖ * c' i) ∧ ∑ i, c' i • v i = x := by
  have hres : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
    exact hϖ.not_isUnit
  have h1 : ∑ i, IsLocalRing.residue O (c i) • MvPolynomial.map (IsLocalRing.residue O) (v i) = 0 := by
    rw [← sel_red_sum, h, smul_eq_C_mul, map_mul, map_C, hres, C_0, zero_mul]
  have h2 := Fintype.linearIndependent_iff.mp hv _ h1
  have h3 : ∀ i, ϖ ∣ c i := fun i => by
    have := (IsLocalRing.residue_eq_zero_iff _).mp (h2 i)
    rwa [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at this
  choose c' hc' using h3
  refine ⟨c', hc', ?_⟩
  have h4 : ϖ • ∑ i, c' i • v i = ϖ • x := by
    rw [← h, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc' i, mul_smul]
  exact smul_right_injective _ hϖ.ne_zero h4

theorem sel_li {ι : Type} [Fintype ι] (v : ι → MvPolynomial σ O)
    (hv : LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (v i)) :
    LinearIndependent O v := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hP : ∀ n : ℕ, ∀ c : ι → O, ∑ i, c i • v i = 0 → ∀ i, ϖ ^ n ∣ c i := by
    intro n
    induction n with
    | zero => intro c _ i; simp
    | succ n ih =>
      intro c hc i
      obtain ⟨c', hc', hs⟩ := sel_key v hv hϖ c 0 (by rw [hc, smul_zero])
      obtain ⟨e, he⟩ := ih c' hs i
      exact ⟨e, by rw [hc' i, he, pow_succ]; ring⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hne
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne hϖ
  obtain ⟨e, he⟩ := hP (n + 1) c hc i
  have h1 : ϖ ^ n * (u : O) = ϖ ^ n * (ϖ * e) := by
    rw [← mul_assoc, ← pow_succ, ← he, hu]; ring
  have h2 : (u : O) = ϖ * e := mul_left_cancel₀ (pow_ne_zero n hϖ.ne_zero) h1
  exact hϖ.not_isUnit (isUnit_of_mul_isUnit_left (h2 ▸ u.isUnit))

theorem sel_sat {ι : Type} [Fintype ι] (v : ι → MvPolynomial σ O)
    (hv : LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (v i))
    (a : O) (x : MvPolynomial σ O) (ha : a ≠ 0) (h : a • x ∈ Submodule.span O (Set.range v)) :
    x ∈ Submodule.span O (Set.range v) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  have h1 : ϖ ^ n • x ∈ Submodule.span O (Set.range v) := by
    have := Submodule.smul_mem _ ((u⁻¹ : Oˣ) : O) h
    rwa [smul_smul, ← mul_assoc, Units.inv_mul, one_mul] at this
  clear h ha
  induction n with
  | zero => simpa using h1
  | succ n ih =>
    apply ih
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).mp h1
    obtain ⟨c', -, hs⟩ := sel_key v hv hϖ c (ϖ ^ n • x) (by rw [hc, smul_smul, ← pow_succ'])
    exact (Submodule.mem_span_range_iff_exists_fun O).mpr ⟨c', hs⟩

end DVR

theorem restSel : RestSel := by
  intro O _ _ _ σ s hs G hG
  classical
  obtain ⟨b, hbG, hspan, hli⟩ := exists_linearIndependent (FF O) (MvPolynomial.map (IsLocalRing.residue O) '' G)

  have hsub : ∀ y ∈ MvPolynomial.map (IsLocalRing.residue O) '' G, y ∈ restrictSupport (FF O) s := by
    rintro y ⟨g, hg, rfl⟩
    have hg' := hG g hg
    rw [mem_restrictSupport_iff] at hg' ⊢
    exact fun m hm => hg' (Finset.mem_coe.mpr (support_map_subset _ _ hm))
  have : Finite ((fun m : σ →₀ ℕ => (monomial m (1 : FF O))) '' s) := (hs.image _).to_subtype
  have hfin : Finite b := by
    refine hli.finite_of_le_span_finite _ ((fun m : σ →₀ ℕ => (monomial m (1 : FF O))) '' s) ?_
    rintro y ⟨⟨y', hy'⟩, rfl⟩
    have := hsub y' (hbG hy')
    rwa [restrictSupport_eq_span] at this
  let : Fintype b := Fintype.ofFinite b

  have hpre : ∀ y : b, ∃ g ∈ G, MvPolynomial.map (IsLocalRing.residue O) g = (y : MvPolynomial σ (FF O)) :=
    fun y => hbG y.2
  choose v hvG hv using hpre
  have hli' : LinearIndependent (FF O) fun i => MvPolynomial.map (IsLocalRing.residue O) (v i) := by
    have : (fun i => MvPolynomial.map (IsLocalRing.residue O) (v i)) = ((↑) : b → MvPolynomial σ (FF O)) :=
      funext hv
    rw [this]; exact hli
  have hliO : LinearIndependent O v := sel_li v hli'
  have : Finite s := hs.to_subtype
  have : Module.Finite O (restrictSupport O s) := Module.Finite.of_basis (basisRestrictSupport O s)
  have hle : Submodule.span O (Set.range v) ≤ Submodule.span O G :=
    Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact hvG i)
  have hleN : Submodule.span O (Set.range v) ≤ restrictSupport O s :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hG _ (hvG i))
  refine ⟨Submodule.span O (Set.range v), hle, ?_, ⟨b, Module.Basis.span hliO, fun i => ?_⟩, ?_⟩
  · exact _root_.Bl.ComplementLifts.goal1 _ _ _ (sel_isCompl_restrictSupport O s) hleN (fun a x ha h => sel_sat v hli' a x ha h)
  · rw [Module.Basis.span_apply]; exact hvG i
  · rw [finrank_span_eq_card hliO, ← hspan]
    have : Submodule.span (FF O) b = Submodule.span (FF O) (Set.range ((↑) : b → MvPolynomial σ (FF O))) := by
      rw [Subtype.range_coe]
    rw [this, finrank_span_eq_card hli]

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def Pz (j x : ℤ) : ℕ := p ^ (X.F.dist j x + X.Rj p K j)

open Classical in
def laSet (t : Fin n') : Finset (Fin (r + K) → ℕ) :=
  (Fintype.piFinset fun _ : Fin (r + K) => Finset.range (X.a' p K t + 1)).filter fun v =>
    ∑ c, v c ≤ X.a' p K t ∧ ∀ j : ℤ, ∀ x ∈ X.toLate j, posOf n' x = t →
      (∀ c, v c < X.Pz p K j x) ∧ (∑ c, v c) % X.Pz p K j x = X.a' p K t % X.Pz p K j x

def LA : Finset (Fin n' → Fin (r + K) → ℕ) := Fintype.piFinset (X.laSet p K)

def nz (la : Fin n' → Fin (r + K) → ℕ) (j x : ℤ) : ℕ :=
  (X.a' p K (posOf n' x) - ∑ c, la (posOf n' x) c) / X.Pz p K j x

open Classical in
def EE (la : Fin n' → Fin (r + K) → ℕ) : Finset (Fin X.F.J → Fin r → ℕ) :=
  Fintype.piFinset fun j : Fin X.F.J => Fintype.piFinset fun i : Fin r =>
    (Finset.range (r * X.Qc p K (j.val : ℤ))).filter fun e =>
      e % X.Qc p K (j.val : ℤ) = X.nz p K la (j.val : ℤ) (X.F.fr (j.val : ℤ) i.val) % X.Qc p K (j.val : ℤ)

omit [NeZero n'] in
def eZ (e : Fin X.F.J → Fin r → ℕ) (j : ℤ) : Fin r → ℕ :=
  if h : 0 < X.F.J then e ⟨(j % (X.F.J : ℤ)).toNat % X.F.J, Nat.mod_lt _ h⟩ else 0

open Classical in
def bfam (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : ℤ) : ℤ → ℕ := fun x =>
  if x ∈ X.F.letters j then
    if X.F.IsW j x then
      ∑ i : Fin r, if x = X.F.fr (j - 1) i.val then
        (X.nz p K la (j - 1) x - X.eZ e (j - 1) i) / X.Qc p K (j - 1) else 0
    else if X.F.fr j 0 ≤ x then ∑ i : Fin r, if x = X.F.fr j i.val then X.eZ e j i else 0
    else X.nz p K la j x
  else 0

open Classical in
def setTau (j : ℤ) (b : ℤ → ℕ) (e : Fin r → ℕ) : ℤ → ℕ := fun x =>
  if X.F.fr j 0 ≤ x ∧ x ≤ X.F.fr j (r - 1) then ∑ i : Fin r, if x = X.F.fr j i.val then e i else 0 else b x

def AdmLL (j : ℤ) (b : ℤ → ℕ) : Prop :=
  ∀ x ∈ X.F.LLset j, (X.a' p K (posOf n' x) : ℝ) / (X.Pz p K j x : ℝ) - k (r := r) K < (b x : ℝ) ∧
    (b x : ℝ) ≤ (X.a' p K (posOf n' x) : ℝ) / (X.Pz p K j x : ℝ)

def segBound (j : ℤ) (b : ℤ → ℕ) : ℝ :=
  (1 - 1 / X.a ^ (X.Ns ^ 2)) *
    (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
    (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
    (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) ^ r

open Classical in
def SegOK [NeZero r] [NeZero K] (O : Type) [CommRing O] (j : ℤ) (G : (ℤ → ℕ) → ℝ) : Prop :=
  (∀ b, 0 ≤ G b) ∧
  (∀ b b' : ℤ → ℕ, (∀ x ∈ X.toLate j, b x = b' x) → G b = G b') ∧
  (∀ b : ℤ → ℕ, (∀ x, x ∉ X.F.letters j → b x = 0) →
    (∀ x ∈ X.F.letters j, X.F.IsW j x → X.Bw p K j x ≤ (b x : ℤ)) → X.AdmLL p K j b →
    G b ≤ (Module.finrank O (X.Mj p K O j b) : ℝ)) ∧
  (∀ b : ℤ → ℕ, X.AdmLL p K j b → ∀ ρ : Fin r → ℕ,
    X.segBound p K j b ≤ ∑ e ∈ Fintype.piFinset fun i : Fin r =>
      (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j, G (X.setTau j b e))

end Dat

def RestLam (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∑ la ∈ X.LA p K, ∑ e ∈ X.EE p K la, ∏ j : Fin X.F.J,
        Module.finrank O (X.Mj p K O (j.val : ℤ) (X.bfam p K la e (j.val : ℤ))) ≤
      Module.finrank (FF O) (X.LamBar p K O)

def RestSeg (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ j : ℤ, ∃ G : (ℤ → ℕ) → ℝ, X.SegOK p K O j G

def RestPad (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ la ∈ X.LA p K, ∀ e ∈ X.EE p K la, ∀ j : ℤ,
      (∀ x ∈ X.F.letters j, X.F.IsW j x → X.Bw p K j x ≤ (X.bfam p K la e j x : ℤ)) ∧
      X.AdmLL p K j (X.bfam p K la e j)

def RestSum (C₀ Crk : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ G : ℤ → (ℤ → ℕ) → ℝ,
      (∀ j b, 0 ≤ G j b) →
      (∀ j, ∀ b b' : ℤ → ℕ, (∀ x ∈ X.toLate j, b x = b' x) → G j b = G j b') →
      (∀ j, ∀ b : ℤ → ℕ, X.AdmLL p K j b → ∀ ρ : Fin r → ℕ,
        X.segBound p K j b ≤ ∑ e ∈ Fintype.piFinset fun i : Fin r =>
          (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j,
            G j (X.setTau j b e)) →
      ((p : ℝ) ^ n') ^ (-((r * K : ℕ) : ℤ)) * X.bound K Crk ≤
        ∑ la ∈ X.LA p K, ∑ e ∈ X.EE p K la, ∏ j : Fin X.F.J, G (j.val : ℤ) (X.bfam p K la e (j.val : ℤ))

theorem restCount_of (C₀ Crk : ℝ) (hL : RestLam C₀) (hS : RestSeg C₀) (hP : RestPad C₀) (hSum : RestSum C₀ Crk) :
    RestCount C₀ Crk := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk
  choose G hG using hS p n' r K X O S hX hLa hk
  refine le_trans (hSum p n' r K X hX hLa hk G (fun j => (hG j).1) (fun j => (hG j).2.1) (fun j => (hG j).2.2.2)) ?_
  refine le_trans ?_ (Nat.cast_le.mpr (hL p n' r K X O S hX hLa hk))
  push_cast
  refine Finset.sum_le_sum fun la hla => Finset.sum_le_sum fun e he => ?_
  refine Finset.prod_le_prod₀ (fun j _ => (hG _).1 _) fun j _ => ?_
  obtain ⟨h1, h2⟩ := hP p n' r K X hX hLa hk la hla e he (j.val : ℤ)
  refine (hG _).2.2.1 _ ?_ h1 h2
  intro x hx
  simp [Dat.bfam, hx]

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

open Classical in
def restr (j : ℤ) (b : ℤ → ℕ) : ℤ → ℕ := fun x => if x ∈ X.toLate j then b x else 0

open Classical in
def Bdeg (j : ℤ) (b : ℤ → ℕ) (x : ℤ) : ℕ :=
  if X.F.IsW j x then (X.Bw p K j x - (X.m0 K : ℤ)).toNat else b x

def beS (j : ℤ) (b : ℤ → ℕ) : ℕ := ∑ x ∈ (X.F.letters j).filter (· < X.F.fr j 0), X.Bdeg p K j b x

structure IsPATH (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ)
    (dd : Fin (segN X.F j) → ℕ) : Prop where
  path : ∃ P : PPath (r + K) (segN X.F j) (segLL X.F j) dd, P.mu = μ
  degs : ∀ i, segE X.F j i < X.F.fr j 0 → dd i = X.Bdeg p K j b (segE X.F j i)
  head : ∀ (i : Fin (segN X.F j)) (i' : Fin r), segE X.F j i = X.F.fr j i'.val →
    ∀ m : Fin (r + K), m.val ≤ i'.val → μ i.succ m = (X.beS p K j b : ℤ)

def IsGood [NeZero r] (j : ℤ) (b : ℤ → ℕ) (μ : Fin (segN X.F j + 1) → Fin (r + K) → ℤ) : Prop :=
  ∀ i : Fin (segN X.F j), ¬ X.F.IsW j (segE X.F j i) →
    X.thc p K j b (segE X.F j i) ≤ ((plPart μ i.castSucc (lastIdx r) : ℤ) : ℝ) ∧
    (Even (segE X.F j i) →
      ((∑ c, (tanPart μ i.succ c - tanPart μ i.castSucc c) : ℤ) : ℝ) ≤ X.oc p K j (segE X.F j i)) ∧
    (¬ Even (segE X.F j i) →
      ((∑ c, (plPart μ i.castSucc c - plPart μ i.succ c) : ℤ) : ℝ) ≤ X.oc p K j (segE X.F j i))

def Tset [NeZero r] (j : ℤ) (b : ℤ → ℕ) : Type :=
  {q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) //
    ∃ dd, X.IsPATH p K j b q.1 dd ∧ X.IsGood p K j b q.1 ∧ IsSt (tanPart q.1) q.2}

def Idx [NeZero r] (j : ℤ) (b : ℤ → ℕ) : Type :=
  {q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ) //
    ∃ dd, X.IsPATH p K j b q.1 dd ∧ X.IsGood p K j b q.1 ∧ IsSt (tanPart q.1) q.2.1 ∧
      (∀ v, q.2.2 v + 2 * X.beS p K j b < X.Qc p K j) ∧
      ∀ (i : Fin (segN X.F j)) (i' : Fin r), segE X.F j i = X.F.fr j i'.val →
        dd i + ∑ c, q.2.2 (i', c) = b (X.F.fr j i'.val)}

omit [NeZero n'] in
def Dw (O : Type) [CommRing O] (j : ℤ) : MvPolynomial (ℤ × Fin r) O :=
  Matrix.det (Matrix.of fun a c : Fin r => (MvPolynomial.X (X.F.fr (j - 1) a.val, c) : MvPolynomial (ℤ × Fin r) O))

def famEl [NeZero r] (O : Type) [CommRing O] (j : ℤ) (b : ℤ → ℕ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) : SegRing O r K :=
  plEmb O r K (X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat) *
      ∏ v : Fin r × Fin r, MvPolynomial.X (X.F.fr j v.1.val, v.2) ^ q.2.2 v) *
    segRen X.F j O (r + K) (PsiPl O (plPart q.1) (Ican (plPart q.1)) * PsiTan O (tanPart q.1) q.2.1)

def BOK (j : ℤ) (b : ℤ → ℕ) : Prop :=
  (∀ x, x ∉ X.F.letters j → b x = 0) ∧
  (∀ x ∈ X.F.letters j, X.F.IsW j x → X.Bw p K j x ≤ (b x : ℤ)) ∧ X.AdmLL p K j b

end Dat

def RestMem (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b → ∀ q : X.Idx p K j (X.restr j b), X.famEl p K O j b q.1 ∈ X.Mj p K O j b

def RestInd (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b →
      LinearIndependent O fun q : X.Idx p K j (X.restr j b) => X.famEl p K O j b q.1

def RestFin : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (j : ℤ) (b : ℤ → ℕ), (∀ x, x ∉ X.F.letters j → b x = 0) →
    Module.Finite O (X.Mj p K O j b)

def GoodPathWeight (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b → Finite (X.Tset p K j (X.restr j b)) ∧
      (1 - 1 / X.a ^ (X.Ns ^ 2)) *
        (∏ x ∈ X.F.LLset j, ((Nat.choose (b x + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)) *
        (∏ i : Fin r, ((Nat.choose ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat + (r + K) - 1)
          (r + K - 1) : ℕ) : ℝ)) ≤ (Nat.card (X.Tset p K j (X.restr j b)) : ℝ)

open Classical in
def RestMon (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r),
    X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.AdmLL p K j b → Finite (X.Tset p K j (X.restr j b)) → ∀ ρ : Fin r → ℕ,
      (Nat.card (X.Tset p K j (X.restr j b)) : ℝ) *
          (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) ^ r ≤
        ∑ e ∈ Fintype.piFinset fun i : Fin r =>
          (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = ρ i % X.Qc p K j,
            (Nat.card (X.Idx p K j (X.restr j (X.setTau j b e))) : ℝ)

theorem restSeg_of (C₀ : ℝ) (hM : RestMem C₀) (hI : RestInd C₀) (hF : RestFin) (hT : GoodPathWeight C₀) (hN : RestMon C₀) :
    RestSeg C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j
  refine ⟨fun b => (Nat.card (X.Idx p K j (X.restr j b)) : ℝ), fun b => Nat.cast_nonneg _, ?_, ?_, ?_⟩
  · intro b b' hbb
    have : X.restr j b = X.restr j b' := by
      funext x
      unfold Dat.restr
      split_ifs with hx
      · exact hbb x hx
      · rfl
    simp only [this]
  · intro b h0 hW hA
    have hB : X.BOK p K j b := ⟨h0, hW, hA⟩
    have hfin := hF p n' r K X O j b h0
    have hli := hI p n' r K X O S hX hLa hk j b hB
    have hmem := hM p n' r K X O S hX hLa hk j b hB
    have hli' : LinearIndependent O
        (fun q : X.Idx p K j (X.restr j b) => (⟨X.famEl p K O j b q.1, hmem q⟩ : X.Mj p K O j b)) := by
      refine LinearIndependent.of_comp (X.Mj p K O j b).subtype ?_
      exact hli
    have hfinI : Finite (X.Idx p K j (X.restr j b)) := hli'.finite
    have := Fintype.ofFinite (X.Idx p K j (X.restr j b))
    have h := hli'.fintype_card_le_finrank
    beta_reduce
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast h
  · intro b hA ρ
    obtain ⟨hfin, hT1⟩ := hT p n' r K X hX hLa hk j b hA
    refine le_trans ?_ (hN p n' r K X hX hLa hk j b hA hfin ρ)
    unfold Dat.segBound
    exact mul_le_mul_of_nonneg_right hT1 (by positivity)

end

section
open MvPolynomial

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

theorem segDegSet_finite {r : ℕ} (K : ℕ) (b : ℤ → ℕ) (L : Finset ℤ) (hb : ∀ x, x ∉ L → b x = 0) :
    (Dat.segDegSet (r := r) K b).Finite := by
  classical
  let B : ℤ × Fin (r + K) →₀ ℕ := Finsupp.onFinset (L ×ˢ Finset.univ) (fun v => b v.1) (by
    intro v hv
    by_contra h
    apply hv
    apply hb
    intro hL
    exact h (Finset.mem_product.mpr ⟨hL, Finset.mem_univ _⟩))
  refine (Set.finite_Iic B).subset ?_
  intro m hm v
  have h := hm v.1
  have : m (v.1, v.2) ≤ ∑ c : Fin (r + K), m (v.1, c) :=
    Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)
  rw [h] at this
  simpa [B] using this

theorem finite_restrictSupport' (R : Type) [CommRing R] (σ : Type) (s : Set (σ →₀ ℕ)) (hs : s.Finite) :
    (restrictSupport R s : Submodule R (MvPolynomial σ R)).FG := by
  have heq : (restrictSupport R s : Submodule R (MvPolynomial σ R)) =
      Submodule.span R ((fun m => (monomial m (1 : R) : MvPolynomial σ R)) '' s) := by
    refine le_antisymm (fun P hP => ?_) (Submodule.span_le.mpr ?_)
    · rw [MvPolynomial.mem_restrictSupport_iff] at hP
      rw [P.as_sum]
      refine Submodule.sum_mem _ fun m hm => ?_
      rw [show (monomial m (AddMonoidAlgebra.coeff P m) : MvPolynomial σ R) =
        AddMonoidAlgebra.coeff P m • monomial m (1 : R) by rw [smul_monomial, smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, hP (by exact_mod_cast hm), rfl⟩)
    · rintro _ ⟨m, hm, rfl⟩
      rw [SetLike.mem_coe, MvPolynomial.mem_restrictSupport_iff]
      intro m' hm'
      have h := MvPolynomial.support_monomial_subset (by exact_mod_cast hm')
      rw [Finset.mem_singleton] at h
      rw [h]; exact hm
  rw [heq]; exact Submodule.fg_span (hs.image _)

theorem restFin : RestFin := by
  intro p n' r K _ _ _ X O _ _ _ j b hb
  have hfg := finite_restrictSupport' O (ℤ × Fin (r + K)) _ (segDegSet_finite (r := r) K b (X.F.letters j) hb)
  have hN : IsNoetherian O (restrictSupport O (Dat.segDegSet (r := r) K b) : Submodule O (SegRing O r K)) :=
    isNoetherian_of_fg_of_noetherian _ hfg
  have hle : X.Mj p K O j b ≤ restrictSupport O (Dat.segDegSet (r := r) K b) := by
    intro P hP
    exact hP.1.2
  have : IsNoetherian O (X.Mj p K O j b) := isNoetherian_of_le hle
  infer_instance

end

section
open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

def sumBin (r K n : ℕ) : ℝ := ((Nat.choose (n + (r + K) - 1) (r + K - 1) : ℕ) : ℝ)

theorem sum_one_le_bin (r K n : ℕ) : 1 ≤ sumBin r K n := by
  unfold sumBin
  exact_mod_cast Nat.succ_le_of_lt (Nat.choose_pos (by omega))

theorem sum_one_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h1 : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  calc (1 : ℝ) = ∏ _i ∈ s, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) h1

theorem sum_single_le_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) (h1 : ∀ i ∈ s, 1 ≤ f i) {a : ι} (ha : a ∈ s) :
    f a ≤ ∏ i ∈ s, f i := by
  classical
  rw [← Finset.mul_prod_erase s f ha]
  have h2 : (1 : ℝ) ≤ ∏ i ∈ s.erase a, f i := sum_one_le_prod _ _ fun i hi => h1 i (Finset.mem_of_mem_erase hi)
  have h3 : 0 ≤ f a := le_trans zero_le_one (h1 a ha)
  nlinarith

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ)

def sumTset (la : Fin n' → Fin (r + K) → ℕ) (j : ℤ) : Finset (Fin r → ℕ) :=
  Fintype.piFinset fun i : Fin r =>
    (Finset.range (r * X.Qc p K j)).filter fun e => e % X.Qc p K j = X.nz p K la j (X.F.fr j i.val) % X.Qc p K j

def sumhT (t : Fin n') (v : Fin (r + K) → ℕ) : ℝ :=
  ∏ j : Fin X.F.J, ∏ x ∈ X.F.LLset (j.val : ℤ),
    if posOf n' x = t then sumBin r K ((X.a' p K t - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1

def sumSt (t : Fin n') : ℝ := ∑ v ∈ X.laSet p K t, X.sumhT p K t v

omit [NeZero n'] in
def firstSumFactor : ℝ := 1 - 1 / X.a ^ (X.Ns ^ 2)

def sumWf (j : ℤ) : ℝ := ∏ i : Fin r, sumBin r K ((X.Bw p K j (X.F.fr (j - 1) i.val) - (X.m0 K : ℤ)).toNat)

def sumTf (j : ℤ) : ℝ := (((X.Qc p K j : ℕ) : ℝ) ^ (r - 1) * max 0 (1 - (r : ℝ) / (2 * X.Y))) ^ r

theorem sum_segBound_eq (j : ℤ) (b : ℤ → ℕ) :
    X.segBound p K j b = (X.firstSumFactor * X.sumWf p K j * X.sumTf p K j) * ∏ x ∈ X.F.LLset j, sumBin r K (b x) := by
  unfold segBound firstSumFactor sumWf sumTf sumBin
  ring

end Dat

structure SumFacts {n' r : ℕ} [NeZero n'] (X : Dat n' r) (p K : ℕ) : Prop where
  tiling : ∀ φ : Fin n' → ℝ,
    ∏ t ∈ X.F.TT, φ t = ∏ j ∈ Finset.range X.F.J, ∏ x ∈ X.toLate (j : ℤ), φ (posOf n' x)
  split : ∀ (j : ℤ) (ψ : ℤ → ℝ),
    ∏ x ∈ X.toLate j, ψ x = (∏ x ∈ X.F.LLset j, ψ x) * ∏ i : Fin r, ψ (X.F.fr j i.val)
  LLsub : ∀ j x, x ∈ X.F.LLset j → x ∈ X.toLate j ∧ x < X.F.fr j 0
  frlate : ∀ j (i : Fin r), X.F.fr j i.val ∈ X.toLate j
  uniqP : ∀ j j' x x', x ∈ X.toLate j → x' ∈ X.toLate j' → posOf n' x = posOf n' x' →
    X.Pz p K j x = X.Pz p K j' x'
  kP : ∀ j x, x ∈ X.toLate j → (r + K) * X.Pz p K j x ≤ X.a' p K (posOf n' x)
  compA : ∀ t ∈ X.F.TT, sumBin r K (X.deg t) * (1 - 5 / X.Y) ≤ sumBin r K (X.a' p K t)
  compW : ∀ j (i : Fin r), sumBin r K (X.a' p K (posOf n' (X.F.fr j i.val))) * (1 - 1 / X.Y) ≤
    (((X.Pz p K j (X.F.fr j i.val) * X.Qc p K j : ℕ) : ℝ)) ^ (r + K - 1) *
      sumBin r K ((X.Bw p K (j + 1) (X.F.fr j i.val) - (X.m0 K : ℤ)).toNat)
  prodQ : ∏ j ∈ Finset.range X.F.J, X.Qc p K (j : ℤ) = p ^ n'
  perW : ∀ j (i : Fin r),
    X.Bw p K (j + X.F.J) (X.F.fr (j + X.F.J - 1) i.val) = X.Bw p K j (X.F.fr (j - 1) i.val)
  JN : X.F.J ≤ X.F.TT.card
  a32 : 32 * X.Y ≤ X.a

section Steps

variable {n' r : ℕ} [NeZero n'] {X : Dat n' r} {p K : ℕ}

omit [NeZero n'] in
theorem sum_eZ_val (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) : X.eZ e (j.val : ℤ) = e j := by
  have hJ : 0 < X.F.J := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  unfold Dat.eZ
  rw [dite_eq_left hJ]
  congr 1
  apply Fin.ext
  have h1 : ((j.val : ℤ) % (X.F.J : ℤ)) = j.val := Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)
  simp only [h1, Int.toNat_natCast]
  exact Nat.mod_eq_of_lt j.isLt

theorem sum_late_mem {j x : ℤ} (hx : x ∈ X.toLate j) :
    x ∈ X.F.letters j ∧ ¬ X.F.IsW j x ∧ x ≤ X.F.fr j (r - 1) ∧ posOf n' x ∈ X.F.TT := by
  classical
  have hx' := Finset.mem_filter.mp hx
  have h2 := Finset.mem_filter.mp hx'.1
  exact ⟨hx'.1, hx'.2, (Finset.mem_Icc.mp h2.1).2, h2.2⟩

theorem sum_bfam_late (la : Fin n' → Fin (r + K) → ℕ) (e : Fin X.F.J → Fin r → ℕ) (j : Fin X.F.J) (x : ℤ)
    (hx : x ∈ X.toLate (j.val : ℤ)) :
    X.bfam p K la e (j.val : ℤ) x = X.setTau (j.val : ℤ) (X.nz p K la (j.val : ℤ)) (e j) x := by
  obtain ⟨h1, h2, h3, -⟩ := sum_late_mem hx
  unfold Dat.bfam Dat.setTau
  rw [ite_eq_left h1, ite_eq_right h2, sum_eZ_val]
  by_cases h : X.F.fr (j.val : ℤ) 0 ≤ x
  · rw [ite_eq_left h, ite_eq_left ⟨h, h3⟩]
  · rw [ite_eq_right h, ite_eq_right (fun hh => h hh.1)]

theorem family_degrees_admissible (hr : 0 < r) (hp : 0 < p) (hLL : ∀ j x, x ∈ X.F.LLset j → x ∈ X.toLate j)
    (la : Fin n' → Fin (r + K) → ℕ) (hla : la ∈ X.LA p K) (j : ℤ) :
    X.AdmLL p K j (X.nz p K la j) := by
  classical
  intro x hx
  have hv : la (posOf n' x) ∈ X.laSet p K (posOf n' x) := (Fintype.mem_piFinset.mp hla) _
  obtain ⟨-, hle, hall⟩ := Finset.mem_filter.mp hv
  obtain ⟨hlt, hmod⟩ := hall j x (hLL j x hx) rfl
  set P := X.Pz p K j x with hPdef
  set n := X.a' p K (posOf n' x) with hn
  set s := ∑ c, la (posOf n' x) c with hs
  have hP : 0 < P := by rw [hPdef]; unfold Dat.Pz; exact pow_pos hp _
  have hdvd : P ∣ n - s := (Nat.modEq_iff_dvd' hle).mp hmod
  have hnz : X.nz p K la j x = (n - s) / P := rfl
  have hPr : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hcast : ((X.nz p K la j x : ℕ) : ℝ) = ((n : ℝ) - s) / P := by
    rw [hnz, Nat.cast_div hdvd hPr.ne', Nat.cast_sub hle]
  have hslt : s < (r + K) * P := by
    calc s < ∑ _c : Fin (r + K), P := by
            rw [hs]
            exact Finset.sum_lt_sum_of_nonempty ⟨⟨0, by omega⟩, Finset.mem_univ _⟩ fun c _ => hlt c
      _ = (r + K) * P := by simp
  have hslt' : (s : ℝ) < Dat.k (r := r) K * P := by
    unfold Dat.k
    exact_mod_cast hslt
  rw [hcast]
  constructor
  · rw [sub_div, sub_lt_sub_iff_left, div_lt_iff₀ hPr]
    exact hslt'
  · exact div_le_div_of_nonneg_right (by have : (0 : ℝ) ≤ s := Nat.cast_nonneg _; linarith) hPr.le

theorem first_sum_factor_bounds (hY : 1 ≤ X.Y) (ha : 32 * X.Y ≤ X.a) (hNs : 1 ≤ X.Ns) :
    1 - 1 / (32 * X.Y) ≤ X.firstSumFactor ∧ 0 ≤ X.firstSumFactor := by
  have ha1 : 1 ≤ X.a := by linarith
  have h1 : X.a ≤ X.a ^ (X.Ns ^ 2) := by
    calc X.a = X.a ^ 1 := (pow_one _).symm
      _ ≤ X.a ^ (X.Ns ^ 2) := pow_le_pow_right₀ ha1 (Nat.one_le_pow _ _ hNs)
  have h2 : 1 / X.a ^ (X.Ns ^ 2) ≤ 1 / (32 * X.Y) :=
    one_div_le_one_div_of_le (by linarith) (ha.trans h1)
  have h3 : 1 / (32 * X.Y) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  unfold Dat.firstSumFactor
  constructor <;> linarith

end Steps
end

section
open Finset Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

section Steps

variable {n' r : ℕ} [NeZero n'] {X : Dat n' r} {p K : ℕ}

theorem sum_one_le_hT (t : Fin n') (v : Fin (r + K) → ℕ) : 1 ≤ X.sumhT p K t v := by
  unfold Dat.sumhT
  refine sum_one_le_prod _ _ fun j _ => sum_one_le_prod _ _ fun x _ => ?_
  split_ifs
  · exact sum_one_le_bin _ _ _
  · exact le_rfl

theorem sum_mem_laSet (F : SumFacts X p K) {j0 x0 : ℤ} (hx0 : x0 ∈ X.toLate j0) (v : Fin (r + K) → ℕ)
    (h1 : ∀ c, v c < X.Pz p K j0 x0) (h2 : ∑ c, v c ≤ X.a' p K (posOf n' x0))
    (h3 : (∑ c, v c) % X.Pz p K j0 x0 = X.a' p K (posOf n' x0) % X.Pz p K j0 x0) :
    v ∈ X.laSet p K (posOf n' x0) := by
  classical
  unfold Dat.laSet
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun c => ?_, h2, fun j x hx hpos => ?_⟩
  · rw [Finset.mem_range]
    have : v c ≤ ∑ c, v c := Finset.single_le_sum (f := v) (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)
    omega
  · rw [F.uniqP j j0 x x0 hx hx0 hpos]
    exact ⟨h1, h3⟩

theorem sum_St_nontop (t : Fin n') (ht : t ∉ X.F.TT) : 1 ≤ X.sumSt p K t := by
  classical
  have h0 : (0 : Fin (r + K) → ℕ) ∈ X.laSet p K t := by
    unfold Dat.laSet
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun c => by simp, by simp, fun j x hx hpos => ?_⟩
    exact absurd (hpos ▸ (sum_late_mem hx).2.2.2) ht
  unfold Dat.sumSt
  exact (sum_one_le_hT t 0).trans
    (Finset.single_le_sum (f := fun v => X.sumhT p K t v) (fun v _ => zero_le_one.trans (sum_one_le_hT t v)) h0)

theorem sum_St_nonneg (t : Fin n') : 0 ≤ X.sumSt p K t :=
  Finset.sum_nonneg fun v _ => zero_le_one.trans (sum_one_le_hT t v)

theorem Pz_pos (hp : 0 < p) (j x : ℤ) : 0 < X.Pz p K j x := by unfold Dat.Pz; exact pow_pos hp _

theorem sum_St_LL (F : SumFacts X p K) (hr : 0 < r) (hp : 0 < p) (j0 : Fin X.F.J) {x0 : ℤ}
    (hx0 : x0 ∈ X.F.LLset (j0.val : ℤ)) :
    sumBin r K (X.a' p K (posOf n' x0)) ≤ X.sumSt p K (posOf n' x0) := by
  classical
  have hl := (F.LLsub _ _ hx0).1
  have hd := sum_digit_count (r + K) (X.a' p K (posOf n' x0)) (X.Pz p K (j0.val : ℤ) x0) (by omega) (Pz_pos hp _ _)
    (X.laSet p K (posOf n' x0)) (fun v h1 h2 h3 => sum_mem_laSet F hl v h1 h2 h3)
  have hd' : sumBin r K (X.a' p K (posOf n' x0)) ≤ ∑ v ∈ X.laSet p K (posOf n' x0),
      sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j0.val : ℤ) x0) := by
    unfold sumBin
    exact_mod_cast hd
  refine hd'.trans (Finset.sum_le_sum fun v _ => ?_)
  unfold Dat.sumhT
  have hin : ∀ j : Fin X.F.J, ∀ x ∈ X.F.LLset (j.val : ℤ), (1 : ℝ) ≤
      (if posOf n' x = posOf n' x0 then
        sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1) := by
    intro j x _
    split_ifs
    · exact sum_one_le_bin _ _ _
    · exact le_rfl
  have s1 := sum_single_le_prod (X.F.LLset (j0.val : ℤ)) (fun x => if posOf n' x = posOf n' x0 then
        sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j0.val : ℤ) x) else 1) (hin j0) hx0
  have s2 := sum_single_le_prod (Finset.univ : Finset (Fin X.F.J)) (fun j => ∏ x ∈ X.F.LLset (j.val : ℤ),
      if posOf n' x = posOf n' x0 then
        sumBin r K ((X.a' p K (posOf n' x0) - ∑ c, v c) / X.Pz p K (j.val : ℤ) x) else 1)
      (fun j _ => sum_one_le_prod _ _ (hin j)) (Finset.mem_univ j0)
  simp only [ite_true] at s1
  exact s1.trans s2

theorem sum_St_fr (F : SumFacts X p K) (hr : 0 < r) (hp : 0 < p) (j0 : ℤ) (i : Fin r) :
    ((X.Pz p K j0 (X.F.fr j0 i.val) : ℕ) : ℝ) ^ (r + K - 1) ≤ X.sumSt p K (posOf n' (X.F.fr j0 i.val)) := by
  classical
  have hl := F.frlate j0 i
  have hd := sum_label_count (r + K) (X.a' p K (posOf n' (X.F.fr j0 i.val))) (X.Pz p K j0 (X.F.fr j0 i.val)) (by omega)
    (Pz_pos hp _ _) (F.kP _ _ hl) (X.laSet p K (posOf n' (X.F.fr j0 i.val)))
    (fun v h1 h2 h3 => sum_mem_laSet F hl v h1 h2 h3)
  have hd' : ((X.Pz p K j0 (X.F.fr j0 i.val) : ℕ) : ℝ) ^ (r + K - 1) ≤
      ((X.laSet p K (posOf n' (X.F.fr j0 i.val))).card : ℝ) := by exact_mod_cast hd
  refine hd'.trans ?_
  unfold Dat.sumSt
  calc ((X.laSet p K (posOf n' (X.F.fr j0 i.val))).card : ℝ)
      = ∑ _v ∈ X.laSet p K (posOf n' (X.F.fr j0 i.val)), (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun v _ => sum_one_le_hT _ v

theorem sum_LA :
    ∑ la ∈ X.LA p K, ∏ j : Fin X.F.J, ∏ x ∈ X.F.LLset (j.val : ℤ), sumBin r K (X.nz p K la (j.val : ℤ) x) =
      ∏ t : Fin n', X.sumSt p K t := by
  classical
  unfold Dat.sumSt
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun la _ => ?_
  unfold Dat.sumhT
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finset.prod_ite_eq]
  simp [Dat.nz]

theorem sub_le_mul_one_sub_and_mem_unit_interval {P c s : ℝ} (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hs : s ≤ P) :
    s - c ≤ P * (1 - c) ∧ 0 ≤ P * (1 - c) ∧ P * (1 - c) ≤ 1 := by
  refine ⟨by nlinarith, mul_nonneg hP0 (by linarith), by nlinarith⟩

end Steps
end

end Formalism.MainNotions.SelectionLemmas.Pf
