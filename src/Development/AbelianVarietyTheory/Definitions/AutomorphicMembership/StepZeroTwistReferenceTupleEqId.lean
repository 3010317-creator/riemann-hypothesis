module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexFormsFiniteDimensional
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Formalism.LocalToGlobal.Columns.CoefColLemmas
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology
open scoped TensorProduct

namespace GlobalTheory.Mem.ColAd

structure PtLaw {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    (S : GStep E K n) (b : S.β) (pt : DecoF E n ST SG Q → S.D b) (c : ℕ) : Prop where
  rat : ∀ γ : UF E n, ∃ g : S.G b, S.gam b g = ufGL E n γ ∧ S.chr b g = 1 ∧
    ∀ p, pt (((γ, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) = g • pt p
  lev : ∀ k : GLQ E n Q, (∀ P, k P ∈ prinCong n P.1 c) → ∃ g : S.G b, S.gam b g = 1 ∧ S.chr b g = 1 ∧
    ∀ p, pt (((1, 1, k) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • p) = g • pt p

section Form

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : InfF D) (V : HSp D) {n : ℕ} [NeZero n] (hn : V.rank = n) {ι : Type} [Fintype ι] (t : ι ≃ D.what₂.Tau)
  {K : Type} [Field K] [NumberField K] [StarRing K] (emb : ι → D.host.E →+* K) (σ : K →+* ℂ)
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 D.host.E))} (S : GStep D.host.E K n) (b : S.β)
  (pt : DecoF D.host.E n ST SG Q → S.D b) (c : ℕ) (x₀ : GL (Fin n) (AfE D.host.F D.host.E)) (l : (Fr emb σ n → ℂ) →ₗ[ℂ] ℂ)

def adFun : (S.Cl → Fr emb σ n → ℂ) →ₗ[ℂ] (GA D V → ℂ) :=
  LinearMap.pi fun g => l ∘ₗ lT (Gr emb σ n) (infN θ V hn t g) ∘ₗ valL S emb σ b (pt (ptOf ST SG Q c (finN V hn g * x₀)))

variable {S b pt c emb σ} {lam : ι → DomWeight n} {φ : S.Cl → Fr emb σ n → ℂ}

variable {V x₀}


end Form

end GlobalTheory.Mem.ColAd

namespace GlobalTheory.Mem.Col2.ColIn

open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr

attribute [local instance] starE

variable {B : Base} {X : PreX B.toPre} (I : ColIn B X)

instance neZeroN (R : Ranks) (j : ℕ) : NeZero (R.N j) := ⟨(R.N_pos j).ne'⟩

instance neZeroN' (R : Ranks) : NeZero (R.N R.m - 1) := ⟨by have := R.m_add_three_le_k; unfold Ranks.N; omega⟩

theorem zero_succ_ne (R : Ranks) : 0 + 1 ≠ R.m := by have := R.two_le_m; omega

def baseTop (u : B.Word) (a : I.ι) : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u B.R.m :=
  tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u (DecoF.base _ _ _ _ _)

variable {I}

theorem Ok.gram_X (h : I.Ok) (j : ℕ) : (B.sp.X j).gram = 1 := by
  obtain ⟨hs, h1, -⟩ := h.spaces
  rw [h1 j]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem Ok.exists_isPtOf (h : I.Ok) (u : B.Word) (a : I.ι) {n : ℕ}
    (p : DecoF B.host.E n ((B.primes X).vT u) (B.primes X).vGs (I.Q a)) : ∃ x, IsPtOf B.sp.cm x p := by
  classical
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hd : Disjoint ((B.primes X).vT u) (rowSG (B.primes X) I.sel (I.tup a)) := Finset.disjoint_left.2 fun P h1 h2 =>
    GlobalTheory.Proof.NarrowJetMoments.notMem_rowSG hPr h.sel_ok (hPr.T_prime u) (h.T_mem u) (hPr.T_ne_g u) h2 (T_mem_vT hPr u ⟨P, h1⟩)
  refine PtExist.exists_isPtOf_cm B.sp.cm n _ _ _ p (hd.mono_right Finset.subset_union_left) (hd.mono_right Finset.subset_union_right)
    ((LevTwist.levOk_twists B X I h).2.1.mono_right (I.Q_subset_SQ a)) fun P hP => ?_
  have h1 := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem P
  unfold Sall at h1
  simp only [Finset.mem_union] at h1 hP ⊢
  exact (h1 hP).1

end GlobalTheory.Mem.Col2.ColIn

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr
open GlobalTheory.Mem.Col2.ColIn (zero_succ_ne)

attribute [local instance] starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def ptAt (u : B.Word) (a : I.ι) {j : ℕ} (hj : j + 1 ≠ B.R.m) (b : Idx I.sel (I.tup a) (I.idx a) j)
    (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u j) : (I.stp u a j).D b :=
  ⟨(p, ∅), by rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj]; rfl⟩

variable {I}

variable (h : I.Ok) (l : I.Laws) (Z : Later B (I.cols l)) {θ : InfF (I.rec7 l Z)} (hθ : IsInfFam θ)

def eT : Tau B.R ≃ (I.rec7 l Z).what₂.Tau := Equiv.refl _


def src (u : B.Word) : Z.W.Mu u →ₗ[ℂ] ((I.stp u I.mu0 0).Cl → Fr B.fields.emb B.embLL (B.R.N 0) → ℂ) :=
  ((I.cols l).mem u).A.Mram.subtype ∘ₗ (Z.W.eMu u).toLinearMap


include l in
theorem idx_zero_eq (u : B.Word) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) (c : (I.stp u a 0).Cl) : c.1 = b := by
  obtain ⟨c', rfl⟩ := (l.bij0 u a b).2 c
  rfl

theorem stepZeroTwist_reference_tuple_eq_id (u : B.Word) (φ : (I.stp u I.mu0 0).Cl → Fr B.fields.emb B.embLL (B.R.N 0) → ℂ) :
    (I.cols l).e0Tw u I.mu0 φ = φ := by
  have key : ∀ c, I.eCls0 l u I.mu0 c = c := fun c => by
    obtain ⟨b, q⟩ := c
    obtain rfl : b = (l.idx0 I.mu0).some := idx_zero_eq l u _ _ ⟨b, q⟩
    have e : I.pt0 u I.mu0 I.mu0 ((I.stp u I.mu0 0).rep ⟨_, q⟩) = (I.stp u I.mu0 0).rep ⟨_, q⟩ := by
      have := ((I.stp u I.mu0 0).rep ⟨_, q⟩).2
      rw [ysAt_ys_of_ne I.sel _ _ (zero_succ_ne B.R)] at this
      exact Subtype.ext (Prod.ext (extTo_self (I.twistPrimes_reference_tuple_eq_empty.symm ▸ Finset.disjoint_empty_right _ : Disjoint _ (I.Q I.mu0)) _) (Eq.symm this))
    show (I.stp u I.mu0 0).cl _ (I.pt0 u I.mu0 I.mu0 _) = _
    rw [e]
    exact congrArg (Sigma.mk _) ((I.stp u I.mu0 0).rp_spec _ q)
  funext c
  exact congrArg φ ((Equiv.symm_apply_eq _).2 (key c).symm)

end GlobalTheory.Mem.Col2.TC

end
