module

public import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
public import Mathlib.RingTheory.MvPowerSeries.Equiv
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Chart
namespace GlobalTheory.JetSer
variable {R : Type} [CommRing R] {κ : Type}

theorem jet_mk_eq_iff (m : ℕ) (P Q : MvPolynomial κ R) :
    (Ideal.Quotient.mk _ P : JetR R κ m) = Ideal.Quotient.mk _ Q ↔
      ∀ e : κ →₀ ℕ, Finsupp.degree e < m + 1 → P.coeff e = Q.coeff e := by
  rw [Ideal.Quotient.eq]
  refine (MvPolynomial.mem_pow_idealOfVars_iff' (m + 1) (P - Q)).trans ?_
  simp only [MvPolynomial.coeff_sub, sub_eq_zero]

/-- Exponents of monomials that survive in a jet of order `m`. -/
abbrev JetExponent (κ : Type) (m : ℕ) := {d : κ →₀ ℕ // d.degree ≤ m}

private def jetCoefficientMap (R κ : Type) [CommRing R] (m : ℕ) :
    JetR R κ m →ₗ[R] JetExponent κ m →₀ R := by
  let I := MvPolynomial.idealOfVars κ R ^ (m + 1)
  let res : MvPolynomial κ R →ₗ[R] JetExponent κ m →₀ R :=
    (Finsupp.lcomapDomain (R := R) (M := R) Subtype.val Subtype.val_injective).comp
      (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap
  refine (I.restrictScalars R).liftQ res ?_
  intro p hp
  rw [LinearMap.mem_ker]
  ext e
  change p.coeff e.val = 0
  exact (MvPolynomial.mem_pow_idealOfVars_iff' (m + 1) p).mp hp e.val (Nat.lt_succ_of_le e.prop)

private theorem jetCoefficientMap_mk (m : ℕ) (p : MvPolynomial κ R) (e : JetExponent κ m) :
    jetCoefficientMap R κ m (Ideal.Quotient.mk _ p) e = p.coeff e.val :=
  rfl

/-- A jet is determined by a finitely supported vector of its surviving monomial coefficients. -/
@[no_expose]
def jetMonomialEquiv (R κ : Type) [CommRing R] (m : ℕ) :
    JetR R κ m ≃ₗ[R] JetExponent κ m →₀ R :=
  LinearEquiv.ofBijective (jetCoefficientMap R κ m) ⟨by
    intro p q h
    obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective p
    obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact (jet_mk_eq_iff m P Q).2 fun d hd =>
      congrArg (fun a : JetExponent κ m →₀ R => a ⟨d, Nat.le_of_lt_succ hd⟩) h, by
    intro v
    let coeffs : MvPolynomial κ R ≃ₗ[R] (κ →₀ ℕ) →₀ R := AddMonoidAlgebra.coeffLinearEquiv R
    let inc : JetExponent κ m ↪ (κ →₀ ℕ) := ⟨Subtype.val, Subtype.val_injective⟩
    refine ⟨Ideal.Quotient.mk _ (coeffs.symm (v.embDomain inc)), ?_⟩
    ext e
    rw [jetCoefficientMap_mk]
    change coeffs (coeffs.symm (v.embDomain inc)) (inc e) = v e
    rw [coeffs.apply_symm_apply, Finsupp.embDomain_apply_self]⟩

@[simp]
theorem jetMonomialEquiv_mk (m : ℕ) (p : MvPolynomial κ R) (e : JetExponent κ m) :
    jetMonomialEquiv R κ m (Ideal.Quotient.mk _ p) e = p.coeff e.val :=
  jetCoefficientMap_mk m p e

theorem jetMonomialEquiv_trunc (m : ℕ) (p : JetR R κ (m + 1)) (e : JetExponent κ m) :
    jetMonomialEquiv R κ m (jetTruncR R κ m p) e =
      jetMonomialEquiv R κ (m + 1) p ⟨e.val, e.prop.trans (Nat.le_succ m)⟩ := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective p
  change jetMonomialEquiv R κ m (Ideal.Quotient.mk _ q) e =
    jetMonomialEquiv R κ (m + 1) (Ideal.Quotient.mk _ q) ⟨e.val, e.prop.trans (Nat.le_succ m)⟩
  rw [jetMonomialEquiv_mk, jetMonomialEquiv_mk]

/-- For each bound, only finitely many coefficients of degree at most that bound are nonzero. -/
def HasFiniteDegreeSupport (g : MvPowerSeries κ R) : Prop :=
  ∀ m, (Function.support fun e : JetExponent κ m => coeff e.val g).Finite

/-- Jets of every order that agree under one-step truncation. -/
abbrev CompatibleJets (R κ : Type) [CommRing R] :=
  {p : ∀ m, JetR R κ m // ∀ m, jetTruncR R κ m (p (m + 1)) = p m}

private def seriesOfJets (p : CompatibleJets R κ) : MvPowerSeries κ R :=
  fun e => jetMonomialEquiv R κ e.degree (p.val e.degree) ⟨e, le_rfl⟩

private theorem seriesOfJets_coeff (p : CompatibleJets R κ) (m : ℕ) (e : JetExponent κ m) :
    coeff e.val (seriesOfJets p) = jetMonomialEquiv R κ m (p.val m) e := by
  obtain ⟨e, he⟩ := e
  induction m, he using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    calc
      _ = jetMonomialEquiv R κ m (p.val m) ⟨e, hm⟩ := ih
      _ = _ := by rw [← p.property m, jetMonomialEquiv_trunc]

private def jetOfSeries (g : {g : MvPowerSeries κ R // HasFiniteDegreeSupport g}) (m : ℕ) :
    JetR R κ m :=
  (jetMonomialEquiv R κ m).symm (Finsupp.ofSupportFinite _ (g.property m))

private theorem jetOfSeries_coeff (g : {g : MvPowerSeries κ R // HasFiniteDegreeSupport g})
    (m : ℕ) (e : JetExponent κ m) :
    jetMonomialEquiv R κ m (jetOfSeries g m) e = coeff e.val g.val :=
  congrArg (fun v : JetExponent κ m →₀ R => v e) ((jetMonomialEquiv R κ m).apply_symm_apply _)

/-- Over any coordinate set, compatible jets describe exactly the power series with
finitely many nonzero coefficients in each bounded range of degrees. -/
@[no_expose]
def compatibleJetsEquiv (R κ : Type) [CommRing R] :
    CompatibleJets R κ ≃ {g : MvPowerSeries κ R // HasFiniteDegreeSupport g} where
  toFun p := ⟨seriesOfJets p, fun m => by
    refine (jetMonomialEquiv R κ m (p.val m)).support.finite_toSet.subset ?_
    intro e he
    apply Finsupp.mem_support_iff.mpr
    rw [← seriesOfJets_coeff p m e]
    exact he⟩
  invFun g := ⟨jetOfSeries g, fun m => by
    apply (jetMonomialEquiv R κ m).injective
    ext e
    simp only [jetMonomialEquiv_trunc, jetOfSeries_coeff]⟩
  left_inv p := by
    apply Subtype.ext
    funext m
    apply (jetMonomialEquiv R κ m).injective
    ext e
    exact (jetOfSeries_coeff _ m e).trans (seriesOfJets_coeff p m e)
  right_inv g := by
    apply Subtype.ext
    ext e
    exact jetOfSeries_coeff g e.degree ⟨e, le_rfl⟩

theorem compatibleJetsEquiv_coeff (p : CompatibleJets R κ) (m : ℕ) (e : JetExponent κ m) :
    coeff e.val ((compatibleJetsEquiv R κ p).val) = jetMonomialEquiv R κ m (p.val m) e :=
  seriesOfJets_coeff p m e

variable [Finite κ]

@[simp]
theorem jetMonomialEquiv_toJet (m : ℕ) (g : MvPowerSeries κ R) (e : JetExponent κ m) :
    jetMonomialEquiv R κ m (toJet m g) e = coeff e.val g := by
  unfold toJet
  rw [jetMonomialEquiv_mk, coeff_truncTotal_eq_ite, ite_eq_left (Nat.lt_succ_of_le e.prop)]

theorem toJet_eq_mk_iff (m : ℕ) (g : MvPowerSeries κ R) (Q : MvPolynomial κ R) :
    toJet m g = Ideal.Quotient.mk _ Q ↔
      ∀ e : κ →₀ ℕ, Finsupp.degree e < m + 1 → coeff e g = Q.coeff e := by
  unfold toJet
  rw [jet_mk_eq_iff]
  refine forall₂_congr fun e he => ?_
  rw [coeff_truncTotal_eq_ite, if_pos he]

theorem toJet_eq_iff (m : ℕ) (g g' : MvPowerSeries κ R) :
    toJet m g = toJet m g' ↔ ∀ e : κ →₀ ℕ, Finsupp.degree e < m + 1 → coeff e g = coeff e g' := by
  refine (toJet_eq_mk_iff m g _).trans (forall₂_congr fun e he => ?_)
  rw [coeff_truncTotal_eq_ite, if_pos he]

theorem toJet_coe (m : ℕ) (Q : MvPolynomial κ R) :
    toJet m (Q : MvPowerSeries κ R) = Ideal.Quotient.mk _ Q :=
  (toJet_eq_mk_iff m _ Q).2 fun e _ => MvPolynomial.coeff_coe Q e


variable (R κ) in
def toJetHom (m : ℕ) : MvPowerSeries κ R →ₐ[R] JetR R κ m :=
  (truncTotalAlgHom κ R (m + 1)).restrictScalars R

theorem toJetHom_apply (m : ℕ) (g : MvPowerSeries κ R) : toJetHom R κ m g = toJet m g := rfl

theorem jetTruncR_toJet (m : ℕ) (g : MvPowerSeries κ R) :
    jetTruncR R κ m (toJet (m + 1) g) = toJet m g := by
  symm
  refine (toJet_eq_mk_iff m g (truncTotal (m + 1 + 1) g)).2 fun e he => ?_
  rw [coeff_truncTotal_eq_ite, if_pos (by omega)]

theorem jetAug_toJet (m : ℕ) (g : MvPowerSeries κ R) :
    jetAug R κ m (toJet m g) = constantCoeff g := by
  show MvPolynomial.aeval (fun _ : κ => (0 : R)) (truncTotal (m + 1) g) = _
  rw [MvPolynomial.aeval_zero', MvPolynomial.constantCoeff_eq, coeff_truncTotal_eq_ite, if_pos (by simp)]
  rfl

theorem eq_of_toJet_eq {g g' : MvPowerSeries κ R} (h : ∀ m, toJet m g = toJet m g') : g = g' := by
  ext e
  exact (toJet_eq_iff _ g g').1 (h (Finsupp.degree e)) e (Nat.lt_succ_self _)

theorem exists_toJet_eq (p : ∀ m, JetR R κ m) (hp : ∀ m, jetTruncR R κ m (p (m + 1)) = p m) :
    ∃ g : MvPowerSeries κ R, ∀ m, toJet m g = p m := by
  let family : CompatibleJets R κ := ⟨p, hp⟩
  refine ⟨(compatibleJetsEquiv R κ family).val, fun m => ?_⟩
  apply (jetMonomialEquiv R κ m).injective
  ext e
  rw [jetMonomialEquiv_toJet]
  exact compatibleJetsEquiv_coeff family m e

theorem exists_jetHom {σ : Type} (a : σ → MvPowerSeries κ R) (ha : ∀ j, constantCoeff (a j) = 0) (m : ℕ) :
    ∃ ψ : JetR R σ m →ₐ[R] JetR R κ m, ∀ j, ψ (zR m j) = toJet m (a j) :=
  ⟨jetLift R (RingHom.ker (jetAug R κ m)) (ker_jetAug_pow κ m) (fun j => toJet m (a j))
    (fun j => (jetAug_toJet m (a j)).trans (ha j)), fun j => jetLift_zR _ _ _ _ j⟩

theorem jetHom_toJet {σ : Type} [Finite σ] (a : σ → MvPowerSeries κ R) (ha : ∀ j, constantCoeff (a j) = 0) (m : ℕ)
    (ψ : JetR R σ m →ₐ[R] JetR R κ m) (hψ : ∀ j, ψ (zR m j) = toJet m (a j)) (g : MvPowerSeries σ R) :
    ψ (toJet m g) = toJet m (subst a g) := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
  have hpoly : ∀ Q : MvPolynomial σ R, ψ (Ideal.Quotient.mk _ Q) = toJet m (subst a (Q : MvPowerSeries σ R)) := by
    intro Q
    rw [subst_coe, ← toJetHom_apply]
    have : ψ.comp (Ideal.Quotient.mkₐ R _) = (toJetHom R κ m).comp (MvPolynomial.aeval a) := by
      apply MvPolynomial.algHom_ext
      intro j
      rw [AlgHom.comp_apply, AlgHom.comp_apply, MvPolynomial.aeval_X, toJetHom_apply]
      exact hψ j
    exact AlgHom.congr_fun this Q
  refine (hpoly (truncTotal (m + 1) g)).trans ((toJet_eq_iff m _ _).2 fun e he => ?_)
  set r : MvPowerSeries σ R := (truncTotal (m + 1) g : MvPolynomial σ R) - g with hr
  have hro : ((m + 1 : ℕ) : ℕ∞) ≤ r.order := nat_le_order fun d hd => by
    rw [hr, map_sub, MvPolynomial.coeff_coe, coeff_truncTotal_eq_ite, if_pos hd, sub_self]
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (a i).order := le_iInf fun i => one_le_order_iff_constCoeff_eq_zero.2 (ha i)
  have h2 : ((m + 1 : ℕ) : ℕ∞) ≤ (subst a r).order := by
    refine le_trans ?_ (le_order_subst hs r)
    calc ((m + 1 : ℕ) : ℕ∞) = 1 * ((m + 1 : ℕ) : ℕ∞) := (one_mul _).symm
      _ ≤ _ := mul_le_mul' h1 hro
  have h3 : coeff e (subst a r) = 0 := coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast he) h2)
  rwa [hr, ← substAlgHom_apply hs, map_sub, map_sub, sub_eq_zero, substAlgHom_apply, substAlgHom_apply] at h3

theorem jetAlg : JetAlgSt := fun R _ κ _ =>
  ⟨fun m => ⟨toJetHom R κ m, fun _ => rfl, fun j => toJet_X m j⟩,
    fun m g => ⟨jetTruncR_toJet m g, jetAug_toJet m g⟩,
    fun _ _ h => eq_of_toJet_eq h, exists_toJet_eq,
    fun _ _ a ha m => ⟨exists_jetHom a ha m, jetHom_toJet a ha m⟩⟩

end GlobalTheory.JetSer
