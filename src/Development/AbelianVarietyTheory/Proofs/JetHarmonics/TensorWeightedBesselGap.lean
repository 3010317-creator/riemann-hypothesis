module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionLocalityInvariantFactorFiniteSumStatement
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselSumStatement
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MirrorDecomposition.HpkRowEsI
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.BesselPieri

theorem gg_mul {k r : ℕ} {a b : Mx k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = _ := by rw [ha', hb']

theorem one_gg (k r : ℕ) : (1 : Mx k r) ∈ GG k r := by
  show (1 : Mx k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

theorem one_N (k r : ℕ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.Nset k r :=
  ⟨one_gg k r, fun _ _ _ => Matrix.one_apply, fun _ _ _ _ _ => Matrix.one_apply⟩

theorem one_UW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : (1 : Mx k r) ∈ Formalism.QuantumDeterminants.UWset k r z :=
  ⟨one_gg k r, fun _ => ⟨Matrix.one_mulVec _, Matrix.one_mulVec _⟩, Matrix.one_mulVec _⟩

theorem herm_iso {ι : Type} [Fintype ι] [DecidableEq ι] {Γ A : Matrix ι ι ℂ} (hA : Aᴴ * Γ * A = Γ) (x y : ι → ℂ) :
    Formalism.QuantumDeterminants.herm Γ (A *ᵥ x) (A *ᵥ y) = Formalism.QuantumDeterminants.herm Γ x y := by
  unfold Formalism.QuantumDeterminants.herm
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hA]

theorem coef_inv {k r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ}
    {d : ℕ} (hρ : IsFRep ρ Γ d) {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {om om' : ι → ℂ}
    (h1 : ∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z, ρ g *ᵥ om = om) (h2 : ∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z', ρ g *ᵥ om' = om')
    {γ : Mx k r} (hγ : γ ∈ GG k r) (p : B.SS k r) (hp : D.inSS p) :
    Formalism.QuantumDeterminants.herm Γ (ρ (B.sgs p γ) *ᵥ om') om = Formalism.QuantumDeterminants.herm Γ (ρ γ *ᵥ om') om := by
  obtain ⟨hh, hn, hh', hn'⟩ := hp
  obtain ⟨-, -, -, hmul, hiso, -⟩ := hρ
  have hi := PI.MirrorSection₂.uw_inv hh
  have ni := PI.MirrorSection₂.n_inv hn
  have ha : (Matrix.of p.1.1)⁻¹ * (Matrix.of p.1.2)⁻¹ ∈ GG k r := gg_mul hi.1 ni.1
  have e1 := h1 _ ⟨_, hi, _, ni, rfl⟩
  have e2 : ρ (Matrix.of p.2.1) *ᵥ om' = om' := h2 _ ⟨_, hh', 1, one_N k r, (Matrix.mul_one _).symm⟩
  have e3 : ρ (Matrix.of p.2.2) *ᵥ om' = om' := h2 _ ⟨1, one_UW k r _, _, hn', (Matrix.one_mul _).symm⟩
  unfold B.sgs
  rw [hmul _ (gg_mul (gg_mul ha hγ) hn'.1) _ hh'.1, hmul _ (gg_mul ha hγ) _ hn'.1, hmul _ ha _ hγ,
    ← mulVec_mulVec, e2, ← mulVec_mulVec, e3, ← mulVec_mulVec]
  conv_lhs => rw [← e1]
  exact herm_iso (hiso _ ha) _ _

end GlobalTheory.BesselPieri
