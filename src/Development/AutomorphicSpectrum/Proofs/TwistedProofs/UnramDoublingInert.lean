module

public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasSumSpherical
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeAddVectorDetValuationStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledLatticePrimitiveIsotropicFrameCompletion
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIwasawaCellsDisjointStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralRightInvariantEqSumOpenSubgroupCosetsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBlockTriangularLeviPartUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviNormalizesUnipotentRadical
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryIwasawaCosetSurjOfLeviElementExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRadicalCosetCountOfHeisenberg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BiInvariantReplaceSameDoubleCosetSumsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualInterEqSumStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixLengthExistsOfElementaryDivisors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LengthCountGeneratingSeriesFormulaStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHeisenbergRadicalCoordinatesStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexUpLatEqProd
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLatticeInverseIndexOfElementaryDivisors
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryBlockDiagonalLeviElement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviRadicalProductLengthOfLatticeStepsStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryLeviSummationGeometricSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallCornerOfHeisenbergDualityStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryRankLeOneIntegralPoints
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmithNormalFormIntegralMatrix
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryDivisorsExistDiscretelyValuedStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriangularRowLatticeTriangularBasis
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalInductionTransitivityOfLeviExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardIntegersModUniformizerEqQSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceZeroIntegersModUniformizerCardOfCardSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceZeroIntegersIndexInUniformizerMultiplesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingIntegralInertPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.FSatakeA
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Formalism.UG Matrix MeasureTheory GlobalTheory.SatakeWeyl GlobalTheory.Doubling GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables GlobalTheory GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertZetaTop

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {q n : ℕ}

theorem v_det_mat (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (g : GU σ n) : Valued.v (mat g).det = 1 := by
  have h : cT σ (mat g) * antiJ L n * mat g = antiJ L n := g.2
  have h1 := congrArg (fun M => Valued.v (det M)) h
  have hJ : IsInt (antiJ L n) := fun i j => by
    unfold antiJ; split_ifs
    · exact one_mem _
    · exact zero_mem _
  simp only [det_mul, map_mul, cT, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hσ,
    v_det_eq_one hJ hJ GlobalTheory.UnitarySwap.antiJ_mul_self, mul_one] at h1
  exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 (by rw [sq, h1])

theorem secVal_pow {ϖ : Lˣ} (hU : IsUnramInv (ϖ : L) σ q) (χ : Lˣ →* ℂˣ) (s : ℂ) (k : ℕ) :
    secVal q χ (s + (n : ℂ) / 2) (ϖ ^ k) = varX q n (χ ϖ) s ^ k := by
  have h := P.fSatake_ord_zpow hU.2.2.2.1 (k : ℤ)
  rw [zpow_natCast] at h
  rw [secVal, Units.val_pow_eq_pow_val, h, map_pow, Units.val_pow_eq_pow_val, varX, mul_pow, ← Complex.cpow_nat_mul]
  congr 2
  push_cast
  ring

theorem section_eq (hC : Completion) {ϖ : Lˣ} (hU : IsUnramInv (ϖ : L) σ q) {χ : Lˣ →* ℂˣ} (hχ : IsUnr χ) {s : ℂ}
    {Φ : GD σ n → ℂ} (hΦ : IsSphSec σ q n χ s Φ) (g : GU σ n) {l : ℕ} (h : HasLen (mat g) l) :
    Φ (io1 σ n g) = varX q n (χ ϖ) s ^ l := by
  apply GlobalTheory.InertZeta.section_eq <;> assumption

theorem closedForm_eq {q : ℕ} (hq : q ≠ 0) (n m : ℕ) (ε s : ℂ) (α : Fin (n / 2) → ℂˣ) (hε : ε = (-1) ^ m) :
    closedForm q n (varX q n ε s) (varY q ε s) α = stdL q n α ε (s + 1 / 2) / dFac q n m s := by
  apply GlobalTheory.InertZeta.closedForm_eq <;> assumption

theorem unramDoublingInert : UnramDoublingInert := by
  intro L _ _ _ ϖ σ q n hU _ _ μ _ hμ χ hχ s Φ hΦ α w hw
  have hq : q ≠ 0 := by have := hU.2.2.2.2.2.1; omega
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hF : FracExists := _root_.GlobalTheory.InertZeta.fracExists_of_smith _root_.GlobalTheory.T.elementaryDivisors_exist_discretelyValued
  have hsec : (fun g => Φ (io1 σ n g) * w g) = fun g => varX q n (χ ϖ) s ^ len (mat g) * w g := funext fun g => by
    rw [section_eq _root_.GlobalTheory.FrameCompletion.completion hU hχ hΦ g (hF L ϖ n hU.2.2.2.1 _ (det_mat_ne_zero g))]
  have hint : ∀ Z, HasSum (fun x : GU σ n ⧸ KU σ n => varX q n (χ ϖ) s ^ len (mat x.out) * w x.out) Z →
      Integrable (fun g => Φ (io1 σ n g) * w g) μ ∧ ∫ g, Φ (io1 σ n g) * w g ∂μ = Z := fun Z hZ => by
    rw [hsec]
    refine _root_.GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets _ μ (KU σ n) (GlobalTheory.LFun.IntPtsUnitary.isOpen_isCompact_KU L ϖ σ q n hU).1 hμ _ Z (fun g k hk => ?_) hZ
    have h1 := hw.1 1 ⟨k, hk⟩ g
    have h2 := len_mat_mul (one_mem _) hk g
    simp only [OneMemClass.coe_one, one_mul] at h1 h2
    rw [h1, h2]
  refine ⟨fun hD => ?_, fun hn => hint 1 (hasSum_small _root_.GlobalTheory.InertZeta.smallRank hU hn (fun g => varX q n (χ ϖ) s ^ len (mat g) * w g)
    fun k hk => ?_)⟩
  · obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExistsU L ϖ σ q n (n / 2) hU (by omega) (by omega) (fun i => (α i : ℂ))
      fun i => (α i).ne_zero
    have h2 := hasSum_spherical hF (_root_.GlobalTheory.T.leviRadicalProductLength_of_lattice_steps _root_.GlobalTheory.T.lattice_add_vector_det_valuation _root_.GlobalTheory.T.dual_inter_eq_sum' _root_.GlobalTheory.InertZeta.RowSpan.spanEq_holds _root_.GlobalTheory.T.unitary_heisenberg_radical_coordinates)
      (_root_.GlobalTheory.InertZeta.count_of_heis _root_.GlobalTheory.T.unitary_heisenberg_radical_coordinates (_root_.GlobalTheory.InertZeta.latIndex_of_smith _root_.GlobalTheory.T.elementaryDivisors_exist_discretelyValued) _root_.GlobalTheory.T.traceZero_integers_index_in_uniformizer_multiples) (_root_.GlobalTheory.T.small_corner_of_heisenberg_duality _root_.GlobalTheory.T.unitary_heisenberg_radical_coordinates _root_.GlobalTheory.T.dual_inter_eq_sum') _root_.GlobalTheory.T.length_count_generating_series_formula (_root_.GlobalTheory.InertZeta.cosetSurj_of_leviExists _root_.GlobalTheory.InertZeta.leviExists)
      _root_.GlobalTheory.T.unitary_iwasawa_cells_disjoint _root_.GlobalTheory.InertZeta.leviExists (_root_.GlobalTheory.InertZeta.sphTrans _root_.GlobalTheory.InertZeta.leviExists) _root_.GlobalTheory.InertZeta.smallRank _root_.GlobalTheory.InertZeta.step hU (n / 2) n (by omega) (by omega)
      (fun i => (α i : ℂ)) (varX q n (χ ϖ) s) (varY q (χ ϖ) s) φ (fun i => (α i).ne_zero) (by
        rw [varX, varY, neg_add, neg_add, Complex.cpow_add _ _ hq0, Complex.cpow_add _ _ hq0, Complex.cpow_neg_one,
          Complex.cpow_neg _ (n : ℂ), Complex.cpow_natCast]
        field_simp) hD.1 hD.2 hφ h1
    have h3 := hint _ (_root_.GlobalTheory.T.biInvariant_replace_same_double_coset_sums _ (KU σ n) (P.isCommensurated_integral_unitary_of_unramified hU n) (fun g => varX q n (χ ϖ) s ^ len (mat g)) w φ _
      (fun a b g => by simp only [len_mat_mul a.2 b.2]) hw.1 (fun g => by
        rw [hw.2.2 _ (Final.DosetIndMem _ _ ℂ g), Final.SatakeInert L ϖ σ q n (n / 2) hU (by omega) (by omega) _
          (fun i => (α i).ne_zero) _ (Final.DosetIndMem _ _ ℂ g) φ hφ, Pi.smul_apply, h1, smul_eq_mul, mul_one]) h2)
    exact ⟨h3.1, h3.2, fun m hm => h3.2.trans (closedForm_eq hq n m _ s α hm)⟩
  · have h1 := hw.1 1 ⟨k, hk⟩ 1
    simp only [OneMemClass.coe_one, one_mul] at h1
    rw [len_of_mem hk, h1, hw.2.1, pow_zero, mul_one]

end GlobalTheory.CompanionTheory.InertZetaTop

end
