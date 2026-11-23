module

public import Development.AutomorphicSpectrum.Statements.GeometryStatements.NonemptyEquivOfCardHom
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderScalarExtension
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderBaseChangeGeneric
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderComapHomStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingIsoFinite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqTopOfEtale
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsDualToInvariantDifferentials
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEndomorphismLift
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEtaleOfUnit
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupFiniteOfProper
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrderNoetherianStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueBtOrderEmbedding
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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

namespace GlobalTheory.CompanionTheory.Ar.BT

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct

theorem lemmaBT_holds : LemmaBT := by
  unfold GlobalTheory.CompanionTheory.Ar.BT.LemmaBT
  intro R _ _ _ _ T _ _ Γ S G _ _ x N i hi hG
  refine ⟨GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ, ?_,
    fun hN => _root_.GlobalTheory.CompanionTheory.Ar.BT.EtaleTop.btOrder_top_eq_top_of_etale R T Γ
      (_root_.GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit R T Γ S G x N i hi hG hN), ?_, ?_,
    fun L _ _ M => _root_.GlobalTheory.CompanionTheory.Ar.BT.omega_isDerAtOne R T Γ S G x N i hi hG L M⟩
  · obtain ⟨j, hj, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.exists_unique_emb_btOrder_top R T Γ
    obtain ⟨hoi, htr⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.isOpenImmersion_emb_and_translatesCover R T Γ j hj
    refine ⟨j, hj, hoi, htr, fun hP => ?_⟩
    exact _root_.GlobalTheory.CompanionTheory.Ar.BT.FiniteIso.isIso_of_finite R T Γ j hj
      (_root_.GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper R T Γ S G x N i hi hP)
  · intro a _ α hα f hf
    obtain ⟨a', _, ha'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion R T Γ S G x N i hi a
    refine GlobalTheory.T.btOrder_comap_hom R T Γ T Γ a' α (fun t => ?_) f hf
    obtain ⟨_, _, hcancel, _⟩ := hi
    apply hcancel
    rw [Over.comp_left, Category.assoc, ha', hα t]
  · intro R' _ _ _ Γ' F hF
    obtain ⟨hd, hΓ'⟩ :=
      _root_.GlobalTheory.CompanionTheory.Ar.BT.btOrder_baseChange R T Γ R' Γ' F hF
    obtain ⟨-, e, he⟩ := _root_.GlobalTheory.CompanionTheory.Ar.BT.ext_tensor_base_change R T R' _
      (GlobalTheory.T.btOrder_isHopfOrder_noetherian R T Γ) hd
    rw [hΓ']
    exact ⟨e, he⟩

end GlobalTheory.CompanionTheory.Ar.BT
