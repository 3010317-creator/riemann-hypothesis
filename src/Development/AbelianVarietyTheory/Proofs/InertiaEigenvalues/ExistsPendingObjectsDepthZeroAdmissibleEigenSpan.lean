module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
public import Formalism.SharpRestriction.LevelLetterCocycles.FourthHypothesisOfLifting
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralActsOnHeckeEigenspaceOfTypeSections
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroAdmissibleAllPendingData
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteGroupDataSeriesIdempotentsLabelSums
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLabelInertiaEigenvalues
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlaceOfOverTypePrime
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LabelTwistMultipliesRootsOfTameLabelsStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyGroupAlgebraCentreLatticeAction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyLocalisedFormsTypeSectionHecke
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointParameterIsTypeParameterOfTame
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RowsExhaust
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalHeckeScalarOnTypeSpacesAllPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionEigenOfLocalisedFormsSection
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

namespace GlobalTheory.PendClose

theorem main : ∀ (D : D7) (M : MtFam D), HeckeTied D M → HeckeRational D M → AVTied D M →
    (∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par, ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w) →
    SumRepresentations.tie0 D → SumRepresentations.adm5 D → IneRep D → LabDepth D → LabGen D → ZLStable D → CenInt D → OnMtPreservesTypeV D →
    SerLL D → CoeffRingsHaveRootsOfUnity D → DepthZ D → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) → ∃ P : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ P ∧ EigSpan P := by
  intro D M hT hR hA hPar h0 h5 hIne hDep hGen hZL hCI hCT hSer hZeta hDZ hAdm
  have hSU : GlobalTheory.EtaJoin.SplitUnif D := GlobalTheory.SplitConjPlace.splitEx_all D
  have hSec : ∀ i, Nonempty (Sec D i) := fun i =>
    _root_.GlobalTheory.PendOf.SecProof.main D M i hT hR hA hSU (_root_.GlobalTheory.HeckeScalarAll.heckeScalar_all D M hT hA i)
  obtain ⟨lz, hlz⟩ := _root_.GlobalTheory.LzExist.exists_lz_serEq D
  obtain ⟨Ω, hΩ⟩ := _root_.GlobalTheory.PendOf.LabIneAll.main D hIne hDep hGen
  have hChar : LabChar D := GlobalTheory.T.labelTwistMultipliesRoots_of_tame_labels D h0 hIne hDep hGen
  obtain ⟨Z⟩ := _root_.GlobalTheory.CenOAct.cenO_nonempty D hSec hZL hCI hCT
  have hPr : PrType D := _root_.GlobalTheory.PendOf.PrTypeProof.main D hSec
  have hSplit : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v) := fun k v =>
    _root_.GlobalTheory.TypeSplit.main D k _ (D.naut.plGw_over k v)
  have hPS : ParSurj D := _root_.GlobalTheory.ParOfPoint.main D hPar h0 h5 hSplit hDep hDZ
  let P : PairedCharacterCondition.Pend D := mk lz hlz hSer hZeta Ω hΩ hChar Z hZL hPr hPS
  exact ⟨P, _root_.GlobalTheory.AdmDepthZero.main D P hAdm, _root_.GlobalTheory.PendOf.EigSpanProof.main D P hSec hCT⟩

end GlobalTheory.PendClose
