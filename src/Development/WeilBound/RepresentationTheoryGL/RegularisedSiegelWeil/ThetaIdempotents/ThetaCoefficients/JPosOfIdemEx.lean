module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlternativeLocalComputationOfComponents
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactnessStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightBoundStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwasawaDecompositionStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PositivityStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SectionEigenfunctionMaximalCompact
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EigenOfRightInvariant
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceRankCutOfAlternative
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformBoundednessStatement
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.GoodPlacesOutsideFiniteSet
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

open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L

namespace GlobalTheory.CompanionTheory.Jp

theorem jPos_of_idemEx : IdemEx → JPos := by
  intro _ D n r t hrt hr ψ hψ χ hχ hres nb hnb S
  have hB2 : SplitPlaceRankCutEigenvalue := _root_.GlobalTheory.CompanionTheory.Jp.split_place_rank_cut_of_local_computation (_root_.GlobalTheory.CompanionTheory.Jp.jpAlt_of_steps _root_.GlobalTheory.CompanionTheory.Jp.Iw.jpIw _root_.GlobalTheory.CompanionTheory.Jp.Hgt.jpHgt _root_.GlobalTheory.CompanionTheory.Jp.Unif.jpUnif _root_.GlobalTheory.CompanionTheory.Jp.Cmp.jpCmp _root_.GlobalTheory.CompanionTheory.Jp.Pos.jpPos)
  obtain ⟨v, hvS, hpsi, τ, hchi⟩ := _root_.PositivityTheory.Rg.Rsw.jacquet_piatetski_first_bound D r ψ hψ χ hχ hres S
  obtain ⟨C, c, hK, hd, hc, hint⟩ := hB2 D n r t hrt hr ψ hψ nb hnb v hpsi τ
  refine ⟨v, hvS, C, c, hK, hd, hc, ?_⟩
  intro νv hH hP z f _ hlaw hinv g
  exact _root_.GlobalTheory.CompanionTheory.Jp.B3.eigen_of_rightInvariant D n χ nb hnb v τ hchi C νv hH z (c z) (hint νv hH hP z) f hlaw hinv g

end GlobalTheory.CompanionTheory.Jp
