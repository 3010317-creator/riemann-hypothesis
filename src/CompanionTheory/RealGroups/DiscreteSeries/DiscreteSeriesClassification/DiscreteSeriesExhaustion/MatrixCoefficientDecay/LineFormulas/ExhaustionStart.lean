module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlagFacts
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.Fub2
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FubiniParabolicMultiple
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InitialStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.LineFacts
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.MaximalCompactStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SlabStatement
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

namespace CompanionTheory.RgExh.Dec.N.S

theorem exhaustion_start : CompanionTheory.RgExh.Dec.Start :=
  _root_.GlobalTheory.CompanionTheory.RgStart.startOf _root_.GlobalTheory.CompanionTheory.GradFlag.flagFacts _root_.GlobalTheory.CompanionTheory.PSubFlag.psubEq _root_.GlobalTheory.CompanionTheory.GradLine.lineFacts _root_.GlobalTheory.CompanionTheory.SlabLemma.slab (_root_.GlobalTheory.CompanionTheory.RgFubOf.fubini_of_parabolic_multiple _root_.GlobalTheory.CompanionTheory.FubNM.fub2) _root_.GlobalTheory.CompanionTheory.RgKMaj.kMaj

end CompanionTheory.RgExh.Dec.N.S
