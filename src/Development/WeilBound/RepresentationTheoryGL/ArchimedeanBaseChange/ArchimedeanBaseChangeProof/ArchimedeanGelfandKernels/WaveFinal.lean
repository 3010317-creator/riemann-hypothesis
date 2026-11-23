module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraEstimateForRegularity
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AsmMultMain
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePropagationSpeedHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralLinearGroupUnimodular
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthFunctionFactsHold
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightDerivativeCalculusHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevInequalityOnGroup
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelExistence
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.AsmKerOne
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

namespace PositivityTheory.RgBcC

theorem wave_existence_speed_multiplicity : WaveEx ∧ WaveSpeed ∧ KerEx ∧ MultAlg := by
  have hL : LgFacts := _root_.GlobalTheory.CompanionTheory.LengthGL.lgFacts
  have hU : Unimod := _root_.GlobalTheory.CompanionTheory.GLUnimod.unimod
  have hS : SobG := _root_.GlobalTheory.CompanionTheory.SobGL.sobG
  have hR : RCalc := _root_.GlobalTheory.CompanionTheory.RCalc.rcalc
  have hKU : KerUniq := _root_.GlobalTheory.CompanionTheory.KerUniq.main
  have hA : AlgEst := _root_.GlobalTheory.CompanionTheory.SkewWords.algEst
  have hsp : WaveSpeed := _root_.GlobalTheory.CompanionTheory.WaveSpd.asmSpeed hL hU hR
  have hcpt : WaveCpt := Fc.asmCpt hL hU hR hS
  have hex : WaveEx := _root_.GlobalTheory.CompanionTheory.WaveAll.asmEx hL hR hsp hcpt
  have hk1 : KerOne := Fc.asmKerOne hL hU hR hS hA hsp
  exact ⟨hex, hsp, _root_.GlobalTheory.CompanionTheory.WaveKer.asmKerEx hL hR hsp hex hKU hk1,
    GlobalTheory.CompanionTheory.WaveMult.asmMult_main hL hU hR hsp hex hKU hk1⟩

end PositivityTheory.RgBcC
