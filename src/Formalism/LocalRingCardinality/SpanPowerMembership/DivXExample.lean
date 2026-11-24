module

public import Formalism.LocalRingCardinality.DataDIV
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

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

def geoExample (F : Type) [Field F] [NumberField F] [StarRing F] : DV.Geo F where
  Var := Empty
  dim := fun Y => Empty.elim Y
  Fn := fun Y => Empty.elim Y
  fnField := fun Y => Empty.elim Y
  fnAlg := fun Y => Empty.elim Y
  Dv := fun Y => Empty.elim Y
  dvGrp := fun Y => Empty.elim Y
  H0 := fun Y => Empty.elim Y
  Cl := fun Y => Empty.elim Y
  supp := fun Y => Empty.elim Y
  inter := fun Y => Empty.elim Y
  vanishOn := fun Y => Empty.elim Y
  Adl := fun Y => Empty.elim Y
  ofW := fun Y => Empty.elim Y
  twist := fun Y => Empty.elim Y
  arTop := fun Y => Empty.elim Y
  arVol := fun Y => Empty.elim Y
  nefA := fun Y => Empty.elim Y

variable (D : D7)

end Formalism.BasicNotions.Examples₂
