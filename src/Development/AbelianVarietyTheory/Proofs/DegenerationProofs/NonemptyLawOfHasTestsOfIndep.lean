module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAddExtension
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInverseExtensionProperClosure
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreEqSpecialFibreOfReductionIndep
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FibreLawOfTestCartesian
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyLawAbelianSchemeProperClosure
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SmoothOfRelativeDimensionGroupSchemeOfTests
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestCartOfSpecialFibreSurjective
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

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

namespace GlobalTheory.ZJ

theorem Core.nonempty_law_of_hasTests_of_indep :
    ∀ C : Core, C.HasTests → C.Indep → Nonempty C.Law := by
  intro C hT hI
  have hF : C.Fib := _root_.GlobalTheory.ZJ.Core.fib_of_indep C hI
  have hS := _root_.GlobalTheory.ZJ.Core.smoothOfRelativeDimension_of_hasTests C hT hF
  have hC : C.TestCart := _root_.GlobalTheory.ZJ.Core.testCart_of_fib C hF hS
  have hL : C.FibLaw := _root_.GlobalTheory.ZJ.Core.fibLaw_of_testCart C hC
  exact _root_.GlobalTheory.ZJ.Core.nonempty_law C hS hC (_root_.GlobalTheory.ZJ.Core.exists_add_extension C hT hS hC hL) (_root_.GlobalTheory.exists_inv_extension C hT hS hC hL)

end GlobalTheory.ZJ
