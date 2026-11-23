module

public import Formalism.FormalGroupLog.Statement
public import Formalism.TorsionNormIteration.InverseIntegralClasses.InvInt
public import Formalism.TorsionNormIteration.InverseIntegralClasses.MapSubtypeInjective
public import Formalism.TorsionNormIteration.InverseIntegralClasses.MemSpanOfNormLe
public import Formalism.TorsionNormIteration.InverseIntegralClasses.NormSigmaLeOne
public import Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne
public import Formalism.TorsionNormIteration.InverseIntegralClasses.SolveExistsProof
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

namespace Formalism.LT

universe u v

theorem funEqSubst : Formalism.G.FunEqSubst.{u, v} :=
  FunEqSubst_of IntegralSubst_proof CoeffBound_valid PowCongr_valid FrobCongr_valid

/-- The scalar, single-Frobenius-term case of Hazewinkel's functional equation lemma.

In Lemma 2.3, take `L = K`, `B = {a : K | ‖a‖ ≤ 1}`, the ideal `pB`, dimension one,
`s₁ = 1 / p`, and `sᵢ = 0` for `i > 1`. The norm condition in `IsFrobLift` is congruence
modulo `pB`; the endomorphism preserves `B` and fixes `p`. The condition `IsFunEqType`
says that `f(T) - (σ f)(T^q) / p` has coefficients in `B`.

For `f(0) = 0` and linear coefficient one, equation (2.5) gives the integral series
`F(X,Y) = f⁻¹(f(X) + f(Y))` asserted here. The source also treats higher dimensions and
arbitrary sequences of matrices `sᵢ`.

See M. Hazewinkel, *On formal groups. The functional equation lemma and some of its
applications*, Astérisque 63 (1979), Lemma 2.3, equation (2.5), p. 74:
https://www.numdam.org/article/AST_1979__63__73_0.pdf. -/
theorem funEqGroup : Formalism.G.FunEqGroup.{u} :=
  FunEqGroup_of SolveExists_proof InvIntegralOfClass_proof FunEqLowCoeff_proof funEqSubst

/-- Integrality of `f⁻¹ ∘ g` for two series of the same functional equation type, with
`f(0) = g(0) = 0` and linear coefficient of `f` equal to one. This is the scalar case
of equation (2.6) in Hazewinkel's Lemma 2.3; see `funEqGroup` for the specialization. -/
theorem funEqHom : Formalism.G.FunEqHom.{u} :=
  FunEqHom_of SolveExists_proof InvIntegralOfClass_proof FunEqLowCoeff_proof funEqSubst

end Formalism.LT
