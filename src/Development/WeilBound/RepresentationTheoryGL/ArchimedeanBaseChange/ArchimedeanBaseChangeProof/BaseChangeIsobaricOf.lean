module

public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
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

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC

namespace PositivityTheory.Rg.BcB

structure Datum (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) where
  c : ℕ
  N : Fin c → ℕ
  h : ∑ i, N i = n
  V : ∀ i, Submodule ℂ (Sm E (N i))
  σ : ∀ i (w : HeightOneSpectrum (𝓞 E)), SmIrr (GL (Fin (N i)) (w.adicCompletion E))
  m : Fin c → (E →+* ℂ) → Multiset ℂ
  pos : ∀ i, 0 < N i
  discrete : ∀ i, IsDiscrete (V i)
  csd : ∀ i, IsCsdGL (V i)
  loc : ∀ i w, IsLocCompGL (V i) w (σ i w)
  inf : ∀ i τ, HasInfCharGL (V i) τ (m i τ)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def SplitAt (π : Submodule ℂ (UA E n → ℂ)) (D : Datum E n) (w : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∃ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D.h w (D.σ · w)) ∧
    IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ

def SatAt (D : Datum E n) (w : HeightOneSpectrum (𝓞 E)) (B : Fin D.c → Multiset ℂˣ) : Prop :=
  ∀ i, GlobalTheory.LGrp.IsSpherical (D.σ i w).ρ (GlobalTheory.LFun.KGL w (n := (D.N i))) ∧ GlobalTheory.LFun.HasSatGL w (D.σ i w).ρ (B i)

def Weak (π : Submodule ℂ (UA E n → ℂ)) (D : Datum E n) : Prop :=
  (∀ τ lam, HasWeightAt π τ lam → ∑ i, D.m i τ = infOfWeight lam) ∧
    {w | IsSplitAt w ∧ ¬ SplitAt π D w}.Finite

def Unr (E : Type) [Field E] [NumberField E] [IsCMField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal

def Rigid : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n →
  ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ D D' : Datum E n, Weak π D → Weak π D' → ∀ w,
    (∀ P : SmIrr (GL (Fin n) (w.adicCompletion E)), GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D'.h w (D'.σ · w)) →
      GlobalTheory.SmGL.IsSubquotient P.ρ (locProd D.h w (D.σ · w))) ∧
    ∀ B, SatAt D w B → ∃ B', SatAt D' w B' ∧ ∑ i, B i = ∑ i, B' i


end PositivityTheory.Rg.BcB

end
