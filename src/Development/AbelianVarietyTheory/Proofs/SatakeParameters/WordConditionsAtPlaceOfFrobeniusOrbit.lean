module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EmbeddingMapsIntoGoodExtension
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeInSumTwistedDualsFitsWord
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeTwistedDualFitsWordFewSmallJumps
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalFieldDegreeEqRamificationMulInertia
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceCompletionLeMaxUnramifiedAway2qdStatement
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsOfConjugatesMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordParams
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WachFunctorLettersInverseFrobeniusOrbit
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

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem wordBase_of_jumpIn : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (HW : HWOf D.loc) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (hG : Good (D.nbr i w hw).Kw 1 C.LL) r ρ π (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → D.nd.l i ∉ D.host.small → D.nd.l i ≠ D.host.q → D.nd.l i ≠ D.host.d → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) → ∃ g, IsOrbit g (DV.frobG D (D.nd.l i))⁻¹ ∧ C.WordBase r ρ π L HW hG (recWord L (liftIdx D i) ε g) := by
  intro D L C₀ HW i w hw C hG r ρ π ε κ hR hA h2 hq hd hI
  have hU : (D.nbr i w hw).Kw.1 ≤ MaximalUnramifiedExtension (D.nd.l i) :=
    GlobalTheory.T.placeCompletion_le_maxUnramified_away_2qd D.nbr i w hw h2 hq hd
  have hF : Formalism.MainNotions.LocalSituation.fontCore ((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw) := hA _ _
  obtain ⟨g, hg, hread⟩ := _root_.GlobalTheory.HTW.Rec.reads_orbit_invFrob D (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
    ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ h2 hq hd
    (D.nbr i w hw).j_dense hU
  refine ⟨g, hg, _root_.GlobalTheory.bridge_degW D.nbr i w hw, ?_, _root_.GlobalTheory.HTW.Rec.recWord_wordNum L C₀ (liftIdx D i) ε g _ hR hg⟩
  exact
    { unram := hU
      split := fun ft => GlobalTheory.splits_of_conjugates_mem _ _ _
        (GlobalTheory.good_conjugates_mem _ _ _ 1 hG) ft
      t1 := _root_.GlobalTheory.HTW.Rec.fits_of_isSubOfSums L C₀ (liftIdx D i) ε (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
        ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ _ _ g hR hF hI hread
      t2 := _root_.GlobalTheory.HTW.Rec.fits_lowCount_of_matRep L C₀ (liftIdx D i) ε (D.loc (D.nd.l i)) (D.nbr i w hw).Kw C.LL
        ((HW (D.nd.l i)).W (D.nbr i w hw).Kw 1 C.LL hG) (Br.cEw D.nbr i w hw) κ _ _ g hR hF hU hI hread }

end GlobalTheory.HTW.Rec
