module

public import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
public import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PtEqOneOfGZero
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerVolumeTheoremStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AntisymmetricPerturbationHoldsStatement
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.CmpHodgeTied
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpPair
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmpPairOfInputs
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
public import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyExistsPosOfFamilyExists
public import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.FarguesHodgeTate
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPosOfHodgeTateInputs
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrdinaryCurveStatementHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.StrongApproximation.SAOpenStatement
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianStatementHolds
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SlopeBoundOfLineLargeDegree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComparisonOfInputsAvoidance
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilSt
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
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

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem goodTower_volume_of_reduced : (PartI ∧ N1ab ∧ N1c ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H), ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D)) → KeyFormula → GlobalTheory.Published.SemiAbelianHomExtension → GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → HT.FarguesHodgeTate → Flat.GagaSections → GroundTheory.Heights₂.Heights.LineOfLargeDegree.Statement → PB.Inputs → Prov.HS → Prov.An → Prov.ZhangDimensionPushDownGrassmannianHeightBounds → ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement → ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement → GlobalTheory.CompanionTheory.Ar.GR.QuotientByFiniteFlatStatement → GlobalTheory.CompanionTheory.Ar.GR.ZarhinStatement → ThetaUnifAV → Top.GoodTowerExistsX ∧ Top.VolumeTheoremX := by
  intro hM hKF hSA hNS hResK hFHT hGaga hLLD hPB hHS hAn hNine hPts hAvoid hQ hZ hTheta
  have hGiven : Top.Given :=
    ⟨hM, hKF, hSA, hNS, hResK, _root_.GlobalTheory.CompanionTheory.Ar.Link.saStatement_holds, hFHT, hGaga,
      (_root_.GlobalTheory.CompanionTheory.Ar.Sl.slopeBound_and_lemmaS_of_siegel hLLD).1, hPB, hHS, hAn, hNine,
      GlobalTheory.T.antisymmetric_perturbation_holds⟩
  have hW : Out.WeilSt := GlobalTheory.CompanionTheory.Ar.Link.weilSt
  have hHTD : GR.HodgeTateDatumStatement := GlobalTheory.CompanionTheory.Ar.GR.Top.main
  have hOrd : GR.OrdinaryCurveStatement := _root_.GlobalTheory.CompanionTheory.Ar.Link.ordinaryCurveStatement
  have hFam : Num.FamilyExistsPos := _root_.GlobalTheory.CompanionTheory.Ar.Num.FamEx.familyExistsPos_holds hFHT hQ hZ hHTD hOrd
  have hCmpSt : Cmp.CmpSt := _root_.GlobalTheory.CompanionTheory.Relay.comparison_of_inputs_avoidance hPB hAvoid hResK
  have hTied : HodgeComparisonCompatibility := _root_.PositivityTheory.UnitarySelfGeneration.cmpHodgeTiedAlt
  have hPair : Cmp.CmpPair := _root_.GlobalTheory.CompanionTheory.Ar.Cmp.PairTop.cmpPair hPB hCmpSt hTied hTheta
  exact GlobalTheory.T.good_tower_volume_theorem hGiven hPts hAvoid hW hFam hPair

end GlobalTheory.CompanionTheory.Ar.Top
