module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NormLeOneOfMemOL
public import Formalism.WeaklyAdmissibleFiltrations.StatementTor
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleRealisationOfFramedMatrices
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsBreuilKisinFrobeniusPeriod
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCrystallineLatticePeriodsOnDisc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFramedFCrystalOfStratifiedPhiModule
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleCrystallineLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyBreuilKisinDatum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyDiscPeriodAinfBasisDataOfIsPer
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
import Mathlib.Tactic.Linter.HaveILetI
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

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem galoisLatticeAction_mul {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) (g h : ↥(GK K)) :
    actT L g ∘ₗ actT L h = actT L (g * h) := by
  ext x
  simp [actT, map_mul]
  rfl

theorem galoisLatticeAction_one {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) :
    actT L 1 = LinearMap.id := by
  ext x
  simp [actT, map_one]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem isUnit_toMatrix_actT {l : ℕ} [Fact l.Prime] {K : FinExt l} {V : Type} [AddCommGroup V] [Module ℚ_[l] V]
    [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] {ρ : Representation ℚ_[l] ↥(GK K) V}
    (L : Formalism.WeaklyAdmissibleFiltrations.Lattice (O := ℤ_[l]) ρ) {d : ℕ} (b : Module.Basis (Fin d) ℤ_[l] ↥L.T) (g : ↥(GK K)) :
    IsUnit (LinearMap.toMatrix b b (actT L g)) := by
  have h1 : LinearMap.toMatrix b b (actT L g) * LinearMap.toMatrix b b (actT L g⁻¹) = 1 := by
    rw [← LinearMap.toMatrix_comp, galoisLatticeAction_mul, mul_inv_cancel, galoisLatticeAction_one, LinearMap.toMatrix_id]
  have h2 : LinearMap.toMatrix b b (actT L g⁻¹) * LinearMap.toMatrix b b (actT L g) = 1 := by
    rw [← LinearMap.toMatrix_comp, galoisLatticeAction_mul, inv_mul_cancel, galoisLatticeAction_one, LinearMap.toMatrix_id]
  exact ⟨⟨_, _, h1, h2⟩, rfl⟩

theorem clause1_perfectPrism : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (P : LocPrime l) (AI : LocAinf l P), IsStd P AI → ∀ (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [Module ℤ_[l] V] [IsScalarTower ℤ_[l] ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (L : Lattice (O := ℤ_[l]) ρ), (∀ x, Continuous fun g => ρ g x) → IsCrys (P.PD K) ρ → ∃ (M : FCrys l ↥(OL K)) (j : M.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] ↥L.T)), Realises K M (ainfObj K) (ainfId K) ↥L.T (fun g => actT L g) j := by
  intro l _ K P AI hStd V _ _ _ _ _ _ _ ρ L hcont hcrys
  haveI : Module.Free ℤ_[l] ↥L.T := L.free
  haveI : Module.Finite ℤ_[l] ↥L.T := Module.Finite.iff_fg.mpr L.fg
  obtain ⟨bk⟩ := _root_.GlobalTheory.BSP.nonempty_bk_of_finExt l K
  obtain ⟨τ, hτ⟩ := _root_.GlobalTheory.BSP.exists_isPer l K bk
  let b := Module.finBasis ℤ_[l] ↥L.T
  obtain ⟨s⟩ := _root_.GlobalTheory.SeedExists.exists_seed l K bk τ hτ P AI hStd V ρ L hcont hcrys _ b
  have hu : ∀ g, IsUnit (LinearMap.toMatrix b b (actT L g)) := fun g => isUnit_toMatrix_actT L b g
  obtain ⟨hs⟩ := _root_.GlobalTheory.BSP.HeightEx.nonempty_height l K bk τ hτ _ _ hu s
  obtain ⟨S, T, hST⟩ := _root_.GlobalTheory.BSP.exists_strat_mreal l K bk τ hτ _ _ hu s hs
  obtain ⟨M, e, hMe⟩ := _root_.GlobalTheory.BSP.StratCrys.exists_framed l K bk _ S
  exact ⟨M, _root_.GlobalTheory.BSP.EtReal.realises_of_mreal l K bk _ S M e hMe ↥L.T (fun g => actT L g) b T hST⟩

end GlobalTheory.BSP
