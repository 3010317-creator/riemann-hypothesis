module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgEquivRootOfUnityEqPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCanonicalAcrisToBdRPlus
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCompatibleRootsOfUnityAndTiltPadic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInjectiveBcrisToBdR
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsBdRPlusSectionOfTheta
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLogTeichmullerAcrisEqMuMulUnit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMaxUnramifiedEmbeddingIntoBcris
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerTiltMinusOnePowDivEnvelope
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

namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem coreEx_alg_tower {l : ℕ} [Fact l.Prime] (a : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) a =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem coreEx_isUnit_l {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (h1 : e.untilt = 1) (h2 : e ≠ 1)
    (w : Per.Acris0 l)
    (hw : (l : Per.AinfP l) * (w : Per.AinfP l) = algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1)) :
    IsUnit (l : Per.Bcris l) := by
  have h0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  have hu : IsUnit (algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (mu e))) := by
    exact GlobalTheory.CrisLoc.unit_of_root l e h1 h2
  have h3 := congrArg ((algebraMap (Per.Acris l) (Per.Bcris l)).comp
    (algebraMap (Per.Acris0 l) (Per.Acris l))) h0
  rw [map_mul, map_natCast, map_pow] at h3
  have h4 : (algebraMap (Per.Acris l) (Per.Bcris l)).comp (algebraMap (Per.Acris0 l) (Per.Acris l))
      (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e)) =
      algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (mu e)) := by
    rw [coreEx_alg_tower, RingHom.comp_apply]
  rw [h4] at h3
  exact isUnit_of_mul_isUnit_left (h3 ▸ hu.pow (l - 1))

theorem nonempty_core : ∀ (l : ℕ) [Fact l.Prime], Nonempty (Core l) := by
  intro l _
  obtain ⟨ζ, ε, z0, zs, z1, hr⟩ := _root_.GlobalTheory.MemLoc.exists_zeta_eps l
  obtain ⟨o, ho⟩ := _root_.GlobalTheory.MemLoc.SecEx.exists_isSec l
  obtain ⟨j, hj⟩ := _root_.GlobalTheory.MemLoc.exists_isCrisP l
  obtain ⟨ι, hι, hinj⟩ := _root_.GlobalTheory.MemLoc.exists_iota_cris_dR l j hj
  have h1 : ε.untilt = 1 := by
    have h := hr 0
    rw [z0, map_one] at h
    exact Subtype.ext h
  have h2 : ε ≠ 1 := by
    intro h
    have h' := hr 1
    rw [h] at h'
    simp only [rootT, Function.iterate_one, map_one] at h'
    apply z1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← h', map_one]
    rfl
  obtain ⟨w, hw, -⟩ := _root_.GlobalTheory.MemLoc.exists_mu_pow_div l ε h1
  have hA : ∀ a : Per.Ainf l, ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
    intro a
    have h := hι (algebraMap (Per.Ainf l) (Per.Acris l) a)
    have h' : j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
      rw [coreEx_alg_tower, hj.on0]; rfl
    rw [h'] at h
    rw [GlobalTheory.RingIface.aB_apply]
    exact h
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.MemLoc.exists_unram_to_cris l o ι ho hinj hA (coreEx_isUnit_l ε h1 h2 w hw)
  obtain ⟨t, -, ht, -⟩ := _root_.GlobalTheory.MemLoc.exists_isLogA l ε h1
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨χ, hχ⟩ := exists_cyclotomicChar l
  exact ⟨⟨ζ, z0, zs, z1, ε, hr, o, ho, j, hj, ι, hι, u, hu, t, ht, σ, hσ, χ, hχ⟩⟩

end

end GlobalTheory.MemLoc
