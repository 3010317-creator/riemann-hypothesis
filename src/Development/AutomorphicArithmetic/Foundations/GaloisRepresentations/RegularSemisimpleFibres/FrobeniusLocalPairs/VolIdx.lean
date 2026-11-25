module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.LiftFactorization
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure

@[expose] public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UpperTheory.Gal.InertialTypesAlt.L

theorem volIdx :
    UpperTheory.Gal.InertialTypesAlt.L.VolIdx := by
  intro G _ _ _ _ _ _ T C H hT ν hν hCT hC hHC hH
  haveI := hν
  have eH : {t : T | (t : G) ∈ H} = ((H.subgroupOf T : Subgroup T) : Set T) := rfl
  have eC : {t : T | (t : G) ∈ C} = ((C.subgroupOf T : Subgroup T) : Set T) := rfl
  have hHo : IsOpen ((H.subgroupOf T : Subgroup T) : Set T) := by
    rw [← eH]
    exact hH
  have hCc : IsCompact ((C.subgroupOf T : Subgroup T) : Set T) := by
    rw [← eC]
    exact hT.isClosedEmbedding_subtypeVal.isCompact_preimage hC
  have hle : H.subgroupOf T ≤ C.subgroupOf T := fun x hx => hHC hx
  haveI : CompactSpace (C.subgroupOf T) := isCompact_iff_compactSpace.mp hCc
  haveI : Finite ((C.subgroupOf T) ⧸ (H.subgroupOf T).subgroupOf (C.subgroupOf T)) :=
    Subgroup.quotient_finite_of_isOpen _ (by
      rw [Subgroup.coe_subgroupOf]
      exact hHo.preimage continuous_subtype_val)
  haveI : ((H.subgroupOf T).subgroupOf (C.subgroupOf T)).FiniteIndex :=
    Subgroup.finiteIndex_of_finite_quotient
  have key := (Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure
    (H.subgroupOf T) (C.subgroupOf T) hle hHo.measurableSet ν).symm
  rw [Subgroup.relIndex_subgroupOf hCT] at key
  have hpos : ν ((H.subgroupOf T : Subgroup T) : Set T) ≠ 0 :=
    (hHo.measure_pos ν ⟨1, (H.subgroupOf T).one_mem⟩).ne'
  have hfinH : ν ((H.subgroupOf T : Subgroup T) : Set T) ≠ ∞ :=
    ((measure_mono (fun x hx => hle hx)).trans_lt hCc.measure_lt_top).ne
  rw [eH, eC]
  refine ⟨?_, ?_⟩
  · rw [measureReal_def, ENNReal.toReal_ne_zero]
    exact ⟨hpos, hfinH⟩
  · simp only [measureReal_def, key, ENNReal.toReal_mul, ENNReal.toReal_natCast]

end UpperTheory.Gal.InertialTypesAlt.L
