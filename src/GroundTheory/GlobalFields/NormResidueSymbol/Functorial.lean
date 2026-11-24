module

public import GroundTheory.GlobalFields.NormResidueSymbol.RangeIdeleNormLeKerIdeleSymbol
import GroundTheory.GlobalFields.NormResidueSymbol.AbstractUnique
public import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialFinite
public import GroundTheory.GlobalFields.NormResidueSymbol.FunctorialInfinite
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Connected.Separation

@[expose] public section

namespace GroundTheory.Global

open IsDedekindDomain NumberField AdeleBaseChange IdeleGroup

noncomputable section

variable {K K' L L' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K'] [Field L]
  [NumberField L] [Field L'] [NumberField L'] [Algebra K K'] [Algebra K L] [Algebra K L']
  [Algebra K' L'] [Algebra L L'] [IsScalarTower K K' L'] [IsScalarTower K L L']


variable (K) in
def restrictScalarsHom : (L' ≃ₐ[K'] L') →* (L' ≃ₐ[K] L') where
  toFun σ := σ.restrictScalars K
  map_one' := rfl
  map_mul' _ _ := rfl

omit [NumberField K] [NumberField K'] [NumberField L'] in
@[simp]
theorem restrictScalarsHom_apply (σ : L' ≃ₐ[K'] L') : restrictScalarsHom K σ = σ.restrictScalars K :=
  rfl

variable [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)] [IsGalois K' L']
  [IsMulCommutative (L' ≃ₐ[K'] L')]

theorem restrictNormal_restrictScalars_ideleSymbol (x : IdeleGroup K') :
    ((ideleSymbol K' L' x).restrictScalars K).restrictNormal L =
      ideleSymbol K L (ideleNorm K K' x) := by
  exact DFunLike.congr_fun (IdeleGroup.continuous_monoidHom_ext
    (ψ := (AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L).comp
      ((restrictScalarsHom K).comp (ideleSymbol K' L')))
    (ψ' := (ideleSymbol K L).comp (ideleNorm K K'))
    ((continuous_of_discreteTopology : Continuous ((AlgEquiv.restrictNormalHom (F := K)
      (K₁ := L') L).comp (restrictScalarsHom (L' := L') K))).comp (continuous_ideleSymbol L'))
    ((continuous_ideleSymbol L).comp (continuous_ideleNorm (K := K) (L := K')))
    (fun v' a ↦ by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
        ideleSymbol_finiteEmbedding, ideleNorm_finiteEmbedding, ideleSymbol_finiteEmbedding]
      exact restrictNormal_localSymbol_norm (below K v') v' a)
    (fun w' a ↦ by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply,
        ideleSymbol_infiniteEmbedding, ideleNorm_infiniteEmbedding, ideleSymbol_infiniteEmbedding]
      exact restrictNormal_infiniteLocalSymbol_norm w' a)) x

end

end GroundTheory.Global
