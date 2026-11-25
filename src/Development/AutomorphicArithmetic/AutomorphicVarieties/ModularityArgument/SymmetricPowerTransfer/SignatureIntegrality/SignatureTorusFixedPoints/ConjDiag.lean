module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.LevelTwoFiniteIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.EvenVal

@[expose] public section

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

theorem UpperTheory.V.Z.Sym.Sig.conjDiag : UpperTheory.V.Z.Sym.Sig.ConjDiag := by
  intro k _ _ _ _ n s s' hs hs' y hy
  have hc : (dg s : GL (Fin n) k) * y = y * dg s' := by
    rw [← hy, ← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
  have hM := congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k)) hc
  simp only [Units.val_mul, dg, val_diagT] at hM
  have key : ∀ i j, y.val i j ≠ 0 → (s i : k) = s' j := by
    intro i j hij
    have e := congrFun (congrFun hM i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm] at e
    exact mul_left_cancel₀ hij e
  have col : ∀ j, ∃ i, y.val i j ≠ 0 := by
    intro j
    by_contra! h
    exact y.det_ne_zero (Matrix.det_eq_zero_of_column_eq_zero j h)
  choose σ hσ using col
  have hσs : ∀ j, (s (σ j) : k) = s' j := fun j => key _ _ (hσ j)
  have increasing : StrictMono (fun i => valuation k (s i : k)) := fun _ _ => hs _ _
  have hmono : StrictMono σ := by
    intro i j hij
    apply increasing.lt_iff_lt.mp
    simpa only [hσs] using hs' i j hij
  obtain rfl : σ = id := hmono.eq_id
  have hdiag (i j) (hij : i ≠ j) : y.val i j = 0 := by
    by_contra h
    exact hij (increasing.injective (congrArg (valuation k) ((key i j h).trans (hσs j).symm)))
  refine ⟨funext fun j => Units.ext (hσs j), fun i => Units.mk0 _ (hσ i), ?_⟩
  apply Units.ext
  simp only [dg, val_diagT, Units.val_mk0]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp
  · rw [hdiag i j hij, Matrix.diagonal_apply_ne _ hij]

end
