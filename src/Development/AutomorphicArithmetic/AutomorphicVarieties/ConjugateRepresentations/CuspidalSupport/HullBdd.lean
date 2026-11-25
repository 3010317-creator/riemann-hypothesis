module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HeckeLocalBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsAutomorphicFormOfBddSubmodule

@[expose] public section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.LFun Formalism.UG Formalism.UG.P Formalism.L2.Host UpperTheory.V.Cj.S
open GroundTheory.Automorphic.AutomorphicForm (UPos unipGL constantTerm archCompact infEmb isExpLieAlgebra)
open UpperTheory.V.Af.Fin (emb e1 e2 blk Bdd)
open GlobalTheory.PRep (fixed)
open scoped TensorProduct

private theorem hull_le {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    {S U : Submodule ℂ (Sm E a)} (h : ∀ T ∈ Comm E a, ∀ φ ∈ S, T φ ∈ U) : hull S ≤ U := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨T, hT, φ, hφ, rfl⟩
  exact h T hT φ hφ

private theorem smEq_aeval {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (z : GroundTheory.Automorphic.AutomorphicForm.UEnv E a) (p : Polynomial ℂ) (φ : Sm E a) :
    Polynomial.aeval (GroundTheory.Automorphic.AutomorphicForm.uAction z) p (UpperTheory.V.Cm.smEq E a φ) =
      UpperTheory.V.Cm.smEq E a (Polynomial.aeval (UpperTheory.V.Cm.uTC E a z) p φ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply, map_smul]
    congr 1
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ih, UpperTheory.V.Cm.smEq_uTC]

theorem UpperTheory.V.Cj.S.hullBdd :
    UpperTheory.V.Cj.S.TypesComm → UpperTheory.V.Cj.S.HullBdd := by
  intro hTC E _ _ _ a S hS L hL
  have haut : ∀ φ ∈ hull S, GroundTheory.Automorphic.AutomorphicForm.IsAutomorphicForm φ.1 := fun φ hφ =>
    (Cm.isAutForm_iff φ).1 (Cm.mem_range_ofAut.1 (hull_le (U := LinearMap.range (Cm.ofAut E a))
      (fun T hT ψ hψ => Cm.mem_range_ofAut.2 (hT.2.2 ψ ((Cm.isAutForm_iff ψ).2
        (UpperTheory.isAutomorphicForm_of_bdd_submodule E a _ hS _ ⟨ψ, hψ, rfl⟩)))) hφ))
  refine ⟨?_, ?_, ⟨L, hL, ?_⟩, ?_, fun z hz => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    exact (haut φ hφ.1).isLeftInvariant
  · rintro _ ⟨φ, hφ, rfl⟩
    exact (haut φ hφ.1).hasModerateGrowth
  · rintro _ ⟨φ, hφ, rfl⟩ u hu g
    rw [Fb.finEmb_eq]
    have h1 : finRep E a u φ = φ := (hφ.2 ⟨u, hu⟩).trans (by simp)
    exact congrFun (congrArg Subtype.val h1) g
  · obtain ⟨V, hV, hst, hm⟩ := hS.types
    refine ⟨V, hV, hst, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩ g
    let U : Submodule ℂ (Sm E a) :=
      { carrier := {ψ | (fun k : archCompact E a => ψ.1 (g * infEmb E a k.1)) ∈ V}
        zero_mem' := V.zero_mem
        add_mem' := fun hx hy => V.add_mem hx hy
        smul_mem' := fun c _ hx => V.smul_mem c hx }
    exact hull_le (U := U) (fun T hT ψ hψ => hTC E a V hV T hT.1 ψ (hm _ ⟨ψ, hψ, rfl⟩) g) hφ.1
  · obtain ⟨p, hp, hm⟩ := hS.centre z hz
    refine ⟨p, hp, ?_⟩
    rintro _ ⟨φ, hφ, rfl⟩
    have h0 : φ ∈ LinearMap.ker (Polynomial.aeval (Cm.uTC E a z) p) := by
      refine hull_le (fun T hT ψ hψ => ?_) hφ.1
      have h1 := hm _ ⟨ψ, hψ, rfl⟩
      rw [Submodule.mem_bot, LinearEquiv.coe_coe, smEq_aeval] at h1
      have h1 : Polynomial.aeval (Cm.uTC E a z) p ψ = 0 :=
        (Cm.smEq E a).injective (h1.trans (Cm.smEq E a).map_zero.symm)
      rw [LinearMap.mem_ker, ← Module.End.mul_apply,
        ← (Algebra.commute_of_mem_adjoin_singleton_of_commute
          (Polynomial.aeval_mem_adjoin_singleton ℂ (Cm.uTC E a z)) (hT.2.1 z hz)).eq,
        Module.End.mul_apply, h1, map_zero]
    rw [Submodule.mem_bot, LinearEquiv.coe_coe, smEq_aeval, LinearMap.mem_ker.1 h0, (Cm.smEq E a).map_zero]
