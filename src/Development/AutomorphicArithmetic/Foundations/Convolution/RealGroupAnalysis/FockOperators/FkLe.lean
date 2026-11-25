module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.VacForm, Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkLe

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.VacForm =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.VacForm", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

private theorem slice_mem {F : Type} [Field F] [NumberField F] {f : V4 F → ℂ}
    (hf : f ∈ schwartzBruhatPi (K := F) (ι := Fin 4)) :
    (fun y : Fin 4 → FiniteAdeleRing (𝓞 F) F => f fun i => ((0, y i) : A F)) ∈
      finiteSchwartzBruhatPi F (ι := Fin 4) := by
  let φ : (V4 F → ℂ) →ₗ[ℂ] (Fin 4 → FiniteAdeleRing (𝓞 F) F) → ℂ :=
    { toFun := fun f y => f fun i => ((0, y i) : A F)
      map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  refine (Submodule.span_le (p := (finiteSchwartzBruhatPi F (ι := Fin 4)).comap φ)).2 ?_ hf
  rintro _ ⟨p, g, hg, rfl⟩
  exact Submodule.smul_mem _ (p (infPartPi fun _ : Fin 4 => (0 : A F))) hg

private theorem gauss_fin {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (δ : F)
    (y : Fin 4 → FiniteAdeleRing (𝓞 F) F) : gauss δ (fun i => ((0, y i) : A F)) = 1 := by
  have key : ∀ a : V4 F, (∀ i, TR.pInf F (a i) = 0) → gauss δ a = 1 := fun a h => by
    simp only [gauss, map_add (f := _), map_sub, map_mul, map_pow, h]
    simp
  exact key _ fun i => map_zero (TR.infEq F).symm

theorem UpperTheory.ConvolutionTheory.R2.Fo.vacForm :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F), ∀ φ ∈ Vac δ, ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ.1 = fun v => gauss δ v * g (finPartPi v) := by
  intro F _ _ _ δ φ hφ
  refine ⟨_, slice_mem φ.2, funext fun v => ?_⟩
  have h := hφ v (fun i => ((0, (v i).2) : A F)) rfl
  rw [gauss_fin, mul_one] at h
  rw [h, mul_comm]
  rfl
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.VacForm =====

-- ===== clump member: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkLe =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkLe", "h": "module\n\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.XApply\npublic import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.VacForm\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Fo
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Fo.fkLe :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (δ : F) (O : Ops F), (∀ w i, ∀ φ ∈ Fock δ, O.x w i φ ∈ Fock δ) ∧ ∀ N ≤ Vac δ, ∀ m, O.Fk N m ≤ Fock δ := by
  intro F _ _ _ δ O
  have hF : ∀ φ : S4 F, (φ : V4 F → ℂ) ∈ Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F),
        ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ = fun v => p v * gauss δ v * g (finPartPi v)} → φ ∈ Fock δ := fun _ h => h
  have hx : ∀ w i, ∀ φ ∈ Fock δ, O.x w i φ ∈ Fock δ := by
    intro w i φ hφ
    have hc : (fun v : V4 F => cw w (v i)) ∈ polyFn (F := F) :=
      Algebra.subset_adjoin ⟨i, w, rfl⟩
    have key : ∀ f : V4 F → ℂ, f ∈ Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F),
        ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ = fun v => p v * gauss δ v * g (finPartPi v)} →
        (fun v => cw w (v i) * f v) ∈ Submodule.span ℂ {φ : V4 F → ℂ | ∃ p ∈ polyFn (F := F),
        ∃ g ∈ finiteSchwartzBruhatPi F (ι := Fin 4), φ = fun v => p v * gauss δ v * g (finPartPi v)} := by
      let mulCw : (V4 F → ℂ) →ₗ[ℂ] (V4 F → ℂ) :=
        { toFun := fun f v => cw w (v i) * f v
          map_add' := fun a b => funext fun v => mul_add _ _ _
          map_smul' := fun c a => funext fun v => by
            simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring }
      intro f hf
      refine (Submodule.span_le (p := Submodule.comap mulCw (Submodule.span ℂ _))).2 ?_ hf
      rintro _ ⟨p, hp, g, hg, rfl⟩
      refine Submodule.subset_span ⟨(fun v : V4 F => cw w (v i)) * p, mul_mem hc hp, g, hg, ?_⟩
      exact funext fun v => show cw w (v i) * (p v * gauss δ v * g (finPartPi v)) = _ by
        simp only [Pi.mul_apply]; ring
    have hφ' := key φ.1 hφ
    have e : ((O.x w i φ : S4 F) : V4 F → ℂ) = fun v => cw w (v i) * φ.1 v := by
      funext v
      exact O.x_apply w i φ v
    apply hF
    rw [e]
    exact hφ'
  refine ⟨hx, fun N hN m => ?_⟩
  have hvac : Vac δ ≤ Fock δ := by
    intro φ hφ
    obtain ⟨g, hg, e⟩ := vacForm F δ φ hφ
    apply hF
    refine Submodule.subset_span ⟨1, one_mem _, g, hg, ?_⟩
    rw [e]
    funext v
    simp
  induction m with
  | zero => exact hN.trans hvac
  | succ m ih =>
    refine sup_le ih (iSup_le fun w => iSup_le fun i => ?_)
    rintro _ ⟨φ, hφ, rfl⟩
    exact hx w i φ (ih hφ)
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.FockOperators.FkLe =====
