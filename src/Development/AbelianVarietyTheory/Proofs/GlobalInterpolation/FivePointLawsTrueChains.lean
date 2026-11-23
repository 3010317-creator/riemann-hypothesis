module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStep
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.JetsAllOfColIn
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChThOkOfColIn
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JetSumTable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KernelJetsLevelPlaceIntegralMoments
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MoveStepOfFamily
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedThetaFamilyVectorsLatticesThetaZero
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SameOfAbove
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelEqPointKernelAtRepresentativesStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelsBoundConjugatePrimePlaces
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TrueChainKernelsBoundLevelPrimePlaces
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UkTermOfMoveStep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeylModuleSimpleClosedLowestAlcove
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLaws
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KAtTopEquiv
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

@[expose] public section

noncomputable section

namespace GlobalTheory.LvT.Built.TrueLaws

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem moveStep_fam (h : I.Ok) (hJ : I.JetsIn) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    GlobalTheory.KerT.MoveStep (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u i (i + 1) := by
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  have hJa := GlobalTheory.KerT.jetsAll_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ a u hi
  obtain ⟨-, -, hcc, hδ, hχ, -⟩ := hH.ana
  have hEq := _root_.GlobalTheory.Mem.NatEqui.eqP _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  obtain ⟨-, hLat, hTh⟩ := _root_.GlobalTheory.NatFamily.family _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  have hM := GlobalTheory.ThetaMove.moveStep_of_family I.dat _ (seamOf B (I.cols l) Z.W Z.V Z.S Z.N Z.G) ⊤ I.J.δ
    (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi I.J.cD I.sel I.S (I.tup a) (I.cst a) u i hi hH hEq hLat
    (fun a b _ _ => hTh a b) hJa
  rw [← AmbIn.amb_eq_ambOf] at hM
  exact hM

theorem kernelCondition_at_row_family (h : I.Ok) (hJ : I.JetsIn) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (a : I.ι) {i : ℕ} (hi : i < B.R.m) :
    Dat.KerUK (B := dat I l Z u a) (i := i) (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  intro b b' d d' P F
  exact UpLaw.kAt_uk B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) I.glob (B.R.m - 2) u i hX hPr
    h.sel_ok (h.T_mem u) (h.idx_ok a) (I.Tp a) I.A (isTerm h u a hi)
    (GlobalTheory.KerT.UK.ukTerm_of_moveStep B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) I.A u i hX hPr h.sel_ok
      (h.T_mem u) (moveStep_fam h hJ l Z u a hi)) b b' d d' P F

theorem laws_true_fam : ∀ (B : GlobalTheory.Mem.Base) (X : PreX B.toPre) (I : TC B X), I.Ok → I.JetsIn → ∀ (l : I.Laws) (l0 : I.Law0 l)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∃ Bd : Built.Dat (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G) u, Bd.ch = tw (I.tw l l0 Z) u a ∧
      (∀ i, i ≤ (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m →
        letI : NumberField Bd.E := Bd.nE
        Nonempty (Split (Bd.J.A i) Bd.J.T)) ∧ Bd.Sees ∧
      (∀ i, i < (_root_.GlobalTheory.Mem.assemble _ _ Z.W Z.V Z.S Z.N Z.G).R.m → ∃ k : Bd.Ker i, Dat.KerEq k ∧ Dat.KerDil k ∧ Dat.KerUK k ∧ Dat.KerBar k ∧ Dat.KerP k) ∧
      Bd = dat I l Z u a := by
  intro B X I h hJ l l0 Z u a
  have hH := GlobalTheory.KerT.hyp_of_colIn B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h a u
  obtain ⟨-, -, hcc, hδ, hχ, -⟩ := hH.ana
  have hE := _root_.GlobalTheory.Mem.NatEqui.eqP _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ
  have hV := (_root_.GlobalTheory.NatFamily.family _ _ _ (I.J.toRec B (I.cols l) Z.W Z.V Z.S Z.N Z.G) I.chi hcc hδ hχ).1
  have hth : ∀ (a : I.ι) (u : B.Word), _root_.Formalism.L2.Col.ChTh.Ok (Ch := I.Ch) (I.cst a)
      (chTh (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) I.A u (B.R.m - 2)) := fun a u =>
    GlobalTheory.ChainTheta.chTh_ok_of_colIn' B (I.cols l) Z.W Z.V Z.S Z.N Z.G I h hJ hE hV a u
  refine ⟨dat I l Z u a, dat_ch I l l0 Z u a, fun i _ => split u a h i, sees l Z u a, fun i hi => ?_, rfl⟩
  change i < B.R.m at hi
  have hKerEq : Dat.KerEq (B := dat I l Z u a) (i := i)
      (kAt (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) I.A u i) := by
    obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
    refine ⟨fun b b' g g' d d' => ?_,
      GlobalTheory.T.trueChainKernel_eq_pointKernel_at_representatives B X I h hJ l Z hV u a i hi⟩
    rcases lt_trichotomy (i + 2) B.R.m with hlt | heq | hgt
    · exact GlobalTheory.MatLaw.kAt_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a)
        I.glob (B.R.m - 2) u i I.A hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) (hth a u) hlt b b' g g' d d'
    · exact GlobalTheory.CoupledLaw.kAt_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a)
        I.glob (B.R.m - 2) u i I.A hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) (hth a u) heq b b' g g' d d'
    · exact TopEq.kAt_top_equiv B.fields (B.primes X) B.R B.wts I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a)
        I.glob (B.R.m - 2) u i I.A hX hPr h.ch_ok h.sel_ok (h.T_mem u) h.g_mem (h.idx_ok a) (h.sharp a) (hth a u) (by omega) b b' g g' d d'
  exact ⟨_, hKerEq, kerDil h l Z u a hi,
    kernelCondition_at_row_family h hJ l Z u a hi, _root_.GlobalTheory.LvT.Built.TrueLaws.kerBar _root_.GlobalTheory.MomTop.jetMoments _root_.GlobalTheory.Alc.inducedSimpleLowestAlcove B X I h hJ l Z u a (hth a u) i hi,
    _root_.GlobalTheory.LvT.Built.TrueLaws.kerP _root_.GlobalTheory.MomTop.jetMoments _root_.GlobalTheory.Alc.inducedSimpleLowestAlcove B X I h hJ l Z u a (hth a u) i hi⟩

end GlobalTheory.LvT.Built.TrueLaws
