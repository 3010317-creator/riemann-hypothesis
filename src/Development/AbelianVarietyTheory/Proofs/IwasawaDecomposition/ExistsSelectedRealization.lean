module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameDegreeZeroFormsSelf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
public import Formalism.LocalToGlobal.Divisibility.NumericScaleExponentEqExtended
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColumnParametersInstanceDataStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwExtend
import Lean.Exception
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw

open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.Mem.R3.SelectionPairing

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.IndefR.AutomorphicEvaluation

theorem pack_move {D : D7} {F0 F0' : ∀ u, Formalism.L2.Forms.Forms0 D u} (hF : F0 = F0') {P : SPack D F0} {P' : SPack D F0'}
    (hP : HEq P P') (Φ : ∀ F1 : ∀ u, Formalism.L2.Forms.Forms0 D u, SPack D F1 → Prop) (h : Φ F0' P') : Φ F0 P := by
  subst hF
  obtain rfl := eq_of_heq hP
  exact h

def spRead {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (b : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (Dc : DefCols Df)
    (hK : X.LevelSubgroupCharacter) (Gd : Formalism.L2.SG.RowDict.GoodOp X) (pw : ∀ u, PerW X hK u) (wU : D.what₂.Word → Dc.Mem)
    (bij : Function.Bijective wU) (eNu : ∀ u, (Fin (Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) : SPer Dc :=
  Formalism.IndefR.Cx.spOf (X := X) b Dc hK Gd (Equiv.ofBijective wU bij).symm (fun m => pw ((Equiv.ofBijective wU bij).symm m))
    (fun m i => D.eMu ((Equiv.ofBijective wU bij).symm m) (D.jN ((Equiv.ofBijective wU bij).symm m)
      (eNu ((Equiv.ofBijective wU bij).symm m)
        (Pi.single (Fin.cast (congrArg Dc.a (Equiv.ofBijective_apply_symm_apply wU bij m)).symm i) 1))))

theorem spRead_congr {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (b : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs}
    (Dc : DefCols Df) (hK : X.LevelSubgroupCharacter) (Gd : Formalism.L2.SG.RowDict.GoodOp X) (pw : ∀ u, PerW X hK u) (wU : D.what₂.Word → Dc.Mem)
    (bij : Function.Bijective wU) (eNu : ∀ u, (Fin (Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V)
    (wU' : D.what₂.Word → Dc.Mem) (bij' : Function.Bijective wU')
    (eNu' : ∀ u, (Fin (Dc.a (wU' u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V) (hW : HEq wU' wU) (hN : HEq eNu' eNu) :
    spRead X b Dc hK Gd pw wU bij eNu = spRead X b Dc hK Gd pw wU' bij' eNu' := by
  cases hW
  cases hN
  rfl

def zscRaw {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)
    (F : Face3 D A3) (L : SizeData₂ D) (Del h0 : ℕ) (c : ℝ) : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3 :=
  fun Zs =>
    let z := Formalism.L2.DIV.ZscOfNum3 A3 F.P0 F.ψ0 (Formalism.L2.DIV.ofRecord D L Del h0) (Equiv.refl _) L.Nc Zs
    { z with l6m := fun j => z.l6m j - c * z.l6u, l6u := 0 }

def Places {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (ι : Formalism.L2.Theta.GA D (Yc D 0) ≃* X.B.I.GA) (g : Formalism.L2.Theta.GA D (Yc D 0)) (c : ℝ) (s : Bool)
    (κ : ℝ) (sE : Tw s R.HE.H →ₗ⋆[ℂ] Tw s (HHX X)) : Prop :=
  ∀ (v : Tw s R.HE.H) (hx : R.HE.e (Tw.out v) ∈ R.EEat (R.levR F true)),
    sE v = Tw.mk s (((1 : ℂ) * (κ : ℂ)) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd ι g c ⟨R.HE.e (Tw.out v), hx⟩) ∧
      RealDat.nP F true * ‖sE v‖ ^ 2 = ‖v‖ ^ 2

theorem exists_places {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (ι : Formalism.L2.Theta.GA D (Yc D 0) ≃* X.B.I.GA) (g : Formalism.L2.Theta.GA D (Yc D 0)) (c : ℝ) (s : Bool)
    (hE : R.models_HE) (hc : 0 < c) (hev : EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd ι g c) :
    ∃ (κ : ℝ) (sE : Tw s R.HE.H →ₗ⋆[ℂ] Tw s (HHX X)), 0 < κ ∧ Places R F X Gd ι g c s κ sE := by
  obtain ⟨κ, sE, hκ, h⟩ := GlobalTheory.Mem.SJ.Place.exists_placement D G Pl0 T A Ks R F X Gd ι g c s hE hc hev
  exact ⟨κ, sE, hκ, fun v hx => ⟨(h v hx).1, (h v hx).2.1⟩⟩

section Args

open Lean Elab Tactic Meta in
local elab "exact_defeq " e:term : tactic =>
  closeMainGoalUsing `exact_defeq fun target _ => do
    let proof ← Term.elabTerm e none
    Term.synthesizeSyntheticMVarsNoPostponing
    let proof ← instantiateMVars proof
    let proofType ← instantiateMVars (← inferType proof)
    let target ← instantiateMVars target
    let localContext ← instantiateLCtxMVars (← getLCtx)
    match Kernel.isDefEq (← getEnv) localContext proofType target with
    | .ok true => return proof
    | .ok false => throwError "term type does not match the goal"
    | .error ex => throwError (ex.toMessageData (← getOptions))

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Top.Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}



private abbrev PackSigma (D : D7) :=
  Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
    (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : Formalism.L2.Pj.CoreJ D)
    (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3), G0 R.Pg D.R.r ≃* G0g D.nd

private def PackZsc {D : D7} (L' : SizeData₂ D) (Del h0 : ℕ) (c : ℝ) : PackSigma D → Prop
  | ⟨_, grp, fin, _, _, _, A3, _, _, _, F, _⟩ => letI := grp; letI := fin; F.Zsc = zscRaw A3 F L' Del h0 c

private theorem pack_zsc {D : D7} (L' : SizeData₂ D) (Del h0 : ℕ) (c : ℝ)
    {G₁ G₂ : Type} {grp₁ : Group G₁} {grp₂ : Group G₂} {fin₁ : Fintype G₁} {fin₂ : Fintype G₂} {Pl₁ Pl₂ I₁ I₂ T₁ T₂ : Type}
    {A₁ : letI := grp₁; letI := fin₁; FamIn3 D.what₂.LL G₁ Pl₁ I₁ (List ℕ) T₁ D.R.m}
    {A₂ : letI := grp₂; letI := fin₂; FamIn3 D.what₂.LL G₂ Pl₂ I₂ (List ℕ) T₂ D.R.m}
    {C₁ C₂ : Formalism.L2.Pj.CoreJ D} {alg₁ : Algebra C₁.Q.c.F D.what₂.LL} {alg₂ : Algebra C₂.Q.c.F D.what₂.LL}
    {R₁ : letI := grp₁; letI := fin₁; letI := alg₁; RealDat3 D A₁ C₁.Q.c.F}
    {R₂ : letI := grp₂; letI := fin₂; letI := alg₂; RealDat3 D A₂ C₂.Q.c.F}
    {F₁ : letI := grp₁; letI := fin₁; Face3 D A₁} {F₂ : letI := grp₂; letI := fin₂; Face3 D A₂}
    {cG₁ : letI := grp₁; letI := fin₁; letI := alg₁; G0 R₁.Pg D.R.r ≃* G0g D.nd}
    {cG₂ : letI := grp₂; letI := fin₂; letI := alg₂; G0 R₂.Pg D.R.r ≃* G0g D.nd}
    (hp : (⟨G₁, grp₁, fin₁, Pl₁, I₁, T₁, A₁, C₁, alg₁, R₁, F₁, cG₁⟩ : PackSigma D) = ⟨G₂, grp₂, fin₂, Pl₂, I₂, T₂, A₂, C₂, alg₂, R₂, F₂, cG₂⟩)
    (h : letI := grp₂; letI := fin₂; F₂.Zsc = zscRaw A₂ F₂ L' Del h0 c) :
    letI := grp₁; letI := fin₁; F₁.Zsc = zscRaw A₁ F₁ L' Del h0 c :=
  (congrArg (PackZsc L' Del h0 c) hp).mpr h

private def PackSp {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hK : X.LevelSubgroupCharacter)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (pw : ∀ u, PerW X hK u) {α β : Type} (wU₀ : α) (eNu₀ : β) : PackSigma D → Prop
  | ⟨_, grp, fin, _, _, _, A3, _, alg, R, F, _⟩ =>
    letI := grp; letI := fin; letI := alg
    let Dc := F.Dc (zsOf R F)
    ∃ (wU : D.what₂.Word → Dc.Mem) (bij : Function.Bijective wU)
      (eNu : ∀ u, (Fin (Dc.a (wU u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V),
      HEq wU wU₀ ∧ HEq eNu eNu₀ ∧ F.Sp (zsOf R F) = spRead X (twAt D.what₂.embLL A3.A.v0) Dc hK Gd pw wU bij eNu

private theorem pack_sp {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hK : X.LevelSubgroupCharacter)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (pw : ∀ u, PerW X hK u) {α β : Type} (wU₀ : α) (eNu₀ : β)
    {G₁ G₂ : Type} {grp₁ : Group G₁} {grp₂ : Group G₂} {fin₁ : Fintype G₁} {fin₂ : Fintype G₂} {Pl₁ Pl₂ I₁ I₂ T₁ T₂ : Type}
    {A₁ : letI := grp₁; letI := fin₁; FamIn3 D.what₂.LL G₁ Pl₁ I₁ (List ℕ) T₁ D.R.m}
    {A₂ : letI := grp₂; letI := fin₂; FamIn3 D.what₂.LL G₂ Pl₂ I₂ (List ℕ) T₂ D.R.m}
    {C₁ C₂ : Formalism.L2.Pj.CoreJ D} {alg₁ : Algebra C₁.Q.c.F D.what₂.LL} {alg₂ : Algebra C₂.Q.c.F D.what₂.LL}
    {R₁ : letI := grp₁; letI := fin₁; letI := alg₁; RealDat3 D A₁ C₁.Q.c.F}
    {R₂ : letI := grp₂; letI := fin₂; letI := alg₂; RealDat3 D A₂ C₂.Q.c.F}
    {F₁ : letI := grp₁; letI := fin₁; Face3 D A₁} {F₂ : letI := grp₂; letI := fin₂; Face3 D A₂}
    {cG₁ : letI := grp₁; letI := fin₁; letI := alg₁; G0 R₁.Pg D.R.r ≃* G0g D.nd}
    {cG₂ : letI := grp₂; letI := fin₂; letI := alg₂; G0 R₂.Pg D.R.r ≃* G0g D.nd}
    (hp : (⟨G₁, grp₁, fin₁, Pl₁, I₁, T₁, A₁, C₁, alg₁, R₁, F₁, cG₁⟩ : PackSigma D) = ⟨G₂, grp₂, fin₂, Pl₂, I₂, T₂, A₂, C₂, alg₂, R₂, F₂, cG₂⟩)
    (h : letI := grp₂; letI := fin₂; letI := alg₂
         let Dc₂ := F₂.Dc (zsOf R₂ F₂)
         ∃ (wU₂ : D.what₂.Word → Dc₂.Mem) (bij₂ : Function.Bijective wU₂)
           (eNu₂ : ∀ u, (Fin (Dc₂.a (wU₂ u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V),
           HEq wU₂ wU₀ ∧ HEq eNu₂ eNu₀ ∧ F₂.Sp (zsOf R₂ F₂) = spRead X (twAt D.what₂.embLL A₂.A.v0) Dc₂ hK Gd pw wU₂ bij₂ eNu₂) :
    letI := grp₁; letI := fin₁; letI := alg₁
    let Dc₁ := F₁.Dc (zsOf R₁ F₁)
    ∃ (wU₁ : D.what₂.Word → Dc₁.Mem) (bij₁ : Function.Bijective wU₁)
      (eNu₁ : ∀ u, (Fin (Dc₁.a (wU₁ u)) → D.what₂.LL) ≃ₗ[D.what₂.LL] (D.div.Nu u).V),
      HEq wU₁ wU₀ ∧ HEq eNu₁ eNu₀ ∧ F₁.Sp (zsOf R₁ F₁) = spRead X (twAt D.what₂.embLL A₁.A.v0) Dc₁ hK Gd pw wU₁ bij₁ eNu₁ :=
  (congrArg (PackSp X hK Gd pw wU₀ eNu₀) hp).mpr h

private def PackSee {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (ι : Formalism.L2.Theta.GA D (Yc D 0) ≃* X.B.I.GA)
    (g : Formalism.L2.Theta.GA D (Yc D 0)) (c κ : ℝ) {α : Type} (sE : α) : PackSigma D → Prop
  | ⟨_, grp, fin, _, _, _, A3, _, alg, R, F, _⟩ =>
    letI := grp; letI := fin; letI := alg
    ∃ sE' : Tw (twAt D.what₂.embLL A3.A.v0) R.toRealDat.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX X),
      HEq sE sE' ∧ Places R.toRealDat F.lv2 X Gd ι g c (twAt D.what₂.embLL A3.A.v0) κ sE'

private theorem pack_see {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (ι : Formalism.L2.Theta.GA D (Yc D 0) ≃* X.B.I.GA)
    (g : Formalism.L2.Theta.GA D (Yc D 0)) (c κ : ℝ)
    {G₁ G₂ : Type} {grp₁ : Group G₁} {grp₂ : Group G₂} {fin₁ : Fintype G₁} {fin₂ : Fintype G₂} {Pl₁ Pl₂ I₁ I₂ T₁ T₂ : Type}
    {A₁ : letI := grp₁; letI := fin₁; FamIn3 D.what₂.LL G₁ Pl₁ I₁ (List ℕ) T₁ D.R.m}
    {A₂ : letI := grp₂; letI := fin₂; FamIn3 D.what₂.LL G₂ Pl₂ I₂ (List ℕ) T₂ D.R.m}
    {C₁ C₂ : Formalism.L2.Pj.CoreJ D} {alg₁ : Algebra C₁.Q.c.F D.what₂.LL} {alg₂ : Algebra C₂.Q.c.F D.what₂.LL}
    {R₁ : letI := grp₁; letI := fin₁; letI := alg₁; RealDat3 D A₁ C₁.Q.c.F}
    {R₂ : letI := grp₂; letI := fin₂; letI := alg₂; RealDat3 D A₂ C₂.Q.c.F}
    {F₁ : letI := grp₁; letI := fin₁; Face3 D A₁} {F₂ : letI := grp₂; letI := fin₂; Face3 D A₂}
    {cG₁ : letI := grp₁; letI := fin₁; letI := alg₁; G0 R₁.Pg D.R.r ≃* G0g D.nd}
    {cG₂ : letI := grp₂; letI := fin₂; letI := alg₂; G0 R₂.Pg D.R.r ≃* G0g D.nd}
    (hp : (⟨G₁, grp₁, fin₁, Pl₁, I₁, T₁, A₁, C₁, alg₁, R₁, F₁, cG₁⟩ : PackSigma D) = ⟨G₂, grp₂, fin₂, Pl₂, I₂, T₂, A₂, C₂, alg₂, R₂, F₂, cG₂⟩)
    {α : Type} (sE : α)
    (hsE : letI := grp₂; letI := fin₂; letI := alg₂
           ∃ sE₂ : Tw (twAt D.what₂.embLL A₂.A.v0) R₂.toRealDat.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A₂.A.v0) (HHX X),
             HEq sE sE₂ ∧ Places R₂.toRealDat F₂.lv2 X Gd ι g c (twAt D.what₂.embLL A₂.A.v0) κ sE₂) :
    letI := grp₁; letI := fin₁; letI := alg₁
    ∃ sE' : Tw (twAt D.what₂.embLL A₁.A.v0) R₁.toRealDat.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A₁.A.v0) (HHX X),
      HEq sE sE' ∧ Places R₁.toRealDat F₁.lv2 X Gd ι g c (twAt D.what₂.embLL A₁.A.v0) κ sE' :=
  (congrArg (PackSee X Gd ι g c κ sE) hp).mpr hsE

theorem zsc_pin (a : TwArgs ex t) (x : R3.TwIn ex) (hx : HEq a.x x) (L' : SizeData₂ (w.st Z).toD7) (Del h0 : ℕ) (c : ℝ)
    (h : a.Zsc = zscRaw (famT t) t.r.z.F L' Del h0 c) : x.F.Zsc = zscRaw x.A3 x.F L' Del h0 c := by
  obtain rfl := eq_of_heq hx
  exact pack_zsc L' Del h0 c a.pack (by with_unfolding_all exact (h :))

theorem sp_pin (a : TwArgs ex t) (x : R3.TwIn ex) (hx : HEq a.x x) (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7) (hK : X.LevelSubgroupCharacter)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (pw : ∀ u, PerW X hK u)
    (Dc : ∀ Zs : DefSub (famT t).fam3.amb3, DefCols ((famT t).side3 t.r.z.F.P1 t.r.z.F.ψ1 Zs)) (Sp : ∀ Zs, SPer (Dc Zs))
    (wU : (w.st Z).toD7.what₂.Word → (Dc (zsOf t.r.z.R t.r.z.F)).Mem) (bij : Function.Bijective wU)
    (eNu : ∀ u, (Fin ((Dc (zsOf t.r.z.R t.r.z.F)).a (wU u)) → (w.st Z).toD7.what₂.LL) ≃ₗ[(w.st Z).toD7.what₂.LL] ((w.st Z).toD7.div.Nu u).V)
    (hD : a.Dc = Dc) (hS : HEq a.Sp Sp) (hW : HEq x.C.wU wU) (hN : HEq x.C.eNu eNu)
    (hz : Sp (zsOf t.r.z.R t.r.z.F) =
      spRead X (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) (Dc (zsOf t.r.z.R t.r.z.F)) hK Gd pw wU bij eNu) :
    HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := X) (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) hK Gd
      x.wd (fun m => pw (x.wd m)) x.bR) := by
  obtain rfl := eq_of_heq hx
  subst hD
  obtain rfl := eq_of_heq hS
  have hsp0_raw :
      ∃ (wU₂ : (w.st Z).toD7.what₂.Word → (a.Dc (zsOf t.r.z.R t.r.z.F)).Mem) (bij₂ : Function.Bijective wU₂)
        (eNu₂ : ∀ u, (Fin ((a.Dc (zsOf t.r.z.R t.r.z.F)).a (wU₂ u)) → (w.st Z).toD7.what₂.LL) ≃ₗ[(w.st Z).toD7.what₂.LL] ((w.st Z).toD7.div.Nu u).V),
        HEq wU₂ wU ∧ HEq eNu₂ eNu ∧
        a.Sp (zsOf t.r.z.R t.r.z.F) =
          spRead X (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) (a.Dc (zsOf t.r.z.R t.r.z.F)) hK Gd pw wU₂ bij₂ eNu₂ :=
    ⟨wU, bij, eNu, HEq.rfl, HEq.rfl, hz⟩
  obtain ⟨wU₁, bij₁, eNu₁, hw₁, hn₁, hz₁⟩ := pack_sp X hK Gd pw wU eNu a.pack (by exact_defeq hsp0_raw)
  exact_defeq (heq_of_eq (hz₁.trans (spRead_congr X _ _ hK Gd pw wU₁ bij₁ eNu₁ a.x.C.wU a.x.C.bij a.x.C.eNu
    (hW.trans hw₁.symm) (hN.trans hn₁.symm))))

theorem see_pin (a : TwArgs ex t) (x : R3.TwIn ex) (hx : HEq a.x x) (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (ι : Formalism.L2.Theta.GA (w.st Z).toD7 (Yc (w.st Z).toD7 0) ≃* X.B.I.GA)
    (g : Formalism.L2.Theta.GA (w.st Z).toD7 (Yc (w.st Z).toD7 0)) (c κ : ℝ)
    (sE : Tw (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) t.r.z.R.toRealDat.HE.H →ₗ⋆[ℂ] Tw (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) (HHX X))
    (h : Places t.r.z.R.toRealDat t.r.z.F.lv2 X Gd ι g c (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) κ sE) :
    ∃ sE' : Tw (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) x.R.toRealDat.HE.H →ₗ⋆[ℂ] Tw (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) (HHX X),
      HEq sE sE' ∧ Places x.R.toRealDat x.F.lv2 X Gd ι g c (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) κ sE' := by
  obtain rfl := eq_of_heq hx
  refine pack_see X Gd ι g c κ a.pack sE ⟨(by with_unfolding_all exact (sE :)), ?_, ?_⟩
  · exact (by with_unfolding_all exact (HEq.refl sE :))
  · exact (by with_unfolding_all exact (h :))


theorem read_cols (Dc : ∀ Zs : DefSub (famT t).fam3.amb3, DefCols ((famT t).side3 t.r.z.F.P1 t.r.z.F.ψ1 Zs)) (Sp₀ : ∀ Zs, SPer (Dc Zs))
    (Zsc₀ : DefSub (famT t).fam3.amb3 → IndefScale (famT t).fam3.base3)
    (C₀ : ReadC t.r.z.R (reFace t.r.z.F Dc Sp₀ Zsc₀) ex.p0 ((by with_unfolding_all exact (t.r.Y :)))) :
    ∃ (wU : (w.st Z).toD7.what₂.Word → (Dc (zsOf t.r.z.R t.r.z.F)).Mem) (_ : Function.Bijective wU)
      (eNu : ∀ u, (Fin ((Dc (zsOf t.r.z.R t.r.z.F)).a (wU u)) → (w.st Z).toD7.what₂.LL) ≃ₗ[(w.st Z).toD7.what₂.LL] ((w.st Z).toD7.div.Nu u).V),
      HEq C₀.wU wU ∧ HEq C₀.eNu eNu := by
  refine ⟨(by with_unfolding_all exact (C₀.wU :)), (by with_unfolding_all exact (C₀.bij :)), (by with_unfolding_all exact (C₀.eNu :)), ?_, ?_⟩
  · exact (by with_unfolding_all exact (HEq.refl C₀.wU :))
  · exact (by with_unfolding_all exact (HEq.refl C₀.eNu :))



theorem see_cast (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7) (hK : X.LevelSubgroupCharacter)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (pw : ∀ u, PerW X hK u)
    (Dc : DefCols ((famT t).side3 t.r.z.F.P1 t.r.z.F.ψ1 (zsOf t.r.z.R t.r.z.F))) (S : SPer Dc)
    (wU : (w.st Z).toD7.what₂.Word → Dc.Mem) (bij : Function.Bijective wU)
    (eNu : ∀ u, (Fin (Dc.a (wU u)) → (w.st Z).toD7.what₂.LL) ≃ₗ[(w.st Z).toD7.what₂.LL] ((w.st Z).toD7.div.Nu u).V)
    (hz : S = spRead X (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) Dc hK Gd pw wU bij eNu)
    (sE : Tw (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) t.r.z.R.toRealDat.HE.H →ₗ⋆[ℂ] Tw (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) (HHX X)) :
    ∃ sEE : (t.r.z.R.toCx3 t.r.z.F).EE →ₗ⋆[ℂ] S.HH, HEq sEE sE := by
  subst hz
  refine ⟨(by with_unfolding_all exact (sE :)), ?_⟩
  exact (by with_unfolding_all exact (HEq.refl sE :))



theorem selection_group_ambient_tie (hC : GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧
      GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay)
    (hA : AmbAre t.r.Z ex.amb ex.amb0) (hM : MjAre t.r.Z Yd)
    (hG : GrpTie (w.st Z).toD7 (famT t).A t.r.z.F.P0 t.r.z.F.ψ0 t.r.z.F.P1 t.r.z.F.ψ1 (t.r.z.R.eG.trans t.r.z.cG))
    (hp : ∀ p, t.r.z.R.EEp3 p ≠ ⊥ → ∀ i, t.r.z.R.Wp3 i p ≠ ⊥ ∧ ∀ v, v ≠ (famT t).A.v0 → t.r.z.R.PartAt t.r.z.F i p v)
    (Dc : ∀ Zs : DefSub (famT t).fam3.amb3, DefCols ((famT t).side3 t.r.z.F.P1 t.r.z.F.ψ1 Zs)) (Sp₀ : ∀ Zs, SPer (Dc Zs))
    (Zsc₀ : DefSub (famT t).fam3.amb3 → IndefScale (famT t).fam3.base3)
    (C₀ : ReadC t.r.z.R (reFace t.r.z.F Dc Sp₀ Zsc₀) ex.p0 ((by with_unfolding_all exact (t.r.Y :))))
    (X : Formalism.L2.SG.HidaSetting.HidaSetting (w.st Z).toD7) (hK : X.LevelSubgroupCharacter) (Gd : Formalism.L2.SG.RowDict.GoodOp X) (pw : ∀ u, PerW X hK u)
    (ι : Formalism.L2.Theta.GA (w.st Z).toD7 (Yc (w.st Z).toD7 0) ≃* X.B.I.GA) (g : Formalism.L2.Theta.GA (w.st Z).toD7 (Yc (w.st Z).toD7 0)) (c : ℝ) (hc : 0 < c)
    (hev : EvalTieT (t.r.z.R.toRealDat.MY 0) t.r.z.R.toRealDat.ν0 t.r.z.R.toRealDat.fd0
      (t.r.z.R.toRealDat.EEat (t.r.z.R.toRealDat.levR t.r.z.F.lv2 true)) X Gd ι g c)
    (L' : SizeData₂ (w.st Z).toD7) (Del h0 : ℕ) (c' : ℝ) :
    ∃ (a : TwArgs ex t) (x : R3.TwIn ex), HEq a.x x ∧ a.Dc = Dc ∧ HEq x.C.wU C₀.wU ∧ HEq x.C.eNu C₀.eNu ∧
      x.F.Zsc = zscRaw x.A3 x.F L' Del h0 c' ∧
      HEq (x.F.Sp (zsOf x.R x.F)) (Formalism.IndefR.Cx.spOf (X := X) (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) (x.F.Dc (zsOf x.R x.F)) hK Gd
        x.wd (fun m => pw (x.wd m)) x.bR) ∧
      ∃ (κ : ℝ) (sE' : Tw (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) x.R.toRealDat.HE.H →ₗ⋆[ℂ]
          Tw (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) (HHX X)),
        HEq x.sEE sE' ∧ 0 < κ ∧ Places x.R.toRealDat x.F.lv2 X Gd ι g c (twAt (w.st Z).toD7.what₂.embLL x.A3.A.v0) κ sE' := by
  obtain ⟨wU, bij, eNu, hw0, hn0⟩ := read_cols (ex := ex) (t := t) Dc Sp₀ Zsc₀ C₀
  obtain ⟨Sp, hSp⟩ : ∃ Sp : ∀ Zs, SPer (Dc Zs), Sp (zsOf t.r.z.R t.r.z.F) =
      spRead X (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) (Dc (zsOf t.r.z.R t.r.z.F)) hK Gd pw wU bij eNu := by
    classical
    exact ⟨Function.update Sp₀ (zsOf t.r.z.R t.r.z.F) _, Function.update_self _ _ _⟩
  obtain ⟨κ, sE, hκ, hsE⟩ := exists_places t.r.z.R.toRealDat t.r.z.F.lv2 X Gd ι g c
    (twAt (w.st Z).toD7.what₂.embLL (famT t).A.v0) t.r.z.pins.char.base.models.HE hc hev
  obtain ⟨sEE, hsEE⟩ := see_cast (ex := ex) (t := t) X hK Gd pw _ _ wU bij eNu hSp sE
  obtain ⟨a, haDc, haSp, haZsc, haSEE, haWU, haENu, -⟩ := GlobalTheory.T.column_params_instance_data hC K B f T w Z Wt L hT Gi Gl Kc Yd cX ex t hA hM hG hp
    Dc Sp₀ Zsc₀ C₀ Sp (zscRaw (famT t) t.r.z.F L' Del h0 c') sEE
  obtain ⟨x, hx⟩ : ∃ x : R3.TwIn ex, HEq a.x x := ⟨a.x, HEq.rfl⟩
  have hW : HEq x.C.wU C₀.wU := by
    obtain rfl := eq_of_heq hx
    exact (by with_unfolding_all exact (haWU :))
  have hN : HEq x.C.eNu C₀.eNu := by
    obtain rfl := eq_of_heq hx
    exact (by with_unfolding_all exact (haENu :))
  have hE : HEq x.sEE sEE := by
    obtain rfl := eq_of_heq hx
    exact (by with_unfolding_all exact (haSEE :))
  obtain ⟨sE', h1, h2⟩ := see_pin a x hx X Gd ι g c κ sE hsE
  exact ⟨a, x, hx, haDc, hW, hN, zsc_pin a x hx L' Del h0 c' haZsc,
    sp_pin a x hx X hK Gd pw Dc Sp wU bij eNu haDc haSp (hW.trans hw0) (hN.trans hn0) hSp,
    κ, sE', (hE.trans hsEE).trans h1, hκ, h2⟩

end Args

end GlobalTheory.Mem.R3.SelectionPairing

end
