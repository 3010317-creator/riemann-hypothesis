module

public import Formalism.SizeWindowBrackets.WindowSettingSatisfiable
public import Formalism.SizeWindowBrackets.ChainSlopeWindows.AdmissibleSchurLemma
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone

@[expose] public section

namespace Formalism.LFunctionChainParameters.PrimeWindowSizeBounds

open Finset Classical
open Formalism.LFunctionChainParameters.DeficitSplitLemmas Formalism.LFunctionChainParameters.LErr

structure Facts (P : Par) (e K z u E X S sb v w8 : ℝ) : Prop where
  hx : 100 ≤ P.x
  he : 0 ≤ e
  hK : 1 ≤ K
  z1 : 1 ≤ z
  hz4 : 100 * K * z ^ 4 ≤ P.x
  u1 : 1 ≤ u
  uz : u ≤ z
  E1 : 1 ≤ E
  hXB : 100 * K * (E ^ 4 * P.x ^ 4) ≤ X
  S1 : 1 ≤ S
  hsb : 100 * K * (E ^ 4 * P.x ^ 4) * (X * S) ≤ sb
  hb : P.b = sb * sb
  ha : P.a = P.x * P.b
  hXp : P.Xp = X
  hvX : v * X = P.b
  v0 : 0 ≤ v
  hbp : P.bp = P.x * v
  hwpp : P.wpp = v / P.n
  hXpp : P.Xpp = P.x * P.n * X
  lx0 : 0 ≤ P.lx
  lxz : P.lx ≤ z
  elx : e * P.lx ≤ z
  logX : Real.log X = u
  loga : Real.log P.a = P.lx + z
  nx : P.x ^ 2 ≤ P.n
  n2x : P.x ^ 2 ≤ (2 : ℝ) ^ P.e₂
  n2n : (2 : ℝ) ^ P.e₂ ≤ P.n
  nE : P.n ≤ E
  kx : P.x ^ 2 ≤ P.k
  kE : P.k ≤ E
  N0 : 0 ≤ P.N
  NE : P.N ≤ E
  t0 : 0 ≤ P.t
  tE : P.t ≤ E
  px : P.x ^ 4 + 1 ≤ (P.p₀ : ℝ)
  pE : (P.p₀ : ℝ) ≤ E
  La0 : 0 ≤ P.La
  Laz : P.La ≤ z ^ 2
  r0 : 0 ≤ P.rG
  rE : P.rG ≤ E
  Sc0 : 0 ≤ P.Sc
  ScS : P.Sc ≤ S
  η0 : 0 ≤ P.η
  ηS : P.η ≤ S
  ρ0 : 0 ≤ P.ρ
  ρx : P.ρ ≤ (P.x ^ 2)⁻¹
  th0 : 0 ≤ P.th
  thx : P.th ≤ P.x⁻¹
  x_sq_le_threshold : P.x ^ 2 ≤ P.K₀
  dx : P.x ^ 2 ≤ (P.d : ℝ)
  C0 : 0 ≤ P.C
  CK : P.C ≤ K
  β0 : 0 ≤ P.β
  βK : P.β ≤ K * (P.x ^ 2)⁻¹
  Co0 : 0 ≤ P.Cord
  CoK : P.Cord ≤ K
  Y1 : 1 ≤ P.Y
  YX : P.Y ≤ 2 * X
  s0 : 0 ≤ P.s₀
  sx : P.s₀ ≤ (P.x ^ 2)⁻¹
  bo0 : 0 ≤ P.bo
  bosb : P.bo ≤ sb
  hδ : P.δ₁ = w8⁻¹
  w81 : 1 ≤ w8
  w8z : w8 ≤ z
  hθ : P.θ = z⁻¹
  Joz : (P.Jo : ℝ) ≤ z
  Ibu : (P.Ib : ℝ) ≤ u
  hE : E = P.x ^ e
  hu : u = P.x ^ (P.ε / 3)
  hz : z = P.x ^ P.ε

theorem facts {P : Par} {e K : ℝ} (hW : Windows P e K) (hL : LargeX P.x P.ε e K) :
    ∃ z u E X S sb v w8 : ℝ, Facts P e K z u E X S sb v w8 := by
  obtain ⟨hε, _, he, hK, ⟨n2x, n2n⟩, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE,
    Sc0, ScS, η0, ηS, ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, β0, βK, Co0, CoK,
    Y1, YX, s0, sx, bo0, bosb⟩ := hW
  obtain ⟨x1, hC, hB, hA⟩ := hL
  have xpos : 0 < P.x := by linarith
  rw [mul_comm 4, Real.rpow_mul xpos.le, Real.rpow_ofNat] at hC; rw [mul_comm 2, Real.rpow_mul xpos.le, Real.rpow_ofNat] at Laz
  have eM : P.x ^ (4 * e + 4) = (P.x ^ e) ^ 4 * P.x ^ 4 := by
    rw [Real.rpow_add xpos, mul_comm 4 e, Real.rpow_mul xpos.le, Real.rpow_ofNat, Real.rpow_ofNat]
  rw [eM] at hB hA; rw [Real.exp_add] at hA
  have z1 : 1 ≤ P.x ^ P.ε := Real.one_le_rpow x1 hε.le
  have hx : 100 ≤ P.x := by linarith [one_le_mul_of_one_le_of_one_le hK (one_le_pow₀ (n := 4) z1)]
  have lx0 : 0 ≤ Real.log P.x := Real.log_nonneg x1
  have helx : 0 ≤ e * Real.log P.x := mul_nonneg he lx0
  have uz : P.x ^ (P.ε / 3) ≤ P.x ^ P.ε := Real.rpow_le_rpow_of_exponent_le x1 (by linarith)
  have hlog : 4 * (e * Real.log P.x) + 4 * Real.log P.x ≤ P.x ^ (P.ε / 3) := by
    have h1 : Real.log P.x * (4 * e + 4) ≤ P.x ^ (P.ε / 3) := by
      rw [← Real.exp_le_exp, ← Real.rpow_def_of_pos xpos, eM]
      exact (le_mul_of_one_le_left (by positivity) (by linarith : (1 : ℝ) ≤ 100 * K)).trans hB
    linarith [show Real.log P.x * (4 * e + 4) = 4 * (e * Real.log P.x) + 4 * Real.log P.x by ring]
  have npos : 0 < P.n := lt_of_lt_of_le (by positivity) n2n
  exact ⟨P.x ^ P.ε, P.x ^ (P.ε / 3), P.x ^ e, Real.exp (P.x ^ (P.ε / 3)), Real.exp (P.x ^ (P.ε / 4)),
    Real.exp (P.x ^ P.ε / 2), Real.exp (P.x ^ P.ε) / Real.exp (P.x ^ (P.ε / 3)), P.x ^ (P.ε / 8),
    { hx, he, hK, z1, hz4 := hC, u1 := Real.one_le_rpow x1 (by positivity), uz
      E1 := Real.one_le_rpow x1 he, hXB := hB, S1 := Real.one_le_exp (by positivity), hsb := hA
      hb := by unfold Par.b bTx; rw [← Real.exp_add, add_halves], ha := rfl, hXp := rfl
      hvX := by unfold Par.b bTx; field_simp, v0 := by positivity, hbp := by unfold Par.bp bpTx aTx bTx XpTx; ring
      hwpp := by unfold Par.wpp wppTx bpTx aTx bTx XpTx; field_simp
      hXpp := by unfold Par.Xpp XppTx wppTx bpTx aTx bTx XpTx; field_simp
      lx0, lxz := by unfold Par.lx; linarith, elx := by unfold Par.lx; linarith, logX := Real.log_exp _
      loga := by unfold Par.a aTx bTx Par.lx; rw [Real.log_mul xpos.ne' (Real.exp_pos _).ne', Real.log_exp]
      nx := n2x.trans n2n, n2x, n2n, nE, kx, kE, N0, NE, t0, tE, px, pE, La0, Laz, r0, rE
      Sc0, ScS, η0, ηS, ρ0, ρx, th0, thx, x_sq_le_threshold, dx, C0, CK, β0, βK, Co0, CoK, Y1, YX, s0, sx, bo0, bosb
      hδ := by unfold Par.δ₁; rw [Real.rpow_neg xpos.le], hθ := by unfold Par.θ; rw [Real.rpow_neg xpos.le]
      w81 := Real.one_le_rpow x1 (by positivity), w8z := Real.rpow_le_rpow_of_exponent_le x1 (by linarith)
      Joz := (Nat.floor_le (by positivity)).trans (Real.rpow_le_rpow_of_exponent_le x1 (by linarith))
      Ibu := Nat.floor_le (by positivity), hE := rfl, hu := rfl, hz := rfl }⟩

lemma scale1' {m T q c b : ℝ} (hm : 0 ≤ m) (hT : 1 ≤ T) (hcb : 0 ≤ c * b) (h : q ≤ c * b) :
    m * q ≤ c * (T * m * b) := by
  linarith [mul_le_mul_of_nonneg_left h hm, mul_nonneg (show 0 ≤ T - 1 by linarith) (mul_nonneg hm hcb)]
lemma scale2 {m T q c b : ℝ} (hm : 0 ≤ m) (hT : 1 ≤ T) (h : q ≤ c * b) :
    m * T * q ≤ c * (T * m * b) := by
  linarith [mul_le_mul_of_nonneg_left h (mul_nonneg hm (show 0 ≤ T by linarith))]
lemma log_four_le_three_halves : Real.log 4 ≤ 3 / 2 := by
  have : Real.log 4 = 2 * Real.log 2 := by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  linarith [Real.log_two_lt_d9]
lemma log_four_nonneg : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
lemma log_two_le_one_alt : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
lemma log_two_nonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)

namespace Facts
variable {P : Par} {e K z u E X S sb v w8 : ℝ} (F : Facts P e K z u E X S sb v w8)
include F
lemma xpos : 0 < P.x := by linarith [F.hx]
lemma x1 : 1 ≤ P.x := by linarith [F.hx]
lemma Kpos : 0 < K := by linarith [F.hK]
lemma zpos : 0 < z := by linarith [F.z1]
lemma Epos : 0 < E := by linarith [F.E1]
lemma Spos : 0 < S := by linarith [F.S1]
lemma M1 : 1 ≤ E ^ 4 * P.x ^ 4 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ F.E1) (one_le_pow₀ F.x1)
lemma one_le_threshold_mul_powers : 1 ≤ K * (E ^ 4 * P.x ^ 4) := one_le_mul_of_one_le_of_one_le F.hK F.M1
lemma X1 : 1 ≤ X := by linarith [F.one_le_threshold_mul_powers, F.hXB]
lemma Xpos : 0 < X := by linarith [F.X1]
lemma one_le_x_mul_s : 1 ≤ X * S := one_le_mul_of_one_le_of_one_le F.X1 F.S1
lemma sb1 : 1 ≤ sb := by linarith [one_le_mul_of_one_le_of_one_le F.one_le_threshold_mul_powers F.one_le_x_mul_s, F.hsb]
lemma bpos : 0 < P.b := by rw [F.hb]; have := F.sb1; positivity
lemma b0 : 0 ≤ P.b := F.bpos.le
lemma sb_le_b : sb ≤ P.b := by rw [F.hb]; exact le_mul_of_one_le_left (by linarith [F.sb1]) F.sb1
lemma hbXS : 100 * K * (E ^ 4 * P.x ^ 4) * (X * S) ≤ P.b := F.hsb.trans F.sb_le_b
lemma hbsb : 100 * K * (E ^ 4 * P.x ^ 4) * (X * S) * sb ≤ P.b := F.hb ▸ mul_le_mul_of_nonneg_right F.hsb (by linarith [F.sb1])
lemma zpow_le {i : ℕ} (hi : i ≤ 4) : 100 * K * z ^ i ≤ P.x :=
  (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ F.z1 hi) (by linarith [F.hK])).trans F.hz4
lemma hundred_z_le_x : 100 * z ≤ P.x := by
  linarith [pow_one z ▸ F.zpow_le (i := 1) (by norm_num), mul_le_mul_of_nonneg_right F.hK F.zpos.le]
lemma rpos : 0 < P.x⁻¹ := inv_pos.2 F.xpos
lemma xr : P.x * P.x⁻¹ = 1 := mul_inv_cancel₀ F.xpos.ne'
lemma r2 : (P.x ^ 2)⁻¹ = P.x⁻¹ ^ 2 := let _ := F; (inv_pow _ _).symm
lemma Kzr {i : ℕ} (hi : i ≤ 4) : 100 * K * z ^ i * P.x⁻¹ ≤ 1 := F.xr ▸ mul_le_mul_of_nonneg_right (F.zpow_le hi) F.rpos.le
lemma Kzr0 (i : ℕ) : 0 ≤ 100 * K * z ^ i * P.x⁻¹ := by have := F.Kpos; have := F.zpos; have := F.rpos; positivity
lemma zr0 (i : ℕ) : 0 ≤ 100 * z ^ i * P.x⁻¹ := by have := F.zpos; have := F.rpos; positivity
lemma div_le_div_sq_of_le {A B y : ℝ} (hAB : A ≤ B) (hB : 0 ≤ B) (hy : P.x ^ 2 ≤ y) :
    A / y ≤ B * P.x⁻¹ ^ 2 := by rw [← F.r2, ← div_eq_mul_inv]; exact div_le_div₀ hB hAB (pow_pos F.xpos 2) hy
lemma npos : 0 < P.n := (pow_pos F.xpos 2).trans_le F.nx
lemma n1 : 1 ≤ P.n := (one_le_pow₀ F.x1).trans F.nx
lemma apos : 0 < P.a := F.ha ▸ mul_pos F.xpos F.bpos
lemma la0 : 0 ≤ P.lx + z := add_nonneg F.lx0 F.zpos.le
lemma la2z : P.lx + z ≤ 2 * z := by linarith [F.lxz]
lemma lax : P.lx + z ≤ P.x := by linarith [F.lxz, F.hundred_z_le_x, F.zpos]
lemma logE : Real.log E = e * P.lx := by rw [F.hE, Real.log_rpow F.xpos]; rfl
lemma log_le_alt {y : ℝ} (hy0 : 0 < y) (hy : y ≤ E) : Real.log y ≤ z := (Real.log_le_log hy0 hy).trans (F.logE ▸ F.elx)
lemma v_le_b : v ≤ P.b := F.hvX ▸ le_mul_of_one_le_right F.v0 F.X1
lemma hsg : sg P K = 100 * K * z ^ 4 * P.x⁻¹ := by
  unfold sg; rw [F.hz, div_eq_mul_inv, mul_comm 4 P.ε, Real.rpow_mul F.xpos.le, Real.rpow_ofNat]
lemma sg0 : 0 ≤ sg P K := F.hsg ▸ F.Kzr0 4
lemma sg1 : sg P K ≤ 1 := F.hsg ▸ F.Kzr le_rfl
lemma Kzr_sg {i : ℕ} (hi : i ≤ 4) : 100 * K * z ^ i * P.x⁻¹ ≤ sg P K :=
  F.hsg ▸ mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ F.z1 hi) (by linarith [F.hK])) F.rpos.le
lemma zr_sg {i : ℕ} (hi : i ≤ 4) : 100 * z ^ i * P.x⁻¹ ≤ sg P K :=
  (mul_le_mul_of_nonneg_right (by linarith [mul_le_mul_of_nonneg_right F.hK (pow_nonneg F.zpos.le i)]) F.rpos.le).trans (F.Kzr_sg hi)
lemma r_sg : P.x⁻¹ ≤ sg P K := F.hsg ▸ le_mul_of_one_le_left F.rpos.le
  (by linarith [one_le_mul_of_one_le_of_one_le F.hK (one_le_pow₀ (n := 4) F.z1)])
lemma close_sg {c w : ℝ} (_hc0 : 0 ≤ c) (hc : c ≤ 1) (hw0 : 0 ≤ w) (hw : w ≤ sg P K) :
    P.b * c * w ≤ sg P K * P.b := by linarith [mul_le_mul_of_nonneg_left (mul_le_mul hc hw hw0 zero_le_one) F.b0]
lemma br_sg : P.b * P.x⁻¹ ≤ sg P K * P.b := by linarith [mul_le_mul_of_nonneg_left F.r_sg F.b0]
lemma monoG {i j i' j' : ℕ} (hi : i ≤ i') (hj : j ≤ j') : E ^ i * P.x ^ j ≤ E ^ i' * P.x ^ j' :=
  mul_le_mul (pow_le_pow_right₀ F.E1 hi) (pow_le_pow_right₀ F.x1 hj) (pow_nonneg F.xpos.le _) (pow_nonneg F.Epos.le _)
lemma mono3 {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) : E ^ i * P.x ^ j ≤ E ^ 4 * P.x ^ 4 * P.x⁻¹ := by
  simpa [show E ^ 4 * P.x ^ 4 * P.x⁻¹ = E ^ 4 * P.x ^ 3 * (P.x * P.x⁻¹) by ring, F.xr] using F.monoG hi hj
private lemma poly_step {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) {c : ℝ} (hc : c ≤ 100) :
    c * K * (E ^ i * P.x ^ j) ≤ 100 * K * (E ^ 4 * P.x ^ 4 * P.x⁻¹) :=
  mul_le_mul (mul_le_mul_of_nonneg_right hc F.Kpos.le) (F.mono3 hi hj)
    (mul_nonneg (pow_nonneg F.Epos.le _) (pow_nonneg F.xpos.le _)) (by linarith [F.Kpos])
lemma polyXS' {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) {c : ℝ} (hc : c ≤ 100) :
    c * K * (E ^ i * P.x ^ j) * (X * S) ≤ sg P K * P.b :=
  (mul_le_mul_of_nonneg_right (F.poly_step hi hj hc) (by linarith [F.one_le_x_mul_s])).trans
    ((le_of_eq_of_le (by ring) (mul_le_mul_of_nonneg_right F.hbXS F.rpos.le)).trans F.br_sg)
lemma polyX' {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 100) :
    c * K * (E ^ i * P.x ^ j) * X ≤ sg P K * P.b :=
  (mul_le_mul_of_nonneg_left (le_mul_of_one_le_right F.Xpos.le F.S1)
    (mul_nonneg (mul_nonneg hc0 F.Kpos.le) (mul_nonneg (pow_nonneg F.Epos.le _) (pow_nonneg F.xpos.le _)))).trans
    (F.polyXS' hi hj hc)
lemma polyv' {i j : ℕ} (hi : i ≤ 4) (hj : j ≤ 3) {c : ℝ} (hc : c ≤ 100) :
    c * K * (E ^ i * P.x ^ j) * v ≤ sg P K * P.b :=
  (mul_le_mul_of_nonneg_right (F.poly_step hi hj hc) F.v0).trans
    ((le_of_eq_of_le (by ring : _ = 100 * K * (E ^ 4 * P.x ^ 4) * v * P.x⁻¹)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right F.hXB F.v0) F.rpos.le)).trans
      (by rw [mul_comm X v, F.hvX]; exact F.br_sg))
private lemma x_le_sq : P.x ≤ P.x ^ 2 := by simpa using pow_le_pow_right₀ F.x1 (by norm_num : 1 ≤ 2)
private lemma x2_le_p0 : P.x ^ 2 ≤ (P.p₀ : ℝ) - 1 := (pow_le_pow_right₀ F.x1 (by norm_num : 2 ≤ 4)).trans (by linarith [F.px])
private lemma log_two_Xp_le : Real.log (2 * P.Xp) ≤ 2 * z := by
  rw [F.hXp, Real.log_mul (by norm_num) F.Xpos.ne', F.logX]; linarith [log_two_le_one_alt, F.uz, F.z1]
private lemma log_Xpp_le : Real.log P.Xpp ≤ 3 * z := by
  rw [F.hXpp, Real.log_mul (mul_pos F.xpos F.npos).ne' F.Xpos.ne', Real.log_mul F.xpos.ne' F.npos.ne', F.logX]
  linarith [F.log_le_alt F.npos F.nE, show Real.log P.x ≤ z from F.lxz, F.uz]
private lemma bKzr_sg (c : ℝ) (i : ℕ) (hi : i ≤ 4) (hc : c ≤ 100) : c * K * z ^ i * P.x⁻¹ * P.b ≤ sg P K * P.b := by
  have := F.Kpos; have := F.zpos; have := F.rpos
  exact mul_le_mul_of_nonneg_right ((by gcongr : _ ≤ 100 * K * z ^ i * P.x⁻¹).trans (F.Kzr_sg hi)) F.b0
private lemma bzr_sg (c : ℝ) (i : ℕ) (hi : i ≤ 4) (hc : c ≤ 100) : c * z ^ i * P.x⁻¹ * P.b ≤ sg P K * P.b := by
  have := F.zpos; have := F.rpos
  exact mul_le_mul_of_nonneg_right ((by gcongr : _ ≤ 100 * z ^ i * P.x⁻¹).trans (F.zr_sg hi)) F.b0
private lemma aKzr_sg (c : ℝ) (i : ℕ) (hi : i ≤ 4) (hc : c ≤ 100) : c * K * z ^ i * P.x⁻¹ ^ 2 * P.a ≤ sg P K * P.b := by
  rw [F.ha, show c * K * z ^ i * P.x⁻¹ ^ 2 * (P.x * P.b) = c * K * z ^ i * P.x⁻¹ * P.b * (P.x * P.x⁻¹) by ring,
    F.xr, mul_one]; exact F.bKzr_sg c i hi hc
private lemma azr_sg (c : ℝ) (i : ℕ) (hi : i ≤ 4) (hc : c ≤ 100) : c * z ^ i * P.x⁻¹ ^ 2 * P.a ≤ sg P K * P.b := by
  rw [F.ha, show c * z ^ i * P.x⁻¹ ^ 2 * (P.x * P.b) = c * z ^ i * P.x⁻¹ * P.b * (P.x * P.x⁻¹) by ring,
    F.xr, mul_one]; exact F.bzr_sg c i hi hc
end Facts

theorem size_floors_bound : SizeFloors := fun P e K m T hW hL hm hT => by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  refine scale1' hm hT (mul_nonneg F.sg0 F.b0) ?_
  rw [F.hXpp, F.loga]; unfold Par.f
  have := F.C0; have := F.CK; have := F.npos; have := F.nE; have := F.N0; have := F.NE; have := F.la0
  have := F.xpos; have := F.Xpos; have := F.Kpos; have := F.Epos; have : P.lx + z ≤ P.x ^ 2 := F.lax.trans F.x_le_sq
  have : (P.lx + z) ^ 2 ≤ E ^ 2 * P.x ^ 2 :=
    (pow_le_pow_left₀ F.la0 F.lax 2).trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ F.E1))
  calc _ ≤ 2 * K * (2 * E) * (P.x * E * X) * (E ^ 2 * P.x ^ 2 + 2 * (E ^ 2 * P.x ^ 2)) := by gcongr
    _ = 12 * K * (E ^ 4 * P.x ^ 3) * X := by ring
    _ ≤ sg P K * P.b := F.polyX' le_rfl le_rfl (by norm_num) (by norm_num)

theorem size_cp_bucket_bound : SizeCp := fun P e K m T hW hL hm hT => by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have hl : Real.log (2 * P.a) = Real.log 2 + (P.lx + z) := by rw [Real.log_mul (by norm_num) F.apos.ne', F.loga]
  have hl0 : 0 ≤ Real.log (2 * P.a) := hl ▸ add_nonneg log_two_nonneg F.la0
  have hlx : Real.log (2 * P.a) ≤ P.x := by rw [hl]; linarith [log_two_le_one_alt, F.la2z, F.hundred_z_le_x, F.z1]
  have hSk0 : 0 ≤ P.Sk := by unfold Par.Sk; linarith [F.Sc0, F.η0, F.kx, pow_pos F.xpos 2]
  have hSk : P.Sk ≤ 3 * (E * S) := by
    unfold Par.Sk; linarith [F.ScS, F.ηS, F.kE, le_mul_of_one_le_left F.Spos.le F.E1, le_mul_of_one_le_right F.Epos.le F.S1]
  have := F.C0; have := F.CK; have := F.npos; have := F.nE; have := F.xpos; have := F.Xpos; have := F.Kpos; have := F.Epos; have := F.Spos
  unfold tCp unitU; linarith [scale2 hm hT (F.hXpp ▸ le_trans
    (by gcongr : 2 * P.C * P.Sk * Real.log (2 * P.a) * (P.x * P.n * X) ≤ 2 * K * (3 * (E * S)) * P.x * (P.x * E * X))
    (le_of_eq_of_le (by ring : _ = 6 * K * (E ^ 2 * P.x ^ 2) * (X * S)) (F.polyXS' (by norm_num) (by norm_num) (by norm_num))))]

theorem size_prime_low_bound : SizePrLow := fun P e K m T hW hL hm hT => by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have := F.C0; have := F.CK; have := F.r0; have := F.rE; have := F.pE; have := F.lx0; have := F.v0; have := F.xpos
  have := F.Kpos; have := F.Epos; have := log_four_le_three_halves; have := log_four_nonneg; have : (0 : ℝ) ≤ P.p₀ := Nat.cast_nonneg _
  have : P.lx ≤ P.x := by linarith [F.lxz, F.hundred_z_le_x, F.zpos]
  exact scale2 hm hT (by unfold Par.Q₁; rw [F.hbp]; calc _ ≤ 2 * (3 / 2) * (E * (K * E * (P.x * v) * P.x)) := by gcongr
    _ = 3 * K * (E ^ 2 * P.x ^ 2) * v := by ring
    _ ≤ sg P K * P.b := F.polyv' (by norm_num) (by norm_num) (by norm_num))

lemma xprime_q_two_expand {P : Par} {e K z u E X S sb v w8 : ℝ} (F : Facts P e K z u E X S sb v w8) :
    P.Xp * P.Q₂ = P.C * P.b + P.C * X * (P.η + P.Sc) + P.C * (P.b / P.n) * P.lx * w8
      + P.C * X * P.t * P.lx * w8 + X * P.bo := by
  unfold Par.Q₂; rw [F.hXp, F.hbp, F.hwpp, F.hδ, ← F.hvX, div_inv_eq_mul]
  have := F.xpos.ne'; have := F.npos.ne'; field_simp; ring

theorem size_prime_high_bound : SizePrHigh := fun P e K m T hW hL hm hT => by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have := F.C0; have := F.CK; have := F.xpos; have := F.Xpos; have := F.Kpos; have := F.Epos; have := F.Spos; have hb := F.b0
  have := F.zpos; have := F.lx0; have := F.lxz; have := F.w8z; have := F.η0; have := F.ηS; have := F.Sc0; have := F.ScS
  have hw0 : 0 ≤ w8 := by linarith [F.w81]
  have hr0 := F.rpos
  have p2 : 4 * (P.C * X * (P.η + P.Sc)) ≤ sg P K * P.b := le_trans (by gcongr : _ ≤ 4 * (K * X * (S + S)))
    (le_of_eq_of_le (by ring : _ = 8 * K * (E ^ 0 * P.x ^ 0) * (X * S)) (F.polyXS' (by norm_num) (by norm_num) (by norm_num)))
  have p3 : 4 * (P.C * (P.b / P.n) * P.lx * w8) ≤ sg P K * P.b := by
    have : P.b / P.n ≤ P.b * P.x⁻¹ := div_eq_mul_inv P.b P.x ▸ div_le_div_of_nonneg_left hb F.xpos (F.x_le_sq.trans F.nx)
    have : 0 ≤ P.b / P.n := div_nonneg hb F.npos.le
    exact le_trans (by gcongr : _ ≤ 4 * (K * (P.b * P.x⁻¹) * z * z)) (le_of_eq_of_le (by ring) (F.bKzr_sg 4 2 (by norm_num) (by norm_num)))
  have p4 : 4 * (P.C * X * P.t * P.lx * w8) ≤ sg P K * P.b := by
    have := F.t0; have := F.tE; have : 0 ≤ P.lx * w8 := by positivity
    have : P.lx * w8 ≤ P.x := le_trans (by gcongr : P.lx * w8 ≤ z * z)
      (by simpa [sq] using (le_mul_of_one_le_left (sq_nonneg z) (by linarith [F.hK] : (1 : ℝ) ≤ 100 * K)).trans (F.zpow_le (i := 2) (by norm_num)))
    rw [show P.C * X * P.t * P.lx * w8 = P.C * X * P.t * (P.lx * w8) by ring]
    exact le_trans (by gcongr : _ ≤ 4 * (K * X * E * P.x))
      (le_of_eq_of_le (by ring : _ = 4 * K * (E ^ 1 * P.x ^ 1) * X) (F.polyX' (by norm_num) (by norm_num) (by norm_num) (by norm_num)))
  have p5 : 4 * (X * P.bo) ≤ sg P K * P.b := by
    have : P.x ≤ E ^ 4 * P.x ^ 4 := by simpa using F.monoG (i := 0) (j := 1) (by norm_num) (by norm_num)
    have hxsb : 4 * 1 * P.x * (X * 1) ≤ sb :=
      le_trans (by have := F.hK; have := F.S1; gcongr; norm_num : _ ≤ 100 * K * (E ^ 4 * P.x ^ 4) * (X * S)) F.hsb
    have hbo : 4 * (X * P.bo) * P.x ≤ P.b := F.hb ▸ le_of_eq_of_le (by ring) (mul_le_mul hxsb F.bosb F.bo0 (by linarith [F.sb1]))
    calc 4 * (X * P.bo) = 4 * (X * P.bo) * P.x * P.x⁻¹ := by rw [mul_assoc, F.xr, mul_one]
      _ ≤ sg P K * P.b := (mul_le_mul_of_nonneg_right hbo hr0.le).trans F.br_sg
  have hXQ : P.Xp * P.Q₂ ≤ (P.C + sg P K) * P.b := by rw [xprime_q_two_expand F]; linarith
  exact scale2 hm hT (by linarith [mul_le_mul_of_nonneg_left hXQ (show 0 ≤ 2 * Real.log 4 by linarith [log_four_nonneg]),
    mul_le_mul_of_nonneg_right (show 2 * Real.log 4 ≤ 3 by linarith [log_four_le_three_halves]) (mul_nonneg F.sg0 hb)])

theorem size_or_bucket_bound : SizeOr := fun P e K m T hW hL hm hT => by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have := F.C0; have := F.CK; have := F.xpos; have := F.Kpos; have := F.zpos; have := F.lx0; have := F.lxz; have := F.rpos; have := F.apos
  have hz3 : z ≤ z ^ 3 := by simpa using pow_le_pow_right₀ F.z1 (by norm_num : 1 ≤ 3)
  have c12 : P.La / P.k + 1 / P.K₀ ≤ 2 * z ^ 2 * P.x⁻¹ ^ 2 := by
    linarith [F.div_le_div_sq_of_le F.Laz (by positivity) F.kx, F.div_le_div_sq_of_le le_rfl zero_le_one F.x_sq_le_threshold,
      mul_le_mul_of_nonneg_right (one_le_pow₀ (n := 2) F.z1) (sq_nonneg P.x⁻¹)]
  have c3 : Real.log P.Xp + Real.log 4 ≤ 3 * z := by rw [F.hXp, F.logX]; linarith [F.uz, log_four_le_three_halves, F.z1]
  have c30 : 0 ≤ Real.log P.Xp + Real.log 4 := by rw [F.hXp, F.logX]; linarith [F.u1, log_four_nonneg]
  have c4 : Real.log ((P.p₀ : ℝ) - 1) ≤ z := F.log_le_alt (by linarith [F.x2_le_p0, pow_pos F.xpos 2]) (by linarith [F.pE])
  have c5 : 2 * (Real.log ((P.p₀ : ℝ) - 1) + 1) / ((P.p₀ : ℝ) - 1) ≤ 4 * z ^ 3 * P.x⁻¹ ^ 2 :=
    F.div_le_div_sq_of_le (by linarith [F.z1]) (by positivity) F.x2_le_p0
  have br : (P.La / P.k + 1 / P.K₀) * (Real.log P.Xp + Real.log 4) +
      2 * (Real.log ((P.p₀ : ℝ) - 1) + 1) / ((P.p₀ : ℝ) - 1) ≤ 10 * z ^ 3 * P.x⁻¹ ^ 2 := by
    linarith [mul_le_mul c12 c3 c30 (by positivity),
      show 2 * z ^ 2 * P.x⁻¹ ^ 2 * (3 * z) + 4 * z ^ 3 * P.x⁻¹ ^ 2 = 10 * z ^ 3 * P.x⁻¹ ^ 2 by ring]
  exact scale2 hm hT ((mul_le_mul_of_nonneg_left br (by positivity)).trans
    (le_trans (by gcongr : _ ≤ 2 * K * z * P.a * (10 * z ^ 3 * P.x⁻¹ ^ 2)) (le_of_eq_of_le (by ring) (F.aKzr_sg 20 4 le_rfl (by norm_num)))))

theorem size_orders_bucket_bound : SizeOrders := fun P e K m T hW hL hm hT => by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  unfold tOrders unitU
  have := F.Kpos; have := F.zpos; have := F.rpos; have := F.apos; have := F.Joz; have := F.Co0; have := F.CoK
  have hM1 : 1 ≤ max P.Y P.Xpp := F.Y1.trans (le_max_left _ _)
  have hlM : Real.log (max P.Y P.Xpp) ≤ 3 * z := (max_choice P.Y P.Xpp).elim
    (fun h => h.symm ▸ (Real.log_le_log (by linarith [F.Y1]) (F.hXp ▸ F.YX)).trans (by linarith [F.log_two_Xp_le]))
    (fun h => h.symm ▸ F.log_Xpp_le)
  set M := max P.Y P.Xpp; set n := (2 : ℝ) ^ P.e₂
  have qp : 0 < n := by positivity
  have hL0 : 0 ≤ Real.log (n * M) := Real.log_nonneg (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) hM1)
  have hL3 : Real.log (n * M) ≤ 4 * z := by rw [Real.log_mul qp.ne' (by linarith)]; linarith [F.log_le_alt qp (F.n2n.trans F.nE)]
  have : (0 : ℝ) ≤ P.Jo := Nat.cast_nonneg _
  linarith [scale2 hm hT ((mul_le_mul_of_nonneg_left
    (F.div_le_div_sq_of_le (by gcongr : P.Cord * P.Jo * Real.log (n * M) ^ 2 ≤ K * z * (4 * z) ^ 2) (by positivity) F.n2x)
    (by positivity : 0 ≤ 4 * P.a)).trans (le_of_eq_of_le (by ring) (F.aKzr_sg 64 3 (by norm_num) (by norm_num))))]

theorem size_band_bound : SizeBand := fun P e K m T hW hL hm hT => by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have := F.xpos; have := F.zpos; have := F.rpos; have := F.apos; have := F.ρ0; have := F.log_two_Xp_le
  have : (0 : ℝ) ≤ P.Ib := Nat.cast_nonneg _; have := F.Ibu.trans F.uz; have : P.ρ ≤ P.x⁻¹ ^ 2 := F.r2 ▸ F.ρx
  have : 1 / (P.p₀ : ℝ) ≤ 1 * P.x⁻¹ ^ 2 := F.div_le_div_sq_of_le le_rfl zero_le_one (by linarith [F.x2_le_p0])
  have : 0 ≤ Real.log (2 * P.Xp) := F.hXp ▸ Real.log_nonneg (by linarith [F.X1])
  unfold tBand unitU; linarith [scale2 hm hT (le_trans
    (by gcongr : 4 * P.a * (P.Ib * ((4 * P.ρ + 1 / (P.p₀ : ℝ)) * Real.log (2 * P.Xp))) ≤
      4 * P.a * (z * ((4 * P.x⁻¹ ^ 2 + 1 * P.x⁻¹ ^ 2) * (2 * z))))
    (le_of_eq_of_le (by ring) (F.azr_sg 40 2 (by norm_num) (by norm_num))))]

theorem size_high_bucket_bound : SizeHigh := fun P e K m T hW hL hm hT => by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have := F.xpos; have := F.b0; have := F.zpos; have := F.rpos; have := F.th0; have := F.thx
  have hXpp1 : 1 ≤ P.Xpp := F.hXpp ▸ one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le F.x1 F.n1) F.X1
  have c3 : Real.log (2 * P.Xpp) ≤ 4 * z := by
    rw [Real.log_mul (by norm_num) (by linarith)]; linarith [F.log_Xpp_le, log_two_le_one_alt, F.z1]
  have c4 : P.a * P.th ^ 2 ≤ P.b * P.x⁻¹ := F.ha ▸ le_trans (by gcongr : P.x * P.b * P.th ^ 2 ≤ P.x * P.b * P.x⁻¹ ^ 2)
    (le_of_eq_of_le (by ring : _ = P.b * P.x⁻¹ * (P.x * P.x⁻¹)) (by rw [F.xr, mul_one]))
  have c5 : P.wpp * P.th ≤ P.b * P.x⁻¹ := F.hwpp ▸ mul_le_mul ((div_le_self F.v0 F.n1).trans F.v_le_b) F.thx F.th0 F.b0
  have c6 : 0 ≤ P.a * P.th ^ 2 + P.wpp * P.th :=
    add_nonneg (by have := F.apos; positivity) (by rw [F.hwpp]; have := F.v0; have := F.npos; positivity)
  exact scale2 hm hT ((mul_le_mul (by linarith : 2 * Real.log (2 * P.Xpp) ≤ 2 * (4 * z))
    (add_le_add c4 c5) c6 (by positivity)).trans (le_of_eq_of_le (by ring) (F.bzr_sg 16 1 (by norm_num) (by norm_num))))

theorem size_discriminant_bound : SizeD := fun P e K m T hW hL hm hT => by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have := F.xpos; have := F.zpos; have := F.rpos; have := F.apos
  have hx2 : Real.exp 1 ≤ P.x ^ 2 := Real.exp_one_lt_d9.le.trans ((by norm_num : _ ≤ (100 : ℝ) ^ 2).trans (by have := F.hx; gcongr))
  have c1 : Real.log P.d / P.d ≤ 2 * z * P.x⁻¹ ^ 2 := by
    refine (Real.log_div_self_antitoneOn hx2 (hx2.trans F.dx) F.dx).trans ?_
    dsimp only; rw [Real.log_pow, div_eq_mul_inv, F.r2]; push_cast; have : Real.log P.x ≤ z := F.lxz; gcongr
  rw [tD, mul_div_assoc]; exact scale2 hm hT ((mul_le_mul_of_nonneg_left c1 (by positivity)).trans
    (le_of_eq_of_le (by ring) (F.azr_sg 4 1 (by norm_num) (by norm_num))))

lemma unitU_nonneg {P : Par} {m T : ℝ} (hm : 0 ≤ m) (hT : 1 ≤ T) : 0 ≤ unitU P m T :=
  mul_nonneg (mul_nonneg (by linarith) hm) (Real.exp_pos _).le

theorem side_condition_of_windows : SideConditionsOfWindows := fun P _ _ hW hL => by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have hx := F.hx; have := F.xpos; have := F.rpos; have := F.npos; have := F.x_le_sq; have := F.x2_le_p0
  have hw0 : 0 < P.wpp := F.hwpp ▸ div_pos ((pos_iff_pos_of_mul_pos (F.hvX ▸ F.bpos)).2 F.Xpos) F.npos
  have hw8 : 0 < w8 := by linarith [F.w81]
  have hbp0 : 0 ≤ P.bp := F.hbp ▸ mul_nonneg F.xpos.le F.v0
  refine ⟨hw0, F.th0, F.thx.trans ((inv_anti₀ (by norm_num) hx).trans (by norm_num)),
    ?_, ?_, F.ha ▸ one_le_mul_of_one_le_of_one_le F.x1 (F.sb1.trans F.sb_le_b),
    F.hXp ▸ F.X1, by exact_mod_cast (show (3 : ℝ) ≤ P.p₀ by linarith),
    by exact_mod_cast (show (4 : ℝ) ≤ P.d by linarith [F.dx]),
    F.C0, by unfold Par.f; linarith, by unfold Par.Sk; linarith [F.Sc0, F.η0, F.kx],
    by unfold Par.Q₁; have := F.C0; have := F.r0; have := F.lx0; positivity,
    by unfold Par.Q₂; rw [F.hδ, div_inv_eq_mul]
       have := F.C0; have := F.lx0; have := F.η0; have := F.Sc0; have := F.t0; have := F.bo0; positivity,
    F.lx0, F.La0, by linarith [F.kx], by linarith [F.x_sq_le_threshold], F.hXp ▸ F.hXpp⟩
  · rw [F.hXpp]; linarith [le_mul_of_one_le_right F.xpos.le (one_le_mul_of_one_le_of_one_le F.n1 F.X1),
      show P.x * (P.n * X) = P.x * P.n * X by ring]
  · rw [F.hXpp, F.hwpp, F.ha, ← F.hvX]; have := F.npos.ne'; field_simp

theorem large_x_eventually : LargeXEv := fun ε e K hε hε4 => by
  have hε3 : 0 < ε / 3 := by positivity
  have hC : ∀ᶠ x : ℝ in Filter.atTop, 100 * K * x ^ (4 * ε) ≤ x := by
    filter_upwards [(tendsto_rpow_atTop (show 0 < 1 - 4 * ε by linarith)).eventually_ge_atTop (100 * K),
      Filter.eventually_ge_atTop (1 : ℝ)] with x hx hx1
    have xpos : 0 < x := by linarith
    exact (mul_le_mul_of_nonneg_right hx (Real.rpow_nonneg xpos.le _)).trans_eq
      (by rw [← Real.rpow_add xpos, sub_add_cancel, Real.rpow_one])
  have hB : ∀ᶠ x : ℝ in Filter.atTop, 100 * K * x ^ (4 * e + 4) ≤ Real.exp (x ^ (ε / 3)) := by
    filter_upwards [((isLittleO_log_rpow_atTop hε3).const_mul_left (4 * e + 4)).bound (by norm_num : (0 : ℝ) < 1 / 2),
      (tendsto_rpow_atTop hε3).eventually_ge_atTop (2 * Real.log (100 * (|K| + 1))),
      Filter.eventually_ge_atTop (1 : ℝ)] with x hx hxA hx1
    have xpos : 0 < x := by linarith
    have h1 := (le_abs_self ((4 * e + 4) * Real.log x)).trans (Real.norm_eq_abs _ ▸ hx)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg xpos.le _), mul_comm] at h1
    refine (mul_le_mul_of_nonneg_right (by linarith [le_abs_self K] : 100 * K ≤ 100 * (|K| + 1)) (Real.rpow_nonneg xpos.le _)).trans ?_
    rw [← Real.exp_log (show 0 < 100 * (|K| + 1) by positivity), Real.rpow_def_of_pos xpos, ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    (((hC.and hB).and ((tendsto_rpow_atTop (show 0 < 2 * ε / 3 by positivity)).eventually_ge_atTop 6)).and (Filter.eventually_ge_atTop 1))
  refine ⟨x0, fun x hx => ?_⟩
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hx0 x hx
  have xpos : 0 < x := by linarith
  have hz6 : 6 * x ^ (ε / 3) ≤ x ^ ε := (mul_le_mul_of_nonneg_right c3 (Real.rpow_nonneg xpos.le _)).trans_eq
    (by rw [← Real.rpow_add xpos]; congr 1; ring)
  refine ⟨c4, c1, c2, (mul_le_mul_of_nonneg_right c2 (Real.exp_pos _).le).trans ?_⟩
  rw [← Real.exp_add]; exact Real.exp_le_exp.2 (by linarith [Real.rpow_le_rpow_of_exponent_le c4 (show ε / 4 ≤ ε / 3 by linarith)])

theorem second_term_le : SecondLe := fun Ps s cl Sg θ m T a hm hT ha hcl => by
  rw [← Finset.sum_filter, Finset.mul_sum]
  refine (Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun p _ _ => ?_).trans
    (Finset.sum_congr rfl fun _ _ => by ring).le
  · rw [Finset.mem_filter] at hp ⊢; exact hcl p hp.1 hp.2
  · have := div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p); positivity

theorem first_kind_bound : FirstKind := by
  obtain ⟨C, hC⟩ := first_kind_bucket_bound
  refine ⟨C, fun e J Y X' ρ p₀ s h1 h2 h3 h4 h5 h6 h7 h8 =>
    hC e J ⌊Real.log X'⌋₊ Y X' ρ p₀ (fun i => X' ^ ((1 : ℝ) / ((i + 1 : ℕ) : ℝ))) s h1 h2 h3 h4 h5
      (by linarith) (fun i _ => ?_) (fun p hp => ?_)⟩
  · have hx : (1 : ℝ) ≤ X' := by linarith
    refine ⟨Real.one_le_rpow hx (by positivity), (Real.rpow_le_rpow_of_exponent_le hx ?_).trans (Real.rpow_one X').le⟩
    rw [div_le_one (by positivity)]; push_cast; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  · obtain ⟨a1, a2, a3 | ⟨b1, i, b2, b3, b4⟩⟩ := h8 p hp
    · exact ⟨a1, a2, Or.inl a3⟩
    · have hi := Nat.le_floor (band_exponent_bound X' ρ p i h7 (by linarith) (by exact_mod_cast h6.trans b1) b4)
      obtain ⟨c1, c2⟩ := band_root_bound X' ρ p i (by linarith) h4 (by linarith) (Nat.cast_nonneg p) b2 b3 b4
      exact ⟨a1, a2, Or.inr ⟨i - 1, by omega, b1, by simpa [Nat.sub_add_cancel b2] using c1,
        by simpa [Nat.sub_add_cancel b2] using c2⟩⟩

lemma first_le {C₁ : ℝ}
    (hC₁ : ∀ (e J : ℕ) (Y X' ρ p₀ : ℝ) (s : Finset ℕ), 1 ≤ e → 1 ≤ J → 1 ≤ Y →
      0 ≤ ρ → ρ ≤ 1 / 2 → 8 ≤ p₀ → 2 ≤ X' →
      (∀ p ∈ s, p.Prime ∧ p ≠ 2 ∧
        (((p : ℝ) ≤ Y ∧ ∃ hl : Nat.Coprime p (4 * 2 ^ e), orderOf (Formalism.RankGapBounds.LocalQuadraticParts.hOf e p hl) ≤ J) ∨
          (p₀ ≤ p ∧ ∃ i : ℕ, 1 ≤ i ∧ X' * (1 - ρ) ≤ (p : ℝ) ^ i ∧ (p : ℝ) ^ i ≤ X' * (1 + ρ)))) →
      ∑ p ∈ s, Real.log p / p ≤
        C₁ * J * Real.log (2 ^ e * Y) ^ 2 / (2 : ℝ) ^ e +
          (⌊Real.log X'⌋₊ : ℝ) * ((4 * ρ + 1 / p₀) * Real.log (2 * X')))
    {P : Par} {e K : ℝ} (hCord : C₁ ≤ P.Cord) (hW : Windows P e K) (hL : LargeX P.x P.ε e K)
    (Ps : Finset ℕ) (cl : ℕ → PClass) (hPs : ∀ p ∈ Ps, p.Prime ∧ p ≠ 2) (hF : FirstHyp P Ps cl)
    (m T : ℝ) (hm : 0 ≤ m) (hT : 0 ≤ T) :
    4 * m * T * P.a * (∑ p ∈ Ps.filter (fun p => cl p = PClass.first), Real.log p / p) ≤
      tOrders P m T + tBand P m T := by
  obtain ⟨z, u, E, X, S, sb, v, w8, F⟩ := facts hW hL
  have he2 : 1 ≤ P.e₂ := Nat.one_le_iff_ne_zero.2 fun h0 => by
    have h1 := F.n2x; rw [h0, pow_zero] at h1; linarith [F.hx, F.x_le_sq]
  have h := hC₁ P.e₂ P.Jo (max P.Y P.Xpp) P.Xp P.ρ P.p₀ (Ps.filter fun p => cl p = PClass.first) he2
    (Nat.le_floor (by simpa using Real.one_le_rpow F.x1 (by have := hW.1; positivity)))
    (F.Y1.trans (le_max_left _ _)) F.ρ0
    (F.ρx.trans ((inv_anti₀ (by norm_num) (F.hx.trans F.x_le_sq)).trans (by norm_num)))
    (by linarith [F.x2_le_p0, F.x_le_sq, F.hx])
    (F.hXp ▸ by linarith [F.one_le_threshold_mul_powers, F.hXB]) fun p hp => by
      rw [Finset.mem_filter] at hp
      refine ⟨(hPs p hp.1).1, (hPs p hp.1).2, ?_⟩
      rcases hF p hp.1 hp.2 with ⟨a1, hl, a2⟩ | ⟨b1, b2⟩
      · exact Or.inl ⟨a1, hl, Nat.le_floor a2.le⟩
      · exact Or.inr ⟨by exact_mod_cast b1, b2⟩
  rw [show ⌊Real.log P.Xp⌋₊ = P.Ib by rw [F.hXp, F.logX, F.hu]; rfl] at h
  have hJ0 : (0 : ℝ) ≤ P.Jo := Nat.cast_nonneg _
  have h2 : C₁ * P.Jo * Real.log (2 ^ P.e₂ * max P.Y P.Xpp) ^ 2 / (2 : ℝ) ^ P.e₂ ≤
      P.Cord * P.Jo * Real.log (2 ^ P.e₂ * max P.Y P.Xpp) ^ 2 / (2 : ℝ) ^ P.e₂ := by gcongr
  have := F.apos; unfold tOrders tBand
  linarith [mul_le_mul_of_nonneg_left (h.trans (add_le_add_left h2 _)) (show 0 ≤ 4 * m * T * P.a by positivity)]

end Formalism.LFunctionChainParameters.PrimeWindowSizeBounds
