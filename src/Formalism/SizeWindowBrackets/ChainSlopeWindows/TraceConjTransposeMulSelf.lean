module

public import Formalism.SizeWindowBrackets.TraceSquareAndDiagBounds
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Analysis.CStarAlgebra.Basic
public import Mathlib.Basic.Complex.BigOperators

@[expose] public section
open Matrix
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section

section HS
variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k]
lemma hsSq_nonneg (M : Matrix m n ℂ) : 0 ≤ hsSq M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
lemma trace_conjTranspose_mul_self (M : Matrix m n ℂ) :
    (Mᴴ * M).trace = ((hsSq M : ℝ) : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    hsSq, Complex.ofReal_sum]
  rw [Finset.sum_comm]; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]; rfl
lemma hsSq_eq_re (M : Matrix m n ℂ) : hsSq M = (Mᴴ * M).trace.re := by
  rw [trace_conjTranspose_mul_self, Complex.ofReal_re]
lemma hsSq_conjTranspose (M : Matrix m n ℂ) : hsSq Mᴴ = hsSq M := by
  simp only [hsSq, Matrix.conjTranspose_apply, norm_star]; exact Finset.sum_comm
lemma hsSq_smul (c : ℂ) (M : Matrix m n ℂ) : hsSq (c • M) = ‖c‖ ^ 2 * hsSq M := by
  simp only [hsSq, Matrix.smul_apply, smul_eq_mul, norm_mul, mul_pow, Finset.mul_sum]
end HS

section CS
variable {m n : Type} [Fintype m] [Fintype n]
private theorem sum_norm_mul_le_hsNorm_mul (A B : Matrix m n ℂ) :
    ∑ i, ∑ j, ‖A i j‖ * ‖B i j‖ ≤ hsNorm A * hsNorm B := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (m × n))
    (fun p => ‖A p.1 p.2‖) (fun p => ‖B p.1 p.2‖)
  simp only [Fintype.sum_prod_type] at h
  rw [hsNorm, hsNorm, ← Real.sqrt_mul (hsSq_nonneg A)]; exact Real.le_sqrt_of_sq_le h

lemma norm_trace_mul_le (X : Matrix m n ℂ) (Y : Matrix n m ℂ) :
    ‖(X * Y).trace‖ ≤ hsNorm X * hsNorm Y := by
  rw [← show hsNorm Yᵀ = hsNorm Y by
    simp only [hsNorm, hsSq, Matrix.transpose_apply]; exact congrArg Real.sqrt Finset.sum_comm]
  refine le_trans ?_ (sum_norm_mul_le_hsNorm_mul X Yᵀ)
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ =>
    (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun _ _ => norm_mul _ _))

lemma hsSq_one (n : ℕ) : hsSq (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  simp [hsSq, Matrix.one_apply, apply_ite]
lemma hsNorm_nonneg (M : Matrix m n ℂ) : 0 ≤ hsNorm M := Real.sqrt_nonneg _
lemma hsNorm_sq (M : Matrix m n ℂ) : hsNorm M ^ 2 = hsSq M := Real.sq_sqrt (hsSq_nonneg M)
lemma hsSq_add_le (A B : Matrix m n ℂ) : hsSq (A + B) ≤ (hsNorm A + hsNorm B) ^ 2 := by
  calc hsSq (A + B)
      ≤ ∑ i, ∑ j, (‖A i j‖ + ‖B i j‖) ^ 2 := Finset.sum_le_sum fun i _ => Finset.sum_le_sum
        fun j _ => pow_le_pow_left₀ (norm_nonneg _) (norm_add_le (A i j) (B i j)) 2
    _ = hsSq A + hsSq B + 2 * ∑ i, ∑ j, ‖A i j‖ * ‖B i j‖ := by
        simp only [hsSq, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    _ ≤ (hsNorm A + hsNorm B) ^ 2 := by
        rw [add_sq, hsNorm_sq, hsNorm_sq]; linarith [sum_norm_mul_le_hsNorm_mul A B]
lemma hsNorm_le_of_sq (M : Matrix m n ℂ) {e x : ℝ} (he : 0 ≤ e) (h : hsSq M ≤ e * x) :
    hsNorm M ≤ Real.sqrt e * Real.sqrt x := by
  rw [hsNorm, ← Real.sqrt_mul he]; exact Real.sqrt_le_sqrt h
end CS

theorem traceLowerBound : TraceLower := fun n K => by
  have h2 := norm_trace_mul_le (1 : Matrix (Fin n) (Fin n) ℂ) (K - 1)
  have h4 := Complex.re_le_norm (-((1 : Matrix (Fin n) (Fin n) ℂ) * (K - 1)).trace)
  rw [hsNorm, hsSq_one, one_mul, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin] at h2
  rw [Complex.neg_re, norm_neg, one_mul, Matrix.trace_sub, Matrix.trace_one, Fintype.card_fin,
    Complex.sub_re, Complex.natCast_re] at h4; linarith
lemma hsSq_le_of_sub_one (n : ℕ) (K : Matrix (Fin n) (Fin n) ℂ) :
    hsSq K ≤ (Real.sqrt n + hsNorm (K - 1)) ^ 2 := by
  have h := hsSq_add_le (1 : Matrix (Fin n) (Fin n) ℂ) (K - 1)
  rwa [show (1 : Matrix (Fin n) (Fin n) ℂ) + (K - 1) = K by abel, hsNorm, hsSq_one] at h

section Fam
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}
lemma Kd_eq (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u) (u : ι) :
    Kd B ga u = ((ga u : ℝ) : ℂ) • ((B u)ᴴ * B u) := by
  let _ := ‹Fintype ι›; unfold Kd Kp; rw [Real.sqrt_mul_self (hga u)]
lemma trace_Qm (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u) :
    (Qm B ga).trace = ∑ u, (Kd B ga u).trace := by
  unfold Qm; rw [Matrix.trace_sum]; refine Finset.sum_congr rfl fun u _ => ?_
  rw [Kd_eq B ga hga u, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_mul_comm]
lemma hsSq_Kp (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    (u u' : ι) : hsSq (Kp B ga u u') = ga u * ga u' * hsSq ((B u)ᴴ * B u') := by
  let _ := ‹Fintype ι›
  rw [Kp, hsSq_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt (mul_nonneg (hga u) (hga u'))]
lemma trace_Qm_sq (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u) :
    (Qm B ga * Qm B ga).trace = (((∑ u, ∑ u', hsSq (Kp B ga u u') : ℝ)) : ℂ) := by
  unfold Qm; simp only [Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
  rw [Matrix.trace_mul_comm]
  simp only [hsSq_Kp B ga hga u u', Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul,
    smul_eq_mul, ← trace_conjTranspose_mul_self, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Complex.ofReal_mul]
  rw [Matrix.mul_assoc (B u), Matrix.trace_mul_comm (B u), Matrix.trace_mul_comm ((B u')ᴴ * B u)]
  simp only [Matrix.mul_assoc]; ring

lemma Rs_nonneg (d : ι → ℕ) : 0 ≤ Rs d := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
lemma trQ_lower (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    {e0 : ℝ} (he : 0 ≤ e0) (hK : ∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) :
    (1 - Real.sqrt e0) * Rs d ≤ (Qm B ga).trace.re := by
  rw [trace_Qm B ga hga, Complex.re_sum, Rs, Finset.mul_sum]; refine Finset.sum_le_sum fun u _ => ?_
  have h2 := mul_le_mul_of_nonneg_left (hsNorm_le_of_sq _ he (hK u)) (Real.sqrt_nonneg (d u : ℝ))
  rw [show Real.sqrt (d u : ℝ) * (Real.sqrt e0 * Real.sqrt (d u : ℝ)) =
      Real.sqrt e0 * (Real.sqrt (d u : ℝ) * Real.sqrt (d u : ℝ)) by ring,
    Real.mul_self_sqrt (Nat.cast_nonneg _)] at h2
  linarith [traceLowerBound (d u) (Kd B ga u)]

lemma trQsq_upper (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    {Dstar η0 e0 : ℝ} (hD : 0 < Dstar) (hη : -1 ≤ η0) (he : 0 ≤ e0)
    (hP : ∀ u u', u ≠ u' → hsSq (Kp B ga u u') ≤ (1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar)
    (hK : ∀ u, hsSq (Kd B ga u - 1) ≤ e0 * (d u : ℝ)) :
    (Qm B ga * Qm B ga).trace.re ≤ (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * Rs d := by
  classical
  have hη' : 0 ≤ 1 + η0 := by linarith
  have hdiag (u : ι) : hsSq (Kp B ga u u) ≤ (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) := by
    rw [← Real.sq_sqrt (Nat.cast_nonneg (d u)), ← mul_pow]
    exact (hsSq_le_of_sub_one (d u) (Kd B ga u)).trans (pow_le_pow_left₀
      (add_nonneg (Real.sqrt_nonneg _) (hsNorm_nonneg _))
      (by linarith [hsNorm_le_of_sq _ he (hK u)]) 2)
  rw [trace_Qm_sq B ga hga, Complex.ofReal_re]
  calc ∑ u, ∑ u', hsSq (Kp B ga u u')
      ≤ ∑ u, ∑ u', ((1 + η0) * (d u : ℝ) * (d u' : ℝ) / Dstar +
          if u = u' then (1 + Real.sqrt e0) ^ 2 * (d u : ℝ) else 0) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => by
          by_cases h : u = u'
          · subst h; rw [ite_eq_left rfl]; linarith [hdiag u,
              show 0 ≤ (1 + η0) * (d u : ℝ) * (d u : ℝ) / Dstar by positivity]
          · rw [ite_eq_right h, add_zero]; exact hP u u' h
    _ = (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * Rs d := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
        rw [← Finset.mul_sum, ← Rs]; congr 1; simp only [Rs, sq, Finset.sum_mul, Finset.mul_sum,
          Finset.sum_div]; exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
end Fam

section Compress
variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq k]
lemma proj_herm (V : Matrix m k ℂ) : (1 - V * Vᴴ)ᴴ = 1 - V * Vᴴ := by
  let _ := (‹Fintype m›, ‹DecidableEq k›)
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
lemma proj_idem (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
  have hP : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
  simp only [sub_mul, mul_sub, one_mul, mul_one, hP]; abel
lemma hsSq_split (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) (M : Matrix m n ℂ) :
    hsSq M = hsSq (Vᴴ * M) + hsSq ((1 - V * Vᴴ) * M) := by
  rw [hsSq_eq_re M, hsSq_eq_re (Vᴴ * M), hsSq_eq_re ((1 - V * Vᴴ) * M), ← Complex.add_re,
    ← Matrix.trace_add]; congr 2
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_mul,
    proj_herm V, show Mᴴ * (1 - V * Vᴴ) * ((1 - V * Vᴴ) * M) =
      Mᴴ * ((1 - V * Vᴴ) * (1 - V * Vᴴ)) * M by simp only [Matrix.mul_assoc], proj_idem V hV]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]; abel
lemma hsSq_left_le (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) (M : Matrix m n ℂ) :
    hsSq (Vᴴ * M) ≤ hsSq M := by linarith [hsSq_split V hV M, hsSq_nonneg ((1 - V * Vᴴ) * M)]
end Compress

lemma hsSq_compress {a b c e : ℕ} (V : Matrix (Fin a) (Fin c) ℂ) (hV : Vᴴ * V = 1)
    (W : Matrix (Fin b) (Fin e) ℂ) (hW : Wᴴ * W = 1) (M : Matrix (Fin a) (Fin b) ℂ) :
    hsSq (Vᴴ * M * W) ≤ hsSq M := by
  have h1 := hsSq_left_le W hW (Vᴴ * M)ᴴ
  rw [← Matrix.conjTranspose_mul, hsSq_conjTranspose, hsSq_conjTranspose] at h1
  exact h1.trans (hsSq_left_le V hV M)
lemma trace_proj (n k : ℕ) (V : Matrix (Fin n) (Fin k) ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ).trace = ((((n : ℝ) - (k : ℝ)) : ℝ) : ℂ) := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, hV, Matrix.trace_one, Matrix.trace_one,
    Fintype.card_fin, Fintype.card_fin]; push_cast; ring

lemma ram_gap (n k : ℕ) (K : Matrix (Fin n) (Fin n) ℂ) (V : Matrix (Fin n) (Fin k) ℂ)
    (hV : Vᴴ * V = 1) {e0 : ℝ} (he : 0 ≤ e0) (hK : hsSq (K - 1) ≤ e0 * n) :
    0 ≤ (n : ℝ) - k ∧ K.trace.re - (Vᴴ * K * V).trace.re ≤
      ((n : ℝ) - k) + Real.sqrt ((n : ℝ) - k) * (Real.sqrt e0 * Real.sqrt n) := by
  have hnk : hsSq (1 - V * Vᴴ) = (n : ℝ) - k := Complex.ofReal_injective <| by
    have h := trace_conjTranspose_mul_self (1 - V * Vᴴ)
    rwa [proj_herm V, proj_idem V hV, trace_proj n k V hV, eq_comm] at h
  refine ⟨hnk ▸ hsSq_nonneg _, ?_⟩
  have hre := congrArg Complex.re (show K.trace - (Vᴴ * K * V).trace =
      (1 - V * Vᴴ).trace + ((K - 1) * (1 - V * Vᴴ)).trace by
    rw [Matrix.trace_mul_comm (Vᴴ * K) V, ← Matrix.mul_assoc, Matrix.trace_mul_comm (V * Vᴴ) K]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub]
    ring)
  have hcs := norm_trace_mul_le (K - 1) (1 - V * Vᴴ)
  rw [show hsNorm (1 - V * Vᴴ) = Real.sqrt ((n : ℝ) - k) by rw [hsNorm, hnk]] at hcs
  rw [Complex.sub_re, Complex.add_re, trace_proj n k V hV, Complex.ofReal_re] at hre
  linarith [Complex.re_le_norm (((K - 1) * (1 - V * Vᴴ)).trace), hcs,
    mul_le_mul_of_nonneg_right (hsNorm_le_of_sq _ he hK) (Real.sqrt_nonneg ((n : ℝ) - k))]

lemma num_main {s η0 η1 a : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 4) (hη0 : -1 ≤ η0) (hη0' : η0 ≤ s / 2)
    (hη1' : η1 ≤ s / 2) (_hL : 0 ≤ 1 + η1) (ha : 0 ≤ a) (ha' : a ≤ s / 2) :
    (1 + η1) * ((1 + η0) + (1 + a) ^ 2 * s) ≤ (1 + 5 * s) * (1 - a) ^ 2 := by
  have hs' : 0 ≤ 1 / 4 - s := by linarith
  calc (1 + η1) * ((1 + η0) + (1 + a) ^ 2 * s)
      ≤ (1 + s / 2) * ((1 + s / 2) + (1 + s / 2) ^ 2 * s) :=
        (mul_le_mul_of_nonneg_right (by linarith) (add_nonneg (by linarith)
          (mul_nonneg (sq_nonneg _) hs0.le))).trans (mul_le_mul_of_nonneg_left (add_le_add
            (by linarith) (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by linarith)
              (by linarith) 2) hs0.le)) (by linarith))
    _ ≤ (1 + 5 * s) * (1 - s / 2) ^ 2 := by
        rw [← sub_nonneg, show (1 + 5 * s) * (1 - s / 2) ^ 2 - (1 + s / 2) *
          ((1 + s / 2) + (1 + s / 2) ^ 2 * s) = s / 8 * (3 + 52 * (1 / 4 - s) +
          15 / 4 * s ^ 2 + (1 / 4 - s) * s ^ 2) by ring]; positivity
    _ ≤ (1 + 5 * s) * (1 - a) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith) 2) (by linarith)

lemma num_ram {s a t : ℝ} (hs0 : 0 < s) (hs : s ≤ 1 / 20) (ha : 0 ≤ a) (ha' : a ≤ s / 2)
    (ht : 0 ≤ t) (ht' : t ≤ 1 / 2) :
    (1 + 5 * s) * (1 - a) ^ 2 ≤ (1 + 5 * s + 3 * t) * (1 - a - t ^ 2 - t * a) ^ 2 := by
  have hb0 : 0 ≤ 1 - a := by linarith
  have hP0 : 0 ≤ 1 + 5 * s + 3 * t := by linarith
  have hk : 0 ≤ 3 * (1 - a) - 2 * (1 + 5 * s + 3 * t) * (t + a) := by
    linarith [mul_le_mul_of_nonneg_right
      (by linarith : 2 * (1 + 5 * s + 3 * t) ≤ 11 / 2) (by linarith : 0 ≤ t + a)]
  rw [← sub_nonneg, show (1 + 5 * s + 3 * t) * (1 - a - t ^ 2 - t * a) ^ 2 -
    (1 + 5 * s) * (1 - a) ^ 2 = t * (1 - a) * (3 * (1 - a) - 2 * (1 + 5 * s + 3 * t) * (t + a)) +
    (1 + 5 * s + 3 * t) * (t ^ 2 + t * a) ^ 2 by ring]; positivity

lemma num_step {T2 T1 R Dst D X L c b : ℝ} (hD : 0 < D) (hDs : 0 < Dst) (hDD : D ≤ L * Dst)
    (hX : 0 ≤ X) (hT2 : T2 ≤ R ^ 2 / Dst * X) (hb : 0 ≤ b * R) (hT1 : b * R ≤ T1)
    (hc : L * X ≤ c * b ^ 2) (hc0 : 0 ≤ c) : T2 ≤ c * T1 ^ 2 / D := by
  rw [le_div_iff₀ hD]; refine le_of_mul_le_mul_right ?_ hDs
  rw [div_mul_eq_mul_div, le_div_iff₀ hDs] at hT2
  linarith [mul_le_mul_of_nonneg_right hT2 hD.le,
    mul_le_mul_of_nonneg_left hDD (mul_nonneg (sq_nonneg R) hX),
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc (sq_nonneg R)) hDs.le,
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb hT1 2) hc0) hDs.le,
    show T2 * D * Dst = T2 * Dst * D by ring, show R ^ 2 * X * (L * Dst) = R ^ 2 * (L * X) * Dst by ring,
    show R ^ 2 * (c * b ^ 2) * Dst = c * (b * R) ^ 2 * Dst by ring]

section Ram
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
lemma Kp_ram (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (u u' : ι) : Kp (Bram B V) ga u u' = (V u)ᴴ * Kp B ga u u' * V u' := by
  let _ := ‹Fintype ι›
  simp only [Kp, Bram, Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
lemma Kd_ram_sub (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (hV : Isom V) (u : ι) :
    Kd (Bram B V) ga u - 1 = (V u)ᴴ * (Kd B ga u - 1) * V u := by
  rw [Kd, Kp_ram, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV u, Kd]

theorem compressTraceLowerBound : RamTrace :=
  fun ι _ D d r B V ga de e0 hV hga hde he hK hsum => by
  have hu (u : ι) := ram_gap (d u) (r u) (Kd B ga u) (V u) (hV u) he (hK u)
  have hCS : ∑ u, Real.sqrt ((d u : ℝ) - r u) * Real.sqrt (d u) ≤ Real.sqrt de * Rs d := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun u => Real.sqrt ((d u : ℝ) - r u)) (fun u => Real.sqrt (d u))
    simp only [fun u => Real.sq_sqrt (hu u).1, fun u => Real.sq_sqrt (Nat.cast_nonneg (d u))] at h
    exact (Real.le_sqrt_of_sq_le h).trans <|
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hsum (Rs_nonneg d))).trans_eq <| by
        rw [mul_assoc, Real.sqrt_mul hde, Real.sqrt_mul_self (Rs_nonneg d)]
  have hsumu := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) =>
    (show Kd (Bram B V) ga u = _ from Kp_ram B V ga u u) ▸ (hu u).2
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    show ∑ u, Real.sqrt ((d u : ℝ) - r u) * (Real.sqrt e0 * Real.sqrt (d u)) =
      Real.sqrt e0 * ∑ u, Real.sqrt ((d u : ℝ) - r u) * Real.sqrt (d u) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring] at hsumu
  rw [trace_Qm B ga hga, trace_Qm (Bram B V) ga hga, Complex.re_sum, Complex.re_sum,
    Real.sqrt_mul hde e0]; linarith [mul_le_mul_of_nonneg_left hCS (Real.sqrt_nonneg e0)]

theorem compressDiagDefectBound : CompressDiagDefectBound :=
  fun ι _ D d r B V ga de e0 hV hde he hK hsum => by
  have h1 : (1 - de) * Rs d ≤ Rs r := by
    unfold Rs at hsum ⊢; rw [Finset.sum_sub_distrib] at hsum; linarith
  have h2 : Rs d ≤ 2 * Rs r := by
    linarith [mul_le_mul_of_nonneg_right (by linarith : (1 / 2 : ℝ) ≤ 1 - de) (Rs_nonneg d)]
  refine ⟨h1, ?_⟩; unfold F2
  calc ∑ u, hsSq (Kd (Bram B V) ga u - 1)
      ≤ ∑ u, e0 * (d u : ℝ) := Finset.sum_le_sum fun u _ => by
        rw [Kd_ram_sub B V ga hV u]; exact (hsSq_compress (V u) (hV u) (V u) (hV u) _).trans (hK u)
    _ = e0 * Rs d := by rw [Rs, Finset.mul_sum]
    _ ≤ 2 * e0 * Rs r := by linarith [mul_le_mul_of_nonneg_left h2 he]

lemma cor_common (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u)
    {Dstar sg η0 η1 e0 : ℝ} (hD : 0 < Dstar) (hs0 : 0 < sg) (hs : sg ≤ 1 / 4) (hR : Dstar / sg ≤ Rs d)
    (hη0 : -1 ≤ η0) (he : 0 ≤ e0) (ha' : Real.sqrt e0 ≤ sg / 2) (hS : InputS B ga Dstar η0 η1 e0) :
    0 < (D : ℝ) ∧ 0 ≤ 1 + η1 ∧ 0 < Rs d ∧ (Qm B ga * Qm B ga).trace.re ≤
      Rs d ^ 2 / Dstar * ((1 + η0) + (1 + Real.sqrt e0) ^ 2 * sg) ∧
      (1 - Real.sqrt e0) * Rs d ≤ (Qm B ga).trace.re := by
  obtain ⟨hP, hK, hDD⟩ := hS
  have hT : 0 < Rs d := lt_of_lt_of_le (div_pos hD hs0) hR; have hF1 := trQ_lower B ga hga he hK
  have hDpos : 0 < (D : ℝ) := by
    rcases Nat.eq_zero_or_pos D with rfl | h0
    · simp only [Matrix.trace_fin_zero, Complex.zero_re] at hF1
      linarith [mul_pos (by linarith : 0 < 1 - Real.sqrt e0) hT]
    · exact_mod_cast h0
  have hTT : Rs d ≤ Rs d ^ 2 / Dstar * sg := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hD]
    exact (mul_le_mul_of_nonneg_left ((div_le_iff₀ hs0).1 hR) hT.le).trans_eq (by ring)
  refine ⟨hDpos, (mul_nonneg_iff_of_pos_right hD).mp (hDpos.le.trans hDD), hT, ?_, hF1⟩
  calc (Qm B ga * Qm B ga).trace.re
      ≤ (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * Rs d :=
        trQsq_upper B ga hga hD hη0 he hP hK
    _ ≤ (1 + η0) * Rs d ^ 2 / Dstar + (1 + Real.sqrt e0) ^ 2 * (Rs d ^ 2 / Dstar * sg) := by gcongr
    _ = Rs d ^ 2 / Dstar * ((1 + η0) + (1 + Real.sqrt e0) ^ 2 * sg) := by ring

theorem compressTraceSquareBound : CompressTraceSquareBound :=
  fun ι _ D d r B V ga Dstar sg η0 η1 e0 de hV hga hD hs0 hs hR hη0 hη0' hη1' he ha' hde0 hde hsum hS => by
  obtain ⟨hDpos, hL, hT, hF2, _⟩ := cor_common B ga hga hD hs0 (by linarith) hR hη0 he ha' hS
  obtain ⟨_, hK, hDD⟩ := hS
  have hlow := compressTraceLowerBound ι D d r B V ga de e0 hV hga hde0 he hK hsum
  have hT2c : (Qm (Bram B V) ga * Qm (Bram B V) ga).trace.re ≤ (Qm B ga * Qm B ga).trace.re := by
    rw [trace_Qm_sq (Bram B V) ga hga, trace_Qm_sq B ga hga, Complex.ofReal_re, Complex.ofReal_re]
    exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun u' _ => by
      rw [Kp_ram]; exact hsSq_compress (V u) (hV u) (V u') (hV u') _
  have ht0 := Real.sqrt_nonneg de; have ha0 := Real.sqrt_nonneg e0
  have ht1 : Real.sqrt de ≤ 1 / 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by linarith⟩
  have hT1' : (1 - Real.sqrt e0 - Real.sqrt de ^ 2 - Real.sqrt de * Real.sqrt e0) * Rs d ≤
      (Qm (Bram B V) ga).trace.re := by
    rw [Real.sqrt_mul hde0 e0] at hlow; rw [Real.sq_sqrt hde0]; linarith
  exact num_step hDpos hD hDD (add_nonneg (by linarith) (mul_nonneg (sq_nonneg _) hs0.le))
    (hT2c.trans hF2)
    (mul_nonneg (by rw [Real.sq_sqrt hde0]; linarith [mul_le_mul_of_nonneg_right ht1 ha0]) hT.le)
    hT1' (by linarith [num_main hs0 (by linarith) hη0 hη0' hη1' hL ha0 ha',
      num_ram hs0 hs ha0 ha' ht0 ht1]) (by linarith)
end Ram

end
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
