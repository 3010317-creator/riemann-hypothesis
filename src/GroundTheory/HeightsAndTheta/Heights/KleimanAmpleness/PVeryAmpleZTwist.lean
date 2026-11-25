module

public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZTwistSt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.VeryAmpleZFamilySt
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleTwistLocal
public import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.TwistAlg
import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace VeryAmpleZTwist

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E]

theorem chart_smul_eq {I : Chart x} (c : chartRing S x I) (z : E) : c • z = (c : Ω) • z := rfl

theorem smul_mem_twist_twist (G : SubSystem S x E) (P Q : SubSystem S x Ω) (I : Chart x) {q : Ω}
    (hq : q ∈ P.sub I) {z : E} (hz : z ∈ (G.twist Q).sub I) : q • z ∈ ((G.twist P).twist Q).sub I := by
  change z ∈ Submodule.span (chartRing S x I)
    {z | ∃ q' ∈ Q.sub I, ∃ y ∈ G.sub I, z = q' • y} at hz
  refine (Submodule.span_le (p := (((G.twist P).twist Q).sub I).comap
    (DistribSMul.toLinearMap (chartRing S x I) E q))).2 ?_ hz
  rintro _ ⟨q', hq', y, hy, rfl⟩
  change q • (q' • y) ∈ ((G.twist P).twist Q).sub I
  refine Submodule.subset_span ⟨q', hq', q • y, Submodule.subset_span ⟨q, hq, y, hy, rfl⟩, ?_⟩
  rw [smul_smul, smul_smul, mul_comm]

theorem smul_mem_twist_pow (G : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {c d : ℕ} {w : Ω}
    (hw : w ∈ (H.pow c).sub I) {z : E} (hz : z ∈ (G.twist (H.pow d)).sub I) :
    w • z ∈ (G.twist (H.pow (d + c))).sub I := by
  change z ∈ Submodule.span (chartRing S x I)
    {z | ∃ q ∈ (H.pow d).sub I, ∃ y ∈ G.sub I, z = q • y} at hz
  refine (Submodule.span_le (p := ((G.twist (H.pow (d + c))).sub I).comap
    (DistribSMul.toLinearMap (chartRing S x I) E w))).2 ?_ hz
  rintro _ ⟨q, hq, y, hy, rfl⟩
  change w • (q • y) ∈ (G.twist (H.pow (d + c))).sub I
  refine Submodule.subset_span ⟨q * w, AmpleTwistLocal.mul_mem_pow H I hq c hw, y, hy, ?_⟩
  rw [smul_smul, mul_comm]

theorem mem_twist_pow_add (G : SubSystem S x E) (H : SubSystem S x Ω) (I : Chart x) {a b : ℕ} {z : E}
    (hz : z ∈ ((G.twist (H.pow a)).twist (H.pow b)).sub I) : z ∈ (G.twist (H.pow (a + b))).sub I := by
  change z ∈ Submodule.span (chartRing S x I)
    {z | ∃ q ∈ (H.pow b).sub I, ∃ y ∈ (G.twist (H.pow a)).sub I, z = q • y} at hz
  refine (Submodule.span_le (p := (G.twist (H.pow (a + b))).sub I)).2 ?_ hz
  rintro _ ⟨q, hq, y, hy, rfl⟩
  exact smul_mem_twist_pow G H I hq hy

theorem prod_mem_pow (H : SubSystem S x Ω) (I : Chart x) {r : ℕ} {h : Fin (r + 1) → Ω}
    (hh : ∀ l, h l ∈ H.sub I) (T : Finset (Fin (r + 1))) : ∏ l ∈ T, h l ∈ (H.pow T.card).sub I := by
  classical
  induction T using Finset.induction_on with
  | empty => exact one_mem_twistMod_zero I
  | insert l T hl ih =>
    rw [Finset.prod_insert hl, Finset.card_insert_of_notMem hl]
    exact Submodule.subset_span ⟨h l, hh l, _, ih, rfl⟩

theorem proof (hFam : VeryAmpleZFamily.Statement.{u, v, w}) : VeryAmpleZTwist.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F H r h hH a J
  obtain ⟨F', hF'⟩ := hFam S Ω N x E F H r h hH
  obtain ⟨j, hj⟩ := J.2.1
  have hj0 : h j ≠ 0 := (mem_support h).mp (J.2.2 hj)
  have hmem : ∀ l I, h l ∈ H.sub I := fun l I => (Submodule.mem_iInf _).mp (hH.mem_secs l) I
  have hpow : ∀ I, h j ^ a ∈ (H.pow a).sub I := fun I => by
    have h1 : h j ∈ (H.pow 1).sub I := by rw [SubSystem.pow_sub, pow_one]; exact hmem j I
    simpa using AmpleTwistLocal.pow_mem_pow H.toSubSystem I h1 a

  have fwd : ∀ y ∈ secsOnZ F.toSubSystem H.toSubSystem h J,
      h j ^ a • y ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J := by
    intro y hy
    refine (Submodule.mem_iInf _).mpr fun I => ?_
    have hyI : y ∈ secsOnZChart F.toSubSystem H.toSubSystem h I J := (Submodule.mem_iInf _).mp hy I
    refine (Submodule.span_le (p :=
      (secsOnZChart (F.twist (H.pow a)) H.toSubSystem h I J).comap
        (DistribSMul.toLinearMap S E (h j ^ a)))).2 ?_ hyI
    rintro y ⟨n, hn⟩
    change h j ^ a • y ∈ secsOnZChart (F.twist (H.pow a)) H.toSubSystem h I J
    refine Submodule.subset_span ⟨n, ?_⟩
    rw [smul_smul, mul_comm (xProd J ^ n), ← smul_smul]
    exact smul_mem_twist_twist _ _ _ I (hpow I) hn

  have bwd : ∀ e ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J,
      (h j ^ a)⁻¹ • e ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
    classical
    intro e he
    refine (Submodule.mem_iInf _).mpr fun I => ?_
    have heI : e ∈ secsOnZChart (F.twist (H.pow a)) H.toSubSystem h I J := (Submodule.mem_iInf _).mp he I
    set u := ∏ l ∈ J.1.erase j, h l with hu
    have hxu : xProd J = h j * u := (Finset.mul_prod_erase J.1 h hj).symm
    have hk : J.1.card = (J.1.erase j).card + 1 := by
      rw [Finset.card_erase_of_mem hj]
      have := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    have hua : u ^ a ∈ (H.pow ((J.1.erase j).card * a)).sub I :=
      AmpleTwistLocal.pow_mem_pow H.toSubSystem I (prod_mem_pow H.toSubSystem I (fun l => hmem l I) _) a
    refine (Submodule.span_le (p :=
      (secsOnZChart F.toSubSystem H.toSubSystem h I J).comap
        (DistribSMul.toLinearMap S E (h j ^ a)⁻¹))).2 ?_ heI
    rintro e ⟨n, hn⟩
    change (h j ^ a)⁻¹ • e ∈ secsOnZChart F.toSubSystem H.toSubSystem h I J
    refine Submodule.subset_span ⟨n + a, ?_⟩
    have heq : xProd J ^ (n + a) • (h j ^ a)⁻¹ • e = u ^ a • (xProd J ^ n • e) := by
      rw [smul_smul, smul_smul, hxu]
      congr 1
      field_simp
      ring
    have hdeg : a + J.1.card * n + (J.1.erase j).card * a = J.1.card * (n + a) := by
      rw [hk]; ring
    rw [heq, ← hdeg]
    exact smul_mem_twist_pow _ _ I hua (mem_twist_pow_add _ _ I hn)
  have hq : h j ^ a ∈ twistMod S h (a : ℤ) J := by
    rw [twistMod_eq_span (a : ℤ) J hj, zpow_natCast]
    exact Submodule.mem_span_singleton_self _
  apply le_antisymm
  · intro z hz
    rw [Submodule.restrictScalars_mem] at hz
    suffices H1 : ∀ c : chartRing S h J, c • z ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J by
      simpa using H1 1
    refine Submodule.span_induction (p := fun z _ => ∀ c : chartRing S h J,
      c • z ∈ secsOnZ (F.twist (H.pow a)) H.toSubSystem h J) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨q, hq, y, hy, rfl⟩ c
      rw [twistMod_eq_span (a : ℤ) J hj, Submodule.mem_span_singleton] at hq
      obtain ⟨d, rfl⟩ := hq
      have hy' : y ∈ F'.sub J := by
        have : y ∈ (F'.sub J).restrictScalars S := by rw [hF' J]; exact hy
        exact this
      have hcd : (c * d) • y ∈ secsOnZ F.toSubSystem H.toSubSystem h J := by
        rw [← hF' J]; exact Submodule.smul_mem _ (c * d) hy'
      have heq : c • ((d • h j ^ (a : ℤ)) • y) = h j ^ a • ((c * d) • y) := by
        rw [chart_smul_eq, chart_smul_eq, smul_eq_mul, zpow_natCast, smul_smul, chart_smul_eq (c * d),
          smul_smul]
        congr 1
        push_cast
        ring
      rw [heq]
      exact fwd _ hcd
    · intro c; rw [smul_zero]; exact Submodule.zero_mem _
    · intro b e _ _ hb he c; rw [smul_add]; exact Submodule.add_mem _ (hb c) (he c)
    · intro c' e _ he c; rw [smul_smul]; exact he (c * c')
  · intro e he
    have heq : e = h j ^ a • ((h j ^ a)⁻¹ • e) := by
      rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hj0), one_smul]
    rw [Submodule.restrictScalars_mem, heq]
    exact Submodule.subset_span ⟨h j ^ a, by exact_mod_cast hq, _, bwd e he, rfl⟩

end VeryAmpleZTwist

end

end GroundTheory.Heights₂.Heights.Kleiman
