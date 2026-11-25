module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AevalNeZeroOfNotMem
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.GenericFibreKerTarget
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.IsFieldIntersection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.IsRatSectionOn

@[expose] public section

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem minorIJ_map {R S : Type} [CommRing R] [CommRing S] {N : ℕ} (f : R →+* S) (A : Matrix (Fin N) (Fin N) R)
    (I J : Finset (Fin N)) : minorIJ (A.map f) I J = f (minorIJ A I J) := by
  unfold minorIJ
  split_ifs with e
  · rw [RingHom.map_det]; rfl
  · exact (map_zero f).symm

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem regAt_neg {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} {s : Ω} (hs : RegAt x (mCoordIdeal z) s) :
    RegAt x (mCoordIdeal z) (-s) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  refine ⟨d, -g, h, fun m hm k => hg m (by rwa [support_neg] at hm) k, hh, hn, ?_⟩
  rw [map_neg, heq, neg_mul]

def regRing (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) : Subring Ω where
  carrier := {s | RegAt x (mCoordIdeal z) s}
  mul_mem' := ValRing.regAt_mul
  one_mem' := ValRing.regAt_one x z
  add_mem' := ValRing.regAt_add
  zero_mem' := ValRing.regAt_zero x z
  neg_mem' := regAt_neg

def regVal (x : (Σ k, ι k) → Ω) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) : regRing x z →+* ℂ where
  toFun s := valAt x s z
  map_one' := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.1
  map_zero' := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.1
  map_mul' s t := ((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t s.2 t.2).2.2.1
  map_add' s t := ((ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t s.2 t.2).2.2.2

def valMat {N : ℕ} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (A : Matrix (Fin N) (Fin N) Ω) :
    Matrix (Fin N) (Fin N) ℂ := Matrix.of fun a b => valAt x (A a b) z

variable {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ}

theorem reg_sum (hz : z ∈ mcPts (mCoordIdeal x)) {σ : Type} (s : Finset σ) (f : σ → Ω)
    (hf : ∀ i ∈ s, RegAt x (mCoordIdeal z) (f i)) :
    RegAt x (mCoordIdeal z) (∑ i ∈ s, f i) ∧ valAt x (∑ i ∈ s, f i) z = ∑ i ∈ s, valAt x (f i) z := by
  let S : regRing x z := ∑ i ∈ s.attach, ⟨f i.1, hf i.1 i.2⟩
  have hS : ∑ i ∈ s, f i = (S : Ω) := by simpa [S] using (Finset.sum_attach s f).symm
  rw [hS]
  refine ⟨S.2, ?_⟩
  change regVal x hz S = ∑ i ∈ s, valAt x (f i) z
  dsimp [S]
  rw [map_sum]
  exact Finset.sum_attach s fun i => valAt x (f i) z

theorem reg_mul (hz : z ∈ mcPts (mCoordIdeal x)) {s t : Ω} (hs : RegAt x (mCoordIdeal z) s)
    (ht : RegAt x (mCoordIdeal z) t) :
    RegAt x (mCoordIdeal z) (s * t) ∧ valAt x (s * t) z = valAt x s z * valAt x t z := by
  obtain ⟨hm, -, hv, -⟩ := (ValRing.regAt_valAt_ring K ι Ω x z hz).2.2.2.2 s t hs ht
  exact ⟨hm, hv⟩

theorem regMat_mul {N : ℕ} (hz : z ∈ mcPts (mCoordIdeal x)) {A B : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) (hB : ∀ a b, RegAt x (mCoordIdeal z) (B a b)) :
    (∀ a b, RegAt x (mCoordIdeal z) ((A * B) a b)) ∧ valMat x z (A * B) = valMat x z A * valMat x z B := by
  let A' : Matrix (Fin N) (Fin N) (regRing x z) := fun a b => ⟨A a b, hA a b⟩
  let B' : Matrix (Fin N) (Fin N) (regRing x z) := fun a b => ⟨B a b, hB a b⟩
  have hM : A * B = (A' * B').map (regRing x z).subtype := by
    ext a b
    rw [Matrix.mul_apply, Matrix.map_apply, Matrix.mul_apply, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; rfl
  refine ⟨fun a b => hM ▸ ((A' * B') a b).2, ?_⟩
  ext a b
  rw [valMat, Matrix.of_apply, hM]
  change regVal x hz ((A' * B') a b) = (valMat x z A * valMat x z B) a b
  rw [Matrix.mul_apply, map_sum, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; rfl

theorem reg_minor {N : ℕ} (hz : z ∈ mcPts (mCoordIdeal x)) {A : Matrix (Fin N) (Fin N) Ω}
    (hA : ∀ a b, RegAt x (mCoordIdeal z) (A a b)) (I J : Finset (Fin N)) :
    RegAt x (mCoordIdeal z) (minorIJ A I J) ∧ valAt x (minorIJ A I J) z = minorIJ (valMat x z A) I J := by
  let A' : Matrix (Fin N) (Fin N) (regRing x z) := fun a b => ⟨A a b, hA a b⟩
  have hmap : A'.map (regRing x z).subtype = A := by
    ext a b
    rfl
  have h1 : minorIJ A I J = ((minorIJ A' I J : regRing x z) : Ω) := by
    have h := minorIJ_map (regRing x z).subtype A' I J
    rw [hmap] at h
    exact h
  have h2 : valMat x z A = A'.map (regVal x hz) := by
    ext a b
    rfl
  refine ⟨?_, ?_⟩
  · rw [h1]
    exact (minorIJ A' I J).2
  · rw [h2, minorIJ_map, h1]
    rfl

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
