module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StPtsBilinear
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegrePartition
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StSegreChart

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar ptsIntegral pot segre)

theorem StokesStatement.of_found (hBil : PtsBilinear.Statement) (hPart : SegrePartition.Statement)
    (hChart : SegreChart.Statement) (hSV : StokesOnVariety.Statement) :
    ReciprocityTheory.ChartRestriction.G.Geo.StokesStatement := by
  classical
  intro K _ ι _ P n L B B' hP hL hB hB' hB0 hB'0
  have hw := isDegZeroSmooth_log hB hB0
  have hw' := isDegZeroSmooth_log hB' hB'0
  have hne : ∀ k, Nonempty (ι k) := fun k => by
    obtain ⟨i, -⟩ := hP.2.1.2.2 k
    exact ⟨i⟩
  obtain ⟨δ, hδ, ρ, hρs, hρ1, hρ0⟩ := hPart K ι hne
  have hpiece : ∀ i, IsDegZeroSmooth (fun z => ρ i z * Real.log (B.h z)) := fun i => (hρs i).mul hw
  have hsum : (fun z => Real.log (B.h z)) = fun z => ∑ i, ρ i z * Real.log (B.h z) := by
    funext z
    rw [← Finset.sum_mul, hρ1 z, one_mul]
  obtain ⟨hA, hC⟩ := hBil K ι P n L _ _ _ hP hL hpiece hw'
  rw [hsum]
  refine hA.trans (Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hC.symm)
  obtain ⟨m, Js, U, V, Φ, hJ, hU, h1, h2⟩ := hChart K ι P n L _ _ i δ hP hL (hpiece i) hw' hδ
    (fun z hz => by simp only [hρ0 i z hz, zero_mul])
  rw [h1, h2]
  refine Finset.sum_congr rfl fun J hJs => ?_
  obtain ⟨hJp, hJd, hUs, hVs, hΦs⟩ := hJ J hJs
  exact hSV m n J U V Φ hJp hJd hUs hVs hΦs (Or.inl hU)

end GroundTheory.Heights₂.Heights
