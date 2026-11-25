module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty

@[expose] public section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
noncomputable section
namespace GlobalTheory.CompanionTheory.GrForm

variable {O : Type} [CommRing O] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}

theorem lift_cocycle_mem {W : X.Opens} {d : ℕ} {t : Fin d → Γ(X, W)} {u : Fin d → ∀ T : Thick (LL q), T.B}
    (hu : IsLift W t u) {Q : ObjectProperty (Thick (LL q))} (hQ : ∀ T, Q T → InU W T) (i : Fin d)
    {T T' : Q.FullSubcategory} (φ : T ⟶ T') :
    (show (sP Q).A.obj T' from u i T'.obj) - ((sP Q).A.map φ).hom (show (sP Q).A.obj T from u i T.obj) ∈ (sP Q).J.S T' := by
  have h := hQ _ T.property
  have h' := hQ _ T'.property
  change u i T'.obj - φ.hom.φ (u i T.obj) ∈ T'.obj.J
  refine Ideal.Quotient.eq.1 ?_
  rw [hu i T'.obj h', ev_nat φ.hom h h' (t i), ← hu i T.obj h]
  rfl

theorem lft_res_sub_mem {W W' : X.Opens} (hW : W' ≤ W) (T : Thick (LL q)) (h : InU W T) (h' : InU W' T) (f : Γ(X, W)) :
    lft W T f - lft W' T (rs hW f) ∈ T.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [lft_spec T h f, lft_spec T h' (rs hW f), ev_res hW T h h' f]

theorem stRes : StRes := by
  intro O _ X q W W' hW d t u hu P P' hPP hP hP' r x c hc
  obtain ⟨f, hf, rfl, hz⟩ := hc
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil P'
  have hP'W : ∀ T, P' T → InU W T := fun T h => hP T (hPP T h)
  refine ⟨(resU (GF q r) hPP).pullC r f, ?_, rfl, ?_⟩
  · let f' : CH.Cn (P.ι ⋙ GF q r) r := f
    have hf' : CH.d (P.ι ⋙ GF q r) r f' = 0 := hf
    change CH.d (P'.ι ⋙ GF q r) r ((resU (GF q r) hPP).pullC r f') = 0
    rw [(resU (GF q r) hPP).d_pullC, hf', map_zero]
  · intro s
    refine (hz (s ⋙ ObjectProperty.ιOfLE hPP)).trans ?_
    refine Ideal.Quotient.eq.2 ?_
    have hdiff : ∀ I : Idx r d,
        wz (Φ := sP P') (fun i T => u i T.obj) I.1 s *
          ((show (sP P').A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) -
            (show (sP P').A.obj (s.obj (Fin.last r)) from lft W' (s.obj (Fin.last r)).obj (rs hW (x I)))) ∈
          (sFil P' ((r : ℤ) + 1)).S (s.obj (Fin.last r)) := by
      intro I
      have hw := wz_mem hF (fun i T => u i T.obj)
        (fun i {T T'} φ => lift_cocycle_mem hu hP'W i φ) I.1 s
      have hδ : (show (sP P').A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) -
          (show (sP P').A.obj (s.obj (Fin.last r)) from lft W' (s.obj (Fin.last r)).obj (rs hW (x I))) ∈
          (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) := by
        have e : (sFil P' ((1 : ℕ) : ℤ)).S (s.obj (Fin.last r)) = (sP P').J.S (s.obj (Fin.last r)) := hF.one _
        rw [e]
        exact lft_res_sub_mem hW _ (hP'W _ (s.obj (Fin.last r)).property) (hP' _ (s.obj (Fin.last r)).property) (x I)
      have := hF.mul r 1 _ hw hδ
      simpa using this
    have hsum := Ideal.sum_mem _ (t := Finset.univ) (fun I _ => hdiff I)
    have heq : (∑ I : Idx r d,
        wz (Φ := sP P') (fun i T => u i T.obj) I.1 s *
          ((show (sP P').A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I)) -
            (show (sP P').A.obj (s.obj (Fin.last r)) from lft W' (s.obj (Fin.last r)).obj (rs hW (x I))))) =
        (∑ I : Idx r d, wz (Φ := sP P') (fun i T => u i T.obj) I.1 s *
          (show (sP P').A.obj (s.obj (Fin.last r)) from lft W (s.obj (Fin.last r)).obj (x I))) -
        (∑ I : Idx r d, wz (Φ := sP P') (fun i T => u i T.obj) I.1 s *
          (show (sP P').A.obj (s.obj (Fin.last r)) from lft W' (s.obj (Fin.last r)).obj (rs hW (x I)))) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun I _ => mul_sub _ _ _
    exact heq ▸ hsum

end GlobalTheory.CompanionTheory.GrForm
