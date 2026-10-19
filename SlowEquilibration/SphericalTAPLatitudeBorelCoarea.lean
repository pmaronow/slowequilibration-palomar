-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPLatitudeLIntegralChange

@[expose] public section

/-! Exact spherical latitude disintegration on arbitrary Borel sets inside
the physical latitude interval. This extends the earlier interval version
without a regularity assumption on the set. -/

namespace SlowEquilibration.SphericalTAPLatitudeBorelCoarea
noncomputable section
open MeasureTheory Set SphericalModel
open SphericalTAPLatitudeLIntegralChange
open scoped ENNReal
set_option autoImplicit false

theorem radial_subtype_borel_lintegral_eq_latitude
    (I : Set ℝ) (hI : MeasurableSet I) (hsub : I ⊆ Icc (-1:ℝ) 1)
    (G : ℝ → ℝ≥0∞) :
    (∫⁻ s : Ioi (0:ℝ),
      {t : Ioi (0:ℝ) | (t:ℝ) < 2}.indicator
        (fun t => I.indicator
          (fun q => ENNReal.ofReal (t:ℝ) * G q) (radialLatitude t)) s
      ∂(volume.comap (Subtype.val : Ioi (0:ℝ) → ℝ))) =
      ∫⁻ q in I, G q ∂volume := by
  let F : ℝ → ℝ≥0∞ := I.indicator G
  have hpoint (s : Ioi (0:ℝ)) :
      {t : Ioi (0:ℝ) | (t:ℝ) < 2}.indicator
        (fun t => I.indicator
          (fun q => ENNReal.ofReal (t:ℝ) * G q) (radialLatitude t)) s =
      {t : Ioi (0:ℝ) | (t:ℝ) < 2}.indicator
        (fun t => ENNReal.ofReal (t:ℝ) * F (radialLatitude t)) s := by
    by_cases hs : (s:ℝ) < 2
    · rw [Set.indicator_of_mem (show s ∈ {t : Ioi (0:ℝ) | (t:ℝ) < 2} from hs),
        Set.indicator_of_mem (show s ∈ {t : Ioi (0:ℝ) | (t:ℝ) < 2} from hs)]
      by_cases hq : radialLatitude (s:ℝ) ∈ I
      · simp only [F, Set.indicator_of_mem hq]
      · simp only [F, Set.indicator_of_notMem hq, mul_zero]
    · rw [Set.indicator_of_notMem (show s ∉ {t : Ioi (0:ℝ) | (t:ℝ) < 2} from hs),
        Set.indicator_of_notMem (show s ∉ {t : Ioi (0:ℝ) | (t:ℝ) < 2} from hs)]
  simp_rw [hpoint]
  have hcut : MeasurableSet {t : Ioi (0:ℝ) | (t:ℝ) < 2} :=
    measurableSet_Iio.preimage measurable_subtype_coe
  rw [lintegral_indicator hcut]
  have himage : (Subtype.val : Ioi (0:ℝ) → ℝ) ''
      {t : Ioi (0:ℝ) | (t:ℝ) < 2} = Ioo (0:ℝ) 2 := by
    ext r
    constructor
    · rintro ⟨s,hs,rfl⟩
      exact ⟨s.property,hs⟩
    · intro hr
      exact ⟨⟨r,hr.1⟩,hr.2,rfl⟩
  change (∫⁻ s in {t : Ioi (0:ℝ) | (t:ℝ) < 2},
    (fun r : ℝ => ENNReal.ofReal r * F (radialLatitude r)) (s:ℝ)
    ∂(volume.comap (Subtype.val : Ioi (0:ℝ) → ℝ))) = _
  rw [setLIntegral_subtype (μ := (volume : Measure ℝ)) measurableSet_Ioi
    {t : Ioi (0:ℝ) | (t:ℝ) < 2}
    (fun r : ℝ => ENNReal.ofReal r * F (radialLatitude r)), himage]
  rw [setLIntegral_congr (Ioo_ae_eq_Icc (μ:=volume))]
  have hchange := radialLatitude_lintegral_Icc
    (a := (0:ℝ)) (b := 2) (by norm_num) (by norm_num) F
  have hend : radialLatitude (2:ℝ) = -1 := by norm_num [radialLatitude]
  have hstart : radialLatitude (0:ℝ) = 1 := by norm_num [radialLatitude]
  rw [hend,hstart] at hchange
  rw [← hchange]
  change (∫⁻ q in Icc (-1:ℝ) 1, I.indicator G q ∂volume) =
    ∫⁻ q in I, G q ∂volume
  rw [lintegral_indicator hI, Measure.restrict_restrict_of_subset hsub]

/-- Genuine restricted-partition coarea for any Borel latitude set. -/
theorem partitionOn_borel_latitude_eq_lintegral
    {n : ℕ} (hn : 2 ≤ n) (β : ℝ)
    {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (I : Set ℝ) (hI : MeasurableSet I) (hsub : I ⊆ Icc (-1:ℝ) 1) :
    ENNReal.ofReal (partitionOn β H (overlapRegion u I)) =
      latitudeNormalization n *
        ∫⁻ q in I, ENNReal.ofReal (latitudeDensityPartition n β H u q)
          ∂volume := by
  rw [partitionOn_latitude_coarea hn β hH u hu hI]
  congr 1
  calc
    _ = ∫⁻ s : Ioi (0:ℝ),
        {t : Ioi (0:ℝ) | (t:ℝ) < 2}.indicator
          (fun t => I.indicator
            (fun q => ENNReal.ofReal (t:ℝ) *
              ENNReal.ofReal (latitudeDensityPartition n β H u q))
            (radialLatitude t)) s
        ∂(volume.comap (Subtype.val : Ioi (0:ℝ) → ℝ)) := by
          apply lintegral_congr
          intro s
          by_cases hs : (s:ℝ) < 2
          · rw [Set.indicator_of_mem (show s ∈ {t : Ioi (0:ℝ) | (t:ℝ)<2} from hs),
                Set.indicator_of_mem (show s ∈ {t : Ioi (0:ℝ) | (t:ℝ)<2} from hs)]
            by_cases hq : radialLatitude (s:ℝ) ∈ I
            · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq]
              exact ENNReal.ofReal_mul s.property.le
            · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
          · rw [Set.indicator_of_notMem
                (show s ∉ {t : Ioi (0:ℝ) | (t:ℝ)<2} from hs),
                Set.indicator_of_notMem
                (show s ∉ {t : Ioi (0:ℝ) | (t:ℝ)<2} from hs)]
    _ = _ := radial_subtype_borel_lintegral_eq_latitude I hI hsub
      (fun q => ENNReal.ofReal (latitudeDensityPartition n β H u q))

/-- Real-valued Borel coarea. The only extra condition is ordinary
integrability of the explicit latitude density on the chosen set. -/
theorem partitionOn_borel_latitude_eq_real_integral
    {n : ℕ} (hn : 2 ≤ n) (β : ℝ)
    {H : Vector (n+1) → ℝ} (hH : Continuous H)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (I : Set ℝ) (hI : MeasurableSet I) (hsub : I ⊆ Icc (-1:ℝ) 1)
    (hden : IntegrableOn (latitudeDensityPartition n β H u) I volume) :
    partitionOn β H (overlapRegion u I) =
      (latitudeNormalization n).toReal *
        ∫ q in I, latitudeDensityPartition n β H u q ∂volume := by
  have hcoarea := partitionOn_borel_latitude_eq_lintegral hn β hH
    u hu I hI hsub
  have hreal : ENNReal.ofReal
      (∫ q in I, latitudeDensityPartition n β H u q ∂volume) =
      ∫⁻ q in I, ENNReal.ofReal (latitudeDensityPartition n β H u q)
        ∂volume :=
    ofReal_integral_eq_lintegral_ofReal hden
      (Filter.Eventually.of_forall fun q => latitudeDensityPartition_nonneg n β H u q)
  rw [← hreal] at hcoarea
  have h := congrArg ENNReal.toReal hcoarea
  rw [ENNReal.toReal_ofReal (partitionOn_nonneg β H _),
    ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (integral_nonneg
      (fun q => latitudeDensityPartition_nonneg n β H u q))] at h
  exact h

end
end SlowEquilibration.SphericalTAPLatitudeBorelCoarea
