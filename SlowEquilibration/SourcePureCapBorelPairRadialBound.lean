-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapBorelLatitudePairENN
public import SlowEquilibration.SourcePureLatitudeProductRadialDisintegration

/-! Uniform original-posterior pair control on every Borel latitude band
inside one high-latitude cap, after exact physical product coarea. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapBorelPairRadialBound
noncomputable section
open Classical Set Filter MeasureTheory
open SphericalModel SphericalMarkedWindows PureStationarity
open SphericalPureOriginalConditionalBandFubini
open SourcePureCapPosteriorPairIntegrable
open SourcePureCapBorelRadialFirst
open SourcePureCapBorelLatitudePairENN
open SourcePureLatitudeRadialDisintegration
open SourcePureLatitudeProductRadialDisintegration
open SphericalTAPCriticalPureLatitudeVariance
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem latitude_pair_band_ae {n : ℕ}
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (q₁ q₂ : ℝ) :
    ∀ᵐ z ∂(latitudeLaw u (latitudeFrameAt u) q₁).prod
      (latitudeLaw u (latitudeFrameAt u) q₂),
      overlap z.1 u = q₁ ∧ overlap z.2 u = q₂ := by
  have hset : MeasurableSet {z : Vector (n+1) × Vector (n+1) |
      overlap z.1 u = q₁ ∧ overlap z.2 u = q₂} := by
    apply MeasurableSet.inter <;> apply measurableSet_eq_fun
    · exact (by unfold overlap; fun_prop :
        Measurable (fun z : Vector (n+1) × Vector (n+1) => overlap z.1 u))
    · exact measurable_const
    · exact (by unfold overlap; fun_prop :
        Measurable (fun z : Vector (n+1) × Vector (n+1) => overlap z.2 u))
    · exact measurable_const
  apply (Measure.ae_prod_iff_ae_ae hset).mpr
  have h₁ := latitudeLaw_overlap_ae_all u hu q₁
  have h₂ := latitudeLaw_overlap_ae_all u hu q₂
  filter_upwards [h₁] with w₁ hw₁
  filter_upwards [h₂] with w₂ hw₂
  constructor
  · rw [show overlap w₁ u = overlap u w₁ by unfold overlap; rw [real_inner_comm]]
    exact hw₁
  · rw [show overlap w₂ u = overlap u w₂ by unfold overlap; rw [real_inner_comm]]
    exact hw₂

theorem pair_band_latitude_lintegral_le
    (n p : ℕ) (β H : ℝ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (I : Set ℝ)
    (q₁ q₂ C : ℝ) (hC : 0 ≤ C)
    (hbound : q₁ ∈ I → q₂ ∈ I →
      (∫⁻ z : Vector (n+1) × Vector (n+1),
        ENNReal.ofReal (originalPurePairMeanProfile n p 1 β H u z)
        ∂(latitudeLaw u (latitudeFrameAt u) q₁).prod
          (latitudeLaw u (latitudeFrameAt u) q₂)) ≤
        ENNReal.ofReal (C*Real.exp (β*H*q₁^p+(n+1 : ℕ)*β^2*
          sourcePureLatitudeVariance p 1 q₁/2)*
          Real.exp (β*H*q₂^p+(n+1 : ℕ)*β^2*
          sourcePureLatitudeVariance p 1 q₂/2))) :
    (∫⁻ z : Vector (n+1) × Vector (n+1),
      ENNReal.ofReal (((overlapRegion u I) ×ˢ (overlapRegion u I)).indicator
        (originalPurePairMeanProfile n p 1 β H u) z)
      ∂(latitudeLaw u (latitudeFrameAt u) q₁).prod
        (latitudeLaw u (latitudeFrameAt u) q₂)) ≤
      ENNReal.ofReal C *
        (if q₁ ∈ I then ENNReal.ofReal (Real.exp (β*H*q₁^p+
          (n+1 : ℕ)*β^2*sourcePureLatitudeVariance p 1 q₁/2)) else 0)*
        (if q₂ ∈ I then ENNReal.ofReal (Real.exp (β*H*q₂^p+
          (n+1 : ℕ)*β^2*sourcePureLatitudeVariance p 1 q₂/2)) else 0) := by
  have heq : ∀ᵐ z ∂(latitudeLaw u (latitudeFrameAt u) q₁).prod
      (latitudeLaw u (latitudeFrameAt u) q₂),
      ENNReal.ofReal (((overlapRegion u I) ×ˢ (overlapRegion u I)).indicator
        (originalPurePairMeanProfile n p 1 β H u) z) =
        if q₁ ∈ I ∧ q₂ ∈ I then
          ENNReal.ofReal (originalPurePairMeanProfile n p 1 β H u z) else 0 := by
    filter_upwards [latitude_pair_band_ae u hu q₁ q₂] with z hz
    by_cases hq₁ : q₁ ∈ I <;> by_cases hq₂ : q₂ ∈ I
    · have hm : z ∈ (overlapRegion u I) ×ˢ (overlapRegion u I) :=
        ⟨by simpa [overlapRegion,hz.1] using hq₁,
          by simpa [overlapRegion,hz.2] using hq₂⟩
      simp only [hq₁,hq₂,and_self,ite_true,Set.indicator_of_mem hm]
    · have hm : z ∉ (overlapRegion u I) ×ˢ (overlapRegion u I) := by
        intro h
        exact hq₂ (by simpa [overlapRegion,hz.2] using h.2)
      simp only [hq₁,hq₂, and_false,ite_false,Set.indicator_of_notMem hm,
        ENNReal.ofReal_zero]
    · have hm : z ∉ (overlapRegion u I) ×ˢ (overlapRegion u I) := by
        intro h
        exact hq₁ (by simpa [overlapRegion,hz.1] using h.1)
      simp only [hq₁,hq₂,false_and,ite_false,Set.indicator_of_notMem hm,
        ENNReal.ofReal_zero]
    · have hm : z ∉ (overlapRegion u I) ×ˢ (overlapRegion u I) := by
        intro h
        exact hq₁ (by simpa [overlapRegion,hz.1] using h.1)
      simp only [hq₁,hq₂,false_and,ite_false,Set.indicator_of_notMem hm,
        ENNReal.ofReal_zero]
  rw [lintegral_congr_ae heq]
  by_cases hq₁ : q₁ ∈ I <;> by_cases hq₂ : q₂ ∈ I
  · simp only [hq₁,hq₂,and_self,ite_true]
    rw [← ENNReal.ofReal_mul hC,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ C*Real.exp
        (β*H*q₁^p+(n+1 : ℕ)*β^2*sourcePureLatitudeVariance p 1 q₁/2))]
    exact hbound hq₁ hq₂
  · simp [hq₁,hq₂]
  · simp [hq₁,hq₂]
  · simp [hq₁,hq₂]

/-- Source `pc-band-second` at the level of the exact physical sphere pair
integral. The constant is independent of the Borel band, field value,
critical point, and ambient dimension. -/
theorem pure_original_borel_band_sphere_pair_bound
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hsub : pureResidualCoefficient p β a < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2=(n+1 : ℕ) →
      ∀ (H : ℝ), ∀ (I : Set ℝ), MeasurableSet I → I ⊆ Ico a 1 →
      (∫⁻ z : Vector (n+1) × Vector (n+1),
        ENNReal.ofReal (((overlapRegion u I) ×ˢ (overlapRegion u I)).indicator
          (originalPurePairMeanProfile n p 1 β H u) z)
        ∂(sphereLaw (n+1)).prod (sphereLaw (n+1))) ≤
        ENNReal.ofReal C *
          (∫⁻ w : Vector (n+1), ENNReal.ofReal
            ((overlapRegion u I).indicator
              (originalPureMeanProfile n p 1 β H u) w)
            ∂sphereLaw (n+1))^2 := by
  obtain ⟨C,hC,hLat⟩ := original_pair_profile_latitude_lintegral_bound
    p hp β ha hsub
  refine ⟨C,hC,?_⟩
  filter_upwards [hLat,Filter.eventually_ge_atTop 2] with n hnLat hn
  intro u hu H I hI hIcap
  let B := overlapRegion u I
  have hB : MeasurableSet B := overlapRegion_measurable u hI
  have hBB : MeasurableSet (B ×ˢ B) := hB.prod hB
  let F : Vector (n+1) × Vector (n+1) → ℝ≥0∞ := fun z =>
    ENNReal.ofReal ((B ×ˢ B).indicator
      (originalPurePairMeanProfile n p 1 β H u) z)
  have hF : Measurable F := ENNReal.measurable_ofReal.comp
    ((originalPurePairMeanProfile_continuous n p 1 β H u).measurable.indicator hBB)
  let W := radialMeanWeight n p β H I
  have hW : Measurable W := radialMeanWeight_measurable n p β H hI
  let ρ := radialLaw n
  have : IsProbabilityMeasure ρ := radialLaw_probability hn
  have hinner (s : Ioi (0 : ℝ) × Ioi (0 : ℝ)) :
      (∫⁻ z, F z ∂(latitudeLaw u (latitudeFrameAt u)
        (1-(s.1 : ℝ)^2/2)).prod
        (latitudeLaw u (latitudeFrameAt u) (1-(s.2 : ℝ)^2/2))) ≤
        ENNReal.ofReal C * W s.1 * W s.2 := by
    let q₁ : ℝ := 1-(s.1 : ℝ)^2/2
    let q₂ : ℝ := 1-(s.2 : ℝ)^2/2
    have hfixed := pair_band_latitude_lintegral_le n p β H u hu I
      q₁ q₂ C hC.le (fun hq₁ hq₂ =>
        hnLat u hu H q₁ (hIcap hq₁) q₂ (hIcap hq₂))
    simpa only [F,B,W,radialMeanWeight,q₁,q₂,mul_assoc] using hfixed
  calc
    (∫⁻ z : Vector (n+1) × Vector (n+1),
      ENNReal.ofReal ((B ×ˢ B).indicator
        (originalPurePairMeanProfile n p 1 β H u) z)
      ∂(sphereLaw (n+1)).prod (sphereLaw (n+1))) =
      ∫⁻ s : Ioi (0 : ℝ) × Ioi (0 : ℝ),
        (∫⁻ z, F z ∂(latitudeLaw u (latitudeFrameAt u)
          (1-(s.1 : ℝ)^2/2)).prod
          (latitudeLaw u (latitudeFrameAt u) (1-(s.2 : ℝ)^2/2)))
        ∂ρ.prod ρ := sphereLaw_prod_lintegral_radialLaw hn u hu F hF
    _ ≤ ∫⁻ s : Ioi (0 : ℝ) × Ioi (0 : ℝ),
        ENNReal.ofReal C * (W s.1 * W s.2) ∂ρ.prod ρ := by
      apply lintegral_mono
      intro s
      simpa only [mul_assoc] using hinner s
    _ = ENNReal.ofReal C * (∫⁻ s, W s ∂ρ)^2 := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_prod_mul hW.aemeasurable hW.aemeasurable]
      ring
    _ = ENNReal.ofReal C *
        (∫⁻ w : Vector (n+1), ENNReal.ofReal
          (B.indicator (originalPureMeanProfile n p 1 β H u) w)
          ∂sphereLaw (n+1))^2 := by
      rw [original_pure_mean_borel_radial n p hn β H u hu hI]


end
end SlowEquilibration.SourcePureCapBorelPairRadialBound
