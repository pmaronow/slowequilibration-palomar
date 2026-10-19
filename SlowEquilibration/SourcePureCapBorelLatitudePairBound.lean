-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapPosteriorBandSecondFubini
public import SlowEquilibration.SourcePureCapMixedLatitudeAngularIntegral

/-! The exact original-posterior two-spin profile has one uniform angular
comparison on any pair of cap latitudes. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapBorelLatitudePairBound
noncomputable section
open Set Filter MeasureTheory
open SphericalModel PureStationarity
open SphericalPureOriginalConditionalBandFubini
open SourcePureCapPosteriorPairIntegrable
open SourcePureCapMixedLatitudeAngularIntegral
open SourcePureCapPosteriorCrossKernel
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_original_pair_profile_latitude_ae
    (n p : ℕ) (hn : 1 ≤ n) (hp : 2 ≤ p) (β H : ℝ)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    {q₁ q₂ : ℝ} (hq₁ : |q₁| ≤ 1) (hq₂ : |q₂| ≤ 1) :
    ∀ᵐ z ∂(latitudeLaw u (latitudeFrameAt u) q₁).prod
        (latitudeLaw u (latitudeFrameAt u) q₂),
      originalPurePairMeanProfile n p 1 β H u z =
        Real.exp (β*H*q₁^p+(n+1 : ℕ)*β^2*
          SphericalTAPCriticalPureLatitudeVariance.sourcePureLatitudeVariance p 1 q₁/2)*
        Real.exp (β*H*q₂^p+(n+1 : ℕ)*β^2*
          SphericalTAPCriticalPureLatitudeVariance.sourcePureLatitudeVariance p 1 q₂/2)*
        pureCrossPairWeight n p hp β q₁ q₂ z := by
  let e := latitudeFrameAt u
  have he : ∀ x, inner ℝ (e x) u=0 := latitudeFrameAt_orthogonal u hu
  have hlat₁ := latitudeLaw_support hn u hu e he hq₁
  have hlat₂ := latitudeLaw_support hn u hu e he hq₂
  have hmeas : MeasurableSet {z : Vector (n+1) × Vector (n+1) |
      originalPurePairMeanProfile n p 1 β H u z =
        Real.exp (β*H*q₁^p+(n+1 : ℕ)*β^2*
          SphericalTAPCriticalPureLatitudeVariance.sourcePureLatitudeVariance p 1 q₁/2)*
        Real.exp (β*H*q₂^p+(n+1 : ℕ)*β^2*
          SphericalTAPCriticalPureLatitudeVariance.sourcePureLatitudeVariance p 1 q₂/2)*
        pureCrossPairWeight n p hp β q₁ q₂ z} := by
    apply measurableSet_eq_fun
    · exact (originalPurePairMeanProfile_continuous n p 1 β H u).measurable
    · exact (measurable_const.mul measurable_const).mul
        (pureCrossPairWeight_continuous n p hp β q₁ q₂).measurable
  apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
  filter_upwards [hlat₁] with w₁ hw₁
  filter_upwards [hlat₂] with w₂ hw₂
  have hq₁' : overlap u w₁ = q₁ := by
    rw [show overlap u w₁ = overlap w₁ u by unfold overlap; rw [real_inner_comm]]
    exact hw₁.2
  have hq₂' : overlap u w₂ = q₂ := by
    rw [show overlap u w₂ = overlap w₂ u by unfold overlap; rw [real_inner_comm]]
    exact hw₂.2
  unfold originalPurePairMeanProfile originalPureMeanProfile pureCrossPairWeight
  rw [hq₁',hq₂']
  rw [sourceValueTauCross_pure p hp 1 (by positivity)
    (by norm_num : (0 : ℝ) < 1)]
  have hbase : q₁*q₂+(overlap w₁ w₂-q₁*q₂) = overlap w₁ w₂ := by ring
  rw [hbase]
  ring

/-- Source `pc-band-second` at the two fixed radii, with the true original
posterior pair profile and true product latitude law. -/
theorem pure_original_pair_profile_latitude_integral_bound
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hsub : pureResidualCoefficient p β a < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2=(n+1 : ℕ) →
      ∀ (H : ℝ), ∀ q₁ ∈ Ico a 1, ∀ q₂ ∈ Ico a 1,
      (∫ z : Vector (n+1) × Vector (n+1),
        originalPurePairMeanProfile n p 1 β H u z
        ∂(latitudeLaw u (latitudeFrameAt u) q₁).prod
          (latitudeLaw u (latitudeFrameAt u) q₂)) ≤
        C*Real.exp (β*H*q₁^p+(n+1 : ℕ)*β^2*
          SphericalTAPCriticalPureLatitudeVariance.sourcePureLatitudeVariance p 1 q₁/2)*
          Real.exp (β*H*q₂^p+(n+1 : ℕ)*β^2*
          SphericalTAPCriticalPureLatitudeVariance.sourcePureLatitudeVariance p 1 q₂/2) := by
  obtain ⟨C,hC,hAngular⟩ := pure_source_mixed_latitude_angular_integral_bound
    p hp β ha hsub
  refine ⟨C,hC,?_⟩
  filter_upwards [hAngular,Filter.eventually_ge_atTop 1] with n hnAng hn
  intro u hu H q₁ hq₁ q₂ hq₂
  let ν := (latitudeLaw u (latitudeFrameAt u) q₁).prod
    (latitudeLaw u (latitudeFrameAt u) q₂)
  let m₁ := Real.exp (β*H*q₁^p+(n+1 : ℕ)*β^2*
      SphericalTAPCriticalPureLatitudeVariance.sourcePureLatitudeVariance p 1 q₁/2)
  let m₂ := Real.exp (β*H*q₂^p+(n+1 : ℕ)*β^2*
      SphericalTAPCriticalPureLatitudeVariance.sourcePureLatitudeVariance p 1 q₂/2)
  have hae := pure_original_pair_profile_latitude_ae n p hn hp β H u hu
    (abs_le.mpr ⟨by linarith [ha.1,hq₁.1],hq₁.2.le⟩)
    (abs_le.mpr ⟨by linarith [ha.1,hq₂.1],hq₂.2.le⟩)
  have hEq : (∫ z, originalPurePairMeanProfile n p 1 β H u z ∂ν) =
      m₁*m₂*(∫ z, pureCrossPairWeight n p hp β q₁ q₂ z ∂ν) := by
    rw [← integral_const_mul]
    exact integral_congr_ae hae
  rw [hEq]
  have hbound := hnAng u hu q₁ hq₁ q₂ hq₂
  have hnonneg : 0 ≤ m₁*m₂ := mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hh := mul_le_mul_of_nonneg_left hbound hnonneg
  dsimp [m₁,m₂] at *
  nlinarith

end
end SlowEquilibration.SourcePureCapBorelLatitudePairBound
