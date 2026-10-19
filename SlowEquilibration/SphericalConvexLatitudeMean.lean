-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlantedUniformUpper

@[expose] public section

/-! # Actual latitude pressure and profiles for globally convex covariances

The covariance may have odd coefficients. Genuine convexity on [-1,1]
supplies the supporting-line comparison on every nonnegative latitude.
-/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

theorem convex_latitudeQuenchedPressure_eventually_uniform_upper
    (μ : FiniteMixture) (β : ℝ) (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ Icc (0 : ℝ) 1, ∀ (u : Vector (n+1)),
      ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
      (∀ x, inner ℝ (e x) u=0) →
      latitudeQuenchedPressure n μ β u e q ≤ latitudePressureTrial μ β q+ε := by
  apply latitudeQuenchedPressure_eventually_uniform_upper_of_tangent μ β _ isCompact_Icc
    Subset.rfl _ hε
  intro q hq t ht
  have hs : 0 ≤ 1-q^2 := by nlinarith [hq.1, hq.2]
  have harg : q^2+(1-q^2)*t ∈ Icc (-1 : ℝ) 1 := by
    constructor <;> nlinarith [mul_nonneg hs (by linarith [ht.1] : 0 ≤ t+1),
      mul_nonneg hs (by linarith [ht.2] : 0 ≤ 1-t)]
  exact convex_covariance_supporting_line μ hconv ⟨by linarith [hq.1], hq.2⟩ harg

theorem convex_plantedLatitudeQuenchedPressure_eventually_uniform_upper
    (μ : FiniteMixture) (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi)
    {β : ℝ} (hβ : 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ Icc (0 : ℝ) 1, ∀ (u : Vector (n+1)),
      ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
      (∀ x, inner ℝ (e x) u=0) →
      plantedLatitudeQuenchedPressure n μ β u e q ≤
        (β^2*(μ.xi 1+μ.xi q)+q-Real.log (1+q))/2+ε := by
  filter_upwards [convex_latitudeQuenchedPressure_eventually_uniform_upper μ β hconv hε,
    eventually_ge_atTop 1] with n hn hdim
  intro q hq u hu e he
  have hh := hn q hq u hu e he
  rw [plantedLatitudeQuenchedPressure_eq hdim μ hβ u hu e he
    (abs_le.mpr ⟨by linarith [hq.1], hq.2⟩)]
  unfold latitudePressureTrial at hh
  linarith

theorem convex_plantedLatitudeMeanProfile_eventually_uniform_upper
    (μ : FiniteMixture) (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi)
    {β ρ ε : ℝ} (hβ : 0 < β) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ q ∈ Icc (0 : ℝ) ρ, ∀ (u : Vector (n+1)),
      ‖u‖^2=((n+1 : ℕ) : ℝ) → ∀ (e : Vector n →ₗᵢ[ℝ] Vector (n+1)),
      (∀ x, inner ℝ (e x) u=0) →
      plantedLatitudeMeanProfile n μ β u e q ≤ plantedProfileTrial μ β q+ε := by
  have hsmall := (latitudeEntropyError_tendsto ρ).eventually (gt_mem_nhds (half_pos hε))
  filter_upwards [convex_plantedLatitudeQuenchedPressure_eventually_uniform_upper μ hconv hβ
    (half_pos hε), hsmall, eventually_ge_atTop 2] with n hmean hsmall hn
  intro q hq u hu e he
  have hp := plantedLatitudeMeanProfile_le hn μ β u e hρ hq
    (hmean q ⟨hq.1,hq.2.trans hρ.2.le⟩ u hu e he)
  linarith

end
end SlowEquilibration.SphericalModel
