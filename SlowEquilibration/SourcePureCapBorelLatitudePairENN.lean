-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapBorelLatitudePairBound
public import SlowEquilibration.SourcePureCapBorelRadialFirst

/-! Lift the actual fixed-latitude posterior pair comparison to the
nonnegative integral used by arbitrary-Borel radial product coarea. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapBorelLatitudePairENN
noncomputable section
open Classical Set Filter MeasureTheory
open SphericalModel SphericalMarkedWindows PureStationarity
open SphericalPureOriginalConditionalBandFubini
open SourcePureCapPosteriorPairIntegrable
open SourcePureCapBorelLatitudePairBound
open SourcePureCapBorelRadialFirst
open SphericalTAPCriticalPureLatitudeVariance
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem original_pair_profile_latitude_integrable
    (n p : ℕ) (hn : 1 ≤ n) (β H : ℝ)
    (u : Vector (n+1)) (q₁ q₂ : ℝ) :
    Integrable (originalPurePairMeanProfile n p 1 β H u)
      ((latitudeLaw u (latitudeFrameAt u) q₁).prod
        (latitudeLaw u (latitudeFrameAt u) q₂)) := by
  let e := latitudeFrameAt u
  let T : Vector n × Vector n → Vector (n+1) × Vector (n+1) :=
    Prod.map (latitudeMap u e q₁) (latitudeMap u e q₂)
  have hT : Continuous T :=
    (latitudeMap_continuous u e q₁).prodMap (latitudeMap_continuous u e q₂)
  have hF := originalPurePairMeanProfile_continuous n p 1 β H u
  have hcomp : Integrable (originalPurePairMeanProfile n p 1 β H u ∘ T)
      ((sphereLaw n).prod (sphereLaw n)) :=
    (memLp_spherePair_continuous hn (hF.comp hT) 1).integrable le_rfl
  unfold latitudeLaw
  rw [MeasureTheory.Measure.map_prod_map _ _
    (latitudeMap_continuous u e q₁).measurable
    (latitudeMap_continuous u e q₂).measurable]
  exact (integrable_map_measure hF.aestronglyMeasurable
    hT.measurable.aemeasurable).mpr hcomp

/-- ENNReal fixed-latitude form of the pure posterior second-moment bound.
The bound keeps exactly the first-moment factors at the two latitudes. -/
theorem original_pair_profile_latitude_lintegral_bound
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hsub : pureResidualCoefficient p β a < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)), ‖u‖^2=(n+1 : ℕ) →
      ∀ (H : ℝ), ∀ q₁ ∈ Ico a 1, ∀ q₂ ∈ Ico a 1,
      (∫⁻ z : Vector (n+1) × Vector (n+1),
        ENNReal.ofReal (originalPurePairMeanProfile n p 1 β H u z)
        ∂(latitudeLaw u (latitudeFrameAt u) q₁).prod
          (latitudeLaw u (latitudeFrameAt u) q₂)) ≤
        ENNReal.ofReal (C*Real.exp (β*H*q₁^p+(n+1 : ℕ)*β^2*
          sourcePureLatitudeVariance p 1 q₁/2)*
          Real.exp (β*H*q₂^p+(n+1 : ℕ)*β^2*
          sourcePureLatitudeVariance p 1 q₂/2)) := by
  obtain ⟨C,hC,hbound⟩ := pure_original_pair_profile_latitude_integral_bound
    p hp β ha hsub
  refine ⟨C,hC,?_⟩
  filter_upwards [hbound,Filter.eventually_ge_atTop 1] with n hnB hn
  intro u hu H q₁ hq₁ q₂ hq₂
  have hi := original_pair_profile_latitude_integrable n p hn β H u q₁ q₂
  have hnonneg : 0 ≤ᵐ[(latitudeLaw u (latitudeFrameAt u) q₁).prod
      (latitudeLaw u (latitudeFrameAt u) q₂)]
      originalPurePairMeanProfile n p 1 β H u := by
    apply Filter.Eventually.of_forall
    intro z
    unfold originalPurePairMeanProfile originalPureMeanProfile
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hi hnonneg]
  exact ENNReal.ofReal_le_ofReal (hnB u hu H q₁ hq₁ q₂ hq₂)

end
end SlowEquilibration.SourcePureCapBorelLatitudePairENN
