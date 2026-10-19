-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapBorelPairReal
public import SlowEquilibration.SourcePureCapPosteriorBandSecondFubini

/-! Literal source `pc-band-second` for the original pure field under the
actual critical-point value-conditioned disorder law. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapBorelBandSecondMoment
noncomputable section
open Set Filter MeasureTheory
open SphericalModel SphericalMarkedWindows SphericalGaussianJet PureStationarity
open SphericalPureOriginalConditionalBandFubini
open SourcePureCapPosteriorBandSecondFubini
open SourcePureCapBorelPairReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- An exact unconditional posterior second-moment bound for every Borel
band inside a high-latitude cap. One constant works for all values, poles,
and dimensions beyond a threshold. -/
theorem pure_original_conditioned_borel_band_second_moment
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hsub : pureResidualCoefficient p β a < 1/2) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ)),
      ∀ (H : ℝ), ∀ (I : Set ℝ), MeasurableSet I → I ⊆ Ico a 1 →
      let μ := FiniteMixture.pure p hp 1 (by positivity)
      let c := centerCoefficients (mixtureCoefficients μ) 1
      let B := overlapRegion u I
      (∫ J, (partitionOn β (field (mixtureCoefficients μ) J) B)^2
        ∂valueConditionedLaw c u hu (H/(n+1 : ℕ))) ≤
        C*(∫ J, partitionOn β (field (mixtureCoefficients μ) J) B
          ∂valueConditionedLaw c u hu (H/(n+1 : ℕ)))^2 := by
  obtain ⟨C,hC,hSphere⟩ := pure_original_borel_band_sphere_pair_real_bound
    p hp β ha hsub
  refine ⟨C,hC,?_⟩
  filter_upwards [hSphere] with n hn
  intro u hu H I hI hIcap
  let μ := FiniteMixture.pure p hp 1 (by positivity)
  let c := centerCoefficients (mixtureCoefficients μ) 1
  let B := overlapRegion u I
  have h₂ := pure_original_conditioned_band_sq_sphere
    n p hp 1 (by positivity) u hu β H I hI
  have h₁ := pure_original_conditioned_band_mean_sphere
    n p hp 1 (by positivity) (Q := 1) (by positivity) u hu β H I hI
  dsimp only at h₂ h₁
  simp only [Real.sqrt_one,one_pow,one_mul] at h₁
  dsimp only
  rw [h₂,h₁]
  simpa only [integral_indicator (overlapRegion_measurable u hI)] using
    hn u hu H I hI hIcap

end
end SlowEquilibration.SourcePureCapBorelBandSecondMoment
