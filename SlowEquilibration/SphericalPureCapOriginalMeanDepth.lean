-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureOriginalConditionalBandBorel
public import SlowEquilibration.SphericalPureCapDepth
public import SlowEquilibration.SphericalPureCapIntegralDecomposition

@[expose] public section

/-! The original posterior band mean on the manuscript's half-open cap and
its exact finite-dimensional energy-deficit estimate. -/

namespace SlowEquilibration.SphericalPureCapOriginalMeanDepth
noncomputable section
open MeasureTheory Set SphericalModel SphericalMarkedWindows
open SphericalGaussianJet SphericalPureOriginalConditionalBandBorel
open SphericalPureCapIntegralDecomposition SphericalPureCapDepth
open SphericalTAPCriticalPureLatitudeVariance PureStationarity
set_option autoImplicit false

/-- Source `pc-band-mean` on the actual half-open cap `[a,1)`, written
with the raw entropy-power integrand used by the source Laplace analysis. -/
theorem pure_original_conditioned_cap_mean_raw
    (n p : ℕ) (hn : 3 ≤ n) (hp : 4 ≤ p)
    {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    (β H a : ℝ) (ha : 0 < a) (ha1 : a < 1) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    (∫ J, partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u (Ico a 1))
      ∂valueConditionedLaw c u hu (s*H/(n+1 : ℕ))) =
      (latitudeNormalization n).toReal *
        (∫ z in a..1, rawDensity p (n+1) β H z) := by
  dsimp only
  have hinside : Ico a 1 ⊆ Ioo (-1:ℝ) 1 := by
    intro z hz
    exact ⟨by linarith [ha,hz.1],hz.2⟩
  rw [pure_original_conditioned_band_mean_borel n p (by omega)
    (by omega) 1 (by positivity) hQ u hu β H (Ico a 1)
      measurableSet_Ico hinside]
  congr 1
  rw [intervalIntegral.integral_of_le ha1.le]
  rw [← integral_Ico_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ico] with z hz
  have hz0 : 0 ≤ 1-z^2 := by nlinarith [ha,hz.1,hz.2]
  have hres : β^2*sourcePureLatitudeVariance p 1 z =
      pureResidualCoefficient p β z := by
    rw [pureResidualCoefficient_eq p (by omega)]
    unfold sourcePureLatitudeVariance
    ring
  have hpow : (Real.sqrt (1-z^2))^(n-2) =
      (1-z^2)^((((n+1:ℕ):ℝ)-3)/2) := by
    rw [← Real.rpow_natCast,
      ← Real.rpow_div_two_eq_sqrt ((n-2:ℕ):ℝ) hz0]
    congr 1
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    push_cast
    ring
  unfold rawDensity
  rw [hpow,←hres]
  congr 1
  ring

/-- The printed `pc-depth` inequality, now for the original pure
conditional expectation on `[a,1)`, holds at every dimension `N≥4`. -/
theorem pure_original_conditioned_cap_mean_depth_le
    (n p : ℕ) (hn : 3 ≤ n) (hp : 4 ≤ p)
    {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ))
    {β H a v : ℝ} (hβ : 0 < β) (ha : 0 < a)
    (ha1 : a < 1) (hv : 0 ≤ v) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let s := (Real.sqrt Q)^p
    (∫ J, partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u (Ico a 1))
      ∂valueConditionedLaw c u hu (s*(H-v)/(n+1 : ℕ))) ≤
      Real.exp (-β*v*a^p) *
        (∫ J, partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Ico a 1))
          ∂valueConditionedLaw c u hu (s*H/(n+1 : ℕ))) := by
  dsimp only
  rw [pure_original_conditioned_cap_mean_raw n p hn hp hQ u hu β (H-v) a ha ha1,
      pure_original_conditioned_cap_mean_raw n p hn hp hQ u hu β H a ha ha1]
  have hdim : n+1-1=n := by omega
  simpa only [rawDensity,hdim] using
    pure_cap_normalized_integral_depth_le p hβ ha.le ha1 hv (n+1) (by omega)

end
end SlowEquilibration.SphericalPureCapOriginalMeanDepth
