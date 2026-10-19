-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedLowSumENNIntegral
public import SlowEquilibration.SphericalTAPMixedSourceCommonPalmEnvelope
public import SlowEquilibration.NatLogSequenceScales

@[expose] public section

/-! The source's logarithmically corrected critical energy center has a
vanishing quadratic error on the physical dimension scale. -/

namespace SlowEquilibration.SourceMixedLowSumCenterCorrection
noncomputable section
open MeasureTheory Set Filter
open SphericalMarkedWindows TwoAtomStationarity
open SphericalTAPCertificate NatLogWindowScales
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 700000

theorem source_center_quadratic_error_eventually_bounded
    (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : Certificate μ β x Q)
    (data : SourceMaximumFirstMomentConclusions μ β x Q L R)
    {τ C₂ : ℝ} (hτ : 0 < τ) (hC₂ : 0 < C₂) :
    ∀ᶠ d : ℕ in atTop,
      let σ := data.center d-((d+2:ℕ):ℝ)*markE μ β x Q
      3*|σ| ≤ τ*((d+2:ℕ):ℝ) ∧
        C₂*σ^2/((d+2:ℕ):ℝ) ≤ 1 := by
  let c₀ := β*x
  let D : ℝ := 1/(2*c₀)+1
  have hc₀ : 0 < c₀ := mul_pos h.beta_pos h.weight_range.1
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hlog : ∀ᶠ d : ℕ in atTop,
      |data.center d-((d+2:ℕ):ℝ)*markE μ β x Q| ≤
        D*Real.log (d+2:ℕ) :=
    normalized_center_log_bounded hc₀ data.log_constant_pos.le
      data.center data.logarithmic_correction
  have hsqrt : 0 ≤ Real.sqrt C₂ := Real.sqrt_nonneg _
  have hlogScaled : ∀ᶠ d : ℕ in atTop,
      |Real.sqrt C₂ * (data.center d-((d+2:ℕ):ℝ)*markE μ β x Q)| ≤
        (Real.sqrt C₂*D)*Real.log (d+2:ℕ) := by
    filter_upwards [hlog] with d hd
    rw [abs_mul,abs_of_nonneg hsqrt]
    nlinarith [mul_le_mul_of_nonneg_left hd hsqrt]
  have hQuadratic := uniform_log_window_eventually
    (mul_nonneg hsqrt hD) (by norm_num : (0:ℝ)<1)
    (by norm_num : (0:ℝ)<1) (0:ℝ)
  have hLinear := uniform_log_window_eventually
    hD (by norm_num : (0:ℝ)<1) hτ (6:ℝ)
  filter_upwards [hlog,hlogScaled,hQuadratic,hLinear] with d hd hdScaled hq hl
  let σ := data.center d-((d+2:ℕ):ℝ)*markE μ β x Q
  let N : ℝ := ((d+2:ℕ):ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hqsq := (hq _ hdScaled).1
  have hls := (hl _ hd).2
  have hqeq : (Real.sqrt C₂*σ)^2/N = C₂*σ^2/N := by
    rw [mul_pow,Real.sq_sqrt hC₂.le]
  have hlinEq : |6*σ/(2*(1:ℝ)*N)| = 3*|σ|/N := by
    rw [abs_div,abs_mul,abs_of_pos (by positivity : 0 < 2*(1:ℝ)*N)]
    norm_num
    ring
  have hlin : 3*|σ|/N < τ := by
    rw [hlinEq] at hls
    have hinv : 0 ≤ 1/Real.sqrt N := by positivity
    linarith
  dsimp only
  constructor
  · have hh := (div_lt_iff₀ hN).mp hlin
    dsimp [σ,N] at *
    linarith
  · rw [hqeq] at hqsq
    simpa only [σ,N] using hqsq

end
end SlowEquilibration.SourceMixedLowSumCenterCorrection
