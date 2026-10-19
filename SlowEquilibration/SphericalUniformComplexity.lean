-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalMarkedComplexity
public import SlowEquilibration.GOEPhysicalMeanRateBound

/-! Uniform exterior-score complexity of the actual critical-count intensity. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open Filter Set Function
open SphericalModel SphericalGaussianJet SphericalSequentialRegression WholeFieldRegression
open GOEPhysicalPotential
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

def mixedNormalizationError (n : ℕ) (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  (Real.log (sphereKRPrefactor (n+1) μ Q).toReal / (n+2 : ℕ) -
    (1 - Real.log (Q * μ.xi1 Q))/2) +
  (Real.log (n+2 : ℕ) - Real.log (2 * Real.pi * Real.sqrt (μ.scoreCovariance Q).det)) / (n+2 : ℕ)

lemma mixedNormalizationError_tendsto (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    Tendsto (fun n => mixedNormalizationError n μ Q) atTop (𝓝 0) := by
  have h := ((sphereKRPrefactor_log_rate μ hQ).sub_const ((1 - Real.log (Q * μ.xi1 Q))/2)).add
    (log_dimension_div_tendsto.sub
      (constant_div_dimension_tendsto (Real.log (2 * Real.pi * Real.sqrt (μ.scoreCovariance Q).det))))
  convert h using 1
  · funext n
    unfold mixedNormalizationError
    push_cast
    ring
  · simp

lemma mixed_log_complexity_error (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : 2 * Real.sqrt (Q^2 * μ.xi2 Q) < z 1) :
    Real.log (mixedCriticalIntensity n μ Q z).toReal / (n+2 : ℕ) - markedComplexity μ Q z =
      mixedNormalizationError n μ Q +
      (Real.log (physicalMean n (n+2) (Q^2 * μ.xi2 Q) (z 1)) - (n+2 : ℕ) *
        (Real.log (Real.sqrt (Q^2 * μ.xi2 Q)) +
          SemicirclePotential.potential (z 1 / Real.sqrt (Q^2 * μ.xi2 Q)))) / (n+2 : ℕ) := by
  have ha := mul_pos hQ (mixture_xi1_pos μ hQ)
  have hb := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  rw [mixedCriticalIntensity_log n μ hQ hnp z hz, physicalScorePdf_log (n+2) (by omega) μ hQ hnp z]
  unfold markedComplexity mixedNormalizationError
  rw [Real.log_div hb.ne' ha.ne', Real.log_sqrt hb.le]
  push_cast
  field_simp
  ring

/-- The actual mixed count intensity converges to Θ uniformly over every
fixed exterior radial interval, with no restriction on the value coordinate. -/
theorem actual_mixed_complexity_uniform (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) {g Z ε : ℝ} (hg : 0 < g) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ z : EuclideanSpace ℝ (Fin 2),
      z 1 ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z →
      |Real.log (mixedCriticalIntensity n μ Q z).toReal / (n+2 : ℕ) - markedComplexity μ Q z| < ε := by
  obtain ⟨B,hB,hmean⟩ := physicalMean_log_error_bound (Z := Z)
    (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hg
  have hs := (mixedNormalizationError_tendsto μ hQ).abs.add (constant_div_dimension_tendsto B)
  simp only [abs_zero, add_zero] at hs
  filter_upwards [hs.eventually (gt_mem_nhds hε)] with n hn
  intro z hz
  rw [mixed_log_complexity_error n μ hQ hnp z (by linarith [hz.1])]
  have hN : (0:ℝ) < (n+2 : ℕ) := by positivity
  calc
    _ ≤ |mixedNormalizationError n μ Q| +
        |(Real.log (physicalMean n (n+2) (Q^2 * μ.xi2 Q) (z 1)) - (n+2 : ℕ) *
          (Real.log (Real.sqrt (Q^2 * μ.xi2 Q)) +
            SemicirclePotential.potential (z 1 / Real.sqrt (Q^2 * μ.xi2 Q)))) / (n+2 : ℕ)| :=
      abs_add_le _ _
    _ ≤ |mixedNormalizationError n μ Q| + B / (n+2 : ℕ) := by
      rw [abs_div, abs_of_pos hN]
      exact add_le_add_right (div_le_div_of_nonneg_right (hmean n (z 1) hz) hN.le) _
    _ < ε := by simpa only [Nat.cast_add, Nat.cast_ofNat] using hn

end
end SlowEquilibration.SphericalMarkedWindows
