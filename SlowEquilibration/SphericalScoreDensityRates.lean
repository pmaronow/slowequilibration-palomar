-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCountIntensity

/-! Exact logarithmic rates of the actual physical score densities. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Function Filter
open SphericalModel SphericalGaussianJet SphericalSequentialRegression
open GOEPhysicalPotential GOEPhysicalNormalizedMoments
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

lemma physicalScorePdf_toReal_pos (N : ℕ) (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (b : EuclideanSpace ℝ (Fin 2)) : 0 < (physicalScorePdf N μ Q b).toReal := by
  unfold physicalScorePdf
  apply ENNReal.toReal_pos
  · exact (ENNReal.ofReal_pos.mpr (mul_pos
      (div_pos (Nat.cast_pos.mpr hN) (mul_pos (mul_pos (by norm_num) Real.pi_pos)
        (Real.sqrt_pos.mpr (μ.scoreCovariance_det_pos hQ hnp)))) (Real.exp_pos _))).ne'
  · exact ENNReal.ofReal_ne_top

lemma physicalScorePdf_log (N : ℕ) (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (b : EuclideanSpace ℝ (Fin 2)) :
    Real.log (physicalScorePdf N μ Q b).toReal =
      Real.log N - Real.log (2 * Real.pi * Real.sqrt (μ.scoreCovariance Q).det) -
        (N : ℝ) / 2 * scoreQuadratic μ Q b := by
  have hC : 0 < 2 * Real.pi * Real.sqrt (μ.scoreCovariance Q).det :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (Real.sqrt_pos.mpr (μ.scoreCovariance_det_pos hQ hnp))
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  unfold physicalScorePdf
  rw [ENNReal.toReal_ofReal (mul_nonneg (div_nonneg hNr.le hC.le) (Real.exp_pos _).le),
    Real.log_mul (div_pos hNr hC).ne' (Real.exp_ne_zero _),
    Real.log_div hNr.ne' hC.ne', Real.log_exp]
  ring

lemma physicalValuePdf_toReal_pos (N : ℕ) (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (h : ℝ) : 0 < (physicalValuePdf N μ Q h).toReal := by
  unfold physicalValuePdf
  apply ENNReal.toReal_pos
  · apply ne_of_gt
    apply ENNReal.ofReal_pos.mpr
    exact mul_pos (Real.sqrt_pos.mpr (div_pos (Nat.cast_pos.mpr hN)
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) (μ.xi_pos hQ)))) (Real.exp_pos _)
  · exact ENNReal.ofReal_ne_top

lemma physicalValuePdf_log (N : ℕ) (hN : 0 < N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (h : ℝ) :
    Real.log (physicalValuePdf N μ Q h).toReal =
      (Real.log N - Real.log (2 * Real.pi * μ.xi Q)) / 2 -
        (N : ℝ) * h^2 / (2 * μ.xi Q) := by
  have hC : 0 < 2 * Real.pi * μ.xi Q :=
    mul_pos (mul_pos (by norm_num) Real.pi_pos) (μ.xi_pos hQ)
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  unfold physicalValuePdf
  rw [ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le),
    Real.log_mul (Real.sqrt_pos.mpr (div_pos hNr hC)).ne' (Real.exp_ne_zero _),
    Real.log_sqrt (div_nonneg hNr.le hC.le), Real.log_div hNr.ne' hC.ne', Real.log_exp]
  ring

lemma log_dimension_div_tendsto :
    Tendsto (fun n : ℕ => Real.log (n+2 : ℝ) / (n+2 : ℝ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => (n:ℝ)+2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
  simpa only [pow_one, one_mul, add_zero, Function.comp_def] using
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hN

lemma constant_div_dimension_tendsto (C : ℝ) :
    Tendsto (fun n : ℕ => C / (n+2 : ℝ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => (n:ℝ)+2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
  simpa only [Function.comp_def, div_eq_mul_inv, mul_zero] using
    (tendsto_inv_atTop_zero.comp hN).const_mul C

theorem physicalScorePdf_log_rate (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (b : EuclideanSpace ℝ (Fin 2)) :
    Tendsto (fun n : ℕ => Real.log (physicalScorePdf (n+2) μ Q b).toReal / (n+2 : ℕ))
      atTop (𝓝 (-scoreQuadratic μ Q b / 2)) := by
  have h := (log_dimension_div_tendsto.sub
    (constant_div_dimension_tendsto (Real.log (2 * Real.pi * Real.sqrt (μ.scoreCovariance Q).det)))).sub
      (tendsto_const_nhds (x := scoreQuadratic μ Q b / 2))
  convert h using 1
  · funext n
    rw [physicalScorePdf_log (n+2) (by omega) μ hQ hnp b]
    push_cast
    field_simp
  · ring

theorem physicalValuePdf_log_rate (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (h : ℝ) :
    Tendsto (fun n : ℕ => Real.log (physicalValuePdf (n+2) μ Q h).toReal / (n+2 : ℕ))
      atTop (𝓝 (-h^2 / (2 * μ.xi Q))) := by
  have hc := ((log_dimension_div_tendsto.sub
    (constant_div_dimension_tendsto (Real.log (2 * Real.pi * μ.xi Q)))).div_const 2).sub
      (tendsto_const_nhds (x := h^2 / (2 * μ.xi Q)))
  convert hc using 1
  · funext n
    rw [physicalValuePdf_log (n+2) (by omega) μ hQ h]
    push_cast
    field_simp
  · ring

end
end SlowEquilibration.SphericalMarkedWindows
