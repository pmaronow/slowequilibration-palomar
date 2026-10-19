-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalScoreDensityRates

/-! Genuine determinant/Gaussian logarithmic rates of the actual count intensities. -/
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

lemma mixedCriticalIntensity_log (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : 2 * Real.sqrt (Q^2 * μ.xi2 Q) < z 1) :
    Real.log (mixedCriticalIntensity n μ Q z).toReal =
      Real.log (sphereKRPrefactor (n+1) μ Q).toReal +
      Real.log (physicalScorePdf (n+2) μ Q z).toReal +
      Real.log (physicalMean n (n+2) (Q^2 * μ.xi2 Q) (z 1)) := by
  have hp := ENNReal.toReal_pos (sphereKRPrefactor_ne_zero (n+1) μ hQ)
    (sphereKRPrefactor_ne_top (n+1) μ Q)
  have hd := physicalScorePdf_toReal_pos (n+2) (by omega) μ hQ hnp z
  have hm := physicalMean_pos n 1 (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hz
  rw [mixedCriticalIntensity, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hm.le, Real.log_mul (mul_pos hp hd).ne' hm.ne',
    Real.log_mul hp.ne' hd.ne']

/-- The actual mixed count intensity has the Gaussian quadratic and ordinary
GOE determinant exponent, with the exact geometric prefactor explicitly removed. -/
theorem mixedCriticalIntensity_log_rate_relative_geometry (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : 2 * Real.sqrt (Q^2 * μ.xi2 Q) < z 1) :
    Tendsto (fun n : ℕ =>
      (Real.log (mixedCriticalIntensity n μ Q z).toReal -
        Real.log (sphereKRPrefactor (n+1) μ Q).toReal) / (n+2 : ℕ)) atTop
      (𝓝 (Real.log (Real.sqrt (Q^2 * μ.xi2 Q)) +
        SemicirclePotential.potential (z 1 / Real.sqrt (Q^2 * μ.xi2 Q)) -
        scoreQuadratic μ Q z / 2)) := by
  have h := (physicalScorePdf_log_rate μ hQ hnp z).add
    (physical_log_mean_per_ambient_tendsto 1 (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hz)
  convert h using 1
  · funext n
    rw [mixedCriticalIntensity_log n μ hQ hnp z hz]
    ring
  · ring

lemma pureCriticalIntensity_log (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q) (h : ℝ)
    (hh : 2 * Real.sqrt (Q^2 * (FiniteMixture.pure p hp alpha halpha).xi2 Q) < (p:ℝ)*h) :
    let μ := FiniteMixture.pure p hp alpha halpha
    Real.log (pureCriticalIntensity n p hp alpha halpha Q h).toReal =
      Real.log (sphereKRPrefactor (n+1) μ Q).toReal +
      Real.log (physicalValuePdf (n+2) μ Q h).toReal +
      Real.log (physicalMean n (n+2) (Q^2 * μ.xi2 Q) ((p:ℝ)*h)) := by
  let μ := FiniteMixture.pure p hp alpha halpha
  have hpf := ENNReal.toReal_pos (sphereKRPrefactor_ne_zero (n+1) μ hQ)
    (sphereKRPrefactor_ne_top (n+1) μ Q)
  have hd := physicalValuePdf_toReal_pos (n+2) (by omega) μ hQ h
  have hm := physicalMean_pos n 1 (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hh
  dsimp only
  rw [pureCriticalIntensity, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hm.le, Real.log_mul (mul_pos hpf hd).ne' hm.ne',
    Real.log_mul hpf.ne' hd.ne']

/-- The pure analogue uses the true scalar Gaussian rate and the proper radial
shift `p*h`; it does not introduce a singular two-dimensional density. -/
theorem pureCriticalIntensity_log_rate_relative_geometry
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) (h : ℝ)
    (hh : 2 * Real.sqrt (Q^2 * (FiniteMixture.pure p hp alpha halpha).xi2 Q) < (p:ℝ)*h) :
    let μ := FiniteMixture.pure p hp alpha halpha
    Tendsto (fun n : ℕ =>
      (Real.log (pureCriticalIntensity n p hp alpha halpha Q h).toReal -
        Real.log (sphereKRPrefactor (n+1) μ Q).toReal) / (n+2 : ℕ)) atTop
      (𝓝 (Real.log (Real.sqrt (Q^2 * μ.xi2 Q)) +
        SemicirclePotential.potential ((p:ℝ)*h / Real.sqrt (Q^2 * μ.xi2 Q)) -
        h^2 / (2 * μ.xi Q))) := by
  let μ := FiniteMixture.pure p hp alpha halpha
  have hc := (physicalValuePdf_log_rate μ hQ h).add
    (physical_log_mean_per_ambient_tendsto 1 (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hh)
  dsimp only [μ] at hc ⊢
  convert hc using 1
  · funext n
    rw [pureCriticalIntensity_log n p hp alpha halpha hQ h hh]
    ring
  · ring

end
end SlowEquilibration.SphericalMarkedWindows
