-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCountIntensityRates
public import SlowEquilibration.SphericalGeometricPrefactorRates

/-! Actual one-point marked critical-count complexity at fixed exterior scores. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open Filter Function
open SphericalModel SphericalGaussianJet SphericalSequentialRegression WholeFieldRegression
open scoped ENNReal Topology
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The manuscript's actual mixed marked complexity. -/
def markedComplexity (μ : FiniteMixture) (Q : ℝ) (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  1/2 + Real.log ((Q^2 * μ.xi2 Q)/(Q * μ.xi1 Q))/2 - scoreQuadratic μ Q z/2 +
    SemicirclePotential.potential (z 1 / Real.sqrt (Q^2 * μ.xi2 Q))

/-- The literal physical intensity appearing in the exact critical-count
formula has logarithmic rate Θ, with every geometric/Gaussian/GOE factor derived. -/
theorem actual_mixed_critical_intensity_log_rate (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (z : EuclideanSpace ℝ (Fin 2)) (hz : 2 * Real.sqrt (Q^2 * μ.xi2 Q) < z 1) :
    Tendsto (fun n : ℕ => Real.log (mixedCriticalIntensity n μ Q z).toReal / (n+2 : ℕ))
      atTop (𝓝 (markedComplexity μ Q z)) := by
  have ha := mul_pos hQ (mixture_xi1_pos μ hQ)
  have hb := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have h := (mixedCriticalIntensity_log_rate_relative_geometry μ hQ hnp z hz).add
    (sphereKRPrefactor_log_rate μ hQ)
  convert h using 1
  · funext n
    ring
  · unfold markedComplexity
    rw [Real.log_sqrt hb.le, Real.log_div hb.ne' ha.ne']
    congr 1
    ring

/-- Proper pure complexity, on its actual one-dimensional score support. -/
def pureMarkedComplexity (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q h : ℝ) : ℝ :=
  let μ := FiniteMixture.pure p hp alpha halpha
  1/2 + Real.log ((Q^2 * μ.xi2 Q)/(Q * μ.xi1 Q))/2 - h^2/(2 * μ.xi Q) +
    SemicirclePotential.potential ((p:ℝ)*h / Real.sqrt (Q^2 * μ.xi2 Q))

/-- The actual pure critical-point intensity has its scalar marked complexity
rate; both the Hessian shift and Gaussian value density are the proper pure ones. -/
theorem actual_pure_critical_intensity_log_rate
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) (h : ℝ)
    (hh : 2 * Real.sqrt (Q^2 * (FiniteMixture.pure p hp alpha halpha).xi2 Q) < (p:ℝ)*h) :
    Tendsto (fun n : ℕ => Real.log (pureCriticalIntensity n p hp alpha halpha Q h).toReal / (n+2 : ℕ))
      atTop (𝓝 (pureMarkedComplexity p hp alpha halpha Q h)) := by
  let μ := FiniteMixture.pure p hp alpha halpha
  have ha := mul_pos hQ (mixture_xi1_pos μ hQ)
  have hb := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hc := (pureCriticalIntensity_log_rate_relative_geometry p hp alpha halpha hQ h hh).add
    (sphereKRPrefactor_log_rate μ hQ)
  convert hc using 1
  · funext n
    ring
  · change 𝓝 (1/2 + Real.log ((Q^2 * μ.xi2 Q)/(Q * μ.xi1 Q))/2 - h^2/(2 * μ.xi Q) +
        SemicirclePotential.potential ((p:ℝ)*h / Real.sqrt (Q^2 * μ.xi2 Q))) = _
    rw [Real.log_sqrt hb.le, Real.log_div hb.ne' ha.ne']
    congr 1
    ring

end
end SlowEquilibration.SphericalMarkedWindows
