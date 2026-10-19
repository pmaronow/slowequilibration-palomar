-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalUniformComplexity

/-! Uniform pure complexity on its actual one-dimensional score support. -/
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

def valueNormalizationError (n : ℕ) (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  (Real.log (sphereKRPrefactor (n+1) μ Q).toReal / (n+2 : ℕ) -
    (1 - Real.log (Q * μ.xi1 Q))/2) +
  (Real.log (n+2 : ℕ) - Real.log (2 * Real.pi * μ.xi Q)) / (2 * (n+2 : ℕ))

lemma valueNormalizationError_tendsto (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    Tendsto (fun n => valueNormalizationError n μ Q) atTop (𝓝 0) := by
  have h := ((sphereKRPrefactor_log_rate μ hQ).sub_const ((1 - Real.log (Q * μ.xi1 Q))/2)).add
    ((log_dimension_div_tendsto.sub
      (constant_div_dimension_tendsto (Real.log (2 * Real.pi * μ.xi Q)))).div_const 2)
  convert h using 1
  · funext n
    unfold valueNormalizationError
    push_cast
    field_simp
  · simp

lemma pure_log_complexity_error (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q) (h : ℝ)
    (hh : 2 * Real.sqrt (Q^2 * (FiniteMixture.pure p hp alpha halpha).xi2 Q) < (p:ℝ)*h) :
    let μ := FiniteMixture.pure p hp alpha halpha
    Real.log (pureCriticalIntensity n p hp alpha halpha Q h).toReal / (n+2 : ℕ) -
        pureMarkedComplexity p hp alpha halpha Q h =
      valueNormalizationError n μ Q +
      (Real.log (physicalMean n (n+2) (Q^2 * μ.xi2 Q) ((p:ℝ)*h)) - (n+2 : ℕ) *
        (Real.log (Real.sqrt (Q^2 * μ.xi2 Q)) +
          SemicirclePotential.potential ((p:ℝ)*h / Real.sqrt (Q^2 * μ.xi2 Q)))) / (n+2 : ℕ) := by
  let μ := FiniteMixture.pure p hp alpha halpha
  have ha := mul_pos hQ (mixture_xi1_pos μ hQ)
  have hb := mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  dsimp only
  rw [pureCriticalIntensity_log n p hp alpha halpha hQ h hh,
    physicalValuePdf_log (n+2) (by omega) μ hQ h]
  change _ = valueNormalizationError n μ Q + _
  unfold pureMarkedComplexity valueNormalizationError
  change _ = (Real.log (sphereKRPrefactor (n+1) μ Q).toReal / (n+2 : ℕ) -
    (1 - Real.log (Q * μ.xi1 Q))/2) +
    (Real.log (n+2 : ℕ) - Real.log (2 * Real.pi * μ.xi Q)) / (2 * (n+2 : ℕ)) + _
  dsimp only [μ] at ha hb ⊢
  rw [Real.log_div hb.ne' ha.ne', Real.log_sqrt hb.le]
  push_cast
  field_simp
  ring

theorem actual_pure_complexity_uniform
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) {g Z ε : ℝ} (hg : 0 < g) (hε : 0 < ε) :
    let μ := FiniteMixture.pure p hp alpha halpha
    ∀ᶠ n : ℕ in atTop, ∀ h : ℝ,
      (p:ℝ)*h ∈ Icc (2 * Real.sqrt (Q^2 * μ.xi2 Q) + g) Z →
      |Real.log (pureCriticalIntensity n p hp alpha halpha Q h).toReal / (n+2 : ℕ) -
        pureMarkedComplexity p hp alpha halpha Q h| < ε := by
  let μ := FiniteMixture.pure p hp alpha halpha
  obtain ⟨B,hB,hmean⟩ := physicalMean_log_error_bound (Z := Z)
    (mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)) hg
  have hs := (valueNormalizationError_tendsto μ hQ).abs.add (constant_div_dimension_tendsto B)
  simp only [abs_zero, add_zero] at hs
  filter_upwards [hs.eventually (gt_mem_nhds hε)] with n hn
  intro h hh
  rw [pure_log_complexity_error n p hp alpha halpha hQ h (by linarith [hh.1])]
  have hN : (0:ℝ) < (n+2 : ℕ) := by positivity
  calc
    _ ≤ |valueNormalizationError n μ Q| +
        |(Real.log (physicalMean n (n+2) (Q^2 * μ.xi2 Q) ((p:ℝ)*h)) - (n+2 : ℕ) *
          (Real.log (Real.sqrt (Q^2 * μ.xi2 Q)) +
            SemicirclePotential.potential ((p:ℝ)*h / Real.sqrt (Q^2 * μ.xi2 Q)))) / (n+2 : ℕ)| :=
      abs_add_le _ _
    _ ≤ |valueNormalizationError n μ Q| + B / (n+2 : ℕ) := by
      rw [abs_div, abs_of_pos hN]
      exact add_le_add_right (div_le_div_of_nonneg_right (hmean n ((p:ℝ)*h) hh) hN.le) _
    _ < ε := by simpa only [Nat.cast_add, Nat.cast_ofNat] using hn

end
end SlowEquilibration.SphericalMarkedWindows
