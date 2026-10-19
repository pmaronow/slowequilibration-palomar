-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.GaussianRadialFixedEnergyRatio
public import SlowEquilibration.NatLogSequenceScales

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianRadialEnergyTilt
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 300000

theorem fixedTiltFactor_tendsto {D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop,|σ n| ≤ D*Real.log (n+2 : ℕ)) (A c₀ t : ℝ) :
    Tendsto (fun n : ℕ => fixedTiltFactor (n+2 : ℕ) A c₀ (σ n) t)
      atTop (𝓝 (Real.exp (-c₀*t))) := by
  have hσzero := NatLogWindowScales.log_bounded_sequence_div_dimension_tendsto_zero hD σ hσ
  have hInv : Tendsto (fun n : ℕ => 1/((n+2 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [pow_zero] using NatLogWindowScales.log_power_div_dimension_tendsto_zero 0
  have hExponent : Tendsto (fun n : ℕ => -c₀*t-(A*t)*(σ n/(n+2 : ℕ))-
      (A*t^2/2)*(1/(n+2 : ℕ))) atTop (𝓝 (-c₀*t)) := by
    simpa only [mul_zero,sub_zero] using
      ((tendsto_const_nhds.sub (hσzero.const_mul (A*t))).sub (hInv.const_mul (A*t^2/2)))
  convert Real.continuous_exp.continuousAt.tendsto.comp hExponent using 1
  funext n
  unfold fixedTiltFactor
  congr 1
  field_simp

theorem fixed_energy_ratio_tendsto {U : Set ℝ} (hU : MeasurableSet U) (w : ℕ → ℝ → ℝ)
    {A B c₀ m M D : ℝ} (hD : 0 ≤ D) (σ : ℕ → ℝ)
    (hσ : ∀ᶠ n : ℕ in atTop,|σ n| ≤ D*Real.log (n+2 : ℕ))
    (hi : ∀ᶠ n : ℕ in atTop,IntegrableOn (tiltedDensity (w n) (n+2 : ℕ) A B c₀ m (σ n)) U)
    (h0 : ∀ n : ℕ,∀ k∈U,0 ≤ w n k) (hRadius : ∀ k∈U,|k-m| ≤ M)
    (hMass : ∀ᶠ n : ℕ in atTop,0 < energyDensity (w n) U (n+2 : ℕ) A B c₀ m (σ n))
    (hMoment : Tendsto (fun n : ℕ => radialMoment (w n) U (n+2 : ℕ) A B c₀ m (σ n)/
      energyDensity (w n) U (n+2 : ℕ) A B c₀ m (σ n)) atTop (𝓝 (0 : ℝ))) (t : ℝ) :
    Tendsto (fun n : ℕ => energyDensity (w n) U (n+2 : ℕ) A B c₀ m (σ n+t)/
      energyDensity (w n) U (n+2 : ℕ) A B c₀ m (σ n)) atTop (𝓝 (Real.exp (-c₀*t))) := by
  have hFactor := fixedTiltFactor_tendsto hD σ hσ A c₀ t
  have hUpper : Tendsto (fun n : ℕ => fixedTiltFactor (n+2 : ℕ) A c₀ (σ n) t*
      (Real.exp (|B*t| * M)*|B*t|)*(radialMoment (w n) U (n+2 : ℕ) A B c₀ m (σ n)/
        energyDensity (w n) U (n+2 : ℕ) A B c₀ m (σ n))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using (hFactor.mul_const (Real.exp (|B*t| * M)*|B*t|)).mul hMoment
  have hErr : Tendsto (fun n : ℕ => energyDensity (w n) U (n+2 : ℕ) A B c₀ m (σ n+t)/
      energyDensity (w n) U (n+2 : ℕ) A B c₀ m (σ n)-fixedTiltFactor (n+2 : ℕ) A c₀ (σ n) t)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero_norm' _ hUpper
    filter_upwards [hi,hMass] with n hn hMn
    rw [Real.norm_eq_abs]
    exact fixed_energy_ratio_error hU (by positivity) hn (h0 n) hRadius hMn
  simpa only [zero_add,sub_add_cancel] using hErr.add hFactor

end SlowEquilibration.GaussianRadialEnergyTilt
