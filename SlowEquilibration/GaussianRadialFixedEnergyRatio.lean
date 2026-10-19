-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.GaussianRadialTiltMoment
public import SlowEquilibration.RadialExponentialPerturbation

/-! Exact fixed-energy increment ratios are controlled by actual
normalized radial moments. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianRadialEnergyTilt
open Set MeasureTheory
set_option maxHeartbeats 300000

def fixedTiltFactor (N A c₀ σ t : ℝ) : ℝ :=
  Real.exp (-c₀*t-A*σ*t/N-A*t^2/(2*N))

theorem tiltedDensity_fixed_increment {N : ℝ} (hN : 0 < N)
    (w : ℝ → ℝ) (A B c₀ m σ t k : ℝ) :
    tiltedDensity w N A B c₀ m (σ+t) k=
      fixedTiltFactor N A c₀ σ t*(tiltedDensity w N A B c₀ m σ k*Real.exp (-(B*t)*(k-m))) := by
  have he : Real.exp (-c₀*(σ+t)-B*(k-m)*(σ+t)-A*(σ+t)^2/(2*N))=
      Real.exp (-c₀*t-A*σ*t/N-A*t^2/(2*N))*
        Real.exp (-c₀*σ-B*(k-m)*σ-A*σ^2/(2*N))*Real.exp (-(B*t)*(k-m)) := by
    rw [←Real.exp_add,←Real.exp_add]
    congr 1
    field_simp [hN.ne']
    ring
  unfold tiltedDensity fixedTiltFactor
  rw [he]
  ring

theorem energyDensity_fixed_increment {N : ℝ} (hN : 0 < N)
    (w : ℝ → ℝ) (U : Set ℝ) (A B c₀ m σ t : ℝ) :
    energyDensity w U N A B c₀ m (σ+t)=fixedTiltFactor N A c₀ σ t*
      (∫ k in U,tiltedDensity w N A B c₀ m σ k*Real.exp (-(B*t)*(k-m))) := by
  unfold energyDensity
  rw [←integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (tiltedDensity_fixed_increment hN w A B c₀ m σ t)

theorem fixed_energy_ratio_error {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    {N A B c₀ m M σ t : ℝ} (hN : 0 < N)
    (hi : IntegrableOn (tiltedDensity w N A B c₀ m σ) U) (h0 : ∀ k∈U,0 ≤ w k)
    (hRadius : ∀ k∈U,|k-m| ≤ M) (hMass : 0 < energyDensity w U N A B c₀ m σ) :
    |energyDensity w U N A B c₀ m (σ+t)/energyDensity w U N A B c₀ m σ-
      fixedTiltFactor N A c₀ σ t| ≤
      fixedTiltFactor N A c₀ σ t*(Real.exp (|B*t| * M)*|B*t|)*
        (radialMoment w U N A B c₀ m σ/energyDensity w U N A B c₀ m σ) := by
  have hh := RadialExponentialPerturbation.radial_exp_normalized_error hU hi
    (fun k hk => mul_nonneg (h0 k hk) (Real.exp_pos _).le) hRadius (-(B*t)) hMass
  simp only [abs_neg] at hh
  have he : energyDensity w U N A B c₀ m (σ+t)/energyDensity w U N A B c₀ m σ-
      fixedTiltFactor N A c₀ σ t=fixedTiltFactor N A c₀ σ t*
      ((∫ k in U,tiltedDensity w N A B c₀ m σ k*Real.exp (-(B*t)*(k-m)))/
        energyDensity w U N A B c₀ m σ-1) := by
    rw [energyDensity_fixed_increment hN]
    ring
  have hfactorPos : 0 < fixedTiltFactor N A c₀ σ t := Real.exp_pos _
  rw [he,abs_mul,abs_of_pos hfactorPos]
  simpa only [radialMoment,energyDensity,mul_assoc] using
    (mul_le_mul_of_nonneg_left hh hfactorPos.le)

end SlowEquilibration.GaussianRadialEnergyTilt
