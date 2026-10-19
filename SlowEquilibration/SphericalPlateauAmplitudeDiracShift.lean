-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeDiracTrial
public import SlowEquilibration.SphericalPlateauAmplitudeScalars

@[expose] public section

/-! # Source coefficients of the actual fixed-atom bank trial

The selected literal tensor coefficient is the square of the source
latitude amplitude. Its trial shift has the exact source formula and is
strictly positive at the source maximizer for both transverse probes.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set SphericalModel
open SphericalPlateauAmplitudeScalars
open scoped Topology
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem amplitudeSelectedCoefficient_eq_amplitudeSq (μ : FiniteMixture)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) (r : ℝ) :
    amplitudeSelectedCoefficient μ p₀ k r=
      amplitudeSq (mixtureCoefficients μ p₀) p₀.val.val (k.val+1) r := rfl

theorem amplitudeSelectedCoefficient_eq_amplitude_sq (μ : FiniteMixture)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) {r : ℝ} (hr : |r|≤1) :
    amplitudeSelectedCoefficient μ p₀ k r=
      (amplitude (mixtureCoefficients μ p₀) p₀.val.val (k.val+1) r)^2 := by
  rw [amplitudeSelectedCoefficient_eq_amplitudeSq]
  exact (amplitude_sq_eq (mixtureCoefficients_nonnegative μ p₀) hr _ _).symm

theorem amplitudeDiracShiftCoefficient_eq_source (μ : FiniteMixture) (β : ℝ)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) (r : ℝ) :
    amplitudeDiracShiftCoefficient μ β p₀ k r=
      trialShiftCoefficient β (mixtureCoefficients μ p₀) p₀.val.val (k.val+1) r := rfl

theorem amplitudeDiracShiftCoefficient_eq_amplitude_sq (μ : FiniteMixture) (β : ℝ)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) {r : ℝ} (hr : |r|≤1) :
    amplitudeDiracShiftCoefficient μ β p₀ k r=
      (β^2/2)*(amplitude (mixtureCoefficients μ p₀) p₀.val.val (k.val+1) r)^2*
        (1-(amplitudeDiracAtom r)^(k.val+1)) := by
  unfold amplitudeDiracShiftCoefficient
  rw [amplitudeSelectedCoefficient_eq_amplitude_sq μ p₀ k hr]

theorem amplitudeDiracShiftCoefficient_continuous (μ : FiniteMixture) (β : ℝ)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) :
    Continuous (amplitudeDiracShiftCoefficient μ β p₀ k) :=
  trialShiftCoefficient_continuous β (mixtureCoefficients μ p₀) p₀.val.val (k.val+1)

theorem amplitudeDiracShiftCoefficient_nonneg (μ : FiniteMixture) (β : ℝ)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) {r : ℝ} (hr : |r|≤1) :
    0≤amplitudeDiracShiftCoefficient μ β p₀ k r :=
  trialShiftCoefficient_nonneg (mixtureCoefficients_nonnegative μ p₀) hr _ _

theorem amplitudeDiracShiftCoefficient_pos (μ : FiniteMixture) {β : ℝ} (hβ : β≠0)
    (p₀ : Degree μ.maxDegree) (hp₀ : 0 < mixtureCoefficients μ p₀) (k : Fin 2)
    {r : ℝ} (hr : r∈Ioo (0 : ℝ) 1) :
    0<amplitudeDiracShiftCoefficient μ β p₀ k r := by
  apply trialShiftCoefficient_pos hβ hp₀ hr
  · omega
  · have hp := p₀.property
    have hk := k.isLt
    omega

theorem twice_amplitudeDiracShiftCoefficient (μ : FiniteMixture) (β : ℝ)
    (p₀ : Degree μ.maxDegree) (k : Fin 2) {r : ℝ} (hr : 0≤r) :
    2*amplitudeDiracShiftCoefficient μ β p₀ k r=
      β^2*amplitudeSelectedCoefficient μ p₀ k r*(1-(r/(1+r))^(k.val+1)) :=
  twice_trialShiftCoefficient_of_nonneg β (mixtureCoefficients μ p₀) p₀.val.val (k.val+1) hr

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
