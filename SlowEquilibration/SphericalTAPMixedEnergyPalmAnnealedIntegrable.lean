-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedEnergyPalmCoareaRatio

@[expose] public section

/-! The annealed latitude factor in the mixed energy-Palm coarea ratio is
continuous in the radial mark and hence integrable under the genuine compactly
supported all-critical radial law. -/

namespace SlowEquilibration.SphericalTAPMixedEnergyPalmAnnealedIntegrable
noncomputable section
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPMixedBandExponent
open SphericalTAPMixedJointCompactIntegrable
set_option autoImplicit false

theorem mixed_annealed_latitude_continuous
    (d : ℕ) (μ : FiniteMixture) (β Q e q b : ℝ) :
    Continuous (fun k : ℝ => ∫ a in Icc (q-b) (q+b),
      (Real.sqrt (1-a^2))^(d-1) *
        Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume) := by
  have hξ := sourceMixedXi_joint_continuous μ β Q e
  have hf : Continuous (fun z : ℝ × ℝ =>
      (Real.sqrt (1-z.2^2))^(d-1) *
        Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e z.1 z.2)) := by
    fun_prop
  exact continuous_parametric_integral_of_continuous hf isCompact_Icc

theorem mixed_annealed_latitude_integrable_palm
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (β e L R q b : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L) (hLR : L < R) :
    Integrable (fun k : ℝ => ∫ a in Icc (q-b) (q+b),
      (Real.sqrt (1-a^2))^(d-1) *
        Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume)
      (sourceAllCriticalRadialLaw d μ Q e L R) := by
  let G := fun k : ℝ => ∫ a in Icc (q-b) (q+b),
    (Real.sqrt (1-a^2))^(d-1) *
      Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume
  have hG : Continuous G := mixed_annealed_latitude_continuous d μ β Q e q b
  let : IsProbabilityMeasure (sourceAllCriticalRadialLaw d μ Q e L R) :=
    sourceAllCriticalRadialLaw_probability d μ hQ e hEdge hLR
  obtain ⟨C,hC⟩ : ∃ C : ℝ, ∀ x ∈ G '' Icc L R, ‖x‖ ≤ C :=
    ((isCompact_Icc.image hG).isBounded).exists_norm_le
  apply Integrable.of_bound hG.aestronglyMeasurable C
  filter_upwards [sourceAllCriticalRadialLaw_ae_mem d μ Q e L R] with k hk
  exact hC (G k) (mem_image_of_mem G ⟨hk.1.le,hk.2.le⟩)

end
end SlowEquilibration.SphericalTAPMixedEnergyPalmAnnealedIntegrable
