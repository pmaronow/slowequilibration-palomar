-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedQuadraticRealTransfer
public import SlowEquilibration.SphericalTAPMixedJointCompactIntegrable

@[expose] public section

/-! Shrinking a physical latitude band preserves the source mixed joint
Laplace upper estimate. This lets the analytic Laplace band and the quadratic
correlation band be chosen simultaneously. -/

namespace SlowEquilibration.SphericalTAPMixedSourceBandShrink
noncomputable section
open Set MeasureTheory StrongFieldComplexity SphericalModel SphericalMarkedWindows
open SphericalTAPMixedSourceLaplaceRatio SphericalTAPMixedPhysicalJointLaplace
open SphericalTAPMixedPhysicalChi SphericalTAPMixedJointCompactIntegrable
set_option autoImplicit false

theorem sourceMixedJointLaplace_mono_band
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (β e L R q b₁ b₂ : ℝ)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L)
    (hLR : L < R) (hb₂ : 0 < b₂)
    (hbb : b₁ ≤ b₂)
    (hband : Icc (q-b₂) (q+b₂) ⊆ Ioo (0:ℝ) 1) :
    sourceMixedJointLaplace d μ β Q e L R q b₁ ≤
      sourceMixedJointLaplace d μ β Q e L R q b₂ := by
  let S₁ := (Icc L R) ×ˢ (Icc (q-b₁) (q+b₁))
  let S₂ := (Icc L R) ×ˢ (Icc (q-b₂) (q+b₂))
  have hsub : S₁ ⊆ S₂ := by
    intro z hz
    exact ⟨hz.1,⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩⟩
  obtain ⟨cχ,Cχ,hcχ,hCχ,hχ⟩ := sourceMixedChi_bounds μ hQ hEdge
  have hnn : ∀ z ∈ S₂, 0 ≤ sourceMixedJointIntegrand d μ β Q e z := by
    intro z hz
    have hχ0 : 0 ≤ sourceMixedChi d μ Q z.1 :=
      (hcχ.trans_le (hχ d z.1 hz.1).1).le
    have ha : z.2 ∈ Ioo (0:ℝ) 1 := hband hz.2
    unfold sourceMixedJointIntegrand
    exact mul_nonneg (mul_nonneg hχ0 (Real.rpow_nonneg (by nlinarith [ha.1,ha.2]) _))
      (Real.exp_pos _).le
  have hInt := sourceMixedJointIntegrand_integrableOn_compact
    d μ hQ β e L R q b₂ hEdge hLR hb₂ hband
  change (∫ z in S₁, sourceMixedJointIntegrand d μ β Q e z ∂planeVolume) ≤
    (∫ z in S₂, sourceMixedJointIntegrand d μ β Q e z ∂planeVolume)
  exact setIntegral_mono_set hInt
    (ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) hnn)
    (Filter.Eventually.of_forall (fun z hz => hsub hz))

end
end SlowEquilibration.SphericalTAPMixedSourceBandShrink
