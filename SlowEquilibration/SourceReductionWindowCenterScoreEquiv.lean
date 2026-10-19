-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceReductionTrueCapPathWeight
public import SlowEquilibration.SphericalLocalMaxPhysicalIntensity

/-! Identifies the source's literal critical centers with the points in the
physical score-window marked Kac--Rice sum. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceReductionWindowCenterScoreEquiv
open Set SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalForm SphericalRotationCovariance
open SphericalAging.HardSphereDynamics
open SourceReductionClosedBandGraph
open SourceReductionFinitePathUnionBound
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 600000

variable {N : ℕ}

/-- The physical sphere center subtype is canonically the exact subtype
summed by `actualScoreWindowCount` for an unnormalized energy window. -/
def physicalWindowCentersScoreEquiv (hN : N ≠ 0)
    (μ : FiniteMixture) (Q m M : ℝ) (U : Set ℝ)
    (J : Disorder N μ.maxDegree) :
    physicalWindowCenters μ Q m M U J ≃
      {u : Vector N | ‖u‖^2=(N:ℝ) ∧
        surfaceGradient
          (field (centerCoefficients (mixtureCoefficients μ) Q) J) u=0 ∧
        actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u ∈
          physicalEnergyWindow N (Icc (m-M) (m+M)) U} where
  toFun u := by
    have hu := u.2
    change (J,u.1.1) ∈ windowCenterGraph μ Q m M U at hu
    rcases hu with ⟨⟨⟨hs,hg⟩,he⟩,hk⟩
    exact ⟨u.1.1,⟨hs,hg,
      (actualScore_mem_physicalEnergyWindow hN _ J u.1.1 _ _).mpr ⟨he,hk⟩⟩⟩
  invFun u := by
    rcases u.2 with ⟨hs,hg,hw⟩
    obtain ⟨he,hk⟩ :=
      (actualScore_mem_physicalEnergyWindow hN _ J u.1 _ _).mp hw
    exact ⟨⟨u.1,(onSphere_iff_norm_sq u.1).mpr hs⟩,
      ⟨⟨⟨hs,hg⟩,he⟩,hk⟩⟩
  left_inv u := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv u := by apply Subtype.ext; rfl

end SlowEquilibration.SourceReductionWindowCenterScoreEquiv
