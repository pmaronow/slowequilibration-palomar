-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalSmoothCapHitRotation
public import SlowEquilibration.ConditionedEntranceSourceJointCapHitProbability
public import SlowEquilibration.ConditionedEntranceMixedSourceAxisFiring

/-! Exact finite-horizon cap-hit probability covariance for the source
posterior cutoff, at each prescribed disorder, axis, and spherical start. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalRotationCovariance
open SphericalSmoothParameter SphericalAging.HardSphereDynamics
open PhysicalHitting
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 1200000

variable {N : ℕ}

theorem sourceAxisCapHitProbability_rotated
    (hN : 1 ≤ N) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : Disorder N μ.maxDegree) (β α : ℝ)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ)
    (e k : ℝ) (H : ℝ≥0)
    (u x : Vector N) (hx : OnSphere x) :
    sourceAxisCapHitProbability μ hQ hnp (rotatedDisorder U J)
      β α χ hχ e k H (U u) (U x) =
    sourceAxisCapHitProbability μ hQ hnp J
      β α χ hχ e k H u x := by
  let g : Vector N × Vector N → Vector N :=
    jointSpatialGradient (fun z : Vector N × Vector N =>
      sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2)
  let g' : Vector N × Vector N → Vector N :=
    jointSpatialGradient (fun z : Vector N × Vector N =>
      sourceSmoothCutoffField μ Q hQ hnp (rotatedDisorder U J) z.1 e k α χ z.2)
  have hg : ContDiff ℝ 1 g :=
    mixedSourceAxisGradient_contDiff μ hQ hnp J α χ hχ e k
  have hg' : ContDiff ℝ 1 g' :=
    mixedSourceAxisGradient_contDiff μ hQ hnp (rotatedDisorder U J) α χ hχ e k
  have hgrad (v : Vector N) :
      g' (U u,U v) = U (g (u,v)) := by
    change gradient (sourceSmoothCutoffField μ Q hQ hnp (rotatedDisorder U J)
      (U u) e k α χ) (U v) =
      U (gradient (sourceSmoothCutoffField μ Q hQ hnp J u e k α χ) v)
    exact sourceSmoothCutoffGradient_rotated hN μ Q hQ hnp U J u v e k α χ hχ
  change capHitProbability β g' hg' H (α / 2)
      (U u,(U u,U x)) =
    capHitProbability β g hg H (α / 2)
      (u,(u,x))
  exact capHitProbability_rotation_at (by omega : N ≠ 0) U β g hg g' hg'
    u (U u) hgrad
    u x hx H (α / 2)

end SlowEquilibration.ConditionedEntrance
