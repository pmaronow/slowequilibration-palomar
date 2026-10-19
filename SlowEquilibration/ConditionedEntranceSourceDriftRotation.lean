-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceFieldRotation
public import SlowEquilibration.SphericalC1Dynamics

/-! The intrinsic source drift inherits exact covariance from the actual
posterior cutoff Hamiltonian, including its observed center gradient. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SphericalRotationCovariance
open SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 900000
variable {N : ℕ}

theorem sourceSmoothCutoffGradient_rotated (hN : 1 ≤ N)
    (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : Disorder N μ.maxDegree)
    (u x : Vector N) (e k α : ℝ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ 2 χ) :
    gradient (sourceSmoothCutoffField μ Q hQ hnp (rotatedDisorder U J)
        (U u) e k α χ) (U x) =
      U (gradient (sourceSmoothCutoffField μ Q hQ hnp J u e k α χ) x) := by
  let H := sourceSmoothCutoffField μ Q hQ hnp J u e k α χ
  have heq : sourceSmoothCutoffField μ Q hQ hnp (rotatedDisorder U J)
      (U u) e k α χ = fun y => H (U.symm y) := by
    funext y
    simpa only [H, U.apply_symm_apply] using
      sourceSmoothCutoffField_rotated μ Q hQ hnp U J u (U.symm y) e k α χ
  have hf : Differentiable ℝ H :=
    (sourceSmoothCutoffField_contDiff hN μ Q hQ hnp J u e k α χ hχ).differentiable
      (by norm_num)
  rw [heq, gradient_comp_rotation U.symm hf (U x)]
  simp [H]

theorem sourceSmoothCutoffDrift_rotated (hN : 1 ≤ N)
    (μ : FiniteMixture) (Q : ℝ) (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : Disorder N μ.maxDegree)
    (u x : Vector N) (e k α β : ℝ) (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ 2 χ) :
    drift β (gradient (sourceSmoothCutoffField μ Q hQ hnp (rotatedDisorder U J)
        (U u) e k α χ)) (U x) =
      U (drift β (gradient (sourceSmoothCutoffField μ Q hQ hnp J u e k α χ)) x) := by
  simp only [drift, sourceSmoothCutoffGradient_rotated hN μ Q hQ hnp U J u x e k α χ hχ,
    ← projection_map, map_sub, map_smul]

end SlowEquilibration.ConditionedEntrance
