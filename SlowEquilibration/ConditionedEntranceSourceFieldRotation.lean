-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothStationarity
public import SlowEquilibration.SphericalRotationCovariance

/-! Rotation covariance of the literal mixed posterior regression correction
and its smooth cutoff Hamiltonian. All center observations are recomputed
from the rotated disorder; they are not free marks. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalRotationCovariance
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 900000
variable {N : ℕ}

theorem sourceCenterGradient_rotated (μ : FiniteMixture) (Q : ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : Disorder N μ.maxDegree)
    (u : Vector N) :
    surfaceGradient
        (field (centerCoefficients (mixtureCoefficients μ) Q) (rotatedDisorder U J))
        (U u) =
      U (surfaceGradient
        (field (centerCoefficients (mixtureCoefficients μ) Q) J) u) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have heq : field c (rotatedDisorder U J) =
      fun x => field c J (U.symm x) :=
    funext (field_precomp_rotation c U J)
  have hf : Differentiable ℝ (field c J) :=
    (field_contDiff c J).differentiable (by norm_num)
  rw [heq]
  have h := surfaceGradient_comp_rotation U.symm hf (U u)
  simpa only [LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply] using h

theorem sourceCenterJet_rotated (μ : FiniteMixture) (Q : ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : Disorder N μ.maxDegree)
    (u : Vector N) :
    jet (centerCoefficients (mixtureCoefficients μ) Q) 1 (U u)
        (fun _ => U u) (rotatedDisorder U J) =
      jet (centerCoefficients (mixtureCoefficients μ) Q) 1 u
        (fun _ => u) J := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have heq : field c (rotatedDisorder U J) =
      fun x => field c J (U.symm x) :=
    funext (field_precomp_rotation c U J)
  have hf : Differentiable ℝ (field c J) :=
    (field_contDiff c J).differentiable (by norm_num)
  simp only [jet, iteratedFDeriv_one_apply]
  rw [← inner_gradient_left, ← inner_gradient_left]
  rw [heq, gradient_comp_rotation U.symm hf (U u)]
  simp only [LinearIsometryEquiv.symm_symm,
    LinearIsometryEquiv.symm_apply_apply, U.inner_map_map, c]

theorem sourceRegressionCorrection_rotated (μ : FiniteMixture) (Q : ℝ)
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : Disorder N μ.maxDegree)
    (u x : Vector N) (e k : ℝ) :
    sourceRegressionCorrection μ Q hQ hnp (rotatedDisorder U J)
        (U u) e k (U x) =
      sourceRegressionCorrection μ Q hQ hnp J u e k x := by
  unfold sourceRegressionCorrection regressionCorrection
  rw [sourceCenterGradient_rotated μ Q U J u,
    sourceCenterJet_rotated μ Q U J u]
  rw [field_rotated]
  simp only [overlap, U.inner_map_map]

/-- The actual smooth posterior field transports with the physical tensor
rotation, for every cutoff and every pair of prescribed marks. -/
theorem sourceSmoothCutoffField_rotated (μ : FiniteMixture) (Q : ℝ)
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : Disorder N μ.maxDegree)
    (u x : Vector N) (e k α : ℝ) (χ : ℝ → ℝ) :
    sourceSmoothCutoffField μ Q hQ hnp (rotatedDisorder U J)
        (U u) e k α χ (U x) =
      sourceSmoothCutoffField μ Q hQ hnp J u e k α χ x := by
  rw [sourceSmoothCutoffField_eq, sourceSmoothCutoffField_eq]
  change field (mixtureCoefficients μ) (rotatedDisorder U J) (U x) + _ =
    field (mixtureCoefficients μ) J x + _
  rw [field_rotated,
    sourceCenterGradient_rotated μ Q U J u,
    sourceRegressionCorrection_rotated μ Q hQ hnp U J u x e k]
  simp only [overlap, U.inner_map_map]

end SlowEquilibration.ConditionedEntrance
