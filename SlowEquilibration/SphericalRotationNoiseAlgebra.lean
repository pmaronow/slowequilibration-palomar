-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceDriftRotation

/-! The physical spherical noise matrix transforms equivariantly under
orthogonal rotations. These are deterministic identities, independent of
the driving Brownian probability space. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalRotationCovariance
open SphericalModel SphericalForm
open SphericalAging.HardSphereDynamics SphericalAging.LocalSDE
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000
variable {N : ℕ}

theorem noiseColumn_rotated_sum (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (x : Vector N) (i : Fin N) :
    (∑ j : Fin N, (U (basisVector i)) j • noiseColumn (U x) j) =
      U (noiseColumn x i) := by
  have hsum := state_sum_basis (U (basisVector i))
  have hlin :
      (∑ j : Fin N, (U (basisVector i)) j • noiseColumn (U x) j) =
      Real.sqrt 2 • projection (U x) (U (basisVector i)) := by
    calc
      _ = Real.sqrt 2 •
          (∑ j : Fin N, (U (basisVector i)) j • projection (U x) (basisVector j)) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        change (U (basisVector i)) j •
            (Real.sqrt 2 • projection (U x) (basisVector j)) =
          Real.sqrt 2 • ((U (basisVector i)) j • projection (U x) (basisVector j))
        exact smul_comm _ _ _
      _ = Real.sqrt 2 • projection (U x)
          (∑ j : Fin N, (U (basisVector i)) j • basisVector j) := by
        congr 1
        simp only [← tangentProjection_apply]
        rw [map_sum]
        simp only [map_smul]
      _ = _ := by rw [hsum]
  rw [hlin]
  simp only [noiseColumn, map_smul, projection_map]

theorem noiseColumn_rotated_matrix (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (x : Vector N) (i k : Fin N) :
    ∑ j : Fin N, (U (basisVector i)) j * (noiseColumn (U x) j) k =
      (U (noiseColumn x i)) k := by
  calc
    _ = (∑ j : Fin N, (U (basisVector i)) j • noiseColumn (U x) j) k := by
      simp [Finset.sum_apply, smul_eq_mul]
    _ = _ := congrArg (fun v : Vector N => v k) (noiseColumn_rotated_sum U x i)

end SlowEquilibration.SphericalRotationCovariance
