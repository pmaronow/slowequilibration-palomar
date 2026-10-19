-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWienerRotation

/-! Orthogonal Wiener path rotations preserve the literal natural
Brownian filtration, pointwise rather than merely up to completion. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalWienerRotation

open SphericalModel SphericalAging MeasureTheory
open scoped NNReal

set_option autoImplicit false

theorem wienerVector_rotate {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (ω : VectorBrownian.Space N) (t : ℝ≥0) :
    wienerVector t (rotateWiener U ω) = U (wienerVector t ω) := by
  ext i
  rfl

@[simp] theorem rotateWiener_symm_rotate {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (ω : VectorBrownian.Space N) :
    rotateWiener U.symm (rotateWiener U ω) = ω := by
  funext i
  ext t
  simp only [rotateWiener_eval, wienerVector_rotate, U.symm_apply_apply]
  rfl

@[simp] theorem rotateWiener_rotate_symm {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (ω : VectorBrownian.Space N) :
    rotateWiener U (rotateWiener U.symm ω) = ω := by
  simpa only [LinearIsometryEquiv.symm_symm] using
    rotateWiener_symm_rotate U.symm ω

/-- Pulling back the natural filtration along the path rotation gives
exactly the same filtration, at every deterministic time. -/
theorem rotateWiener_filtration_eq {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (t : ℝ≥0) :
    (VectorBrownian.filtration N t).comap (rotateWiener U) =
      VectorBrownian.filtration N t := by
  apply le_antisymm
  · exact (rotateWiener_filtered_measurable U t).comap_le
  · have hback := (rotateWiener_filtered_measurable U.symm t).comap_le
    have h := MeasurableSpace.comap_mono (g := rotateWiener U) hback
    simpa only [MeasurableSpace.comap_comp, Function.comp_def,
      rotateWiener_symm_rotate,
      show (fun x : VectorBrownian.Space N => x) = id from rfl,
      MeasurableSpace.comap_id] using h

end SlowEquilibration.SphericalWienerRotation
