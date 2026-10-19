-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalModel
public import Mathlib.Probability.Process.FiniteDimensionalLaws

/-! Orthogonal rotation of the canonical finite vector of continuous
Brownian paths. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalWienerRotation

open SphericalModel SphericalAging MeasureTheory ProbabilityTheory
open scoped Topology NNReal

set_option autoImplicit false
set_option linter.style.haveILetI false

def wienerVector {N : ℕ} (t : ℝ≥0)
    (ω : VectorBrownian.Space N) : Vector N :=
  WithLp.toLp 2 (fun i => ω i t)

theorem wienerVector_continuous {N : ℕ} (ω : VectorBrownian.Space N) :
    Continuous (fun t => wienerVector t ω) := by
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => (ω j).continuous)

theorem wienerVector_measurable {N : ℕ} (t : ℝ≥0) :
    Measurable (wienerVector (N := N) t) := by
  exact (PiLp.continuous_toLp 2 _).measurable.comp
    (measurable_pi_iff.mpr fun j => VectorBrownian.coordinate_measurable j t)

def rotateWiener {N : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (ω : VectorBrownian.Space N) : VectorBrownian.Space N :=
  fun i => ⟨fun t => (U (wienerVector t ω)) i,
    ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp
      (U.continuous.comp (wienerVector_continuous ω)))⟩

@[simp] theorem rotateWiener_eval {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (ω : VectorBrownian.Space N)
    (i : Fin N) (t : ℝ≥0) :
    rotateWiener U ω i t = (U (wienerVector t ω)) i := rfl

theorem rotateWiener_measurable {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) :
    Measurable (rotateWiener U) := by
  apply measurable_pi_iff.mpr
  intro i
  rw [ProbabilityTheory.ContinuousMap.measurable_iff_eval]
  intro t
  exact (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable.comp
    (U.continuous.measurable.comp (wienerVector_measurable t))

theorem wienerVector_past_measurable {N : ℕ} {s t : ℝ≥0} (hst : s ≤ t) :
    @Measurable _ _ (VectorBrownian.filtration N t) inferInstance
      (wienerVector (N := N) s) := by
  have hcoord (i : Fin N) :
      @Measurable _ _ (VectorBrownian.filtration N t) inferInstance
        (fun ω : VectorBrownian.Space N => ω i s) :=
    ((VectorBrownian.coordinate_stronglyAdapted i s).mono
      ((VectorBrownian.filtration N).mono hst)).measurable
  have hpi : @Measurable _ _ (VectorBrownian.filtration N t) inferInstance
      (fun ω : VectorBrownian.Space N => fun i : Fin N => ω i s) := by
    letI : MeasurableSpace (VectorBrownian.Space N) := VectorBrownian.filtration N t
    exact measurable_pi_iff.mpr hcoord
  exact (PiLp.continuous_toLp 2 _).measurable.comp hpi

/-- Rotating paths up to time `t` uses only the Brownian history up to `t`. -/
theorem rotateWiener_filtered_measurable {N : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (t : ℝ≥0) :
    @Measurable _ _ (VectorBrownian.filtration N t) (VectorBrownian.filtration N t)
      (rotateWiener U) := by
  apply Measurable.of_comap_le
  rw [VectorBrownian.filtration, Filtration.natural]
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup₂_le fun s hs => ?_
  have hm : @Measurable _ _ (VectorBrownian.filtration N t) inferInstance
    (fun ω : VectorBrownian.Space N =>
      VectorBrownian.process s (rotateWiener U ω)) := by
    letI : MeasurableSpace (VectorBrownian.Space N) := VectorBrownian.filtration N t
    apply measurable_pi_iff.mpr
    intro i
    exact (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).measurable.comp
      (U.continuous.measurable.comp (wienerVector_past_measurable hs))
  exact hm.comap_le

end SlowEquilibration.SphericalWienerRotation
