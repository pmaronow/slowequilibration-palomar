-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalRotatedItoIntegral

/-! Vector Itô integration commutes with a deterministic finite coordinate
mixing of the Brownian driver and the predictable matrix integrand. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalRotationCovariance
open MeasureTheory ProbabilityTheory StochasticCalculus
open SphericalAging.HardSphereDynamics SphericalAging.VectorIto
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 900000

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem vectorIto_mixed (D E : BrownianDriver N P F)
    (A : Fin N → Fin N → ℝ)
    (hB : ∀ j t, E.coordinate j t =ᵐ[P]
      fun ω => ∑ i : Fin N, A j i * D.coordinate i t ω)
    (V : Fin N → PredictableProcessL2 F P) :
    vectorIto E V = vectorIto D (fun i => ∑ j : Fin N, A j i • V j) := by
  simp only [vectorIto,coordinateIto_mixed D E A hB]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_sum]
  simp only [map_smul]

end SlowEquilibration.SphericalRotationCovariance
