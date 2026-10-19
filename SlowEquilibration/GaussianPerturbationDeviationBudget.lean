-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPerturbationDeviation

@[expose] public section

/-! Combined actual thermal and quenched selected-energy fluctuation
budget. It is uniform in the base spin law and Gaussian dimension. -/
namespace SlowEquilibration.GaussianPerturbationDeviation
noncomputable section
open MeasureTheory Set
open scoped Topology
open GaussianSpinInterpolation GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging GaussianPerturbationResponse GaussianPerturbationIntegrated
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

def totalDeviation (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (x : ℝ) : ℝ :=
  meanThermalDeviation ν L label x+energyFluctuation ν L label x

omit [DecidableEq ι] in
theorem totalDeviation_nonneg (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (x : ℝ) : 0≤totalDeviation ν L label x := by
  apply add_nonneg
  · apply integral_nonneg
    intro w
    exact integral_nonneg (fun _ => abs_nonneg _)
  · exact integral_nonneg (fun _ => abs_nonneg _)

theorem totalDeviation_measurable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ᵐ v ∂ν,‖L v‖≤K) (label : ι → Bool) :
    Measurable (totalDeviation ν L label) :=
  (meanThermalDeviation_measurable ν L hL hK hb label).add
    (energyFluctuation_continuous ν L hL hK hb label).measurable

theorem totalDeviation_intervalIntegrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0≤K) (hb : ∀ᵐ v ∂ν,‖L v‖≤K) (label : ι → Bool) (l u : ℝ) :
    IntervalIntegrable (totalDeviation ν L label) volume l u :=
  (meanThermalDeviation_intervalIntegrable ν L hL hK hb label l u).add
    ((energyFluctuation_continuous ν L hL hK hb label).intervalIntegrable l u)

theorem totalDeviation_integral_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K a r y : ℝ} (hK : 0<K) (hb : ∀ᵐ v ∂ν,‖L v‖≤K) (ha : 0≤a)
    (label : ι → Bool)
    (hdiag : ∀ᵐ v ∂ν,(∑ i,if label i=true then
      (GaussianSpinComparison.coordinateObservable L i v)^2 else 0)≤a)
    (hr : 0<r) (hy : 0<y) (hy1 : y≤1) :
    (∫ x in (0:ℝ)..1,totalDeviation ν L label x) ≤
      (a+r^2)/(2*r)+8*a*y+18*Real.exp (1/2)*K/y := by
  change (∫ x in (0:ℝ)..1,meanThermalDeviation ν L label x+energyFluctuation ν L label x) ≤ _
  rw [intervalIntegral.integral_add
    (meanThermalDeviation_intervalIntegrable ν L hL hK.le hb label 0 1)
    ((energyFluctuation_continuous ν L hL hK.le hb label).intervalIntegrable 0 1)]
  have ht:=meanThermalDeviation_integral_le ν L hL hK.le hb label hdiag hr
  have hq:=energyFluctuation_integral_le ν L hL hK hb ha label hdiag hy hy1
  linarith

end
end SlowEquilibration.GaussianPerturbationDeviation
