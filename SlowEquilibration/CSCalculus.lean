-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CrisantiSommers
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace SlowEquilibration.CrisantiSommers

open MeasureTheory Set Filter
open scoped Topology

private noncomputable def inverseSquare (ζ : Measure ℝ) (t : ℝ) : ℝ :=
  ((xHat ζ t)^2)⁻¹

private lemma inverseSquare_measurable (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q : ℝ} (hq : HasCutoff ζ q) : Measurable (inverseSquare ζ) :=
  ((xHat_continuous ζ hq).measurable.pow_const 2).inv

private lemma inverseSquare_continuousAt (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q s : ℝ} (hq : HasCutoff ζ q) (hs : s < 1) :
    ContinuousAt (inverseSquare ζ) s :=
  ((xHat_continuous ζ hq).continuousAt.pow 2).inv₀ (pow_ne_zero 2 (xHat_pos ζ hq hs).ne')

private lemma inverseSquare_intervalIntegrable (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q s : ℝ} (hq : HasCutoff ζ q) (hs : s < 1) :
    IntervalIntegrable (inverseSquare ζ) volume 0 s := by
  apply ContinuousOn.intervalIntegrable
  apply ((xHat_continuous ζ hq).continuousOn.pow 2).inv₀
  intro t ht
  have ht1 : t < 1 := ht.2.trans_lt (max_lt (by norm_num) hs)
  exact pow_ne_zero 2 (xHat_pos ζ hq ht1).ne'

private lemma triangular_integral_identity (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q s : ℝ} (hq : HasCutoff ζ q) (hs : s < 1) :
    (∫ t in (0:ℝ)..s, (s-t)/((xHat ζ t)^2)) =
      s*(∫ t in (0:ℝ)..s, inverseSquare ζ t)-
        (∫ t in (0:ℝ)..s, t*inverseSquare ζ t) := by
  have hw := inverseSquare_intervalIntegrable ζ hq hs
  have htw : IntervalIntegrable (fun t => t*inverseSquare ζ t) volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    apply continuous_id.continuousOn.mul
    apply ((xHat_continuous ζ hq).continuousOn.pow 2).inv₀
    intro t ht
    have ht1 : t < 1 := ht.2.trans_lt (max_lt (by norm_num) hs)
    exact pow_ne_zero 2 (xHat_pos ζ hq ht1).ne'
  calc
    (∫ t in (0:ℝ)..s, (s-t)/((xHat ζ t)^2)) =
        ∫ t in (0:ℝ)..s, s*inverseSquare ζ t-t*inverseSquare ζ t := by
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [inverseSquare]
      rw [div_eq_mul_inv]
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub (hw.const_mul s) htw,
        intervalIntegral.integral_const_mul]

/-- The actual first derivative of the first-variation potential at every
point below one, including the origin. -/
theorem firstVariation_hasDerivAt (β : ℝ) (η : ℝ → ℝ)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q s η' : ℝ} (hq : HasCutoff ζ q) (hs : s < 1) (hη : HasDerivAt η η' s) :
    HasDerivAt (firstVariation β η ζ)
      (β^2*η'-(∫ t in (0:ℝ)..s, 1/((xHat ζ t)^2))) s := by
  have hw := inverseSquare_intervalIntegrable ζ hq hs
  have hwm : StronglyMeasurableAtFilter (inverseSquare ζ) (𝓝 s) volume := (inverseSquare_measurable ζ hq).aestronglyMeasurable.stronglyMeasurableAtFilter
  have hwc := inverseSquare_continuousAt ζ hq hs
  have hW := intervalIntegral.integral_hasDerivAt_right hw hwm hwc
  have htw : IntervalIntegrable (fun t => t*inverseSquare ζ t) volume 0 s := by
    apply ContinuousOn.intervalIntegrable
    apply continuous_id.continuousOn.mul
    apply ((xHat_continuous ζ hq).continuousOn.pow 2).inv₀
    intro t ht
    have ht1 : t < 1 := ht.2.trans_lt (max_lt (by norm_num) hs)
    exact pow_ne_zero 2 (xHat_pos ζ hq ht1).ne'
  have htm : StronglyMeasurableAtFilter (fun t => t*inverseSquare ζ t) (𝓝 s) volume := (measurable_id.mul (inverseSquare_measurable ζ hq)).aestronglyMeasurable
    |>.stronglyMeasurableAtFilter
  have htc := continuousAt_id.mul hwc
  have hT := intervalIntegral.integral_hasDerivAt_right htw htm htc
  have htri := ((hasDerivAt_id s).mul hW).sub hT
  have hmodel := (hη.const_mul (β^2)).sub htri
  have hder : β^2*η' - (1*(∫ t in (0:ℝ)..s, inverseSquare ζ t)+
      s*inverseSquare ζ s-s*inverseSquare ζ s) =
      β^2*η'-(∫ t in (0:ℝ)..s, 1/((xHat ζ t)^2)) := by
    simp only [inverseSquare, one_div]
    ring
  simp only [id_eq] at hmodel
  rw [hder] at hmodel
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hs] with u hu
  unfold firstVariation
  rw [triangular_integral_identity ζ hq hu]
  rfl

/-- The derivative formula stated using Lean's ordinary `deriv`. -/
theorem firstVariation_deriv (β : ℝ) (η : ℝ → ℝ)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q s : ℝ} (hq : HasCutoff ζ q) (hs : s < 1) (hη : DifferentiableAt ℝ η s) :
    deriv (firstVariation β η ζ) s =
      β^2*deriv η s-(∫ t in (0:ℝ)..s, 1/((xHat ζ t)^2)) :=
  (firstVariation_hasDerivAt β η ζ hq hs hη.hasDerivAt).deriv

/-- The actual second derivative of the first-variation potential. -/
theorem firstVariation_deriv_hasDerivAt (β : ℝ) (η : ℝ → ℝ)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q s η'' : ℝ} (hq : HasCutoff ζ q) (hs : s < 1)
    (hη : DifferentiableOn ℝ η (Iio 1)) (hη' : HasDerivAt (deriv η) η'' s) :
    HasDerivAt (deriv (firstVariation β η ζ))
      (β^2*η''-1/((xHat ζ s)^2)) s := by
  have hw := inverseSquare_intervalIntegrable ζ hq hs
  have hwm : StronglyMeasurableAtFilter (inverseSquare ζ) (𝓝 s) volume := (inverseSquare_measurable ζ hq).aestronglyMeasurable.stronglyMeasurableAtFilter
  have hwc := inverseSquare_continuousAt ζ hq hs
  have hW := intervalIntegral.integral_hasDerivAt_right hw hwm hwc
  have hmodel := (hη'.const_mul (β^2)).sub hW
  have hder : β^2*η''-inverseSquare ζ s = β^2*η''-1/((xHat ζ s)^2) := by
    simp [inverseSquare, one_div]
  rw [hder] at hmodel
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hs] with u hu
  simpa only [Pi.sub_apply, inverseSquare, one_div] using
    firstVariation_deriv β η ζ hq hu
      ((hη u hu).differentiableAt (isOpen_Iio.mem_nhds hu))

/-- The second derivative formula as an equality of ordinary derivatives. -/
theorem firstVariation_second_deriv (β : ℝ) (η : ℝ → ℝ)
    (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q s : ℝ} (hq : HasCutoff ζ q) (hs : s < 1)
    (hη : DifferentiableOn ℝ η (Iio 1)) (hη' : DifferentiableAt ℝ (deriv η) s) :
    deriv (deriv (firstVariation β η ζ)) s =
      β^2*deriv (deriv η) s-1/((xHat ζ s)^2) :=
  (firstVariation_deriv_hasDerivAt β η ζ hq hs hη hη'.hasDerivAt).deriv

end SlowEquilibration.CrisantiSommers
