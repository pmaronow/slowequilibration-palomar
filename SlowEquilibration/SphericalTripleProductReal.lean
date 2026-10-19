-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalHorizonHitMeasurable
public import Mathlib.MeasureTheory.Integral.Prod

/-! Real-valued Fubini formula for measurable events under three genuine
probability measures. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalTripleProductReal
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem triple_prod_real_eq_integral_fibers
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z]
    (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsProbabilityMeasure μZ]
    (E : Set (X × (Y × Z))) (hE : MeasurableSet E) :
    (μX.prod (μY.prod μZ)).real E =
      ∫ x, ∫ y, μZ.real {z | (x,(y,z)) ∈ E} ∂μY ∂μX := by
  have hOuter : Measurable fun x =>
      (μY.prod μZ) {q | (x,q) ∈ E} :=
    measurable_measure_prodMk_left hE
  have hInner (x : X) : Measurable fun y =>
      μZ {z | (x,(y,z)) ∈ E} :=
    measurable_measure_prodMk_left
      (hE.preimage (measurable_const.prodMk measurable_id))
  have hOuterFinite : ∀ᵐ x ∂μX,
      (μY.prod μZ) {q | (x,q) ∈ E} < ∞ :=
    .of_forall fun x => measure_lt_top _ _
  rw [Measure.real, Measure.prod_apply hE]
  change (∫⁻ x, (μY.prod μZ) {q | (x,q) ∈ E} ∂μX).toReal = _
  rw [← integral_toReal hOuter.aemeasurable hOuterFinite]
  apply integral_congr_ae
  apply ae_of_all
  intro x
  have hEx : MeasurableSet {q : Y × Z | (x,q) ∈ E} :=
    hE.preimage (measurable_const.prodMk measurable_id)
  have hInnerFinite : ∀ᵐ y ∂μY,
      μZ {z | (x,(y,z)) ∈ E} < ∞ :=
    .of_forall fun y => measure_lt_top _ _
  change ((μY.prod μZ) {q | (x,q) ∈ E}).toReal =
    ∫ y, (μZ {z | (x,(y,z)) ∈ E}).toReal ∂μY
  rw [Measure.prod_apply hEx]
  change (∫⁻ y, μZ {z | (x,(y,z)) ∈ E} ∂μY).toReal = _
  rw [← integral_toReal (hInner x).aemeasurable hInnerFinite]

end SlowEquilibration.SphericalTripleProductReal
