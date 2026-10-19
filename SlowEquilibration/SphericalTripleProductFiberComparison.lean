-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalTripleProductReal

/-! A three-factor probability union comparison may be checked on every
Wiener fibre and then integrated over disorder and initial state. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalTripleProductReal
open MeasureTheory
set_option autoImplicit false

theorem triple_prod_real_le_integral_add_of_fibers
    {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z]
    (μX : Measure X) (μY : Measure Y) (μZ : Measure Z)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μY]
    [IsProbabilityMeasure μZ]
    (E G : Set (X × (Y × Z))) (hE : MeasurableSet E)
    (hG : MeasurableSet G)
    (C : X × Y → ℝ) (hCm : Measurable C)
    (hCb : ∀ q, ‖C q‖ ≤ 1)
    (P : Set Y) (hP : ∀ᵐ y ∂μY, y ∈ P)
    (hfiber : ∀ x, ∀ y ∈ P,
      μZ.real {z | (x,(y,z)) ∈ E} ≤
        C (x,y) + μZ.real {z | (x,(y,z)) ∈ G}) :
    (μX.prod (μY.prod μZ)).real E ≤
      (∫ x, ∫ y, C (x,y) ∂μY ∂μX) +
        (μX.prod (μY.prod μZ)).real G := by
  let e : X × Y → ℝ := fun q => μZ.real {z | (q.1,(q.2,z)) ∈ E}
  let g : X × Y → ℝ := fun q => μZ.real {z | (q.1,(q.2,z)) ∈ G}
  have hAssocE : MeasurableSet {q : (X × Y) × Z |
      (q.1.1,(q.1.2,q.2)) ∈ E} :=
    hE.preimage (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hAssocG : MeasurableSet {q : (X × Y) × Z |
      (q.1.1,(q.1.2,q.2)) ∈ G} :=
    hG.preimage (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have hem : Measurable e := by
    exact (measurable_measure_prodMk_left hAssocE).ennreal_toReal
  have hgm : Measurable g := by
    exact (measurable_measure_prodMk_left hAssocG).ennreal_toReal
  have heb (q : X × Y) : ‖e q‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hgb (q : X × Y) : ‖g q‖ ≤ 1 := by
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hei : Integrable e (μX.prod μY) :=
    Integrable.of_bound hem.aestronglyMeasurable 1 (.of_forall heb)
  have hgi : Integrable g (μX.prod μY) :=
    Integrable.of_bound hgm.aestronglyMeasurable 1 (.of_forall hgb)
  have hCi : Integrable C (μX.prod μY) :=
    Integrable.of_bound hCm.aestronglyMeasurable 1 (.of_forall hCb)
  have heiX : Integrable (fun x => ∫ y, e (x,y) ∂μY) μX := hei.integral_prod_left
  have hgiX : Integrable (fun x => ∫ y, g (x,y) ∂μY) μX := hgi.integral_prod_left
  have hCiX : Integrable (fun x => ∫ y, C (x,y) ∂μY) μX := hCi.integral_prod_left
  have hInner (x : X) :
      (∫ y, e (x,y) ∂μY) ≤
        (∫ y, C (x,y) ∂μY) + (∫ y, g (x,y) ∂μY) := by
    have heiY : Integrable (fun y => e (x,y)) μY :=
      Integrable.of_bound
        (hem.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        1 (.of_forall fun y => heb (x,y))
    have hgiY : Integrable (fun y => g (x,y)) μY :=
      Integrable.of_bound
        (hgm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        1 (.of_forall fun y => hgb (x,y))
    have hCiY : Integrable (fun y => C (x,y)) μY :=
      Integrable.of_bound
        (hCm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        1 (.of_forall fun y => hCb (x,y))
    rw [← integral_add hCiY hgiY]
    apply integral_mono_ae heiY (hCiY.add hgiY)
    filter_upwards [hP] with y hy
    exact hfiber x y hy
  rw [triple_prod_real_eq_integral_fibers μX μY μZ E hE,
    triple_prod_real_eq_integral_fibers μX μY μZ G hG]
  change (∫ x, ∫ y, e (x,y) ∂μY ∂μX) ≤
    (∫ x, ∫ y, C (x,y) ∂μY ∂μX) +
      (∫ x, ∫ y, g (x,y) ∂μY ∂μX)
  rw [← integral_add hCiX hgiX]
  exact integral_mono heiX (hCiX.add hgiX) hInner

end SlowEquilibration.SphericalTripleProductReal
