-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Probability.HasLaw
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-! Exact ordinary mean and normalized-moment transport through a positive
scalar multiple of an actual random-variable law. -/

namespace SlowEquilibration.ScaledLawNormalizedMoments
noncomputable section
open MeasureTheory ProbabilityTheory
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem normalized_moments_of_scaled_law {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (η : Measure Ω) (ν : Measure X) (D : Ω → ℝ) (f : X → ℝ)
    {a r C : ℝ} (ha : 0<a) (hf : Measurable f)
    (hD : HasLaw D (ν.map (fun x => a*f x)) η)
    (hi : Integrable f ν) (hm : 0<∫ x,f x ∂ν)
    (hmi : Integrable (fun x => (f x/(∫ y,f y ∂ν))^r) ν)
    (hmb : (∫ x,(f x/(∫ y,f y ∂ν))^r ∂ν)≤C) :
    Integrable D η ∧ (∫ x,D x ∂η)=a*(∫ y,f y ∂ν) ∧
      0<∫ x,D x ∂η ∧
      Integrable (fun x => (D x/(∫ y,D y ∂η))^r) η ∧
      (∫ x,(D x/(∫ y,D y ∂η))^r ∂η)≤C := by
  have haf : Measurable (fun x => a*f x) := measurable_const.mul hf
  have hIntId : Integrable id (ν.map (fun x => a*f x)) :=
    (integrable_map_measure aestronglyMeasurable_id haf.aemeasurable).mpr (hi.const_mul a)
  have hIntD : Integrable D η := by
    simpa only [Function.comp_def,id_eq] using hD.integrable_comp hIntId
  have hmean : (∫ x,D x ∂η)=a*(∫ y,f y ∂ν) := by
    rw [hD.integral_eq]
    change (∫ x,id x ∂ν.map (fun x => a*f x))=_
    rw [integral_map haf.aemeasurable aestronglyMeasurable_id]
    exact integral_const_mul a f
  refine ⟨hIntD,hmean,by rw [hmean]; exact mul_pos ha hm,?_⟩
  rw [hmean]
  let g : ℝ → ℝ := fun u => (u/(a*(∫ y,f y ∂ν)))^r
  have hg : Measurable g := (measurable_id.div_const _).pow_const r
  have he (x : X) : g (a*f x)=(f x/(∫ y,f y ∂ν))^r := by
    dsimp only [g]
    rw [mul_div_mul_left _ _ ha.ne']
  have hIntG : Integrable g (ν.map (fun x => a*f x)) := by
    apply (integrable_map_measure hg.aestronglyMeasurable haf.aemeasurable).mpr
    simpa only [Function.comp_def,he] using hmi
  refine ⟨hD.integrable_comp hIntG,?_⟩
  have hh := hD.integral_comp hg.aestronglyMeasurable
  rw [integral_map haf.aemeasurable hg.aestronglyMeasurable] at hh
  simp only [he] at hh
  exact hh.trans_le hmb

end
end SlowEquilibration.ScaledLawNormalizedMoments
