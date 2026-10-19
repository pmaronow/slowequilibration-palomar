-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Probability.HasLaw

/-! Exact coordinate-refresh Fubini for an actual finite probability
cube. It averages a proved one-coordinate GG estimate over all other
perturbation coordinates without assuming pointwise GG smallness. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.FiniteCubeFubini

open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators

set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {V : Type*} [MeasurableSpace V]

 theorem update_joint_measurable (K : ℕ) (i : Fin K) :
    Measurable (fun z : (Fin K → V) × V => Function.update z.1 i z.2) := by
  apply Measurable.of_eval
  intro j
  by_cases h : j=i
  · subst j
    simpa only [Function.update_self] using (measurable_snd : Measurable (fun z : (Fin K → V) × V => z.2))
  · simpa only [Function.update_of_ne h,Function.comp_def] using
      (measurable_pi_apply j).comp (measurable_fst : Measurable (fun z : (Fin K → V) × V => z.1))

/-- Refreshing one coordinate by an independent sample preserves the
actual finite product probability law, hence every bounded expectation. -/
theorem integral_coordinate_refresh (ν : Measure V) [IsProbabilityMeasure ν]
    {n : ℕ} (i : Fin (n+1)) (F : (Fin (n+1) → V) → ℝ) (hF : Measurable F)
    {C : ℝ} (hB : ∀x,‖F x‖≤C) :
    (∫x,(∫t,F (Function.update x i t) ∂ν) ∂Measure.pi (fun _ : Fin (n+1) => ν))=
      ∫x,F x ∂Measure.pi (fun _ : Fin (n+1) => ν) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => V) i
  let μ := Measure.pi (fun _ : Fin n => ν)
  let g : (Fin n → V) → ℝ := fun y => ∫t,F (e.symm (t,y)) ∂ν
  have hMP : MeasurePreserving e (Measure.pi (fun _ : Fin (n+1) => ν)) (ν.prod μ) :=
    measurePreserving_piFinSuccAbove _ i
  have hExt := (measurePreserving_snd (μ := ν) (ν := μ)).comp hMP
  have hg : StronglyMeasurable g :=
    (hF.comp e.symm.measurable).stronglyMeasurable.integral_prod_left'
  have hPair : Integrable (fun z : V × (Fin n → V) => F (e.symm z)) (ν.prod μ) :=
    Integrable.of_bound (hF.comp e.symm.measurable).aestronglyMeasurable C (.of_forall fun z => hB _)
  have hUpdate (x : Fin (n+1) → V) (t : V) :
      e.symm (t,(e x).2)=Function.update x i t := by
    simp only [e,MeasurableEquiv.piFinSuccAbove,Fin.insertNthEquiv]
    exact Fin.insertNth_removeNth i t x
  calc
    _ = ∫x,g ((e x).2) ∂Measure.pi (fun _ : Fin (n+1) => ν) := by
      apply integral_congr_ae
      exact .of_forall fun x => integral_congr_ae (.of_forall fun t => congrArg F (hUpdate x t).symm)
    _ = ∫y,g y ∂μ := hExt.hasLaw.integral_comp hg.aestronglyMeasurable
    _ = ∫z,F (e.symm z) ∂ν.prod μ := (integral_prod_symm _ hPair).symm
    _ = _ := hMP.symm.hasLaw.integral_comp hF.aestronglyMeasurable

/-- An actual averaged one-coordinate bound controls the entire finite
cube expectation. The source cube law is the literal product measure. -/
theorem integral_le_of_coordinate_bound (ν : Measure V) [IsProbabilityMeasure ν]
    {K : ℕ} (i : Fin K) (F : (Fin K → V) → ℝ) (hF : Measurable F)
    {C E : ℝ} (hB : ∀x,‖F x‖≤C)
    (hcoord : ∀ᵐ x ∂Measure.pi (fun _ : Fin K => ν), (∫t,F (Function.update x i t) ∂ν)≤E) :
    (∫x,F x ∂Measure.pi (fun _ : Fin K => ν))≤E := by
  cases K with
  | zero => exact i.elim0
  | succ n =>
    rw [← integral_coordinate_refresh ν i F hF hB]
    have hm : StronglyMeasurable (fun x : Fin (n+1) → V => ∫t,F (Function.update x i t) ∂ν) :=
      (hF.comp (update_joint_measurable (n+1) i)).stronglyMeasurable.integral_prod_right'
    have hi : Integrable (fun x : Fin (n+1) → V => ∫t,F (Function.update x i t) ∂ν)
        (Measure.pi (fun _ : Fin (n+1) => ν)) := by
      apply Integrable.of_bound hm.aestronglyMeasurable C
      exact .of_forall fun x => by
        simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
          (μ := ν) (f := fun t => F (Function.update x i t)) (C := C) (.of_forall fun t => hB _)
    have ht := integral_mono_ae hi (integrable_const E) hcoord
    simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using ht

end SlowEquilibration.FiniteCubeFubini
