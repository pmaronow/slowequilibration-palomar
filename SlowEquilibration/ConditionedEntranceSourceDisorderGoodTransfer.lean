-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceAxisDisorderAverage

/-! The original Gaussian tensor good-event estimate controls the full
disorder mean of the measurable physical cap-hit observable, paying only
the actual probability of the exceptional tensor event. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem unit_observable_good_event_integral_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω→ℝ) (hf : Measurable f)
    (hunit : ∀ ω,f ω∈Icc 0 1) (Good : Set Ω) (hGood : MeasurableSet Good)
    (R : ℝ) (hR : 0≤R) (hBound : ∀ ω∈Good,f ω≤R) :
    (∫ ω,f ω ∂P)≤R+P.real Goodᶜ := by
  let b : Ω→ℝ := Goodᶜ.indicator (fun _ => 1)
  have hfi : Integrable f P := by
    apply Integrable.of_bound hf.aestronglyMeasurable 1
    exact .of_forall fun ω => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hunit ω).1]
      exact (hunit ω).2
  have hbi : Integrable b P := (integrable_const 1).indicator hGood.compl
  have hpoint (ω : Ω) : f ω≤R+b ω := by
    by_cases hω : ω∈Good
    · have hb : b ω=0 := by simp [b,hω]
      rw [hb,add_zero]
      exact hBound ω hω
    · have hb : b ω=1 := by simp [b,hω]
      rw [hb]
      linarith [(hunit ω).2]
  have h := integral_mono hfi ((integrable_const R).add hbi) hpoint
  have hb : (∫ ω,b ω ∂P)=P.real Goodᶜ := by
    simp [b,integral_indicator hGood.compl]
  change (∫ ω,f ω ∂P)≤∫ ω,R+b ω ∂P at h
  rw [integral_add (integrable_const R) hbi,hb] at h
  simpa using h

theorem sourceAxisAveragedCapHitProbability_disorder_good_transfer
    {N : ℕ} (μ : FiniteMixture) (Q : ℝ) (hQ : 0<Q)
    (hnp : μ.minDegree<μ.maxDegree) (α : ℝ) (χ : ℝ→ℝ)
    (hχ : ContDiff ℝ 2 χ) (β : ℝ) (H : ℝ≥0) (e k : ℝ)
    (Good : Set (Disorder N μ.maxDegree)) (hGood : MeasurableSet Good)
    (R : ℝ) (hR : 0≤R)
    (hBound : ∀ J∈Good,
      sourceAxisAveragedCapHitProbability μ Q hQ hnp α χ hχ β H e k J≤R) :
    (∫ J,sourceAxisAveragedCapHitProbability μ Q hQ hnp α χ hχ β H e k J
      ∂disorderLaw N μ.maxDegree)≤
      R+(disorderLaw N μ.maxDegree).real Goodᶜ :=
  unit_observable_good_event_integral_le (disorderLaw N μ.maxDegree) _
    (sourceAxisAveragedCapHitProbability_measurable μ Q hQ hnp α χ hχ β H e k)
    (sourceAxisAveragedCapHitProbability_mem_unit μ Q hQ hnp α χ hχ β H e k)
    Good hGood R hR hBound

end SlowEquilibration.ConditionedEntrance
