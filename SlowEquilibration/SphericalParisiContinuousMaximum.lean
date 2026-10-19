-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ContinuousFieldLaw
public import Mathlib.Probability.HasLaw
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Order.Compact

/-! Genuine compact continuous-field maxima and their Borel field-law
transport. This is a generic observable reduction, with actual full field
law equality as its input and no supplied expected-maximum conclusion. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalParisiContinuousMaximum
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [Nonempty K]

def maximum (f : C(K,ℝ)) : ℝ := ⨆ x : K,f x

omit [Nonempty K] in
theorem evaluation_bddAbove (f : C(K,ℝ)) : BddAbove (range f) := by
  refine ⟨‖f‖,?_⟩
  rintro _ ⟨x,rfl⟩
  exact f.apply_le_norm x

omit [Nonempty K] in
theorem le_maximum (f : C(K,ℝ)) (x : K) : f x ≤ maximum f :=
  le_ciSup (evaluation_bddAbove f) x

theorem maximum_le_norm (f : C(K,ℝ)) : maximum f ≤ ‖f‖ :=
  ciSup_le (fun x => f.apply_le_norm x)

theorem norm_maximum_le_norm (f : C(K,ℝ)) : ‖maximum f‖ ≤ ‖f‖ := by
  rw [Real.norm_eq_abs,abs_le]
  let x : K := Classical.choice inferInstance
  exact ⟨(f.neg_norm_le_apply x).trans (le_maximum f x),maximum_le_norm f⟩

/-- The literal supremum is attained on the actual compact index space. -/
theorem maximum_attained (f : C(K,ℝ)) : ∃ x : K,maximum f=f x := by
  obtain ⟨x,_hx,hmax⟩ := isCompact_univ.exists_isMaxOn (Set.univ_nonempty)
    f.continuous.continuousOn
  exact ⟨x,le_antisymm (ciSup_le (fun y => hmax (mem_univ y))) (le_maximum f x)⟩

theorem maximum_compare (f g : C(K,ℝ)) : maximum f ≤ maximum g+‖f-g‖ := by
  apply ciSup_le
  intro x
  have hn := (f-g).apply_le_norm x
  simp only [ContinuousMap.sub_apply] at hn
  have hm := le_maximum g x
  linarith

theorem maximum_lipschitz : LipschitzWith 1 (maximum (K := K)) := by
  have H : LipschitzWith ((1 : ℝ).toNNReal) (maximum (K := K)) := by
    apply LipschitzWith.of_le_add_mul' (1 : ℝ)
    intro f g
    simpa only [dist_eq_norm,one_mul] using maximum_compare f g
  simpa only [Real.toNNReal_one] using H

theorem maximum_continuous : Continuous (maximum (K := K)) := maximum_lipschitz.continuous

theorem maximum_measurable : Measurable (maximum (K := K)) := maximum_continuous.measurable

omit [CompactSpace K] in
theorem maximum_const (c : ℝ) : maximum (ContinuousMap.const K c)=c := by
  simp only [maximum,ContinuousMap.const_apply,ciSup_const]

theorem maximum_add_const (f : C(K,ℝ)) (c : ℝ) :
    maximum (f+ContinuousMap.const K c)=maximum f+c := by
  obtain ⟨x,hx⟩ := maximum_attained f
  apply le_antisymm
  · apply ciSup_le
    intro y
    simp only [ContinuousMap.add_apply,ContinuousMap.const_apply]
    have H := le_maximum f y
    linarith
  · rw [hx]
    simpa only [ContinuousMap.add_apply,ContinuousMap.const_apply] using
      le_maximum (f+ContinuousMap.const K c) x

theorem maximum_nonneg_smul (f : C(K,ℝ)) {a : ℝ} (ha : 0 ≤ a) :
    maximum (a • f)=a*maximum f := by
  obtain ⟨x,hx⟩ := maximum_attained f
  apply le_antisymm
  · apply ciSup_le
    intro y
    simp only [ContinuousMap.smul_apply,smul_eq_mul]
    exact mul_le_mul_of_nonneg_left (le_maximum f y) ha
  · rw [hx]
    simpa only [ContinuousMap.smul_apply,smul_eq_mul] using le_maximum (a • f) x

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']

theorem maximum_integrable_of_norm (P : Measure Ω) (X : Ω → C(K,ℝ))
    (hX : Measurable X) (hNorm : Integrable (fun w => ‖X w‖) P) :
    Integrable (fun w => maximum (X w)) P := by
  apply hNorm.mono' (maximum_measurable.comp hX).aestronglyMeasurable
  exact .of_forall (fun w => norm_maximum_le_norm (X w))

/-- The true maximum law is the measurable pushforward of the genuine
whole continuous-field law. No mean or ground-state statement is input. -/
theorem maximum_hasLaw (P : Measure Ω) (Λ : Measure C(K,ℝ)) (X : Ω → C(K,ℝ))
    (hX : HasLaw X Λ P) : HasLaw (fun w => maximum (X w)) (Λ.map maximum) P := by
  have hM : HasLaw (maximum (K := K)) (Λ.map maximum) Λ :=
    ⟨maximum_measurable.aemeasurable,rfl⟩
  exact hM.fun_comp hX

theorem maximum_integral_hasLaw (P : Measure Ω) (Λ : Measure C(K,ℝ)) (X : Ω → C(K,ℝ))
    (hX : HasLaw X Λ P) : (∫ w,maximum (X w) ∂P)=∫ f,maximum f ∂Λ :=
  hX.integral_comp maximum_measurable.aestronglyMeasurable

theorem maximum_map_eq_of_field_law (P : Measure Ω) (Q : Measure Ω')
    (X : Ω → C(K,ℝ)) (Y : Ω' → C(K,ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hLaw : P.map X=Q.map Y) :
    P.map (fun w => maximum (X w))=Q.map (fun w => maximum (Y w)) := by
  calc
    _ = (P.map X).map maximum := by
      simpa only [Function.comp_def] using (Measure.map_map maximum_measurable hX).symm
    _ = (Q.map Y).map maximum := by rw [hLaw]
    _ = _ := by simpa only [Function.comp_def] using Measure.map_map maximum_measurable hY

theorem maximum_integral_eq_of_field_law (P : Measure Ω) (Q : Measure Ω')
    (X : Ω → C(K,ℝ)) (Y : Ω' → C(K,ℝ)) (hX : Measurable X) (hY : Measurable Y)
    (hLaw : P.map X=Q.map Y) :
    (∫ w,maximum (X w) ∂P)=∫ w,maximum (Y w) ∂Q := by
  have hx : HasLaw X (P.map X) P := ⟨hX.aemeasurable,rfl⟩
  have hy : HasLaw Y (P.map X) Q := ⟨hY.aemeasurable,hLaw.symm⟩
  exact (maximum_integral_hasLaw P (P.map X) X hx).trans
    (maximum_integral_hasLaw Q (P.map X) Y hy).symm

end SlowEquilibration.SphericalParisiContinuousMaximum
