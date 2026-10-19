-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSFirstVariation
public import SlowEquilibration.CSCDFIntegration

@[expose] public section

namespace SlowEquilibration.CrisantiSommers

open MeasureTheory Set Filter
open scoped Topology NNReal

/-- The genuine pushforward law obtained by truncating every support point. -/
noncomputable def truncate (μ : Measure ℝ) (Q : ℝ) : Measure ℝ :=
  μ.map (fun s => min s Q)

instance truncate_isProbability (μ : Measure ℝ) [IsProbabilityMeasure μ] (Q : ℝ) :
    IsProbabilityMeasure (truncate μ Q) := by
  unfold truncate
  infer_instance

private lemma truncation_measurable (Q : ℝ) : Measurable (fun s : ℝ => min s Q) :=
  (continuous_id.min continuous_const).measurable

/-- The truncation is an actual admissible probability law with cutoff Q. -/
theorem truncate_hasCutoff (μ : Measure ℝ) {q Q : ℝ}
    (hq : HasCutoff μ q) (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) : HasCutoff (truncate μ Q) Q := by
  refine ⟨hQ0, hQ1, ?_⟩
  unfold truncate
  apply (ae_map_iff (truncation_measurable Q).aemeasurable
    (p := fun s => s ∈ Icc 0 Q) measurableSet_Icc).mpr
  filter_upwards [hq.2.2] with s hs
  exact ⟨le_min hs.1 hQ0, min_le_right _ _⟩

private lemma truncated_kernel_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q Q : ℝ} (hq : HasCutoff μ q) (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (t : ℝ) :
    Integrable (fun s => 1-max t (min s Q)) μ := by
  have hT := truncate_hasCutoff μ hq hQ0 hQ1
  have h := kernel_integrable (truncate μ Q) hT t
  exact (integrable_map_measure (by fun_prop) (truncation_measurable Q).aemeasurable).mp h

/-- xHat of the actual truncated pushforward law is the truncated kernel integral. -/
theorem xHat_truncate (μ : Measure ℝ) (Q t : ℝ) :
    xHat (truncate μ Q) t = ∫ s, 1-max t (min s Q) ∂μ := by
  unfold xHat truncate
  rw [integral_map (truncation_measurable Q).aemeasurable (by fun_prop)]

/-- Mean height removed by the genuine support truncation. -/
noncomputable def lostHeight (μ : Measure ℝ) (Q : ℝ) : ℝ :=
  ∫ s, max (s-Q) 0 ∂μ

theorem lostHeight_nonneg (μ : Measure ℝ) (Q : ℝ) : 0 ≤ lostHeight μ Q :=
  integral_nonneg (fun _ => le_max_right _ _)

private lemma lostHeight_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q Q : ℝ} (hq : HasCutoff μ q) (hQ0 : 0 ≤ Q) :
    Integrable (fun s => max (s-Q) 0) μ := by
  apply (integrable_const q).mono' (by fun_prop)
  filter_upwards [hq.2.2] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
  exact max_le (by linarith [hs.2]) hq.1

/-- Truncation increases xHat everywhere. -/
theorem xHat_le_truncate (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q Q : ℝ} (hq : HasCutoff μ q) (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (t : ℝ) :
    xHat μ t ≤ xHat (truncate μ Q) t := by
  rw [xHat_truncate]
  exact integral_mono (kernel_integrable μ hq t)
    (truncated_kernel_integrable μ hq hQ0 hQ1 t)
    (fun s => sub_le_sub_left (max_le_max_left t (min_le_left s Q)) 1)

/-- Below Q, the xHat gain is exactly the mean removed height. -/
theorem xHat_truncate_gain (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q Q t : ℝ} (hq : HasCutoff μ q) (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (ht : t ≤ Q) :
    xHat (truncate μ Q) t-xHat μ t = lostHeight μ Q := by
  rw [xHat_truncate]
  unfold xHat lostHeight
  rw [← integral_sub (truncated_kernel_integrable μ hq hQ0 hQ1 t) (kernel_integrable μ hq t)]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro s
  dsimp only
  by_cases hs : s ≤ Q
  · rw [min_eq_left hs, max_eq_right (sub_nonpos.mpr hs)]
    ring
  · have hQs : Q ≤ s := le_of_not_ge hs
    rw [min_eq_right hQs, max_eq_right ht, max_eq_right (ht.trans hQs),
      max_eq_left (sub_nonneg.mpr hQs)]
    ring

/-- The elementary inverse-square primitive controlling the uniform cutoff. -/
theorem integral_inverse_square_one_sub {Q : ℝ} (hQ : Q < 1) :
    (∫ t in (0:ℝ)..Q, ((1-t)^2)⁻¹) = Q/(1-Q) := by
  have hcont : ContinuousOn (fun t : ℝ => ((1-t)^2)⁻¹) (uIcc 0 Q) := by
    apply ((continuous_const.sub continuous_id).continuousOn.pow 2).inv₀
    intro t ht
    exact pow_ne_zero 2 (sub_pos.mpr (ht.2.trans_lt (max_lt (by norm_num) hQ))).ne'
  have hder : ∀ t ∈ uIcc (0:ℝ) Q, HasDerivAt (fun t : ℝ => (1-t)⁻¹) (((1-t)^2)⁻¹) t := by
    intro t ht
    have hne := (sub_pos.mpr (ht.2.trans_lt (max_lt (by norm_num) hQ))).ne'
    have hraw : HasDerivAt (fun u : ℝ => (1-u)⁻¹) (-((0:ℝ)-1)/(1-t)^2) t :=
      ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).inv hne
    convert hraw using 1
    simp only [zero_sub, neg_neg, one_div]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hcont.intervalIntegrable]
  have hne : 1-Q ≠ 0 := (sub_pos.mpr hQ).ne'
  field_simp
  ring

private lemma integrable_cutoff (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : HasCutoff μ q) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc 0 q)) : Integrable f μ := by
  have hi := hf.integrableOn_compact isCompact_Icc (μ := μ)
  simpa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hq.2.2] using hi

private lemma truncation_energy_bound (η : ℝ → ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {q Q : ℝ} (hq : HasCutoff μ q)
    (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (L : ℝ≥0)
    (hη : LipschitzOnWith L η (Icc (0:ℝ) 1)) :
    (∫ s, η s ∂μ)-(∫ s, η s ∂truncate μ Q) ≤ (L:ℝ)*lostHeight μ Q := by
  have hT := truncate_hasCutoff μ hq hQ0 hQ1
  have hiμ := integrable_cutoff μ hq (hη.continuousOn.mono
    (fun s hs => ⟨hs.1, hs.2.trans hq.2.1.le⟩))
  have hiT := integrable_cutoff (truncate μ Q) hT (hη.continuousOn.mono
    (fun s hs => ⟨hs.1, hs.2.trans hQ1.le⟩))
  have hiComp : Integrable (fun s => η (min s Q)) μ :=
    (integrable_map_measure hiT.aestronglyMeasurable (truncation_measurable Q).aemeasurable).mp hiT
  have hpoint : ∀ᵐ s ∂μ, η s-η (min s Q) ≤ (L:ℝ)*max (s-Q) 0 := by
    filter_upwards [hq.2.2] with s hs
    have hd := hη.dist_le_mul s ⟨hs.1, hs.2.trans hq.2.1.le⟩ (min s Q)
      ⟨le_min hs.1 hQ0, (min_le_right _ _).trans hQ1.le⟩
    change |η s-η (min s Q)| ≤ (L:ℝ)*|s-min s Q| at hd
    have heq : |s-min s Q|=max (s-Q) 0 := by
      by_cases hsQ : s ≤ Q
      · simp [min_eq_left hsQ, max_eq_right (sub_nonpos.mpr hsQ)]
      · have hQs : Q ≤ s := le_of_not_ge hsQ
        simp [min_eq_right hQs, abs_of_nonneg (sub_nonneg.mpr hQs), max_eq_left (sub_nonneg.mpr hQs)]
    rw [heq] at hd
    exact (le_abs_self _).trans hd
  have h := integral_mono_ae (hiμ.sub hiComp) ((lostHeight_integrable μ hq hQ0).const_mul (L:ℝ)) hpoint
  have hmap : (∫ s, η s ∂truncate μ Q) = ∫ s, η (min s Q) ∂μ := by
    unfold truncate
    exact integral_map (truncation_measurable Q).aemeasurable hiT.aestronglyMeasurable
  change (∫ s, η s-η (min s Q) ∂μ) ≤ (∫ s, (L:ℝ)*max (s-Q) 0 ∂μ) at h
  rw [integral_sub hiμ hiComp, integral_const_mul] at h
  rw [hmap]
  exact h

private lemma inverse_truncate_difference_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q Q t : ℝ} (hq : HasCutoff μ q) (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (ht : t < 1) :
    (xHat (truncate μ Q) t)⁻¹-(xHat μ t)⁻¹ ≤
      -(xHat (truncate μ Q) t-xHat μ t)/((1-t)^2) := by
  have hT := truncate_hasCutoff μ hq hQ0 hQ1
  have hx := xHat_pos μ hq ht
  have hy := xHat_pos (truncate μ Q) hT ht
  have hc : 0 < 1-t := sub_pos.mpr ht
  have hgain := xHat_le_truncate μ hq hQ0 hQ1 t
  have hprod : xHat (truncate μ Q) t*xHat μ t ≤ (1-t)^2 := by
    have h := mul_le_mul (xHat_upper_bound (truncate μ Q) hT t)
      (xHat_upper_bound μ hq t) hx.le hc.le
    simpa only [pow_two] using h
  have heq : (xHat (truncate μ Q) t)⁻¹-(xHat μ t)⁻¹ =
      -(xHat (truncate μ Q) t-xHat μ t)/(xHat (truncate μ Q) t*xHat μ t) := by
    field_simp
    ring
  rw [heq]
  apply (div_le_div_iff₀ (mul_pos hy hx) (sq_pos_of_pos hc)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hprod (sub_nonneg.mpr hgain)]

private lemma truncation_entropy_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q Q q' : ℝ} (hq : HasCutoff μ q) (hQ0 : 0 ≤ Q) (hQ1 : Q < 1)
    (hQq' : Q ≤ q') (hq' : q' < 1) :
    (∫ t in (0:ℝ)..q', (xHat (truncate μ Q) t)⁻¹)-
      (∫ t in (0:ℝ)..q', (xHat μ t)⁻¹) ≤ -lostHeight μ Q*(Q/(1-Q)) := by
  have hT := truncate_hasCutoff μ hq hQ0 hQ1
  have hiM0 := inverse_xHat_intervalIntegrable μ hq (a := 0) (b := Q) (by norm_num) hQ1
  have hiT0 := inverse_xHat_intervalIntegrable (truncate μ Q) hT (a := 0) (b := Q) (by norm_num) hQ1
  have hiM1 := inverse_xHat_intervalIntegrable μ hq (a := Q) (b := q') hQ1 hq'
  have hiT1 := inverse_xHat_intervalIntegrable (truncate μ Q) hT (a := Q) (b := q') hQ1 hq'
  have hiM := inverse_xHat_intervalIntegrable μ hq (a := 0) (b := q') (by norm_num) hq'
  have hiT := inverse_xHat_intervalIntegrable (truncate μ Q) hT (a := 0) (b := q') (by norm_num) hq'
  have hw : IntervalIntegrable (fun t : ℝ => ((1-t)^2)⁻¹) volume 0 Q := by
    apply ContinuousOn.intervalIntegrable
    apply ((continuous_const.sub continuous_id).continuousOn.pow 2).inv₀
    intro t ht
    exact pow_ne_zero 2 (sub_pos.mpr (ht.2.trans_lt (max_lt (by norm_num) hQ1))).ne'
  have hfirst := intervalIntegral.integral_mono_on hQ0 (hiT0.sub hiM0)
    (hw.const_mul (-lostHeight μ Q)) (fun t ht => ?_)
  · have hfirst' : (∫ t in (0:ℝ)..Q, (xHat (truncate μ Q) t)⁻¹-(xHat μ t)⁻¹) ≤
        -lostHeight μ Q*(Q/(1-Q)) := by
      change (∫ t in (0:ℝ)..Q, (xHat (truncate μ Q) t)⁻¹-(xHat μ t)⁻¹) ≤
        (∫ t in (0:ℝ)..Q, -lostHeight μ Q*((1-t)^2)⁻¹) at hfirst
      rwa [intervalIntegral.integral_const_mul, integral_inverse_square_one_sub hQ1] at hfirst
    have hsecond := intervalIntegral.integral_mono_on hQq' (hiT1.sub hiM1)
      (intervalIntegrable_const (c := (0:ℝ))) (fun t ht => ?_)
    · have hsecond' : (∫ t in Q..q', (xHat (truncate μ Q) t)⁻¹-(xHat μ t)⁻¹) ≤ 0 := by
        simpa using hsecond
      have hsplit := intervalIntegral.integral_add_adjacent_intervals (hiT0.sub hiM0) (hiT1.sub hiM1)
      have hsub : (∫ t in (0:ℝ)..q', (xHat (truncate μ Q) t)⁻¹-(xHat μ t)⁻¹) =
          (∫ t in (0:ℝ)..q', (xHat (truncate μ Q) t)⁻¹)-(∫ t in (0:ℝ)..q', (xHat μ t)⁻¹) :=
        intervalIntegral.integral_sub hiT hiM
      change (∫ t in (0:ℝ)..Q, (xHat (truncate μ Q) t)⁻¹-(xHat μ t)⁻¹)+
        (∫ t in Q..q', (xHat (truncate μ Q) t)⁻¹-(xHat μ t)⁻¹) = _ at hsplit
      rw [hsub] at hsplit
      linarith
    · exact sub_nonpos.mpr (inv_anti₀ (xHat_pos μ hq (ht.2.trans_lt hq'))
        (xHat_le_truncate μ hq hQ0 hQ1 t))
  · have h := inverse_truncate_difference_bound μ hq hQ0 hQ1 (ht.2.trans_lt hQ1)
    rw [xHat_truncate_gain μ hq hQ0 hQ1 ht.2] at h
    simpa only [div_eq_mul_inv] using h

/-- Uniform support truncation cannot increase the actual functional when
its entropy advantage dominates the Lipschitz energy cost. -/
theorem functional_truncate_le (β : ℝ) (η : ℝ → ℝ) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {q Q : ℝ} (hq : HasCutoff μ q)
    (hQ0 : 0 ≤ Q) (hQ1 : Q < 1) (L : ℝ≥0)
    (hη : LipschitzOnWith L η (Icc (0:ℝ) 1))
    (hcoef : β^2*(L:ℝ) ≤ Q/(1-Q)) :
    functional β η (truncate μ Q) Q ≤ functional β η μ q := by
  let q' := max q Q
  have hq' : q' < 1 := max_lt hq.2.1 hQ1
  have hT := truncate_hasCutoff μ hq hQ0 hQ1
  have hT' : HasCutoff (truncate μ Q) q' := hT.mono (le_max_right _ _) hq'
  have hμ' : HasCutoff μ q' := hq.mono (le_max_left _ _) hq'
  rw [functional_cutoff_independent (truncate μ Q) β η hT hT',
    functional_cutoff_independent μ β η hq hμ']
  have henergy := truncation_energy_bound η μ hq hQ0 hQ1 L hη
  have hentropy := truncation_entropy_bound μ hq hQ0 hQ1 (le_max_right q Q) hq'
  have hloss := lostHeight_nonneg μ Q
  have hβenergy := mul_le_mul_of_nonneg_left henergy (sq_nonneg β)
  have hcost := mul_le_mul_of_nonneg_right hcoef hloss
  unfold functional
  nlinarith

/-- A single cutoff below one works uniformly for every admissible law. -/
theorem exists_uniform_cutoff (β : ℝ) (L : ℝ≥0) :
    ∃ Q : ℝ, Q ∈ Ioo 0 1 ∧ β^2*(L:ℝ) ≤ Q/(1-Q) := by
  let A := β^2*(L:ℝ)
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg β) L.property
  let Q := (A+1)/(A+2)
  have hden : 0 < A+2 := by linarith
  have hQ0 : 0 < Q := div_pos (by linarith) hden
  have hQ1 : Q < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  have hratio : Q/(1-Q)=A+1 := by
    have hsum : 1-Q=1/(A+2) := by dsimp only [Q]; field_simp; ring
    rw [hsum]
    dsimp only [Q]
    field_simp
  exact ⟨Q, ⟨hQ0,hQ1⟩, by rw [hratio]; linarith⟩

end SlowEquilibration.CrisantiSommers
