-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ExpectedTailEnvelopes
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Dominated convergence normalizes the true centered density using
the actual tail-equals-one identity. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ExpectedTailCentering
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 300000

theorem normalized_density_limit {f : ℕ → ℝ → ℝ} (m : ℕ → ℝ) {c₀ cMinus : ℝ}
    (hc₀ : 0 < c₀) (hcm : 0 < cMinus)
    (hc : ∀ᶠ n : ℕ in atTop,Continuous (f n))
    (hp : ∀ᶠ n : ℕ in atTop,∀ H : ℝ,0 < f n H)
    (hnorm : ∀ᶠ n : ℕ in atTop,tail (f n) (m n)=1)
    (hratio : ∀ t : ℝ,Tendsto (fun n : ℕ => f n (m n+t)/f n (m n))
      atTop (𝓝 (Real.exp (-c₀*t))))
    (henv : ∀ᶠ n : ℕ in atTop,∀ v : ℝ,0 ≤ v → f n (m n+v)/f n (m n) ≤ Real.exp (-cMinus*v)) :
    Tendsto (fun n : ℕ => f n (m n)) atTop (𝓝 c₀) := by
  have hg : IntegrableOn (fun v : ℝ => Real.exp (-cMinus*v)) (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_mul_Ioi (neg_neg_of_pos hcm) 0)
  have hmeas : ∀ᶠ n : ℕ in atTop,AEStronglyMeasurable
      (fun v : ℝ => f n (m n+v)/f n (m n)) (volume.restrict (Ici 0)) := by
    filter_upwards [hc] with n hn
    exact ((hn.comp (continuous_const.add continuous_id)).div_const _).aestronglyMeasurable
  have hbound : ∀ᶠ n : ℕ in atTop,∀ᵐ v ∂volume.restrict (Ici (0 : ℝ)),
      ‖f n (m n+v)/f n (m n)‖ ≤ Real.exp (-cMinus*v) := by
    filter_upwards [hp,henv] with n hpn hen
    filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
    rw [Real.norm_of_nonneg (div_nonneg (hpn _).le (hpn _).le)]
    exact hen v hv
  have hI := tendsto_integral_filter_of_dominated_convergence (fun v : ℝ => Real.exp (-cMinus*v))
    hmeas hbound hg (ae_of_all _ hratio)
  have hIntegral : (∫ v in Ici (0 : ℝ),Real.exp (-c₀*v))=1/c₀ := by
    rw [integral_Ici_eq_integral_Ioi,integral_exp_mul_Ioi (neg_neg_of_pos hc₀)]
    simp only [mul_zero,Real.exp_zero]
    ring
  rw [hIntegral] at hI
  have he : (fun n : ℕ => ∫ v in Ici (0 : ℝ),f n (m n+v)/f n (m n))=ᶠ[atTop]
      (fun n : ℕ => 1/f n (m n)) := by
    filter_upwards [hnorm] with n hn
    rw [integral_div,←tail_eq_shift,hn]
  have hInv := hI.congr' he
  have hDensityLimit := hInv.inv₀ (by positivity : (1/c₀ : ℝ) ≠ 0)
  simpa only [one_div,inv_inv] using hDensityLimit

theorem normalized_centered_density_limit {f : ℕ → ℝ → ℝ} (m : ℕ → ℝ) {c₀ : ℝ}
    (hp : ∀ᶠ n : ℕ in atTop,0 < f n (m n))
    (hbase : Tendsto (fun n : ℕ => f n (m n)) atTop (𝓝 c₀))
    (hratio : ∀ t : ℝ,Tendsto (fun n : ℕ => f n (m n+t)/f n (m n))
      atTop (𝓝 (Real.exp (-c₀*t)))) (t : ℝ) :
    Tendsto (fun n : ℕ => f n (m n+t)) atTop (𝓝 (c₀*Real.exp (-c₀*t))) := by
  have hh := hbase.mul (hratio t)
  have he : (fun n : ℕ => f n (m n)*(f n (m n+t)/f n (m n)))=ᶠ[atTop]
      (fun n : ℕ => f n (m n+t)) := by
    filter_upwards [hp] with n hn
    exact mul_div_cancel₀ _ hn.ne'
  exact hh.congr' he

theorem tail_eq_shift_from (f : ℝ → ℝ) (h t : ℝ) :
    tail f (h+t)=∫ v in Ici t,f (h+v) := by
  calc
    tail f (h+t)=∫ x : ℝ,(Ici (h+t)).indicator f x := (integral_indicator measurableSet_Ici).symm
    _=∫ x : ℝ,(Ici (h+t)).indicator f (h+x) := (integral_add_left_eq_self _ h).symm
    _=∫ x : ℝ,(Ici t).indicator (fun x => f (h+x)) x := by
      apply integral_congr_ae
      apply ae_of_all
      intro x
      have he : h+t ≤ h+x ↔ t ≤ x := by constructor <;> intro hx <;> linarith
      simp only [Set.indicator,mem_Ici,he]
    _=∫ v in Ici t,f (h+v) := integral_indicator measurableSet_Ici

theorem normalized_centered_tail_limit {f : ℕ → ℝ → ℝ} (m : ℕ → ℝ) {c₀ cMinus cPlus : ℝ}
    (hc₀ : 0 < c₀) (hcm : 0 < cMinus) (hcp : 0 ≤ cPlus)
    (hc : ∀ᶠ n : ℕ in atTop,Continuous (f n))
    (hp : ∀ᶠ n : ℕ in atTop,∀ H : ℝ,0 < f n H)
    (hbase : Tendsto (fun n : ℕ => f n (m n)) atTop (𝓝 c₀))
    (hratio : ∀ t : ℝ,Tendsto (fun n : ℕ => f n (m n+t)/f n (m n))
      atTop (𝓝 (Real.exp (-c₀*t))))
    (henv : ∀ᶠ n : ℕ in atTop,
      (∀ v : ℝ,0 ≤ v → f n (m n+v)/f n (m n) ≤ Real.exp (-cMinus*v)) ∧
      (∀ v : ℝ,v ≤ 0 → f n (m n+v)/f n (m n) ≤ Real.exp (-cPlus*v))) (t : ℝ) :
    Tendsto (fun n : ℕ => tail (f n) (m n+t)) atTop (𝓝 (Real.exp (-c₀*t))) := by
  let g : ℝ → ℝ := fun v => Real.exp (-cMinus*v)+Real.exp (-cPlus*t)*(Icc t 0).indicator 1 v
  have hconstant : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc t 0) :=
    integrableOn_const (by rw [Real.volume_Icc];exact ENNReal.ofReal_ne_top)
  have hg : IntegrableOn g (Ici t) :=
    (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi (integrableOn_exp_mul_Ioi (neg_neg_of_pos hcm) t)).add
      ((hconstant.integrable_indicator measurableSet_Icc).const_mul (Real.exp (-cPlus*t))).restrict
  have hmeas : ∀ᶠ n : ℕ in atTop,AEStronglyMeasurable
      (fun v : ℝ => f n (m n+v)/f n (m n)) (volume.restrict (Ici t)) := by
    filter_upwards [hc] with n hn
    exact ((hn.comp (continuous_const.add continuous_id)).div_const _).aestronglyMeasurable
  have hbound : ∀ᶠ n : ℕ in atTop,∀ᵐ v ∂volume.restrict (Ici t),
      ‖f n (m n+v)/f n (m n)‖ ≤ g v := by
    filter_upwards [hp,henv] with n hpn hen
    filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
    rw [Real.norm_of_nonneg (div_nonneg (hpn _).le (hpn _).le)]
    by_cases hv0 : 0 ≤ v
    · apply (hen.1 v hv0).trans
      change Real.exp (-cMinus*v) ≤ Real.exp (-cMinus*v)+Real.exp (-cPlus*t)*(Icc t 0).indicator 1 v
      have hind : 0 ≤ (Icc t 0).indicator (1 : ℝ → ℝ) v := Set.indicator_nonneg (fun _ _ => zero_le_one) _
      nlinarith [Real.exp_pos (-cPlus*t)]
    · have hv' : v ≤ 0 := (lt_of_not_ge hv0).le
      apply (hen.2 v hv').trans
      have hExp : Real.exp (-cPlus*v) ≤ Real.exp (-cPlus*t) := Real.exp_le_exp.mpr (by
        have hvt : t ≤ v := hv
        nlinarith)
      change Real.exp (-cPlus*v) ≤ Real.exp (-cMinus*v)+Real.exp (-cPlus*t)*(Icc t 0).indicator 1 v
      have hvIcc : v∈Icc t 0 := ⟨hv,hv'⟩
      rw [Set.indicator_of_mem hvIcc]
      change Real.exp (-cPlus*v) ≤ Real.exp (-cMinus*v)+Real.exp (-cPlus*t)*1
      nlinarith [Real.exp_pos (-cMinus*v)]
  have hI := tendsto_integral_filter_of_dominated_convergence g hmeas hbound hg (ae_of_all _ hratio)
  have hIntegral : (∫ v in Ici t,Real.exp (-c₀*v))=Real.exp (-c₀*t)/c₀ := by
    rw [integral_Ici_eq_integral_Ioi,integral_exp_mul_Ioi (neg_neg_of_pos hc₀)]
    ring
  rw [hIntegral] at hI
  have hproduct := hbase.mul hI
  have he : (fun n : ℕ => f n (m n)*(∫ v in Ici t,f n (m n+v)/f n (m n)))=ᶠ[atTop]
      (fun n : ℕ => tail (f n) (m n+t)) := by
    filter_upwards [hp] with n hn
    rw [integral_div,tail_eq_shift_from]
    exact mul_div_cancel₀ _ (hn _).ne'
  have hlimit : c₀*(Real.exp (-c₀*t)/c₀)=Real.exp (-c₀*t) := mul_div_cancel₀ _ hc₀.ne'
  rw [hlimit] at hproduct
  exact hproduct.congr' he

end SlowEquilibration.ExpectedTailCentering
