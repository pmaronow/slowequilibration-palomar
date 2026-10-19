-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ExpectedTailNormalizedLimits
public import SlowEquilibration.ExpectedCompactLogarithmicCentering

/-! Dominated convergence for a moving normalized center of a nonnegative
measurable density with a compact mark cutoff. The density may jump. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ExpectedTailCentering
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 400000

theorem compact_normalized_density_and_tail_limits
    {f : ℕ → ℝ → ℝ} (m : ℕ → ℝ) {c₀ cMinus A : ℝ}
    (hc₀ : 0 < c₀) (hcm : 0 < cMinus)
    (hmeas : ∀ᶠ n : ℕ in atTop, Measurable (f n))
    (hnonneg : ∀ᶠ n : ℕ in atTop, ∀ H : ℝ, 0 ≤ f n H)
    (hpositive : ∀ᶠ n : ℕ in atTop, 0 < f n (m n))
    (hnorm : ∀ᶠ n : ℕ in atTop, tail (f n) (m n)=1)
    (hratio : ∀ t : ℝ, Tendsto (fun n : ℕ => f n (m n+t)/f n (m n))
      atTop (𝓝 (Real.exp (-c₀*t))))
    (henv : ∀ᶠ n : ℕ in atTop, ∀ v : ℝ,
      f n (m n+v)/f n (m n) ≤ A*Real.exp (-cMinus*v)) :
    Tendsto (fun n : ℕ => f n (m n)) atTop (𝓝 c₀) ∧
    ∀ t : ℝ, Tendsto (fun n : ℕ => tail (f n) (m n+t))
      atTop (𝓝 (Real.exp (-c₀*t))) := by
  have hIntegral (t : ℝ) :
      Tendsto (fun n : ℕ =>
        ∫ v in Ici t, f n (m n+v)/f n (m n)) atTop
        (𝓝 (Real.exp (-c₀*t)/c₀)) := by
    have hg : IntegrableOn (fun v : ℝ => A*Real.exp (-cMinus*v)) (Ici t) :=
      (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
        (integrableOn_exp_mul_Ioi (neg_neg_of_pos hcm) t)).const_mul A
    have hmeas' : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
        (fun v : ℝ => f n (m n+v)/f n (m n)) (volume.restrict (Ici t)) := by
      filter_upwards [hmeas] with n hn
      exact ((hn.comp (measurable_const.add measurable_id)).div_const _).aestronglyMeasurable
    have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ v ∂volume.restrict (Ici t),
        ‖f n (m n+v)/f n (m n)‖ ≤ A*Real.exp (-cMinus*v) := by
      filter_upwards [hnonneg,hpositive,henv] with n hnn hp he
      filter_upwards [ae_restrict_mem measurableSet_Ici] with v hv
      rw [Real.norm_of_nonneg (div_nonneg (hnn _) hp.le)]
      exact he v
    have hh := tendsto_integral_filter_of_dominated_convergence
      (fun v : ℝ => A*Real.exp (-cMinus*v)) hmeas' hbound hg
      (ae_of_all _ hratio)
    have he : (∫ v in Ici t,Real.exp (-c₀*v))=Real.exp (-c₀*t)/c₀ := by
      rw [integral_Ici_eq_integral_Ioi,integral_exp_mul_Ioi (neg_neg_of_pos hc₀)]
      ring
    simpa only [he] using hh
  have hInv : Tendsto (fun n : ℕ => 1/f n (m n)) atTop (𝓝 (1/c₀)) := by
    have hh := hIntegral 0
    simp only [mul_zero,Real.exp_zero] at hh
    have he : (fun n : ℕ =>
        ∫ v in Ici (0 : ℝ),f n (m n+v)/f n (m n)) =ᶠ[atTop]
        (fun n : ℕ => 1/f n (m n)) := by
      filter_upwards [hnorm] with n hn
      rw [integral_div,←tail_eq_shift,hn]
    exact hh.congr' he
  have hBase : Tendsto (fun n : ℕ => f n (m n)) atTop (𝓝 c₀) := by
    have hh := hInv.inv₀ (by positivity : (1/c₀ : ℝ) ≠ 0)
    simpa only [one_div,inv_inv] using hh
  refine ⟨hBase,?_⟩
  intro t
  have hProduct := hBase.mul (hIntegral t)
  have he : (fun n : ℕ => f n (m n)*
      (∫ v in Ici t,f n (m n+v)/f n (m n))) =ᶠ[atTop]
      (fun n : ℕ => tail (f n) (m n+t)) := by
    filter_upwards [hpositive] with n hn
    rw [integral_div,tail_eq_shift_from]
    exact mul_div_cancel₀ _ hn.ne'
  have hLimit : c₀*(Real.exp (-c₀*t)/c₀)=Real.exp (-c₀*t) :=
    mul_div_cancel₀ _ hc₀.ne'
  rw [hLimit] at hProduct
  exact hProduct.congr' he

end SlowEquilibration.ExpectedTailCentering
