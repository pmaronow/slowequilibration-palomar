-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.NormalizedRadialMeasure

/-! Exact affine-score expectation and its quantitative deviation, using the
actual signed and absolute radial first moments. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.NormalizedRadialMeasure
open Set MeasureTheory
set_option maxHeartbeats 300000

theorem affine_score_integral {f : ℝ → ℝ} {U : Set ℝ}
    (hf : IntegrableOn f U) {m a B c₀ : ℝ}
    (hm : IntegrableOn (fun k => (k-m)*f k) U) :
    (∫ k in U,(c₀+a+B*(k-m))*f k)=
      (c₀+a)*(∫ k in U,f k)+B*(∫ k in U,(k-m)*f k) := by
  calc
    _=(∫ k in U,(c₀+a)*f k+B*((k-m)*f k)) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun _ => by ring)
    _=_ := by rw [integral_add (hf.const_mul _) (hm.const_mul _),integral_const_mul,integral_const_mul]

theorem affine_score_expectation_deviation {f : ℝ → ℝ} {U : Set ℝ}
    (hf : IntegrableOn f U) (h0 : ∀ k,0 ≤ f k) (hZ : 0 < ∫ k in U,f k)
    {m a B c₀ : ℝ} (hm : IntegrableOn (fun k => (k-m)*f k) U) :
    |(∫ k in U,(c₀+a+B*(k-m))*f k)/(∫ k in U,f k)-c₀| ≤
      |a|+|B| *(∫ k in U,|k-m| *f k)/(∫ k in U,f k) := by
  rw [affine_score_integral hf hm]
  have he : ((c₀+a)*(∫ k in U,f k)+B*(∫ k in U,(k-m)*f k))/(∫ k in U,f k)-c₀=
      a+B*(∫ k in U,(k-m)*f k)/(∫ k in U,f k) := by field_simp;ring
  rw [he]
  have hMoment : |∫ k in U,(k-m)*f k| ≤ ∫ k in U,|k-m| *f k := by
    simpa only [abs_mul,abs_of_nonneg (h0 _)] using
      (abs_integral_le_integral_abs (f := fun k => (k-m)*f k) (μ := volume.restrict U))
  apply (abs_add_le _ _).trans
  rw [abs_div,abs_mul,abs_of_pos hZ]
  have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hMoment (abs_nonneg B)) hZ.le
  exact add_le_add le_rfl hh
end SlowEquilibration.NormalizedRadialMeasure
