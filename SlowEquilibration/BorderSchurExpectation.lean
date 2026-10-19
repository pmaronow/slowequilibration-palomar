-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.OneBorderMoments

/-! # Ordinary expectation transfer for a true Schur approximation

All functions remain on their original common probability space. A good-event
Schur identity and ordinary second moments give a first-moment error estimate;
no independence or determinant approximation is built into the conclusion.
-/

@[expose] public section

namespace SlowEquilibration.BorderSchurExpectation

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Cauchy--Schwarz in ordinary real expectations, with literal squared
functions on the right. -/
lemma integral_abs_mul_le_sqrt_sq {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, |f x| * |g x| ∂μ) ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hf' : MemLp (fun x => |f x|) 2 μ := by simpa only [Real.norm_eq_abs] using hf.norm
  have hg' : MemLp (fun x => |g x|) 2 μ := by simpa only [Real.norm_eq_abs] using hg.norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 from by rw [Real.holderConjugate_iff]; norm_num)
    (ae_of_all μ (fun x => abs_nonneg (f x)))
    (ae_of_all μ (fun x => abs_nonneg (g x))) (by simpa using hf') (by simpa using hg')
  simpa only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] using h

/-- A true second moment controls the absolute expectation on a measurable
rare event. -/
lemma integral_indicator_abs_le_sqrt_sq [IsProbabilityMeasure μ]
    {f : Ω → ℝ} (hf : MemLp f 2 μ) {H : Set Ω} (hH : MeasurableSet H) :
    (∫ x, H.indicator (fun y => |f y|) x ∂μ) ≤
      Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (μ.real H) := by
  have hI : MemLp (H.indicator (fun _ : Ω => (1 : ℝ))) 2 μ :=
    (memLp_const 1).indicator hH
  have h := integral_abs_mul_le_sqrt_sq hf hI
  have hleft : (fun x => |f x| * |H.indicator (fun _ : Ω => (1 : ℝ)) x|) =
      H.indicator (fun x => |f x|) := by
    funext x
    by_cases hx : x ∈ H <;> simp [hx]
  have hright : (fun x => H.indicator (fun _ : Ω => (1 : ℝ)) x ^ 2) =
      H.indicator (fun _ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ∈ H <;> simp [hx]
  rw [hleft, hright, integral_indicator_const 1 hH] at h
  simpa only [smul_eq_mul, mul_one] using h

/-- The raw full determinant may differ from the clipped Schur expression
on the rare complement. Actual second moments bound that loss, while the
literal Schur error controls the good event. -/
theorem integral_abs_error_of_good_event [IsProbabilityMeasure μ]
    (D B T : Ω → ℝ) (hD : MemLp D 2 μ) (hB : MemLp B 2 μ)
    (s : ℝ) (hT : MemLp (fun x => T x - s) 2 μ)
    (G : Set Ω) (hG : MeasurableSet G)
    (hgood : ∀ᵐ x ∂μ, x ∈ G → |D x - |s| * B x| ≤ |B x| * |T x - s|) :
    Integrable (fun x => |D x - |s| * B x|) μ ∧
      (∫ x, |D x - |s| * B x| ∂μ) ≤
        Real.sqrt (∫ x, B x ^ 2 ∂μ) * Real.sqrt (∫ x, (T x - s) ^ 2 ∂μ) +
          (Real.sqrt (∫ x, D x ^ 2 ∂μ) + |s| * Real.sqrt (∫ x, B x ^ 2 ∂μ)) *
            Real.sqrt (μ.real Gᶜ) := by
  have hDi := hD.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hBi := hB.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hErr : Integrable (fun x => |D x - |s| * B x|) μ := (hDi.sub (hBi.const_mul |s|)).abs
  have hBabs : MemLp (fun x => |B x|) 2 μ := by simpa only [Real.norm_eq_abs] using hB.norm
  have hTabs : MemLp (fun x => |T x - s|) 2 μ := by simpa only [Real.norm_eq_abs] using hT.norm
  have hProd : Integrable (fun x => |B x| * |T x - s|) μ :=
    memLp_one_iff_integrable.mp (hBabs.mul hTabs)
  have hDbad : Integrable (Gᶜ.indicator (fun x => |D x|)) μ := hDi.abs.indicator hG.compl
  have hBbad : Integrable (Gᶜ.indicator (fun x => |B x|)) μ := hBi.abs.indicator hG.compl
  have hMajor : Integrable (fun x => |B x| * |T x - s| +
      Gᶜ.indicator (fun x => |D x|) x + |s| * Gᶜ.indicator (fun x => |B x|) x) μ :=
    (hProd.add hDbad).add (hBbad.const_mul |s|)
  have hpoint : ∀ᵐ x ∂μ, |D x - |s| * B x| ≤ |B x| * |T x - s| +
      Gᶜ.indicator (fun x => |D x|) x + |s| * Gᶜ.indicator (fun x => |B x|) x := by
    filter_upwards [hgood] with x hx
    by_cases hxG : x ∈ G
    · have hxGc : x ∉ Gᶜ := by simpa only [mem_compl_iff, not_not] using hxG
      simpa only [Set.indicator_of_notMem hxGc, add_zero, mul_zero] using hx hxG
    · have ha : |D x - |s| * B x| ≤ |D x| + |s| * |B x| := by
        simpa only [abs_mul, abs_abs] using abs_sub (D x) (|s| * B x)
      simp only [Set.indicator_of_mem (show x ∈ Gᶜ from hxG)]
      nlinarith [mul_nonneg (abs_nonneg (B x)) (abs_nonneg (T x - s))]
  refine ⟨hErr, (integral_mono_ae hErr hMajor hpoint).trans ?_⟩
  have hsplit : (∫ x, |B x| * |T x - s| + Gᶜ.indicator (fun x => |D x|) x +
      |s| * Gᶜ.indicator (fun x => |B x|) x ∂μ) =
      (∫ x, |B x| * |T x - s| ∂μ) +
      (∫ x, Gᶜ.indicator (fun x => |D x|) x ∂μ) +
      |s| * (∫ x, Gᶜ.indicator (fun x => |B x|) x ∂μ) := by
    have h1 := integral_add (hProd.add hDbad) (hBbad.const_mul |s|)
    have h2 := integral_add hProd hDbad
    simp only [Pi.add_apply] at h1 h2
    rw [h1, h2, integral_const_mul]
  rw [hsplit]
  have hprod := integral_abs_mul_le_sqrt_sq hB hT
  have hdb := integral_indicator_abs_le_sqrt_sq hD hG.compl
  have hbb := integral_indicator_abs_le_sqrt_sq hB hG.compl
  calc
    _ ≤ Real.sqrt (∫ x, B x ^ 2 ∂μ) * Real.sqrt (∫ x, (T x - s) ^ 2 ∂μ) +
        Real.sqrt (∫ x, D x ^ 2 ∂μ) * Real.sqrt (μ.real Gᶜ) +
          |s| * (Real.sqrt (∫ x, B x ^ 2 ∂μ) * Real.sqrt (μ.real Gᶜ)) :=
      add_le_add (add_le_add hprod hdb) (mul_le_mul_of_nonneg_left hbb (abs_nonneg s))
    _ = _ := by ring

/-- The same bound also controls the literal ordinary full/bulk first
moments, so an approximation of their normalization is a conclusion. -/
theorem abs_mean_error_of_good_event [IsProbabilityMeasure μ]
    (D B T : Ω → ℝ) (hD : MemLp D 2 μ) (hB : MemLp B 2 μ)
    (s : ℝ) (hT : MemLp (fun x => T x - s) 2 μ)
    (G : Set Ω) (hG : MeasurableSet G)
    (hgood : ∀ᵐ x ∂μ, x ∈ G → |D x - |s| * B x| ≤ |B x| * |T x - s|) :
    |(∫ x, D x ∂μ) - |s| * (∫ x, B x ∂μ)| ≤
      Real.sqrt (∫ x, B x ^ 2 ∂μ) * Real.sqrt (∫ x, (T x - s) ^ 2 ∂μ) +
        (Real.sqrt (∫ x, D x ^ 2 ∂μ) + |s| * Real.sqrt (∫ x, B x ^ 2 ∂μ)) *
          Real.sqrt (μ.real Gᶜ) := by
  have hDi := hD.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hBi := hB.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have h := integral_abs_error_of_good_event D B T hD hB s hT G hG hgood
  have hnorm := norm_integral_le_integral_norm (fun x => D x - |s| * B x) (μ := μ)
  rw [integral_sub hDi (hBi.const_mul |s|), integral_const_mul, Real.norm_eq_abs] at hnorm
  exact hnorm.trans (by simpa only [Real.norm_eq_abs] using h.2)

end
end SlowEquilibration.BorderSchurExpectation
