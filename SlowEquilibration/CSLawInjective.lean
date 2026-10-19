-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CrisantiSommers
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

@[expose] public section

namespace SlowEquilibration.CrisantiSommers

open MeasureTheory Set Filter
open scoped Topology

private lemma kernel_right_derivative (t s : ℝ) :
    HasDerivWithinAt (fun u => 1-max u s) (if s ≤ t then -1 else 0) (Ici t) t := by
  classical
  by_cases hs : s ≤ t
  · rw [ite_eq_left hs]
    have hraw : HasDerivWithinAt (fun u : ℝ => 1-u) ((0:ℝ)-1) (Ici t) t :=
      ((hasDerivAt_const t (1:ℝ)).sub (hasDerivAt_id t)).hasDerivWithinAt
    have h : HasDerivWithinAt (fun u : ℝ => 1-u) (-1) (Ici t) t := by
      convert hraw using 1
      norm_num
    apply h.congr_of_mem _ le_rfl
    intro u hu
    rw [max_eq_left (hs.trans hu)]
  · rw [ite_eq_right hs]
    have h := hasDerivWithinAt_const t (Ici t) (1-s)
    apply h.congr_of_eventuallyEq
    · have hIio : ∀ᶠ u in 𝓝 t, u < s := Iio_mem_nhds (lt_of_not_ge hs)
      filter_upwards [hIio.filter_mono nhdsWithin_le_nhds] with u hu
      rw [max_eq_right hu.le]
    · rw [max_eq_right (le_of_not_ge hs)]

/-- The right derivative of the genuine integrated distribution function
is minus the probability distribution function, including its atoms. -/
theorem xHat_hasRightDerivative (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q : ℝ} (hq : HasCutoff ζ q) (t : ℝ) :
    HasDerivWithinAt (xHat ζ) (-ζ.real (Iic t)) (Ici t) t := by
  classical
  let l : Filter ℝ := 𝓝[Ici t \ {t}] t
  let F : ℝ → ℝ → ℝ := fun u s => slope (fun v => 1-max v s) t u
  let f : ℝ → ℝ := fun s => if s ≤ t then -1 else 0
  have hmeas : ∀ᶠ u in l, AEStronglyMeasurable (F u) ζ := by
    apply Eventually.of_forall
    intro u
    unfold F
    simp only [slope_def_field]
    fun_prop
  have hbound : ∀ᶠ u in l, ∀ᵐ s ∂ζ, ‖F u s‖ ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    apply Eventually.of_forall
    intro s
    have hut : t < u := lt_of_le_of_ne hu.1 (by simpa using Ne.symm hu.2)
    have hden : 0 < |u-t| := abs_pos.mpr (sub_ne_zero.mpr hut.ne')
    unfold F
    rw [slope_def_field, Real.norm_eq_abs, abs_div]
    have heq : (1-max u s)-(1-max t s)=-(max u s-max t s) := by ring
    rw [heq, abs_neg]
    exact (div_le_iff₀ hden).mpr (by simpa using abs_max_sub_max_le_abs u t s)
  have hlim : ∀ᵐ s ∂ζ, Tendsto (fun u => F u s) l (𝓝 (f s)) := by
    apply Eventually.of_forall
    intro s
    exact hasDerivWithinAt_iff_tendsto_slope.mp (kernel_right_derivative t s)
  have hDCT := tendsto_integral_filter_of_dominated_convergence (μ := ζ)
    (fun _ => (1:ℝ)) hmeas hbound (integrable_const _) hlim
  have hf : (∫ s, f s ∂ζ) = -ζ.real (Iic t) := by
    change (∫ s, (Iic t).indicator (fun _ => (-1:ℝ)) s ∂ζ) = _
    rw [integral_indicator measurableSet_Iic]
    simp
  rw [hf] at hDCT
  rw [hasDerivWithinAt_iff_tendsto_slope]
  apply hDCT.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  unfold F
  rw [slope_def_field]
  symm
  unfold xHat
  calc
    ((∫ s, 1-max u s ∂ζ)-(∫ s, 1-max t s ∂ζ))/(u-t) =
        ∫ s, ((1-max u s)-(1-max t s))/(u-t) ∂ζ := by
      rw [integral_div, integral_sub (kernel_integrable ζ hq u) (kernel_integrable ζ hq t)]
    _ = _ := by simp only [slope_def_field]

/-- The actual hatted function determines its probability law. -/
theorem measure_eq_of_xHat_eq (μ ζ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ζ]
    {qμ qζ : ℝ} (hμ : HasCutoff μ qμ) (hζ : HasCutoff ζ qζ)
    (heq : xHat μ = xHat ζ) : μ = ζ := by
  apply Measure.ext_of_Iic
  intro t
  have hm := (xHat_hasRightDerivative μ hμ t).derivWithin (uniqueDiffWithinAt_Ici t)
  have hz := (xHat_hasRightDerivative ζ hζ t).derivWithin (uniqueDiffWithinAt_Ici t)
  rw [heq] at hm
  have hreal : μ.real (Iic t) = ζ.real (Iic t) := by linarith
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top ζ _)).mp hreal

private lemma xHat_nonpos_eq_zero (ζ : Measure ℝ) [IsProbabilityMeasure ζ]
    {q t : ℝ} (hq : HasCutoff ζ q) (ht : t ≤ 0) : xHat ζ t = xHat ζ 0 := by
  unfold xHat
  apply integral_congr_ae
  filter_upwards [hq.2.2] with s hs
  rw [max_eq_right (ht.trans hs.1), max_eq_right hs.1]

/-- It suffices to compare hatted functions on any common support cutoff;
the actual laws, rather than just their entropy terms, then coincide. -/
theorem measure_eq_of_xHat_eq_on_cutoff (μ ζ : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ζ]
    {q : ℝ} (hμ : HasCutoff μ q) (hζ : HasCutoff ζ q)
    (heq : EqOn (xHat μ) (xHat ζ) (Icc 0 q)) : μ = ζ := by
  apply measure_eq_of_xHat_eq μ ζ hμ hζ
  funext t
  by_cases ht0 : t ≤ 0
  · rw [xHat_nonpos_eq_zero μ hμ ht0, xHat_nonpos_eq_zero ζ hζ ht0]
    exact heq ⟨le_rfl, hμ.1⟩
  · by_cases htq : t ≤ q
    · exact heq ⟨le_of_not_ge ht0, htq⟩
    · rw [xHat_tail μ hμ (le_of_not_ge htq), xHat_tail ζ hζ (le_of_not_ge htq)]

end SlowEquilibration.CrisantiSommers
