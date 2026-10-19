-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceGradientCauchy
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Tactic

/-! The weighted gradient commutator is a genuine finite-dimensional
L² pairing under the tilted law. This identifies its two square energies
with the projected inverse-reference Fisher moment and the physical
weighted gradient energy. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem weighted_gradient_defect_cauchy
    {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (ν : Measure E) (k F U : E → ℝ) (a b : ι → E → ℝ)
    (hk : Measurable k) (hF : Measurable F) (hU : Measurable U)
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (hFlo : ∀ᵐ z ∂ν, 1 ≤ F z)
    (hUb : ∀ᵐ z ∂ν, |U z| ≤ 1)
    (hK : Integrable (fun z => k z ^ 2 *
      (∑ i, (a i z) ^ 2 / F z)) ν)
    (hB : Integrable (fun z => F z *
      (∑ i, (b i z) ^ 2)) ν) :
    |∫ z, k z * U z * (∑ i, a i z * b i z) ∂ν| ≤
      Real.sqrt ((∫ z, k z ^ 2 * (∑ i, (a i z) ^ 2 / F z) ∂ν) *
        (∫ z, F z * (∑ i, (b i z) ^ 2) ∂ν)) := by
  let X : E → EuclideanSpace ℝ ι := fun z =>
    WithLp.toLp 2 (fun i => k z * a i z / Real.sqrt (F z))
  let Y : E → EuclideanSpace ℝ ι := fun z =>
    WithLp.toLp 2 (fun i => Real.sqrt (F z) * U z * b i z)
  have hXm : AEStronglyMeasurable X ν := by
    apply Measurable.aestronglyMeasurable
    exact (WithLp.measurable_toLp 2 (ι → ℝ)).comp
      (measurable_pi_iff.mpr fun i => ((hk.mul (ha i)).div (hF.sqrt)))
  have hYm : AEStronglyMeasurable Y ν := by
    apply Measurable.aestronglyMeasurable
    exact (WithLp.measurable_toLp 2 (ι → ℝ)).comp
      (measurable_pi_iff.mpr fun i => ((hF.sqrt.mul hU).mul (hb i)))
  have hXsq : (fun z => ‖X z‖ ^ 2) =ᵐ[ν]
      (fun z => k z ^ 2 * (∑ i, (a i z)^2 / F z)) := by
    filter_upwards [hFlo] with z hz
    have hFp : 0 < F z := by linarith
    simp only [X,EuclideanSpace.real_norm_sq_eq]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_pow, mul_pow, Real.sq_sqrt hFp.le]
    ring
  have hYsq : ∀ᵐ z ∂ν, ‖Y z‖ ^ 2 ≤ F z * (∑ i, (b i z)^2) := by
    filter_upwards [hFlo,hUb] with z hz hu
    have hU2 : U z ^ 2 ≤ 1 := by
      obtain ⟨hlo,hhi⟩ := abs_le.mp hu
      nlinarith [mul_nonneg (sub_nonneg.mpr hhi) (show 0 ≤ 1+U z by linarith)]
    simp only [Y,EuclideanSpace.real_norm_sq_eq]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith : 0 ≤ F z)]
    have hc : 0 ≤ F z * (b i z)^2 := mul_nonneg (by linarith) (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_left hU2 hc]
  have hXi : Integrable (fun z => ‖X z‖ ^ 2) ν := hK.congr hXsq.symm
  have hYi : Integrable (fun z => ‖Y z‖ ^ 2) ν := by
    apply Integrable.mono_nonneg hB (by fun_prop)
      (by filter_upwards [] with z; positivity)
    exact hYsq
  have hYint : (∫ z, ‖Y z‖ ^ 2 ∂ν) ≤
      ∫ z, F z * (∑ i, (b i z)^2) ∂ν :=
    integral_mono_ae hYi hB hYsq
  have hXint : (∫ z, ‖X z‖ ^ 2 ∂ν) =
      ∫ z, k z ^ 2 * (∑ i, (a i z)^2 / F z) ∂ν :=
    integral_congr_ae hXsq
  have hcross : (fun z => inner ℝ (X z) (Y z)) =ᵐ[ν]
      (fun z => k z * U z * (∑ i, a i z * b i z)) := by
    filter_upwards [hFlo] with z hz
    have hsp : 0 < Real.sqrt (F z) := Real.sqrt_pos.2 (by linarith)
    simp only [X,Y,EuclideanSpace.inner_eq_star_dotProduct,
      star_trivial, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp [ne_of_gt hsp]
  have h := integral_inner_abs_le_sqrt ν X Y hXm hYm hXi hYi
  have hX0 : 0 ≤ ∫ z, ‖X z‖ ^ 2 ∂ν := integral_nonneg fun _ => sq_nonneg _
  have h' := h.trans (Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_left hYint hX0))
  rw [hXint,integral_congr_ae hcross] at h'
  exact h'

end SlowEquilibration.ConditionedEntrance
