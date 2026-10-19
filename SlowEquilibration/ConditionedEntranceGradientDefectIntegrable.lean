-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceWeightedGradientDefectCauchy

/-! The two actual L¹ energy densities make the signed gradient defect
Bochner integrable. No bounded tilt multiplier is needed here. -/
@[expose] public section
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 400000

private theorem scalar_defect_cross
    (F U a b : ℝ) (hF : 1 ≤ F) (hU : |U| ≤ 1) :
    |U*a*b| ≤ (F*b^2+a^2/F)/2 := by
  have hpos : 0 < F := by linarith
  have hne : F ≠ 0 := ne_of_gt hpos
  have he : F*((F*b^2+a^2/F)/2)=((F*b)^2+a^2)/2 := by
    field_simp [hne]
  have hab : |a*b| ≤ (F*b^2+a^2/F)/2 := by
    apply abs_le.mpr
    constructor
    · apply (mul_le_mul_iff_right₀ hpos).mp
      rw [mul_neg,he]
      nlinarith [sq_nonneg (F*b+a)]
    · apply (mul_le_mul_iff_right₀ hpos).mp
      rw [he]
      nlinarith [sq_nonneg (F*b-a)]
  calc
    |U*a*b| = |U| * |a*b| := by rw [mul_assoc,abs_mul]
    _ ≤ |a*b| := mul_le_of_le_one_left (abs_nonneg _) hU
    _ ≤ _ := hab

theorem weighted_gradient_defect_integrable
    {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    (ν : Measure E) (k F U : E → ℝ) (a b : ι → E → ℝ)
    (hk : Measurable k) (_hF : Measurable F) (hU : Measurable U)
    (ha : ∀ i, Measurable (a i)) (hb : ∀ i, Measurable (b i))
    (hFlo : ∀ᵐ z ∂ν, 1 ≤ F z)
    (hUb : ∀ᵐ z ∂ν, |U z| ≤ 1)
    (hKint : Integrable (fun z => k z^2 *
      (∑ i, (a i z)^2/F z)) ν)
    (hBint : Integrable (fun z => F z *
      (∑ i, (b i z)^2)) ν) :
    Integrable (fun z => k z * U z * (∑ i, a i z*b i z)) ν := by
  let K : E → ℝ := fun z => k z^2*(∑ i, (a i z)^2/F z)
  let B : E → ℝ := fun z => F z*(∑ i, (b i z)^2)
  let C : E → ℝ := fun z => k z*U z*(∑ i, a i z*b i z)
  have hCm : Measurable C := (hk.mul hU).mul
    (Finset.measurable_sum _ (fun i _ => (ha i).mul (hb i)))
  have hpoint : ∀ᵐ z ∂ν, ‖C z‖ ≤ (K z+B z)/2 := by
    filter_upwards [hFlo,hUb] with z hz hu
    have hsum : |U z*(∑ i, (k z*a i z)*b i z)| ≤
        (B z+K z)/2 := by
      calc
        |U z*(∑ i, (k z*a i z)*b i z)| =
            |∑ i, U z*(k z*a i z)*b i z| := by
              rw [Finset.mul_sum]
              congr 1
              apply Finset.sum_congr rfl
              intro i _
              ring
        _ ≤ ∑ i, |U z*(k z*a i z)*b i z| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (F z*(b i z)^2+(k z*a i z)^2/F z)/2 :=
          Finset.sum_le_sum (fun i _ => scalar_defect_cross _ _ _ _ hz hu)
        _ = (B z+K z)/2 := by
          rw [← Finset.sum_div,Finset.sum_add_distrib,← Finset.mul_sum]
          have hksum : (∑ i, (k z*a i z)^2/F z) =
              k z^2*(∑ i, (a i z)^2/F z) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
          rw [hksum]
    have hceq : C z = U z*(∑ i, (k z*a i z)*b i z) := by
      calc
        C z = U z*(k z*(∑ i, a i z*b i z)) := by dsimp only [C]; ring
        _ = U z*(∑ i, (k z*a i z)*b i z) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
    rw [Real.norm_eq_abs,hceq]
    linarith [hsum]
  have hD : Integrable (fun z => (K z+B z)/2) ν :=
    (hKint.add hBint).div_const 2
  exact hD.mono' hCm.aestronglyMeasurable hpoint

end SlowEquilibration.ConditionedEntrance
