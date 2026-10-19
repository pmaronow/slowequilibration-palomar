-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceNormalizedTiltInitial

/-! The initial-law total-variation term in the entropy-resolvent
comparison. Its `4η` rate follows from the first axis moment and the
literal global normalizer; no initial-law closeness is assumed. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace SlowEquilibration.ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 400000

theorem normalizedTilt_initialDensity_l1_le_four_eta
    {U E : Type*} [MeasurableSpace U] [MeasurableSpace E]
    (θ : Measure U) (μ : Measure E)
    [IsProbabilityMeasure θ] [IsProbabilityMeasure μ]
    (w : U × E → ℝ) (hw : Measurable w)
    (he : Integrable (fun z => Real.exp (w z)) (θ.prod μ))
    (f₀ : E → ℝ) (hf₀ : Integrable f₀ μ) (hf₀pos : ∀ x, 0 ≤ f₀ x)
    (hf₀mass : (∫ x, f₀ x ∂μ) = 1)
    (hfprod : Integrable (fun z : U × E => f₀ z.2) (θ.prod μ))
    (hewprod : Integrable (fun z : U × E => Real.exp (w z) * f₀ z.2)
      (θ.prod μ))
    {η : ℝ} (hη : 0 ≤ η) (hηhalf : η ≤ 1/2)
    (haxis : ∀ᵐ x ∂μ,
      (∫ u, |Real.exp (w (u,x))-1| ∂θ) ≤ η) :
    let M := ∫ z, Real.exp (w z) ∂θ.prod μ
    (∫ z, |M * Real.exp (-w z) * f₀ z.2 - f₀ z.2|
      ∂normalizedTilt (θ.prod μ) w M) ≤ 4*η := by
  dsimp only
  let M := ∫ z, Real.exp (w z) ∂θ.prod μ
  have hc : |M-1| ≤ η := exponential_mass_close_one θ μ w he rfl haxis
  have hMhalf : (1/2 : ℝ) ≤ M := by
    have hl := (abs_le.mp hc).1
    linarith
  have hM : 0 < M := by linarith
  have hdiff : Integrable (fun z : U × E => |M-Real.exp (w z)| * f₀ z.2)
      (θ.prod μ) := by
    have hi := (hfprod.const_mul M).sub hewprod
    convert hi.abs using 1
    funext z
    change |M-Real.exp (w z)| * f₀ z.2 =
      |M*f₀ z.2-Real.exp (w z)*f₀ z.2|
    rw [← sub_mul, abs_mul, abs_of_nonneg (hf₀pos _)]
  have haxis' : ∀ᵐ x ∂μ,
      (∫ u, |M-Real.exp (w (u,x))| ∂θ) ≤ |M-1|+η := by
    filter_upwards [he.prod_left_ae,haxis] with x hx hax
    have hi : Integrable (fun u => |M-Real.exp (w (u,x))|) θ :=
      ((integrable_const M).sub hx).abs
    have hi' : Integrable (fun u => |Real.exp (w (u,x))-1|) θ :=
      (hx.sub (integrable_const (1 : ℝ))).abs
    calc
      (∫ u, |M-Real.exp (w (u,x))| ∂θ) ≤
          ∫ u, |M-1|+|Real.exp (w (u,x))-1| ∂θ := by
            apply integral_mono hi ((integrable_const _).add hi')
            intro u
            calc
              |M-Real.exp (w (u,x))| ≤ |M-1|+|1-Real.exp (w (u,x))| :=
                abs_sub_le M 1 _
              _ = _ := by
                change |M-1| + |1-Real.exp (w (u,x))| =
                  |M-1| + |Real.exp (w (u,x))-1|
                rw [abs_sub_comm (1 : ℝ) (Real.exp (w (u,x)))]
      _ = |M-1|+(∫ u, |Real.exp (w (u,x))-1| ∂θ) := by
          rw [integral_add (integrable_const _) hi']
          simp
      _ ≤ |M-1|+η := by linarith
  have hweighted := weighted_frozen_axis_integral_bound θ μ
    (fun z => |M-Real.exp (w z)|) f₀ hf₀ (.of_forall hf₀pos) hdiff haxis'
  have hnum : (∫ z, |M-Real.exp (w z)| * f₀ z.2 ∂θ.prod μ) ≤ 2*η := by
    rw [hf₀mass,mul_one] at hweighted
    linarith
  have hrewrite : (fun z : U × E =>
      Real.exp (w z)*|M*Real.exp (-w z)*f₀ z.2-f₀ z.2|) =
      fun z => |M-Real.exp (w z)| * f₀ z.2 := by
    funext z
    have hexp : Real.exp (w z)*Real.exp (-w z)=1 := by
      rw [← Real.exp_add]
      simp
    calc
      Real.exp (w z)*|M*Real.exp (-w z)*f₀ z.2-f₀ z.2| =
          Real.exp (w z)*|M*Real.exp (-w z)-1| * f₀ z.2 := by
            rw [show M*Real.exp (-w z)*f₀ z.2-f₀ z.2 =
              (M*Real.exp (-w z)-1)*f₀ z.2 by ring,abs_mul,
              abs_of_nonneg (hf₀pos _)]
            ring
      _ = |Real.exp (w z)*(M*Real.exp (-w z)-1)| * f₀ z.2 := by
            rw [abs_mul,abs_of_pos (Real.exp_pos _)]
      _ = |M-Real.exp (w z)| * f₀ z.2 := by
            rw [show Real.exp (w z)*(M*Real.exp (-w z)-1) =
              M-Real.exp (w z) by nlinarith [hexp]]
  rw [integral_normalizedTilt _ w hw hM, hrewrite]
  apply (div_le_iff₀ hM).2
  nlinarith [mul_nonneg hη (by linarith : 0 ≤ 2*M-1)]

end SlowEquilibration.ConditionedEntrance
