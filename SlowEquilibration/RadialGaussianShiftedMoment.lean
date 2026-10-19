-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.RadialLaplaceBounds

/-! First moments of a true density under a Gaussian envelope, allowing
the envelope center to move under the exact physical energy tilt. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.RadialGaussianBounds
open Set MeasureTheory
set_option maxHeartbeats 300000

theorem density_shifted_first_moment_upper {f : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hf : IntegrableOn f U) (h0 : ∀ k∈U,0 ≤ f k)
    {A a center m : ℝ} (hA : 0 ≤ A) (ha : 0 < a)
    (henv : ∀ k∈U,f k ≤ A*gaussian a center k) :
    (∫ k in U,|k-m| * f k) ≤
      A*(Real.sqrt (Real.pi/(a/2))/Real.sqrt a)+
        |center-m| * A*Real.sqrt (Real.pi/a) := by
  let g : ℝ → ℝ := fun k => A*(|k-center| * gaussian a center k)+
    (|center-m| * A)*gaussian a center k
  have hg : Integrable g :=
    ((gaussian_moment_integrable ha center).const_mul A).add
      ((gaussian_integrable ha center).const_mul (|center-m| * A))
  have hpoint : ∀ k∈U,|k-m| * f k ≤ g k := by
    intro k hk
    have htriangle : |k-m| ≤ |k-center|+|center-m| := abs_sub_le k center m
    calc
      _ ≤ (|k-center|+|center-m|)*f k := mul_le_mul_of_nonneg_right htriangle (h0 k hk)
      _ ≤ (|k-center|+|center-m|)*(A*gaussian a center k) :=
        mul_le_mul_of_nonneg_left (henv k hk) (by positivity)
      _=g k := by dsimp [g];ring
  have hi : IntegrableOn (fun k => |k-m| * f k) U := by
    apply (hg.restrict (s := U)).mono'
    · exact (by fun_prop : Continuous (fun k : ℝ => |k-m|)).aestronglyMeasurable.mul hf.aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hU] with k hk
      rw [Real.norm_of_nonneg (mul_nonneg (abs_nonneg _) (h0 k hk))]
      exact hpoint k hk
  calc
    _ ≤ ∫ k in U,g k := setIntegral_mono_on hi (hg.restrict (s := U)) hU hpoint
    _ ≤ ∫ k : ℝ,g k := setIntegral_le_integral hg (ae_of_all _ (fun k => by
      dsimp [g,gaussian]
      positivity))
    _=A*(∫ k : ℝ,|k-center| * gaussian a center k)+
        |center-m| * A*Real.sqrt (Real.pi/a) := by
      rw [integral_add ((gaussian_moment_integrable ha center).const_mul A)
        ((gaussian_integrable ha center).const_mul (|center-m| * A)),
        integral_const_mul,integral_const_mul,gaussian_integral]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (gaussian_first_moment_le ha center) hA
      linarith

end SlowEquilibration.RadialGaussianBounds
