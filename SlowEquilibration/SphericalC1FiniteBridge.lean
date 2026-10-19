-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalC1Dynkin
public import SlowEquilibration.SphericalReversibility

/-! The canonical C¹ construction coincides with the established finite
polynomial spherical diffusion, by genuine physical pathwise uniqueness. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalC1Dynamics
open Set MeasureTheory ProbabilityTheory SphericalModel SphericalDynamics SphericalReversibility
open SphericalAging SphericalAging.HardSphereDynamics
open scoped NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {N : ℕ}

theorem process_eq_mixed (hN : N≠0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    ∀ᵐ ω ∂VectorBrownian.law N,∀ t,t≤T →
      process β (mixedGradient μ J) ((mixedGradient_contDiff μ J).of_le (by simp)) x t ω=
        mixedProcess μ J β x t ω := by
  apply physicalSolution_unique (NullAugmentation.driver (VectorBrownian.driver N)) β
    (mixedGradient μ J) ((mixedGradient_contDiff μ J).of_le (by simp)) x T
  · exact process_physical hN β _ _ x hx T
  · exact mixedProcess_physical hN μ J β x hx T
  · exact (process_onSphere hN β _ _ x hx).mono (fun _ h t _ => h t)
  · exact (mixedProcess_onSphere hN μ J β x hx).mono (fun _ h t _ => h t)

theorem expectation_eq_mixed (hN : N≠0) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (x : State N) (hx : OnSphere x)
    (t : ℝ≥0) (f : State N → ℝ) :
    expectation β (mixedGradient μ J) ((mixedGradient_contDiff μ J).of_le (by simp)) t f x=
      mixedExpectation μ J β t f x := by
  rw [mixedExpectation_eq_actual]
  exact integral_congr_ae ((process_eq_mixed hN μ J β x hx t).mono
    (fun _ h => congrArg f (h t le_rfl)))

theorem expectation_eq_kernel (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (t : ℝ≥0) (f : State N → ℝ) (hf : StronglyMeasurable f) (x : State N) :
    expectation β g hg t f x=∫ y,f y ∂transitionKernel β g hg t x := by
  rw [transitionKernel_apply,transitionLaw,integral_map (process_measurable β g hg x t).aemeasurable
    hf.aestronglyMeasurable]
  rfl

theorem expectation_stronglyMeasurable (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (t : ℝ≥0) (f : State N → ℝ) (hf : StronglyMeasurable f) :
    StronglyMeasurable (expectation β g hg t f) := by
  have he : expectation β g hg t f=fun x => ∫ y,f y ∂transitionKernel β g hg t x :=
    funext (expectation_eq_kernel β g hg t f hf)
  rw [he]
  exact hf.integral_kernel

theorem expectation_norm_le (β : ℝ) (g : State N → State N) (hg : ContDiff ℝ 1 g)
    (t : ℝ≥0) (f : State N → ℝ) (C : ℝ) (hC : ∀ y,‖f y‖≤C) (x : State N) :
    ‖expectation β g hg t f x‖≤C := by
  simpa only [expectation,probReal_univ,mul_one] using
    norm_integral_le_of_norm_le_const (μ := VectorBrownian.law N)
      (.of_forall (fun ω => hC (process β g hg x t ω)))

end SlowEquilibration.SphericalC1Dynamics
