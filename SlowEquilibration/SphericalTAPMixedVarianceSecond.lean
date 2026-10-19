-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedScoreSecond

@[expose] public section

/-! Contact second derivative of the literal conditioned latitude variance. -/

namespace SlowEquilibration.SphericalTAPMixedVarianceSecond
noncomputable section
open SphericalTAPMixedBandExponent SphericalTAPMixedScoreSecond
open SphericalTAPMixedGradientSecond SphericalMarkedWindows ConditionedEntrance
set_option autoImplicit false

private theorem score_smooth (μ : FiniteMixture) (Q : ℝ) :
    ContDiff ℝ ⊤ (sourceMixedScoreReduction μ Q) := by
  unfold sourceMixedScoreReduction sourceMixedCross
  simp only [scorePairEquiv_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  unfold valueTheta radialTheta monomialSum FiniteMixture.xi FiniteMixture.xi1
  fun_prop

private theorem gradient_smooth (μ : FiniteMixture) (Q : ℝ) :
    ContDiff ℝ ⊤ (sourceMixedGradientReduction μ Q) := by
  unfold sourceMixedGradientReduction FiniteMixture.xi1
  fun_prop

theorem sourceMixedVariance_second_contact
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) :
    deriv (deriv (sourceMixedVariance μ Q)) (Real.sqrt Q) =
      4*Q*μ.xi2 Q-2*(1-Q)*Q*((μ.xi2 Q)^2/μ.xi1 Q+μ.v1 Q) := by
  let S := sourceMixedScoreReduction μ Q
  let D := sourceMixedGradientReduction μ Q
  have hv : sourceMixedVariance μ Q = fun a => μ.xi 1-S a-D a := by
    funext a
    rfl
  have hs : Differentiable ℝ S := (score_smooth μ Q).differentiable (by simp)
  have hd : Differentiable ℝ D := (gradient_smooth μ Q).differentiable (by simp)
  have hfirst : deriv (sourceMixedVariance μ Q) =
      fun a => -deriv S a-deriv D a := by
    funext a
    rw [hv]
    convert (((hasDerivAt_const a (μ.xi 1)).sub (hs a).hasDerivAt).sub
      (hd a).hasDerivAt).deriv using 1
    ring
  rw [hfirst]
  have hsd : DifferentiableAt ℝ (deriv S) (Real.sqrt Q) := by
    have hh : ContDiffAt ℝ 2 S (Real.sqrt Q) :=
      (score_smooth μ Q).contDiffAt.of_le (by norm_num)
    have h1 : ContDiffAt ℝ 1 (deriv S) (Real.sqrt Q) :=
      hh.derivWithin (by norm_num)
    exact h1.differentiableAt (by norm_num)
  have hdd : DifferentiableAt ℝ (deriv D) (Real.sqrt Q) := by
    have hh : ContDiffAt ℝ 2 D (Real.sqrt Q) :=
      (gradient_smooth μ Q).contDiffAt.of_le (by norm_num)
    have h1 : ContDiffAt ℝ 1 (deriv D) (Real.sqrt Q) :=
      hh.derivWithin (by norm_num)
    exact h1.differentiableAt (by norm_num)
  have hh := (((hsd.hasDerivAt).neg).sub hdd.hasDerivAt).deriv
  convert hh using 1
  rw [sourceMixedScoreReduction_second_contact μ hQ hnp,
    sourceMixedGradientReduction_second_contact μ hQ]
  ring

end
end SlowEquilibration.SphericalTAPMixedVarianceSecond
