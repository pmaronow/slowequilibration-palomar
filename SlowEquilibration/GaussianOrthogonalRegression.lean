-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegressionDensity

/-! Sequential regression of orthogonal Gaussian observations, for arbitrary
nonnegative Borel marks of the entire coefficient vector. The identity holds
at the literal zero target, not merely for almost every observation. -/

@[expose] public section

namespace SlowEquilibration.GaussianRegression

open MeasureTheory ProbabilityTheory Set Function
open scoped ENNReal Topology RealInnerProductSpace

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

lemma orthogonal_observation_lift_zero (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (hAB : A.comp B.adjoint = 0) (b : G) : A (lift B b) = 0 := by
  exact congrArg (fun L : G →L[ℝ] F => L ((gram B).inverse b)) hAB

lemma orthogonal_observation_symm (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (hAB : A.comp B.adjoint = 0) : B.comp A.adjoint = 0 := by
  have h := congrArg ContinuousLinearMap.adjoint hAB
  simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    map_zero] using h

/-- Orthogonality of the observations makes their exact residual projections
compose to the residual of any equivalent full joint observation. -/
theorem orthogonal_joint_residual (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (C : E →L[ℝ] H) (hA : Surjective A) (hB : Surjective B) (hC : Surjective C)
    (hAB : A.comp B.adjoint = 0) (hker : C.ker = A.ker ⊓ B.ker) :
    residual C = (residual A).comp (residual B) := by
  have hBA := orthogonal_observation_symm A B hAB
  rw [residual_eq_starProjection C hC]
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · rw [hker]
    refine ⟨residual_mem_ker A hA (residual B x), ?_⟩
    change B (residual B x - lift A (A (residual B x))) = 0
    rw [map_sub, orthogonal_observation_lift_zero B A hBA,
      show B (residual B x) = 0 from residual_mem_ker B hB x, sub_self]
  · intro y hy
    rw [hker] at hy
    have he : x - residual A (residual B x) =
        lift B (B x) + lift A (A (residual B x)) := by
      simp only [residual, sub_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.comp_apply]
      abel
    change inner ℝ (x - residual A (residual B x)) y = 0
    rw [he, real_inner_comm, inner_add_right,
      lift_orthogonal_ker B (B x) y hy.2,
      lift_orthogonal_ker A (A (residual B x)) y hy.1, add_zero]

/-- The canonical joint lift of a score-only displacement is the original
score lift, proved by orthogonality to the actual joint kernel. -/
theorem orthogonal_joint_lift (B : E →L[ℝ] G) (C : E →L[ℝ] H)
    (hC : Surjective C) (hker : C.ker ≤ B.ker) (b : G) :
    lift C (C (lift B b)) = lift B b := by
  have hz : residual C (lift B b) = 0 := by
    rw [residual_eq_starProjection C hC]
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (C.ker.zero_mem)
    intro y hy
    rw [sub_zero, real_inner_comm]
    exact lift_orthogonal_ker B b y (hker hy)
  have h := residual_add_lift_observation C (lift B b)
  rwa [hz, zero_add] at h

variable [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace H] [BorelSpace H]

/-- Sequential disintegration at a specified zero observation. Every Borel
function of the complete coefficient field is retained. -/
theorem orthogonal_zero_disintegration (A : E →L[ℝ] F) (B : E →L[ℝ] G)
    (C : E →L[ℝ] H) (hA : Surjective A) (hB : Surjective B) (hC : Surjective C)
    (hAB : A.comp B.adjoint = 0) (hker : C.ker = A.ker ⊓ B.ker)
    (phi : E → ℝ≥0∞) (hphi : Measurable phi) :
    (∫⁻ z, phi z ∂regressionKernel A 0) =
      ∫⁻ b, ∫⁻ z, phi z ∂regressionKernel C (C (lift B b)) ∂observationLaw B := by
  have hres := orthogonal_joint_residual A B C hA hB hC hAB hker
  have hsub : C.ker ≤ B.ker := hker ▸ inf_le_right
  have hsamp (b : G) (g : E) :
      residual A (residual B g + lift B b) = residual C g + lift C (C (lift B b)) := by
    rw [map_add, orthogonal_joint_lift B C hC hsub, hres]
    change residual A (residual B g) + (lift B b - lift A (A (lift B b))) = _
    rw [orthogonal_observation_lift_zero A B hAB, map_zero, sub_zero]
    rfl
  rw [regressionKernel_apply, lintegral_map hphi (by fun_prop)]
  simp only [map_zero, add_zero]
  have hd := regression_disintegration B hB
    (fun p : G × E => phi (residual A p.2))
    (hphi.comp ((residual A).continuous.measurable.comp measurable_snd))
  change (∫⁻ z, phi (residual A z) ∂stdGaussian E) = _
  rw [hd]
  apply lintegral_congr
  intro b
  dsimp only
  rw [regressionKernel_apply, regressionKernel_apply,
    lintegral_map (show Measurable (fun y => phi (residual A y)) from
      hphi.comp (residual A).continuous.measurable) (by fun_prop),
    lintegral_map hphi (by fun_prop)]
  exact lintegral_congr fun g => congrArg phi (hsamp b g)

/-- Exact change to a rescaled observation law, before replacing that law by
its canonical Gaussian density. -/
theorem lintegral_observationLaw_rescale (B : E →L[ℝ] G) (r : ℝ) (hr : r ≠ 0)
    (f : G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ b, f b ∂observationLaw B) =
      ∫⁻ b, f (r • b) ∂observationLaw (r⁻¹ • B) := by
  unfold observationLaw
  rw [lintegral_map hf B.continuous.measurable,
    lintegral_map (show Measurable (fun b => f (r • b)) from hf.comp (by fun_prop)) (by fun_prop)]
  simp only [ContinuousLinearMap.smul_apply, smul_smul, mul_inv_cancel₀ hr, one_smul]

theorem scaled_observation_surjective (B : E →L[ℝ] G) (hB : Surjective B)
    (r : ℝ) (hr : r ≠ 0) : Surjective (r⁻¹ • B) := by
  intro b
  obtain ⟨g, hg⟩ := hB (r • b)
  refine ⟨g, ?_⟩
  simp only [ContinuousLinearMap.smul_apply, hg, smul_smul, inv_mul_cancel₀ hr, one_smul]

theorem observationPdf_measurable (B : E →L[ℝ] G) : Measurable (observationPdf B) := by
  unfold observationPdf
  fun_prop

end
end SlowEquilibration.GaussianRegression
