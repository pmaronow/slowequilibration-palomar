-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegressionSchur
public import SlowEquilibration.GaussianResidualCoercivity

/-! Genuine sequential Gaussian disintegration at a specified gradient-zero
fiber, without requiring the original mark observation to be independent. -/
@[expose] public section
namespace SlowEquilibration.GaussianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory GaussianObservationCoercivity
open scoped RealInnerProductSpace ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

omit [FiniteDimensional ℝ G] in
lemma mark_gradient_pair_ker (A : E →L[ℝ] F) (B : E →L[ℝ] G) (_hA : Surjective A) :
    (pairHilbert B A).ker=A.ker ⊓ (B.comp (residual A)).ker := by
  ext z
  change (WithLp.toLp 2 (B z,A z)=0) ↔ A z=0 ∧ B (residual A z)=0
  constructor
  · intro hz
    have hAz:=congrArg WithLp.snd hz
    have hBz:=congrArg WithLp.fst hz
    change A z=0 at hAz
    change B z=0 at hBz
    exact ⟨hAz,by simp only [residual,sub_apply,ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,hAz,map_zero,sub_zero,hBz]⟩
  · rintro ⟨hAz,hBz⟩
    have hres : residual A z=z := by
      change z-lift A (A z)=z
      rw [hAz,map_zero,sub_zero]
    rw [hres] at hBz
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · exact hBz
    · exact hAz

lemma residual_mark_joint_target (A : E →L[ℝ] F) (hA : Surjective A) (B : E →L[ℝ] G)
    (hB : Surjective (B.comp (residual A))) (b : G) :
    pairHilbert B A (lift (B.comp (residual A)) b)=WithLp.toLp 2 (b,0) := by
  have hBA:=(residual_observation_cross_zero A hA B)
  have hAB:=congrArg ContinuousLinearMap.adjoint hBA
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,map_zero] at hAB
  have hAz:=orthogonal_observation_lift_zero A (B.comp (residual A)) hAB b
  have hres : residual A (lift (B.comp (residual A)) b)=lift (B.comp (residual A)) b := by
    change lift (B.comp (residual A)) b-lift A (A (lift (B.comp (residual A)) b))=lift (B.comp (residual A)) b
    rw [hAz,map_zero,sub_zero]
  rw [pairHilbert_apply]
  congr 1
  apply Prod.ext
  · have h:=observation_lift_apply (B.comp (residual A)) hB b
    change B (residual A (lift (B.comp (residual A)) b))=b at h
    rwa [hres] at h
  · exact hAz

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace G] [BorelSpace G]

/-- Every Borel function of the original Gaussian field survives exact
sequential disintegration on the literal gradient-zero fiber. -/
theorem nonorthogonal_zero_disintegration (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E →L[ℝ] G) (hB : Surjective (B.comp (residual A)))
    (hC : Surjective (pairHilbert B A)) (phi : E → ℝ≥0∞) (hphi : Measurable phi) :
    (∫⁻ z,phi z ∂regressionKernel A 0)=
      ∫⁻ b,∫⁻ z,phi z ∂regressionKernel (pairHilbert B A) (WithLp.toLp 2 (b,0))
        ∂observationLaw (B.comp (residual A)) := by
  have hBA:=residual_observation_cross_zero A hA B
  have hAB:=congrArg ContinuousLinearMap.adjoint hBA
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint,map_zero] at hAB
  have h:=orthogonal_zero_disintegration A (B.comp (residual A)) (pairHilbert B A)
    hA hB hC hAB (mark_gradient_pair_ker A B hA) phi hphi
  simpa only [residual_mark_joint_target A hA B hB] using h

end
end SlowEquilibration.GaussianRegression
