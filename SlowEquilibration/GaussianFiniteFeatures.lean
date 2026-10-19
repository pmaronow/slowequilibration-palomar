-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianRegression
public import Mathlib.Probability.Distributions.Gaussian.CharFun
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-! # Genuine finite Gaussian feature laws from their literal Gram kernel -/
namespace SlowEquilibration.GaussianFiniteFeatures
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E F I : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [Fintype I]

def observation (f : I → E →L[ℝ] ℝ) : E →L[ℝ] EuclideanSpace ℝ I :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi f)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I] in
lemma observation_apply (f : I → E →L[ℝ] ℝ) (x : E) (i : I) : observation f x i=f i x := rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma observation_adjoint (f : I → E →L[ℝ] ℝ) (u : EuclideanSpace ℝ I) :
    (observation f).adjoint u=∑ i, (u i) • (f i).adjoint 1 := by
  apply ext_inner_right ℝ
  intro x
  rw [(observation f).adjoint_inner_left,PiLp.inner_apply,sum_inner]
  apply Finset.sum_congr rfl
  intro i hi
  rw [real_inner_smul_left,(f i).adjoint_inner_left]
  simp only [RCLike.inner_apply,RCLike.conj_to_real,observation_apply]
  ring

/-- Equal feature Gram kernels give equality of the actual joint Gaussian law. -/
theorem observation_law_eq (f : I → E →L[ℝ] ℝ) (g : I → F →L[ℝ] ℝ)
    (hgram : ∀ i j,inner ℝ ((f i).adjoint 1) ((f j).adjoint 1)=
      inner ℝ ((g i).adjoint 1) ((g j).adjoint 1)) :
    (stdGaussian E).map (observation f)=(stdGaussian F).map (observation g) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      ContinuousLinearMap.integral_id_map IsGaussian.integrable_id,
      integral_id_stdGaussian,integral_id_stdGaussian,map_zero,map_zero]
  · ext u v
    rw [covarianceBilin_map IsGaussian.memLp_two_id,covarianceBilin_map IsGaussian.memLp_two_id,
      covarianceBilin_stdGaussian,covarianceBilin_stdGaussian,innerSL_apply_apply,
      innerSL_apply_apply,observation_adjoint,observation_adjoint,observation_adjoint,
      observation_adjoint]
    simp only [sum_inner,inner_sum,real_inner_smul_left,real_inner_smul_right]
    simp_rw [hgram]

/-- The ordinary coordinate-vector law is equal as well; no Hilbert norm
convention is used to alter its actual probability distribution. -/
theorem feature_law_eq (f : I → E →L[ℝ] ℝ) (g : I → F →L[ℝ] ℝ)
    (hgram : ∀ i j,inner ℝ ((f i).adjoint 1) ((f j).adjoint 1)=
      inner ℝ ((g i).adjoint 1) ((g j).adjoint 1)) :
    (stdGaussian E).map (fun x i => f i x)=(stdGaussian F).map (fun x i => g i x) := by
  have h := congrArg (Measure.map (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)))
    (observation_law_eq f g hgram)
  rw [Measure.map_map (by fun_prop) (by fun_prop),Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h

end
end SlowEquilibration.GaussianFiniteFeatures
