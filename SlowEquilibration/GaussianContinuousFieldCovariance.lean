-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianContinuousFieldLaw

@[expose] public section

/-! Actual evaluation covariance identifies the ordinary whole continuous-field law. -/
namespace SlowEquilibration.GaussianContinuousFieldLaw
noncomputable section
open MeasureTheory ProbabilityTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K E F : Type*}
  [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K] [T2Space K] [Nonempty K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

omit [CompactSpace K] [SecondCountableTopology K] [T2Space K] [Nonempty K]
  [MeasurableSpace E] [BorelSpace E] in
lemma evaluation_feature_inner (X : E →L[ℝ] C(K,ℝ)) (x y : K) :
    inner ℝ ((evaluationFeature X x).adjoint 1) ((evaluationFeature X y).adjoint 1)=
      evaluationFeature X x ((evaluationFeature X y).adjoint 1) := by
  rw [(evaluationFeature X x).adjoint_inner_left]
  simp only [RCLike.inner_apply,RCLike.conj_to_real,mul_one]

omit [CompactSpace K] [SecondCountableTopology K] [T2Space K] [Nonempty K] in
lemma evaluation_covariance (X : E →L[ℝ] C(K,ℝ)) (x y : K) :
    cov[fun z => X z x,fun z => X z y;stdGaussian E]=
      evaluationFeature X x ((evaluationFeature X y).adjoint 1) := by
  have heq (a : K) : (fun z : E => X z a)=
      fun z => inner ℝ ((evaluationFeature X a).adjoint 1) z := by
    funext z
    rw [(evaluationFeature X a).adjoint_inner_left]
    simp only [RCLike.inner_apply,RCLike.conj_to_real,mul_one,evaluationFeature_apply]
  rw [heq x,heq y,← covarianceBilin_apply_eq_cov IsGaussian.memLp_two_id,
    covarianceBilin_stdGaussian,innerSL_apply_apply,evaluation_feature_inner]

/-- Every actual centered Gaussian evaluation covariance is enough; no
weak-convergence or pressure-law premise is introduced. -/
theorem continuous_field_law_eq_of_covariance (X : E →L[ℝ] C(K,ℝ))
    (Y : F →L[ℝ] C(K,ℝ))
    (hcov : ∀ x y : K,cov[fun z => X z x,fun z => X z y;stdGaussian E]=
      cov[fun z => Y z x,fun z => Y z y;stdGaussian F]) :
    (stdGaussian E).map X=(stdGaussian F).map Y := by
  apply continuous_field_law_eq X Y
  intro x y
  rw [evaluation_feature_inner,evaluation_feature_inner,
    ← evaluation_covariance,← evaluation_covariance]
  exact hcov x y

end
end SlowEquilibration.GaussianContinuousFieldLaw
