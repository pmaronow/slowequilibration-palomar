-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFiniteFeatures
public import SlowEquilibration.ContinuousFieldLaw

@[expose] public section

/-! # Actual continuous Gaussian field law from its evaluation covariance kernel -/
namespace SlowEquilibration.GaussianContinuousFieldLaw
noncomputable section
open MeasureTheory ProbabilityTheory TopologicalSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K E F : Type*}
  [TopologicalSpace K] [CompactSpace K] [SecondCountableTopology K] [T2Space K] [Nonempty K]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Literal scalar evaluation feature of the actual whole continuous field. -/
def evaluationFeature (X : E →L[ℝ] C(K,ℝ)) (x : K) : E →L[ℝ] ℝ :=
  (ContinuousMap.evalCLM ℝ x).comp X

omit [CompactSpace K] [SecondCountableTopology K] [T2Space K] [Nonempty K]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma evaluationFeature_apply (X : E →L[ℝ] C(K,ℝ)) (x : K) (z : E) :
    evaluationFeature X x z=X z x := rfl

/-- Equality of the actual evaluation Gram kernel determines the full
Borel continuous-field law, despite different coefficient spaces. -/
theorem continuous_field_law_eq (X : E →L[ℝ] C(K,ℝ)) (Y : F →L[ℝ] C(K,ℝ))
    (hgram : ∀ x y : K, inner ℝ ((evaluationFeature X x).adjoint 1)
        ((evaluationFeature X y).adjoint 1)=
      inner ℝ ((evaluationFeature Y x).adjoint 1) ((evaluationFeature Y y).adjoint 1)) :
    (stdGaussian E).map X=(stdGaussian F).map Y := by
  apply ContinuousFieldLaw.continuous_map_law_eq_of_finite_laws
    (stdGaussian E) (stdGaussian F) X Y X.continuous.measurable Y.continuous.measurable
  intro I
  let f : I → E →L[ℝ] ℝ := fun i => evaluationFeature X (denseSeq K (i : ℕ))
  let g : I → F →L[ℝ] ℝ := fun i => evaluationFeature Y (denseSeq K (i : ℕ))
  exact GaussianFiniteFeatures.feature_law_eq f g (fun i j => hgram _ _)

end
end SlowEquilibration.GaussianContinuousFieldLaw
