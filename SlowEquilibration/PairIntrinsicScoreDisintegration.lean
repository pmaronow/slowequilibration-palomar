-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairIntrinsicFrameObservation
public import SlowEquilibration.PairValueObservationGrouping

/-! Actual intrinsic two-point Kac--Rice posterior disintegration through
its true mixed-score or proper pure-value conditional density. -/
@[expose] public section
namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet SphericalForm
open GaussianRegression GaussianObservationCoercivity WholeFieldRegression NormalizedPairObservations
open IntrinsicHessianLaw IntrinsicGradientRegression SphericalPairIntrinsicCoordinates
open scoped RealInnerProductSpace ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Exact full-disorder mixed conditional-score formula for the literal
intrinsic pair Kac--Rice intensity, with a dimension-uniform actual radius. -/
theorem uniform_intrinsic_mixed_score_disintegration (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hdeg : 4 ≤ μ.minDegree) :
    ∃ ρ0 : ℝ,0 < ρ0 ∧ ∀ n : ℕ,∀ x y : Vector (n+1),
      ∀ (hx : ‖x‖^2=(n+1:ℕ)) (hy : ‖y‖^2=(n+1:ℕ)), |overlap x y| ≤ ρ0 →
      ∀ (phi : Disorder (n+1) μ.maxDegree → ℝ≥0∞),Measurable phi →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let e:=tangentFrame x hx
      let f:=tangentFrame y hy
      observationPdf (pairIntrinsicGamma c x y) 0 * (∫⁻ J,phi J ∂coefficientKernel (pairIntrinsicGamma c x y) 0)=
        observationPdf (pairGradient c x y e f) 0 *
          ∫⁻ b,observationPdf (residualPairScore c x y e f) b *
            ∫⁻ J,phi J ∂coefficientKernel (groupedMixedPair c x y e f) (WithLp.toLp 2 (b,0)) := by
  obtain ⟨ρ0,δ,hρ0,hδ,hall⟩:=uniform_mixed_pair_nondegenerate μ hQ hnp hdeg
  refine ⟨ρ0,hρ0,?_⟩
  intro n x y hx hy hr phi hphi
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let e:=tangentFrame x hx
  let f:=tangentFrame y hy
  have hfull:=groupedMixedPair_coercive c x y e f
    (hall (n+1) n (by omega) x y hx hy e f (tangentFrame_orthonormal x hx)
      (tangentFrame_orthonormal y hy) (tangentFrame_tangent x hx) (tangentFrame_tangent y hy) hr).1
  have hgrad:=pair_snd_coercive (scorePair c x y) (pairGradient c x y e f) hfull
  have hA:=observation_surjective _ hδ hgrad
  have hres:=residual_coercivity (pairGradient c x y e f) hA (scorePair c x y) hδ.le hfull
  have hdis:=coefficientKernel_nonorthogonal_zero_disintegration (pairGradient c x y e f) hA
    (scorePair c x y) (observation_surjective _ hδ hres) (observation_surjective _ hδ hfull) phi hphi
  rw [← pairGradient_pdf_zero_eq_intrinsic c x y hx hy,
    ← pairGradient_kernel_zero_eq_intrinsic c x y hx hy hA]
  exact congrArg (fun z : ℝ≥0∞=>observationPdf (pairGradient c x y e f) 0*z) hdis

/-- The proper value-only version omits both redundant radial coordinates;
its pointwise zero-fiber density is derived from the true Gaussian residual. -/
theorem uniform_intrinsic_value_disintegration (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hdeg : 4 ≤ μ.minDegree) :
    ∃ ρ0 : ℝ,0 < ρ0 ∧ ∀ n : ℕ,∀ x y : Vector (n+1),
      ∀ (hx : ‖x‖^2=(n+1:ℕ)) (hy : ‖y‖^2=(n+1:ℕ)), |overlap x y| ≤ ρ0 →
      ∀ (phi : Disorder (n+1) μ.maxDegree → ℝ≥0∞),Measurable phi →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let e:=tangentFrame x hx
      let f:=tangentFrame y hy
      observationPdf (pairIntrinsicGamma c x y) 0 * (∫⁻ J,phi J ∂coefficientKernel (pairIntrinsicGamma c x y) 0)=
        observationPdf (pairGradient c x y e f) 0 *
          ∫⁻ b,observationPdf (residualPairValue c x y e f) b *
            ∫⁻ J,phi J ∂coefficientKernel (groupedValuePair c x y e f) (WithLp.toLp 2 (b,0)) := by
  obtain ⟨ρ0,δ,hρ0,hδ,hall⟩:=uniform_value_pair_nondegenerate μ hQ hdeg
  refine ⟨ρ0,hρ0,?_⟩
  intro n x y hx hy hr phi hphi
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let e:=tangentFrame x hx
  let f:=tangentFrame y hy
  have hfull:=groupedValuePair_coercive c x y e f
    (hall (n+1) n (by omega) x y hx hy e f (tangentFrame_orthonormal x hx)
      (tangentFrame_orthonormal y hy) (tangentFrame_tangent x hx) (tangentFrame_tangent y hy) hr).1
  have hgrad:=pair_snd_coercive (valuePair c x y) (pairGradient c x y e f) hfull
  have hA:=observation_surjective _ hδ hgrad
  have hres:=residual_coercivity (pairGradient c x y e f) hA (valuePair c x y) hδ.le hfull
  have hdis:=coefficientKernel_nonorthogonal_zero_disintegration (pairGradient c x y e f) hA
    (valuePair c x y) (observation_surjective _ hδ hres) (observation_surjective _ hδ hfull) phi hphi
  rw [← pairGradient_pdf_zero_eq_intrinsic c x y hx hy,
    ← pairGradient_kernel_zero_eq_intrinsic c x y hx hy hA]
  exact congrArg (fun z : ℝ≥0∞=>observationPdf (pairGradient c x y e f) 0*z) hdis

end
end SlowEquilibration.PairObservationSmallOverlap
