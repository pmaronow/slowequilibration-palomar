-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianNonorthogonalRegression
public import SlowEquilibration.PairResidualScoreCoercivity

/-! Literal pair-gradient-zero disintegration of all original tensor
coefficients through the actual conditional score density. -/
@[expose] public section
namespace SlowEquilibration.WholeFieldRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel
open GaussianRegression GaussianObservationCoercivity
open scoped ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {N P : ℕ} {F G : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

/-- Exact full-disorder posterior identity at the specified zero-gradient
fiber, with the genuine nonorthogonal conditional score law. -/
theorem coefficientKernel_nonorthogonal_zero_disintegration
    (A : EuclideanDisorder N P →L[ℝ] F) (hA : Surjective A)
    (B : EuclideanDisorder N P →L[ℝ] G) (hB : Surjective (B.comp (GaussianRegression.residual A)))
    (hC : Surjective (pairHilbert B A)) (phi : Disorder N P → ℝ≥0∞) (hphi : Measurable phi) :
    (∫⁻ J,phi J ∂coefficientKernel A 0)=
      ∫⁻ b,observationPdf (B.comp (GaussianRegression.residual A)) b *
        ∫⁻ J,phi J ∂coefficientKernel (pairHilbert B A) (WithLp.toLp 2 (b,0)) := by
  have h:=nonorthogonal_zero_disintegration A hA B hB hC
    (fun g => phi (unpackCLM N P g)) (hphi.comp (unpackCLM N P).continuous.measurable)
  rw [coefficientKernel_apply,lintegral_map hphi (unpackCLM N P).continuous.measurable,h]
  have hm : Measurable (fun b : G => ∫⁻ J,phi J
      ∂coefficientKernel (pairHilbert B A) (WithLp.toLp 2 (b,0))) :=
    hphi.lintegral_kernel.comp (by fun_prop)
  have heq : (fun b : G => ∫⁻ g,phi (unpackCLM N P g)
      ∂regressionKernel (pairHilbert B A) (WithLp.toLp 2 (b,0)))=
      (fun b : G => ∫⁻ J,phi J ∂coefficientKernel (pairHilbert B A) (WithLp.toLp 2 (b,0))) := by
    funext b
    rw [coefficientKernel_apply,lintegral_map hphi (unpackCLM N P).continuous.measurable]
  rw [heq,observationLaw_eq_explicit_density _ hB]
  exact lintegral_withDensity_eq_lintegral_mul volume (observationPdf_measurable _) hm

end
end SlowEquilibration.WholeFieldRegression

namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet
open WholeFieldRegression GaussianRegression GaussianObservationCoercivity NormalizedPairObservations
open scoped ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Genuine full-tensor pair disintegration on a dimension-uniform overlap
neighborhood, preserving every Borel whole-disorder mark. -/
theorem uniform_pair_score_zero_disintegration (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hdeg : 4 ≤ μ.minDegree) :
    ∃ ρ0 : ℝ,0 < ρ0 ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x y : Vector N),
      ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) → |overlap x y| ≤ ρ0 →
      ∀ (phi : Disorder N μ.maxDegree → ℝ≥0∞),Measurable phi →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      (∫⁻ J,phi J ∂coefficientKernel (pairGradient c x y e f) 0)=
        ∫⁻ b,observationPdf (residualPairScore c x y e f) b *
          ∫⁻ J,phi J ∂coefficientKernel (groupedMixedPair c x y e f) (WithLp.toLp 2 (b,0)) := by
  obtain ⟨ρ0,δ,hρ0,hδ,hall⟩:=uniform_mixed_pair_nondegenerate μ hQ hnp hdeg
  refine ⟨ρ0,hρ0,?_⟩
  intro N m hN x y hx hy e f he hf htanx htany hρ phi hphi
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hfull:=groupedMixedPair_coercive c x y e f
    (hall N m hN x y hx hy e f he hf htanx htany hρ).1
  have hGrad:=pair_snd_coercive (scorePair c x y) (pairGradient c x y e f) hfull
  have hA:=observation_surjective _ hδ hGrad
  have hres:=residual_coercivity (pairGradient c x y e f) hA (scorePair c x y) hδ.le hfull
  exact coefficientKernel_nonorthogonal_zero_disintegration (pairGradient c x y e f) hA
    (scorePair c x y) (observation_surjective _ hδ hres) (observation_surjective _ hδ hfull) phi hphi

end
end SlowEquilibration.PairObservationSmallOverlap
