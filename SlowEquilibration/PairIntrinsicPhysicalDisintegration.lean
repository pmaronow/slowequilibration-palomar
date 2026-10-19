-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairIntrinsicScoreDisintegration
public import SlowEquilibration.PairValuePhysicalDensity
public import SlowEquilibration.PairScorePhysicalDensity
public import SlowEquilibration.GaussianDensityDilationIntegral

/-! Genuine physical mixed and proper-value intrinsic pair disintegration.
The full original disorder remains in every mark and posterior, and the
physical pair Jacobians are derived as N² and N from actual density transport. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPairMarkedWindows
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet SphericalForm
open GaussianRegression GaussianObservationCoercivity WholeFieldRegression NormalizedPairObservations
open IntrinsicHessianLaw IntrinsicGradientRegression SphericalPairIntrinsicCoordinates
open PairObservationSmallOverlap
open scoped ENNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

def pairMixedConditionedLaw {n P : ℕ} (c : Degree P → ℝ) (x y : Vector (n+1))
    (hx : ‖x‖^2=(n+1:ℕ)) (hy : ‖y‖^2=(n+1:ℕ)) (b : ScorePairSpace) : Measure (Disorder (n+1) P) :=
  coefficientKernel (groupedMixedPair c x y (tangentFrame x hx) (tangentFrame y hy))
    (WithLp.toLp 2 (Real.sqrt (n+1:ℕ) • b,0))

def pairValueConditionedLaw {n P : ℕ} (c : Degree P → ℝ) (x y : Vector (n+1))
    (hx : ‖x‖^2=(n+1:ℕ)) (hy : ‖y‖^2=(n+1:ℕ)) (b : ValuePairSpace) : Measure (Disorder (n+1) P) :=
  coefficientKernel (groupedValuePair c x y (tangentFrame x hx) (tangentFrame y hy))
    (WithLp.toLp 2 (Real.sqrt (n+1:ℕ) • b,0))

def pairMixedPhysicalPdf {n P : ℕ} (c : Degree P → ℝ) (x y : Vector (n+1))
    (hx : ‖x‖^2=(n+1:ℕ)) (hy : ‖y‖^2=(n+1:ℕ)) (b : ScorePairSpace) : ℝ≥0∞ :=
  ENNReal.ofReal (((n+1:ℕ):ℝ)^2)*
    observationPdf (residualPairScore c x y (tangentFrame x hx) (tangentFrame y hy))
      (Real.sqrt (n+1:ℕ) • b)

def pairValuePhysicalPdf {n P : ℕ} (c : Degree P → ℝ) (x y : Vector (n+1))
    (hx : ‖x‖^2=(n+1:ℕ)) (hy : ‖y‖^2=(n+1:ℕ)) (b : ValuePairSpace) : ℝ≥0∞ :=
  ENNReal.ofReal ((n+1:ℕ):ℝ)*
    observationPdf (residualPairValue c x y (tangentFrame x hx) (tangentFrame y hy))
      (Real.sqrt (n+1:ℕ) • b)

/-- Exact physical four-mark disintegration of the literal intrinsic pair
intensity; all conditioning maps are genuinely surjective on a radius fixed
before dimension, and every Borel full-field mark is retained. -/
theorem uniform_intrinsic_physical_mixed_disintegration (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hdeg : 4 ≤ μ.minDegree) :
    ∃ ρ0 : ℝ,0 < ρ0 ∧ ∀ n : ℕ,∀ x y : Vector (n+1),
      ∀ (hx : ‖x‖^2=(n+1:ℕ)) (hy : ‖y‖^2=(n+1:ℕ)), |overlap x y| ≤ ρ0 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let e:=tangentFrame x hx
      let f:=tangentFrame y hy
      Surjective (groupedMixedPair c x y e f) ∧
        ∀ (phi : Disorder (n+1) μ.maxDegree → ℝ≥0∞),Measurable phi →
          observationPdf (pairIntrinsicGamma c x y) 0 * (∫⁻ J,phi J ∂coefficientKernel (pairIntrinsicGamma c x y) 0)=
            observationPdf (pairGradient c x y e f) 0 *
              ∫⁻ b,pairMixedPhysicalPdf c x y hx hy b * ∫⁻ J,phi J ∂pairMixedConditionedLaw c x y hx hy b := by
  obtain ⟨ρ0,δ,hρ0,hδ,hall⟩:=uniform_mixed_pair_nondegenerate μ hQ hnp hdeg
  refine ⟨ρ0,hρ0,?_⟩
  intro n x y hx hy hr
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let e:=tangentFrame x hx
  let f:=tangentFrame y hy
  have hfull:=groupedMixedPair_coercive c x y e f
    (hall (n+1) n (by omega) x y hx hy e f (tangentFrame_orthonormal x hx)
      (tangentFrame_orthonormal y hy) (tangentFrame_tangent x hx) (tangentFrame_tangent y hy) hr).1
  have hC:=observation_surjective _ hδ hfull
  refine ⟨hC,?_⟩
  intro phi hphi
  have hgrad:=pair_snd_coercive (scorePair c x y) (pairGradient c x y e f) hfull
  have hA:=observation_surjective _ hδ hgrad
  have hres:=residual_coercivity (pairGradient c x y e f) hA (scorePair c x y) hδ.le hfull
  have hdis:=coefficientKernel_nonorthogonal_zero_disintegration (pairGradient c x y e f) hA
    (scorePair c x y) (observation_surjective _ hδ hres) hC phi hphi
  rw [← pairGradient_pdf_zero_eq_intrinsic c x y hx hy,
    ← pairGradient_kernel_zero_eq_intrinsic c x y hx hy hA,hdis]
  congr 1
  have ht:=lintegral_density_dilation
    (observationPdf (residualPairScore c x y e f)) (observationPdf_measurable _)
    (fun b=>ENNReal.ofReal_ne_top) (Real.sqrt_pos.mpr (by positivity : 0 < ((n+1:ℕ):ℝ)))
    (fun b=>∫⁻ J,phi J ∂coefficientKernel (groupedMixedPair c x y e f) (WithLp.toLp 2 (b,0)))
  rw [scorePairSpace_finrank,show (4:ℕ)=2*2 by norm_num,pow_mul,
    Real.sq_sqrt (Nat.cast_nonneg (n+1))] at ht
  exact ht

/-- Proper two-height physical disintegration, including pure models. Its
Jacobian is N and no redundant radial score is conditioned on. -/
theorem uniform_intrinsic_physical_value_disintegration (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hdeg : 4 ≤ μ.minDegree) :
    ∃ ρ0 : ℝ,0 < ρ0 ∧ ∀ n : ℕ,∀ x y : Vector (n+1),
      ∀ (hx : ‖x‖^2=(n+1:ℕ)) (hy : ‖y‖^2=(n+1:ℕ)), |overlap x y| ≤ ρ0 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let e:=tangentFrame x hx
      let f:=tangentFrame y hy
      Surjective (groupedValuePair c x y e f) ∧
        ∀ (phi : Disorder (n+1) μ.maxDegree → ℝ≥0∞),Measurable phi →
          observationPdf (pairIntrinsicGamma c x y) 0 * (∫⁻ J,phi J ∂coefficientKernel (pairIntrinsicGamma c x y) 0)=
            observationPdf (pairGradient c x y e f) 0 *
              ∫⁻ b,pairValuePhysicalPdf c x y hx hy b * ∫⁻ J,phi J ∂pairValueConditionedLaw c x y hx hy b := by
  obtain ⟨ρ0,δ,hρ0,hδ,hall⟩:=uniform_value_pair_nondegenerate μ hQ hdeg
  refine ⟨ρ0,hρ0,?_⟩
  intro n x y hx hy hr
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let e:=tangentFrame x hx
  let f:=tangentFrame y hy
  have hfull:=groupedValuePair_coercive c x y e f
    (hall (n+1) n (by omega) x y hx hy e f (tangentFrame_orthonormal x hx)
      (tangentFrame_orthonormal y hy) (tangentFrame_tangent x hx) (tangentFrame_tangent y hy) hr).1
  have hC:=observation_surjective _ hδ hfull
  refine ⟨hC,?_⟩
  intro phi hphi
  have hgrad:=pair_snd_coercive (valuePair c x y) (pairGradient c x y e f) hfull
  have hA:=observation_surjective _ hδ hgrad
  have hres:=residual_coercivity (pairGradient c x y e f) hA (valuePair c x y) hδ.le hfull
  have hdis:=coefficientKernel_nonorthogonal_zero_disintegration (pairGradient c x y e f) hA
    (valuePair c x y) (observation_surjective _ hδ hres) hC phi hphi
  rw [← pairGradient_pdf_zero_eq_intrinsic c x y hx hy,
    ← pairGradient_kernel_zero_eq_intrinsic c x y hx hy hA,hdis]
  congr 1
  have ht:=lintegral_density_dilation
    (observationPdf (residualPairValue c x y e f)) (observationPdf_measurable _)
    (fun b=>ENNReal.ofReal_ne_top) (Real.sqrt_pos.mpr (by positivity : 0 < ((n+1:ℕ):ℝ)))
    (fun b=>∫⁻ J,phi J ∂coefficientKernel (groupedValuePair c x y e f) (WithLp.toLp 2 (b,0)))
  rw [valuePairSpace_finrank,Real.sq_sqrt (Nat.cast_nonneg (n+1))] at ht
  exact ht

end SlowEquilibration.SphericalPairMarkedWindows
