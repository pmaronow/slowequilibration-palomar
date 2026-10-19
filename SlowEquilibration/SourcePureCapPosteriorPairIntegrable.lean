-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapPosteriorPairMean
public import SlowEquilibration.SphericalCentralOverlapPerturbation

/-! Posterior/two-spin integrability needed for the source pure cap second
moment. The explicit pair-mean integrand is a continuous function on the
compact physical sphere pair. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapPosteriorPairIntegrable
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalPureOriginalConditionalBandFubini
open SourcePureCapPosteriorPairMean
open SourcePureCapPosteriorCrossKernel
set_option autoImplicit false
set_option maxHeartbeats 1000000

def originalPurePairMeanProfile (n p : ℕ) (alpha β H : ℝ)
    (u : Vector (n+1)) (z : Vector (n+1) × Vector (n+1)) : ℝ :=
  let q₁ := overlap u z.1
  let q₂ := overlap u z.2
  let r := overlap z.1 z.2
  originalPureMeanProfile n p alpha β H u z.1*
    originalPureMeanProfile n p alpha β H u z.2*
      Real.exp (β^2*(n+1 : ℕ)*alpha*
        (r^p-(q₁*q₂)^p-(p : ℝ)*(q₁*q₂)^(p-1)*(r-q₁*q₂)))

theorem originalPurePairMeanProfile_continuous (n p : ℕ)
    (alpha β H : ℝ) (u : Vector (n+1)) :
    Continuous (originalPurePairMeanProfile n p alpha β H u) := by
  unfold originalPurePairMeanProfile originalPureMeanProfile
    SphericalTAPCriticalPureLatitudeVariance.sourcePureLatitudeVariance overlap
  fun_prop

theorem pure_original_conditioned_pair_exp_eq_profile
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (u w₁ w₂ : Vector (n+1))
    (hu : ‖u‖^2=(n+1 : ℕ))
    (hw₁ : ‖w₁‖^2=(n+1 : ℕ)) (hw₂ : ‖w₂‖^2=(n+1 : ℕ))
    (β H : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) 1
    (∫ J, Real.exp (β*field (mixtureCoefficients μ) J w₁)*
        Real.exp (β*field (mixtureCoefficients μ) J w₂)
      ∂valueConditionedLaw c u hu (H/(n+1 : ℕ))) =
      originalPurePairMeanProfile n p alpha β H u (w₁,w₂) := by
  dsimp only
  rw [pure_original_conditioned_pair_exp_mean n p hp alpha halpha
    u w₁ w₂ hu hw₁ hw₂ β H]
  unfold originalPurePairMeanProfile
  simp only [sourceValueTauCross_pure p hp alpha halpha
    (by norm_num : (0 : ℝ) < 1),one_pow,mul_one]
  have hbase : overlap u w₁ * overlap u w₂ +
      (overlap w₁ w₂ - overlap u w₁ * overlap u w₂) =
      overlap w₁ w₂ := by ring
  rw [hbase]
  ring

/-- The product of two original Boltzmann weights is genuinely integrable
under the original pure critical-point posterior at all sphere points. -/
theorem pure_original_conditioned_pair_exp_integrable
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (u w₁ w₂ : Vector (n+1))
    (hu : ‖u‖^2=(n+1 : ℕ))
    (hw₁ : ‖w₁‖^2=(n+1 : ℕ)) (hw₂ : ‖w₂‖^2=(n+1 : ℕ))
    (β H : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) 1
    Integrable (fun J : Disorder (n+1) μ.maxDegree =>
      Real.exp (β*field (mixtureCoefficients μ) J w₁)*
        Real.exp (β*field (mixtureCoefficients μ) J w₂))
      (valueConditionedLaw c u hu (H/(n+1 : ℕ))) := by
  dsimp only
  have hmean := pure_original_conditioned_pair_exp_eq_profile n p hp alpha halpha
    u w₁ w₂ hu hw₁ hw₂ β H
  dsimp only at hmean
  by_contra hnot
  rw [integral_undef hnot] at hmean
  have hpositive : 0 < originalPurePairMeanProfile n p alpha β H u (w₁,w₂) := by
    unfold originalPurePairMeanProfile originalPureMeanProfile
    positivity
  exact hpositive.ne' hmean.symm

/-- True joint integrability over conditioned disorder and two independent
uniform physical spins. This does not assume the source band second moment. -/
theorem pure_original_conditioned_exp_pair_prod_integrable
    (n p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1 : ℕ)) (β H : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) 1
    Integrable (fun z : Disorder (n+1) μ.maxDegree ×
        (Vector (n+1) × Vector (n+1)) =>
      Real.exp (β*field (mixtureCoefficients μ) z.1 z.2.1)*
        Real.exp (β*field (mixtureCoefficients μ) z.1 z.2.2))
      ((valueConditionedLaw c u hu (H/(n+1 : ℕ))).prod
        ((sphereLaw (n+1)).prod (sphereLaw (n+1)))) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) 1
  let P := valueConditionedLaw c u hu (H/(n+1 : ℕ))
  let ν := (sphereLaw (n+1)).prod (sphereLaw (n+1))
  let : IsProbabilityMeasure P := by
    unfold P valueConditionedLaw
    infer_instance
  let f := fun z : Disorder (n+1) μ.maxDegree ×
      (Vector (n+1) × Vector (n+1)) =>
    Real.exp (β*field (mixtureCoefficients μ) z.1 z.2.1)*
      Real.exp (β*field (mixtureCoefficients μ) z.1 z.2.2)
  have hf : Continuous f := by
    unfold f
    exact (Real.continuous_exp.comp
      (continuous_const.mul ((field_jointContinuous (mixtureCoefficients μ)).comp
        (continuous_fst.prodMk continuous_snd.fst)))).mul
      (Real.continuous_exp.comp
        (continuous_const.mul ((field_jointContinuous (mixtureCoefficients μ)).comp
          (continuous_fst.prodMk continuous_snd.snd))))
  apply (integrable_prod_iff' hf.measurable.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [sphereLaw_pair_support (by omega : 1 ≤ n+1)] with z hz
    exact pure_original_conditioned_pair_exp_integrable n p hp alpha halpha
      u z.1 z.2 hu hz.1 hz.2 β H
  · have hprof : Integrable (originalPurePairMeanProfile n p alpha β H u) ν :=
      ((memLp_spherePair_continuous (by omega : 1 ≤ n+1)
        (originalPurePairMeanProfile_continuous n p alpha β H u) 1).integrable le_rfl)
    apply hprof.congr
    filter_upwards [sphereLaw_pair_support (by omega : 1 ≤ n+1)] with z hz
    change originalPurePairMeanProfile n p alpha β H u z =
      ∫ J, ‖f (J,z)‖ ∂P
    have hnorm : (fun J : Disorder (n+1) μ.maxDegree => ‖f (J,z)‖) =
        (fun J => f (J,z)) := by
      funext J
      exact Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    rw [hnorm]
    exact (pure_original_conditioned_pair_exp_eq_profile n p hp alpha halpha
      u z.1 z.2 hu hz.1 hz.2 β H).symm

end
end SlowEquilibration.SourcePureCapPosteriorPairIntegrable
