-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCriticalCenteredCountUniform
public import SlowEquilibration.PureTensorSharpMaximum

/-! A uniform coarse upper tail for the literal global maximum of the
center-scaled finite mixture field. This controls energies beyond any fixed
compact contact strip in the proper-pure first-moment argument. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory SphericalModel SphericalGaussianJet PureTensorJetBounds
open SphericalTAPCertificate
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 600000

def sourceMaximumJetEnvelope (N : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (J : Disorder N μ.maxDegree) : ℝ :=
  ∑ q : Degree μ.maxDegree,
    Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q q) *
      pureJetEnvelope N q.val.val 0 (J q)

theorem sourceMaximumJetEnvelope_nonneg (N : ℕ) (hN : 0 < N)
    (μ : FiniteMixture) (Q : ℝ)
    (J : Disorder N μ.maxDegree) : 0 ≤ sourceMaximumJetEnvelope N μ Q J := by
  unfold sourceMaximumJetEnvelope
  exact Finset.sum_nonneg (fun q _ => mul_nonneg (Real.sqrt_nonneg _)
    (pureJetEnvelope_nonneg hN _))

theorem sourceSphereMaximum_le_jetEnvelope (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (J : Disorder (n+2) μ.maxDegree) :
    sourceSphereMaximum n μ Q J ≤ sourceMaximumJetEnvelope (n+2) μ Q J := by
  obtain ⟨y,hy,_hcrit,_hmax,heq⟩ := sourceSphereMaximum_attained n μ Q J
  rw [heq]
  have hnorm : ‖y‖ ≤ Real.sqrt (n+2 : ℕ) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [hy,Real.sq_sqrt (Nat.cast_nonneg _)]
  unfold field sourceMaximumJetEnvelope
  apply Finset.sum_le_sum
  intro q _
  have hblock : |blockField q J y| ≤ pureJetEnvelope (n+2) q.val.val 0 (J q) := by
    simpa only [blockField, norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      iteratedFDeriv_norm_le_pureJetEnvelope (j := 0) (by omega : 0 < n+2)
        (J q) y hnorm
  calc
    Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q q) * blockField q J y ≤
        Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q q) * |blockField q J y| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (Real.sqrt_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left hblock (Real.sqrt_nonneg _)

theorem sourceMaximumJetEnvelope_integrable (N : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (hN : 0 < N) :
    Integrable (sourceMaximumJetEnvelope N μ Q) (disorderLaw N μ.maxDegree) := by
  unfold sourceMaximumJetEnvelope
  exact integrable_finsetSum _ (fun q _ =>
    ((degree_block_hasLaw q).integrable_comp (pureJetEnvelope_integrable hN)).const_mul _)

theorem sourceMaximumJetEnvelope_expected_bound (N : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (hN : 0 < N) :
    (∫ J, sourceMaximumJetEnvelope N μ Q J ∂disorderLaw N μ.maxDegree) ≤
      (N : ℝ) * (∑ q : Degree μ.maxDegree,
        2 * Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q q) *
          Real.sqrt q.val.val) := by
  have hi (q : Degree μ.maxDegree) : Integrable
      (fun J : Disorder N μ.maxDegree =>
        Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q q) *
          pureJetEnvelope N q.val.val 0 (J q)) (disorderLaw N μ.maxDegree) :=
    ((degree_block_hasLaw q).integrable_comp (pureJetEnvelope_integrable hN)).const_mul _
  unfold sourceMaximumJetEnvelope
  rw [integral_finsetSum _ (fun q _ => hi q)]
  calc
    _ ≤ ∑ q : Degree μ.maxDegree,
          Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q q) *
            (2*N*Real.sqrt q.val.val) := by
      apply Finset.sum_le_sum
      intro q _
      rw [integral_const_mul]
      have he := (degree_block_hasLaw q).integral_comp
        (pureJetEnvelope_continuous (j := 0) hN).aestronglyMeasurable
      rw [show (fun J : Disorder N μ.maxDegree =>
        pureJetEnvelope N q.val.val 0 (J q)) =
          pureJetEnvelope N q.val.val 0 ∘ (fun J => J q) from rfl,he]
      apply mul_le_mul_of_nonneg_left
        (expected_pureJetEnvelope_zero_le_two hN (by omega : 1 ≤ q.val.val))
        (Real.sqrt_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring

theorem sourceSphereMaximum_coarse_upper_tail (n : ℕ) (μ : FiniteMixture)
    (Q : ℝ) {B : ℝ} (hB : 0 < B) :
    (disorderLaw (n+2) μ.maxDegree).real
      {J | (n+2 : ℕ)*B ≤ sourceSphereMaximum n μ Q J} ≤
      (∑ q : Degree μ.maxDegree,
        2 * Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q q) *
          Real.sqrt q.val.val) / B := by
  let K : ℝ := ∑ q : Degree μ.maxDegree,
    2 * Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q q) *
      Real.sqrt q.val.val
  let f : Disorder (n+2) μ.maxDegree → ℝ := sourceMaximumJetEnvelope (n+2) μ Q
  have hN : (0 : ℝ) < (n+2 : ℕ) := by positivity
  have hm := mul_meas_ge_le_integral_of_nonneg
    (μ := disorderLaw (n+2) μ.maxDegree)
    (Filter.Eventually.of_forall (sourceMaximumJetEnvelope_nonneg (n+2) (by omega) μ Q))
    (sourceMaximumJetEnvelope_integrable (n+2) μ Q (by omega))
    ((n+2 : ℕ)*B)
  have hsub : {J : Disorder (n+2) μ.maxDegree |
      (n+2 : ℕ)*B ≤ sourceSphereMaximum n μ Q J} ⊆
      {J | (n+2 : ℕ)*B ≤ f J} := by
    intro J hJ
    exact hJ.trans (sourceSphereMaximum_le_jetEnvelope n μ Q J)
  have hmono := measureReal_mono (μ := disorderLaw (n+2) μ.maxDegree)
    hsub (measure_ne_top _ _)
  have hmul := mul_le_mul_of_nonneg_left hmono (mul_nonneg hN.le hB.le)
  have hmean := sourceMaximumJetEnvelope_expected_bound (n+2) μ Q (by omega)
  have hbound : (n+2 : ℕ)*B *
      (disorderLaw (n+2) μ.maxDegree).real
        {J | (n+2 : ℕ)*B ≤ sourceSphereMaximum n μ Q J} ≤ (n+2 : ℕ)*K :=
    (hmul.trans hm).trans hmean
  apply (le_div_iff₀ hB).mpr
  apply (mul_le_mul_iff_right₀ hN).mp
  convert hbound using 1
  all_goals ring

end SlowEquilibration.SphericalMarkedWindows
