-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PosteriorMaximumDeterminant

/-! Exact intensities for literal spherical critical points with strictly
negative intrinsic Hessian. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open SphericalPosteriorMaps NegativeDefiniteOperators GOEMaximumDeterminant
open SphericalSequentialRegression
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

/-- Literal count of intrinsic critical points with negative-definite actual
Hessian and specified normalized scores. -/
def actualNegativeCriticalCount {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (J : Disorder (n+1) P) : ℝ≥0∞ :=
  ∑' _x : {x : Vector (n+1) | ‖x‖^2=(n+1 : ℕ) ∧
    surfaceGradient (field c J) x=0 ∧ actualScore c J x ∈ K ∧
    NegativeDefinite (intrinsicHessian (field c J) x)}, (1 : ℝ≥0∞)

lemma actualNegativeCriticalCount_eq_mark {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (J : Disorder (n+1) P) :
    actualNegativeCriticalCount n c K J =
      actualScoreWindowCount n c K (negativeHessianMark n c) J := by
  unfold actualNegativeCriticalCount actualScoreWindowCount
  rw [tsum_subtype (f := fun _ : Vector (n+1) => (1 : ℝ≥0∞)), tsum_subtype]
  apply tsum_congr
  intro x
  simp only [Set.indicator_apply, mem_ofPred_eq]
  by_cases hx : ‖x‖^2=(n+1 : ℕ)
  · by_cases hg : surfaceGradient (field c J) x=0
    · rw [negativeHessianMark_eq n c J x hx hg]
      by_cases hk : actualScore c J x ∈ K <;>
        by_cases hneg : NegativeDefinite (intrinsicHessian (field c J) x) <;>
        simp only [hx,hg,hk,hneg,and_true,and_false,ite_true,ite_false]
    · simp only [hg,and_false,false_and,ite_false]
  · simp only [hx,false_and,ite_false]

def mixedNegativeIntensity (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (z : EuclideanSpace ℝ (Fin 2)) : ℝ≥0∞ :=
  sphereKRPrefactor (n+1) μ Q * physicalScorePdf (n+2) μ Q z *
    ENNReal.ofReal (maximumMean n (n+2) (Q^2 * μ.xi2 Q) (z 1))

def pureNegativeIntensity (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) (Q h : ℝ) : ℝ≥0∞ :=
  let μ := FiniteMixture.pure p hp alpha halpha
  sphereKRPrefactor (n+1) μ Q * physicalValuePdf (n+2) μ Q h *
    ENNReal.ofReal (maximumMean n (n+2) (Q^2 * μ.xi2 Q) ((p:ℝ)*h))

theorem actual_mixed_negative_count_intensity (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualNegativeCriticalCount (n+1) c K) (disorderLaw (n+2) μ.maxDegree) ∧
    (∫⁻ J, actualNegativeCriticalCount (n+1) c K J ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ z in K, mixedNegativeIntensity n μ Q z := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hkr := actual_mixed_score_window_kacRice (n+1) (by omega) μ hQ hnp K hK
    (negativeHessianMark (n+1) c) (negativeHessianMark_measurable (n+1) c)
  have heq : actualNegativeCriticalCount (n+1) c K =
      actualScoreWindowCount (n+1) c K (negativeHessianMark (n+1) c) :=
    funext (actualNegativeCriticalCount_eq_mark (n+1) c K)
  refine ⟨heq ▸ hkr.1, ?_⟩
  rw [heq, hkr.2]
  have he : mixedWindowIntensity (n+1) μ Q K (negativeHessianMark (n+1) c)
      =ᵐ[sphereLaw (n+2)] (fun _ => ∫⁻ z in K, physicalScorePdf (n+2) μ Q z *
        ENNReal.ofReal (maximumMean n (n+2) (Q^2 * μ.xi2 Q) (z 1))) := by
    filter_upwards [sphereLaw_support (show 1 ≤ n+2 by omega)] with x hx
    rw [mixedWindowIntensity, dite_eq_left hx]
    apply lintegral_congr
    intro z
    rw [mixed_posterior_negative_det_mean n μ hQ hnp x hx z]
  rw [lintegral_congr_ae he, lintegral_const]
  simp only [measure_univ, mul_one]
  rw [← lintegral_const_mul' _ _ (sphereKRPrefactor_ne_top (n+1) μ Q)]
  apply lintegral_congr
  intro z
  exact (mul_assoc _ _ _).symm

theorem actual_pure_negative_count_intensity (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    AEMeasurable (actualNegativeCriticalCount (n+1) c K) (disorderLaw (n+2) μ.maxDegree) ∧
    (∫⁻ J, actualNegativeCriticalCount (n+1) c K J ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ h in pureScoreWindow p K, pureNegativeIntensity n p hp alpha halpha Q h := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hkr := actual_pure_score_window_kacRice (n+1) (by omega) p hp alpha halpha hQ K hK
    (negativeHessianMark (n+1) c) (negativeHessianMark_measurable (n+1) c)
  have heq : actualNegativeCriticalCount (n+1) c K =
      actualScoreWindowCount (n+1) c K (negativeHessianMark (n+1) c) :=
    funext (actualNegativeCriticalCount_eq_mark (n+1) c K)
  refine ⟨heq ▸ hkr.1, ?_⟩
  rw [heq, hkr.2]
  have he : valueWindowIntensity (n+1) μ Q (pureScoreWindow p K) (negativeHessianMark (n+1) c)
      =ᵐ[sphereLaw (n+2)] (fun _ => ∫⁻ h in pureScoreWindow p K,
        physicalValuePdf (n+2) μ Q h *
        ENNReal.ofReal (maximumMean n (n+2) (Q^2 * μ.xi2 Q) ((p:ℝ)*h))) := by
    filter_upwards [sphereLaw_support (show 1 ≤ n+2 by omega)] with x hx
    rw [valueWindowIntensity, dite_eq_left hx]
    apply lintegral_congr
    intro h
    rw [pure_posterior_negative_det_mean n p hp alpha halpha hQ x hx h]
  rw [lintegral_congr_ae he, lintegral_const]
  simp only [measure_univ, mul_one]
  rw [← lintegral_const_mul' _ _ (sphereKRPrefactor_ne_top (n+1) μ Q)]
  apply lintegral_congr
  intro h
  exact (mul_assoc _ _ _).symm

end
end SlowEquilibration.SphericalMarkedWindows
