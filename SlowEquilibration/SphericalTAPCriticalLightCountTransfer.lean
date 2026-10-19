-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalEnergyPalmIntensity
public import SlowEquilibration.SphericalOverlapPartitionMeasurable

@[expose] public section

/-! A determinant-weighted Palm bound for each mark transfers through the
actual global marked Kac--Rice formula to an expected count bound. -/

namespace SlowEquilibration.SphericalTAPCriticalLightCountTransfer
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalSequentialRegression IntrinsicHessianLaw SphereHessian
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Marked Kac--Rice domination for a Borel whole-field weight. The
hypothesis is a local determinant-weighted estimate at each physical center
and score; the conclusion counts actual critical points under the original
unconditioned disorder law. -/
theorem actual_mixed_marked_count_le_of_uniform_palm
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (K : Set (EuclideanSpace ℝ (Fin 2))) (hK : MeasurableSet K)
    (psi : Disorder (d+2) μ.maxDegree → Vector (d+2) → ℝ≥0∞)
    (hpsi : Measurable fun z : Disorder (d+2) μ.maxDegree × Vector (d+2) =>
      psi z.1 z.2)
    {q : ℝ≥0∞} (hq : q ≠ ⊤)
    (hPalm : ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
      (z : EuclideanSpace ℝ (Fin 2)), z ∈ K →
      (∫⁻ J, ENNReal.ofReal |(intrinsicHessian
        (field (centerCoefficients (mixtureCoefficients μ) Q) J) u).det| *
        psi J u
        ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q)
          u hu z) ≤
      q * (∫⁻ J, ENNReal.ofReal |(intrinsicHessian
        (field (centerCoefficients (mixtureCoefficients μ) Q) J) u).det|
        ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q)
          u hu z)) :
    (∫⁻ J, actualScoreWindowCount (d+1)
      (centerCoefficients (mixtureCoefficients μ) Q) K psi J
        ∂disorderLaw (d+2) μ.maxDegree) ≤
      q * (∫⁻ J, actualScoreWindowCount (d+1)
        (centerCoefficients (mixtureCoefficients μ) Q) K (fun _ _ => 1) J
          ∂disorderLaw (d+2) μ.maxDegree) := by
  rw [(actual_mixed_score_window_kacRice (d+1) (by omega) μ hQ hnp K hK
    psi hpsi).2]
  rw [(actual_mixed_score_window_kacRice (d+1) (by omega) μ hQ hnp K hK
    (fun _ _ => 1) measurable_const).2]
  have hinner :
      (∫⁻ u, mixedWindowIntensity (d+1) μ Q K psi u
        ∂sphereLaw (d+2)) ≤
      q * (∫⁻ u, mixedWindowIntensity (d+1) μ Q K (fun _ _ => 1) u
        ∂sphereLaw (d+2)) := by
    rw [← lintegral_const_mul' _ _ hq]
    apply lintegral_mono_ae
    filter_upwards [sphereLaw_support (by omega : 1 ≤ d+2)] with u hu
    rw [mixedWindowIntensity, dite_eq_left hu,
      mixedWindowIntensity, dite_eq_left hu]
    rw [← lintegral_const_mul' _ _ hq]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem hK] with z hz
    simp only [mul_one]
    simpa only [mul_comm,mul_left_comm,mul_assoc] using
      (mul_le_mul_left (hPalm u hu z hz)
        (physicalScorePdf (d+2) μ Q z))
  calc
    _ ≤ sphereKRPrefactor (d+1) μ Q *
        (q * (∫⁻ u, mixedWindowIntensity (d+1) μ Q K (fun _ _ => 1) u
          ∂sphereLaw (d+2))) := by
            simpa only [mul_comm,mul_left_comm,mul_assoc] using
              (mul_le_mul_left hinner (sphereKRPrefactor (d+1) μ Q))
    _ = _ := by ac_rfl

end
end SlowEquilibration.SphericalTAPCriticalLightCountTransfer
