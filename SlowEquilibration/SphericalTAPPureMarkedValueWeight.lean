-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedLowSumMarkedKR
public import SlowEquilibration.SphericalCountIntensity

@[expose] public section

/-! A value-dependent proper-pure marked Kac--Rice bound for the actual
unbounded band partition. The pure radial score is deterministic. -/

namespace SlowEquilibration.SphericalTAPPureMarkedValueWeight
noncomputable section
open MeasureTheory Set SphericalModel SphericalGaussianJet
open SphericalMarkedWindows SphericalTAPMixedLowSumMarkedKR
open SphericalSequentialRegression SphereHessian
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 600000

/-- Integrating a value-dependent determinant-weighted posterior mark gives
the actual pure critical-point intensity multiplied by that value weight. -/
theorem actual_pure_marked_count_le_value_weight
    (d p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q)
    (W : Set ℝ) (hW : MeasurableSet W)
    (psi : Disorder (d+2) (FiniteMixture.pure p hp alpha halpha).maxDegree →
      Vector (d+2) → ℝ≥0∞)
    (hpsi : Measurable fun z : Disorder (d+2)
      (FiniteMixture.pure p hp alpha halpha).maxDegree × Vector (d+2) =>
      psi z.1 z.2)
    (w : ℝ → ℝ≥0∞)
    (hPalm : ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)), ∀ e ∈ W,
      let μ := FiniteMixture.pure p hp alpha halpha
      let c := centerCoefficients (mixtureCoefficients μ) Q
      (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det| *
        psi J u ∂valueConditionedLaw c u hu e) ≤
      w e * ENNReal.ofReal
        (GOEPhysicalPotential.physicalMean d (d+2) (Q^2*μ.xi2 Q) ((p:ℝ)*e))) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualValueWindowCount (d+1) c W psi J
      ∂disorderLaw (d+2) μ.maxDegree) ≤
    ∫⁻ e in W, pureCriticalIntensity d p hp alpha halpha Q e * w e := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  rw [(actual_value_window_kacRice (d+1) (by omega) μ hQ W hW psi hpsi).2]
  have houter : (∫⁻ u, valueWindowIntensity (d+1) μ Q W psi u
      ∂sphereLaw (d+2)) ≤
      ∫⁻ e in W, physicalValuePdf (d+2) μ Q e *
        (w e * ENNReal.ofReal
          (GOEPhysicalPotential.physicalMean d (d+2)
            (Q^2*μ.xi2 Q) ((p:ℝ)*e))) := by
    calc
      _ ≤ ∫⁻ _u : Vector (d+2),
          (∫⁻ e in W, physicalValuePdf (d+2) μ Q e *
            (w e * ENNReal.ofReal
              (GOEPhysicalPotential.physicalMean d (d+2)
                (Q^2*μ.xi2 Q) ((p:ℝ)*e)))) ∂sphereLaw (d+2) := by
        apply lintegral_mono_ae
        filter_upwards [sphereLaw_support (by omega : 1 ≤ d+2)] with u hu
        rw [valueWindowIntensity, dite_eq_left hu]
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem hW] with e he
        simpa only [mul_comm,mul_left_comm,mul_assoc] using
          (mul_le_mul_left (hPalm u hu e he) (physicalValuePdf (d+2) μ Q e))
      _ = _ := by simp
  calc
    _ ≤ sphereKRPrefactor (d+1) μ Q *
      (∫⁻ e in W, physicalValuePdf (d+2) μ Q e *
        (w e * ENNReal.ofReal
          (GOEPhysicalPotential.physicalMean d (d+2)
            (Q^2*μ.xi2 Q) ((p:ℝ)*e)))) :=
      (by simpa only [mul_comm] using
        (mul_le_mul_left houter (sphereKRPrefactor (d+1) μ Q)))
    _ = _ := by
      rw [← lintegral_const_mul' _ _ (sphereKRPrefactor_ne_top (d+1) μ Q)]
      apply lintegral_congr
      intro e
      simp only [pureCriticalIntensity]
      ac_rfl

end
end SlowEquilibration.SphericalTAPPureMarkedValueWeight
