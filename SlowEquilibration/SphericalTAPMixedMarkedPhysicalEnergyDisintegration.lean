-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPalmDensityDisintegration
public import SlowEquilibration.SourceMixedAllCriticalIntensityEnvelope

@[expose] public section

/-! Exact physical-energy coordinates for the marked mixed Kac--Rice score
integral.  The Jacobian applies to arbitrary measurable whole-field marks. -/

namespace SlowEquilibration.SphericalTAPMixedMarkedPhysicalEnergyDisintegration
noncomputable section
open MeasureTheory Set SphericalModel SphericalGaussianJet
open SphericalMarkedWindows SphericalSequentialRegression
open ConditionedDeterminantMoments
open SphericalTAPMixedLowSumMarkedKR
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- An arbitrary nonnegative marked score density, before integrating over
the original sphere, has the source's exact physical-energy Jacobian. -/
theorem marked_score_density_physical_energy
    (d : ℕ) (I U : Set ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z in physicalEnergyWindow (d+2) I U, f z) =
      ∫⁻ H in I, ∫⁻ k in U,
        ENNReal.ofReal (((d+2:ℕ):ℝ))⁻¹ *
          f (scorePairEquiv (H/(d+2:ℕ),k)) := by
  change (∫⁻ z in rectangularScoreWindow
      ((fun h : ℝ => ((d+2:ℕ):ℝ)*h) ⁻¹' I) U, f z) = _
  rw [lintegral_rectangularScoreWindow _ _ f hf]
  rw [setLIntegral_positive_rescale (((d+2:ℕ):ℝ)) (by positivity)]
  apply lintegral_congr
  intro H
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

/-- The actual full-field marked score intensity, after changing only the
physical energy coordinate. The sphere center and conditioned original
tensor law are retained exactly. -/
def sourceMixedBandPhysicalEnergyIntensity
    (d : ℕ) (μ : FiniteMixture) (Q β q b : ℝ)
    (I U : Set ℝ) (u : Vector (d+2)) : ℝ≥0∞ :=
  if hu : ‖u‖^2=((d+2:ℕ):ℝ) then
    ∫⁻ H in I, ∫⁻ k in U,
      ENNReal.ofReal (((d+2:ℕ):ℝ))⁻¹ *
        (physicalScorePdf (d+2) μ Q (scorePairEquiv (H/(d+2:ℕ),k)) *
          ∫⁻ J, ENNReal.ofReal (intrinsicDet μ Q u J) *
            sourceMixedBandMark d μ β q b J u
            ∂mixedLaw μ Q u hu (scorePairEquiv (H/(d+2:ℕ),k)))
  else 0

theorem mixedWindowIntensity_band_eq_physical_energy
    (d : ℕ) (μ : FiniteMixture) (Q β q b : ℝ)
    (I U : Set ℝ) (u : Vector (d+2)) :
    mixedWindowIntensity (d+1) μ Q
      (physicalEnergyWindow (d+2) I U)
      (sourceMixedBandMark d μ β q b) u =
    sourceMixedBandPhysicalEnergyIntensity d μ Q β q b I U u := by
  by_cases hu : ‖u‖^2=((d+2:ℕ):ℝ)
  · rw [mixedWindowIntensity, dite_eq_left hu,
        sourceMixedBandPhysicalEnergyIntensity, dite_eq_left hu]
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let phi : Disorder (d+2) μ.maxDegree → ℝ≥0∞ :=
      fun J => ENNReal.ofReal (intrinsicDet μ Q u J) *
        sourceMixedBandMark d μ β q b J u
    have hD : Measurable (fun J : Disorder (d+2) μ.maxDegree =>
        ENNReal.ofReal (intrinsicDet μ Q u J)) := by
      exact intrinsicDet_measurable c u hu
    have hM : Measurable (fun J : Disorder (d+2) μ.maxDegree =>
        sourceMixedBandMark d μ β q b J u) := by
      change Measurable ((fun z : Disorder (d+2) μ.maxDegree × Vector (d+2) =>
        sourceMixedBandMark d μ β q b z.1 z.2) ∘
        (fun J : Disorder (d+2) μ.maxDegree => (J,u)))
      exact (sourceMixedBandMark_measurable d μ β q b).comp
        ((measurable_id : Measurable
          (fun J : Disorder (d+2) μ.maxDegree => J)).prodMk
          (measurable_const : Measurable
            (fun _ : Disorder (d+2) μ.maxDegree => u)))
    have hphi : Measurable phi := hD.mul hM
    have hTarget : Measurable (fun z : EuclideanSpace ℝ (Fin 2) =>
        jointScoreTarget (d+1) (((d+2:ℕ):ℝ) • z)) := by
      have hSmul : Measurable (fun z : EuclideanSpace ℝ (Fin 2) =>
          (((d+2:ℕ):ℝ) • z)) := by fun_prop
      exact (jointScoreTarget_continuous (d+1)).measurable.comp
        hSmul
    have hf : Measurable (fun z : EuclideanSpace ℝ (Fin 2) =>
        physicalScorePdf (d+2) μ Q z *
          ∫⁻ J, phi J ∂mixedConditionedLaw c u hu z) := by
      exact (physicalScorePdf_measurable (d+2) μ Q).mul
        (hphi.lintegral_kernel.comp hTarget)
    have hcoord := marked_score_density_physical_energy d I U
      (fun z => physicalScorePdf (d+2) μ Q z *
        ∫⁻ J, phi J ∂mixedConditionedLaw c u hu z) hf
    convert hcoord using 1
    · rfl
    · apply lintegral_congr
      intro H
      apply lintegral_congr
      intro k
      rfl
  · rw [mixedWindowIntensity, dite_eq_right hu,
        sourceMixedBandPhysicalEnergyIntensity, dite_eq_right hu]

/-- Exact marked Kac--Rice for the genuine mixed physical band, with
ordinary unnormalized energy and the explicit Jacobian. -/
theorem actual_mixed_band_sum_physical_energy_kacRice
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (β q b E₁ E₂ L R : ℝ) :
    (∫⁻ J, actualScoreWindowCount (d+1)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (d+2) (Icc E₁ E₂) (Ioo L R))
      (sourceMixedBandMark d μ β q b) J
      ∂disorderLaw (d+2) μ.maxDegree) =
    sphereKRPrefactor (d+1) μ Q *
      ∫⁻ u, sourceMixedBandPhysicalEnergyIntensity d μ Q β q b
        (Icc E₁ E₂) (Ioo L R) u ∂sphereLaw (d+2) := by
  rw [actual_mixed_band_sum_marked_kacRice d μ hQ hnp β q b E₁ E₂ L R]
  congr 1
  apply lintegral_congr
  intro u
  exact mixedWindowIntensity_band_eq_physical_energy d μ Q β q b
    (Icc E₁ E₂) (Ioo L R) u

end
end SlowEquilibration.SphericalTAPMixedMarkedPhysicalEnergyDisintegration
