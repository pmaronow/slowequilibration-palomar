-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureHighStripCriticalMean

/-! A maximum in a physical energy interval supplies one literal critical
point in the same scalar-value interval. The resulting Markov bound uses
the original disorder field and its Kac--Rice count. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory SphericalModel SphericalGaussianJet SphericalForm
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal
set_option autoImplicit false

theorem sourceSphereMaximum_between_probability_le_critical_mean
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (l r : ℝ) :
    (disorderLaw (n+2) μ.maxDegree).real
      {J | l ≤ sourceSphereMaximum n μ Q J ∧ sourceSphereMaximum n μ Q J ≤ r} ≤
    sourceUnfilteredValueWindowMean (n+1) μ Q
      (Icc (l/(n+2 : ℕ)) (r/(n+2 : ℕ))) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let I := Icc (l/(n+2 : ℕ)) (r/(n+2 : ℕ))
  let C := actualValueWindowCount (n+1) c I (fun _ _ => 1)
  have hC : AEMeasurable C (disorderLaw (n+2) μ.maxDegree) :=
    (actual_value_window_kacRice (n+1) (by omega) μ hQ I measurableSet_Icc
      (fun _ _ => 1) measurable_const).1
  have hsub : {J : Disorder (n+2) μ.maxDegree |
      l ≤ sourceSphereMaximum n μ Q J ∧ sourceSphereMaximum n μ Q J ≤ r} ⊆
      {J | 1 ≤ C J} := by
    intro J hJ
    obtain ⟨y,hy,hcrit,_hmax,heq⟩ := sourceSphereMaximum_attained n μ Q J
    have hval : actualValue c J y ∈ I := by
      change l/(n+2 : ℕ) ≤ field c J y/(n+2 : ℕ) ∧
        field c J y/(n+2 : ℕ) ≤ r/(n+2 : ℕ)
      rw [←heq]
      exact ⟨div_le_div_of_nonneg_right hJ.1 (by positivity),
        div_le_div_of_nonneg_right hJ.2 (by positivity)⟩
    exact ENNReal.le_tsum (f := fun _z : {z : Vector (n+2) |
      ‖z‖^2=(n+2 : ℕ) ∧ surfaceGradient (field c J) z=0 ∧
      actualValue c J z ∈ I} => (1 : ℝ≥0∞))
      ⟨y,hy,hcrit,hval⟩
  have hmass : disorderLaw (n+2) μ.maxDegree
      {J | l ≤ sourceSphereMaximum n μ Q J ∧ sourceSphereMaximum n μ Q J ≤ r} ≤
      ∫⁻ J, C J ∂disorderLaw (n+2) μ.maxDegree := by
    apply (measure_mono hsub).trans
    simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hC 1
  have hfinite := sourceUnfilteredValueWindowCount_lintegral_lt_top
    (n+1) (by omega) μ hQ I
  exact ENNReal.toReal_mono hfinite.ne hmass

end SlowEquilibration.SphericalMarkedWindows
