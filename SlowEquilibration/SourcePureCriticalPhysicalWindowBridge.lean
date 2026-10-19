-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxCriticalComparison
public import SlowEquilibration.SourcePhysicalPurePairRetainedNormalization
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The literal all-critical value-window count, in the original field,
as a physical-energy integral. The mark cutoff is a scalar-value cutoff
on the pure score line. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory SphericalModel SphericalGaussianJet SphericalSequentialRegression
open SlowEquilibration.PairConditionalDeterminantMoments
open scoped ENNReal
set_option maxHeartbeats 400000

def sourcePureTruncatedCriticalDensity
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q l r H : ℝ) : ℝ :=
  (Ioo l r).indicator (fun H =>
    (pureCriticalPhysicalIntensity n p hp a ha Q H).toReal) H

def sourcePureTruncatedCriticalWindowMean
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q l r L R : ℝ) : ℝ :=
  let μ := FiniteMixture.pure p hp a ha
  let I := Icc L R ∩ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  sourceUnfilteredValueWindowMean (n+1) μ Q
    ((fun h : ℝ => (n+2 : ℕ)*h) ⁻¹' I)

theorem pureCriticalPhysicalIntensity_measurable
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q : ℝ) :
    Measurable (pureCriticalPhysicalIntensity n p hp a ha Q) := by
  exact measurable_const.mul
    ((source_pure_critical_intensity_measurable n p hp a ha Q).comp
      (measurable_id.div_const ((n+2 : ℕ) : ℝ)))

theorem pureCriticalPhysicalIntensity_ne_top
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q H : ℝ) :
    pureCriticalPhysicalIntensity n p hp a ha Q H ≠ ⊤ := by
  have hs := sphereKRPrefactor_ne_top (n+1) (FiniteMixture.pure p hp a ha) Q
  unfold pureCriticalPhysicalIntensity pureCriticalIntensity physicalValuePdf
  finiteness

theorem sourcePureTruncatedCriticalWindowMean_eq_integral
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {Q : ℝ} (hQ : 0 < Q) (l r L R : ℝ) :
    sourcePureTruncatedCriticalWindowMean n p hp a ha Q l r L R =
      ∫ H in Icc L R,
        sourcePureTruncatedCriticalDensity n p hp a ha Q
          ((n+2 : ℕ)*l) ((n+2 : ℕ)*r) H := by
  let μ := FiniteMixture.pure p hp a ha
  let I := Icc L R ∩ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  let S := (fun h : ℝ => (n+2 : ℕ)*h) ⁻¹' I
  let K : Set (EuclideanSpace ℝ (Fin 2)) := {z | z 0 ∈ S}
  have hI : MeasurableSet I := measurableSet_Icc.inter measurableSet_Ioo
  have hS : MeasurableSet S := hI.preimage (measurable_const_mul ((n+2 : ℕ) : ℝ))
  have hK : MeasurableSet K := hS.preimage (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable
  have hLine : pureScoreWindow p K = S := by ext h; rfl
  have hCount := actual_pure_count_intensity n p hp a ha hQ K hK
  change (∫⁻ J, actualScoreWindowCount (n+1)
      (centerCoefficients (mixtureCoefficients μ) Q) K (fun _ _ => 1) J
      ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ h in pureScoreWindow p K, pureCriticalIntensity n p hp a ha Q h at hCount
  change (∫⁻ J, actualValueWindowCount (n+1)
      (centerCoefficients (mixtureCoefficients μ) Q) S (fun _ _ => 1) J
      ∂disorderLaw (n+2) μ.maxDegree).toReal = _
  rw [show (∫⁻ J, actualValueWindowCount (n+1)
      (centerCoefficients (mixtureCoefficients μ) Q) S (fun _ _ => 1) J
      ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ J, actualScoreWindowCount (n+1)
        (centerCoefficients (mixtureCoefficients μ) Q) K (fun _ _ => 1) J
        ∂disorderLaw (n+2) μ.maxDegree by
    apply lintegral_congr
    intro J
    simpa only [hLine] using
      (actual_pure_scoreWindowCount_eq_valueWindowCount (n+1) p hp a ha Q
        K (fun _ _ => 1) J).symm]
  rw [hCount, hLine, setLIntegral_positive_rescale (n+2 : ℕ) (by positivity) I]
  change (∫⁻ H in I, pureCriticalPhysicalIntensity n p hp a ha Q H).toReal = _
  rw [← integral_toReal
    (pureCriticalPhysicalIntensity_measurable n p hp a ha Q).aemeasurable
    (ae_of_all _ (fun H => lt_top_iff_ne_top.mpr
      (pureCriticalPhysicalIntensity_ne_top n p hp a ha Q H)))]
  simpa only [sourcePureTruncatedCriticalDensity, I] using
    (setIntegral_indicator (μ := volume) (s := Icc L R)
      (t := Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r))
      (f := fun H => (pureCriticalPhysicalIntensity n p hp a ha Q H).toReal)
      measurableSet_Ioo).symm

end SlowEquilibration.SphericalMarkedWindows
