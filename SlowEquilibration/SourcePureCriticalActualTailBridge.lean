-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureCriticalTailCountLimit
public import SlowEquilibration.SourcePureCriticalRawRadialGroundLimit

/-! Kac--Rice identifies the pure all-critical physical-intensity tail
with the actual original-field critical count above a physical threshold. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory SphericalModel SphericalGaussianJet
open SlowEquilibration.PairConditionalDeterminantMoments
open ExpectedTailCentering
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 500000

def sourcePureTruncatedCriticalTailMean
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q l r L : ℝ) : ℝ :=
  let μ := FiniteMixture.pure p hp a ha
  let I := Ici L ∩ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  sourceUnfilteredValueWindowMean (n+1) μ Q
    ((fun h : ℝ => (n+2 : ℕ)*h) ⁻¹' I)

theorem sourcePureTruncatedCriticalTailMean_eq_tail
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {Q : ℝ} (hQ : 0 < Q) (l r L : ℝ) :
    sourcePureTruncatedCriticalTailMean n p hp a ha Q l r L =
      tail (sourcePureTruncatedCriticalDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) L := by
  let μ := FiniteMixture.pure p hp a ha
  let I := Ici L ∩ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  let S := (fun h : ℝ => (n+2 : ℕ)*h) ⁻¹' I
  let K : Set (EuclideanSpace ℝ (Fin 2)) := {z | z 0 ∈ S}
  have hI : MeasurableSet I := measurableSet_Ici.inter measurableSet_Ioo
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
  simpa only [sourcePureTruncatedCriticalDensity, tail, I] using
    (setIntegral_indicator (μ := volume) (s := Ici L)
      (t := Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r))
      (f := fun H => (pureCriticalPhysicalIntensity n p hp a ha Q H).toReal)
      measurableSet_Ioo).symm

def sourcePureCenteredUpperTailNormalizedWindow
    (n : ℕ) (m : ℕ → ℝ) (E δ t : ℝ) : Set ℝ :=
  (fun b : ℝ => ((n+3 : ℕ) : ℝ)*b) ⁻¹'
    (Ici (m (n+1)+t) ∩
      Ioo (((n+3 : ℕ) : ℝ)*(E-δ)) (((n+3 : ℕ) : ℝ)*(E+δ)))

theorem sourcePureCenteredUpperTailNormalizedWindow_measurable
    (n : ℕ) (m : ℕ → ℝ) (E δ t : ℝ) :
    MeasurableSet (sourcePureCenteredUpperTailNormalizedWindow n m E δ t) :=
  (measurableSet_Ici.inter measurableSet_Ioo).preimage
    (measurable_const_mul ((n+3 : ℕ) : ℝ))

theorem sourcePureCenteredUpperTailNormalizedWindow_subset_value_box
    (n : ℕ) (m : ℕ → ℝ) (E δ t : ℝ) :
    sourcePureCenteredUpperTailNormalizedWindow n m E δ t ⊆ Icc (E-δ) (E+δ) := by
  intro b hb
  have hN : (0 : ℝ) < (n+3 : ℕ) := by positivity
  have hband := hb.2
  exact ⟨(lt_of_mul_lt_mul_left hband.1 hN.le).le,
    (lt_of_mul_lt_mul_left hband.2 hN.le).le⟩

theorem sourcePureCenteredUpperTailNormalizedWindow_critical_mean
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    (Q E δ t : ℝ) (m : ℕ → ℝ) :
    sourceUnfilteredValueWindowMean (n+2) (FiniteMixture.pure p hp a ha) Q
      (sourcePureCenteredUpperTailNormalizedWindow n m E δ t) =
    sourcePureTruncatedCriticalTailMean (n+1) p hp a ha Q
      (E-δ) (E+δ) (m (n+1)+t) := by
  rfl

end SlowEquilibration.SphericalMarkedWindows
