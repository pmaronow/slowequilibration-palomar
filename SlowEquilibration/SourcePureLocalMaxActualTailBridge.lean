-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureActualCriticalTailLimit
public import SlowEquilibration.SourcePureLocalMaxWindowCountBridge

/-! Genuine negative-Hessian local-maximum upper-tail counts have the
pure physical-intensity upper-tail formula at each finite dimension. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalMarkedWindows
open Set MeasureTheory SphericalModel SphericalGaussianJet
open ExpectedTailCentering
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 450000

def sourcePureTruncatedLocalMaxTailMean
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a) (Q l r L : ℝ) : ℝ :=
  let μ := FiniteMixture.pure p hp a ha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let I := Ici L ∩ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  (∫⁻ J, actualLocalMaxCount (n+1) c
      (physicalEnergyWindow (n+2) I univ) J
    ∂disorderLaw (n+2) μ.maxDegree).toReal

theorem sourcePureTruncatedLocalMaxTailMean_eq_tail
    (n p : ℕ) (hp : 2 ≤ p) (a : ℝ) (ha : 0 < a)
    {Q : ℝ} (hQ : 0 < Q) (l r L : ℝ) :
    sourcePureTruncatedLocalMaxTailMean n p hp a ha Q l r L =
      tail (pureTruncatedLocalMaxDensity n p hp a ha Q
        ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)) L := by
  let μ := FiniteMixture.pure p hp a ha
  let I := Ici L ∩ Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r)
  have hI : MeasurableSet I := measurableSet_Ici.inter measurableSet_Ioo
  have hKR := actual_pure_localMax_physical_intensity n p hp a ha hQ I hI
  change (∫⁻ J, actualLocalMaxCount (n+1)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+2) I univ) J
      ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ H in I, pureLocalMaxPhysicalIntensity n p hp a ha Q H at hKR
  change (∫⁻ J, actualLocalMaxCount (n+1)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+2) I univ) J
      ∂disorderLaw (n+2) μ.maxDegree).toReal = _
  rw [hKR]
  rw [←integral_toReal (pureLocalMaxPhysicalIntensity_measurable n p hp a ha Q).aemeasurable
    (ae_of_all _ (fun H => lt_top_iff_ne_top.mpr
      (pureLocalMaxPhysicalIntensity_ne_top n p hp a ha Q H)))]
  simpa only [pureTruncatedLocalMaxDensity,tail,I] using
    (setIntegral_indicator (μ := volume) (s := Ici L)
      (t := Ioo ((n+2 : ℕ)*l) ((n+2 : ℕ)*r))
      (f := fun H => (pureLocalMaxPhysicalIntensity n p hp a ha Q H).toReal)
      measurableSet_Ioo).symm

end SlowEquilibration.SphericalMarkedWindows
