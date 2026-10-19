-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLinearLower
public import SlowEquilibration.SphericalTAPCriticalPurePalmBandLower

@[expose] public section
namespace SlowEquilibration.SphericalTAPHeavyBandPartitionLower
noncomputable section
open SlowEquilibration.SphericalModel
open SlowEquilibration.SphericalGaussianJet
open MeasureTheory Set
set_option autoImplicit false

/-- The deterministic final step of source Corollary 12.21(2): a single
physical center whose band is not light and whose center energy lies in the
lower half of the source window forces the printed global-partition lower
bound. No independence or disjointness of bands is used. -/
theorem source_heavy_band_implies_partition_lower
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) (Q : ℝ)
    (J : Disorder N μ.maxDegree) (u : Vector N)
    (I : Set ℝ) (hI : MeasurableSet I)
    {β m L δ D : ℝ} (hβ : 0 ≤ β) (hδ : 0 ≤ δ) (hD : 0 ≤ D)
    (henergy : m-L ≤ field (centerCoefficients (mixtureCoefficients μ) Q) J u)
    (hheavy : δ*D*Real.exp
      (β*(field (centerCoefficients (mixtureCoefficients μ) Q) J u-m)) ≤
        partitionOn β (field (mixtureCoefficients μ) J) (overlapRegion u I)) :
    δ*Real.exp (-β*L)*D ≤ partition N β (field (mixtureCoefficients μ) J) := by
  have hβenergy : -β*L ≤
      β*(field (centerCoefficients (mixtureCoefficients μ) Q) J u-m) := by
    nlinarith [mul_nonneg hβ
      (show 0 ≤ field (centerCoefficients (mixtureCoefficients μ) Q) J u-m+L
        by linarith)]
  have hexp := Real.exp_le_exp.mpr hβenergy
  calc
    δ*Real.exp (-β*L)*D = δ*D*Real.exp (-β*L) := by ring
    _ ≤ δ*D*Real.exp
        (β*(field (centerCoefficients (mixtureCoefficients μ) Q) J u-m)) :=
      mul_le_mul_of_nonneg_left hexp (mul_nonneg hδ hD)
    _ ≤ partitionOn β (field (mixtureCoefficients μ) J) (overlapRegion u I) := hheavy
    _ ≤ partition N β (field (mixtureCoefficients μ) J) :=
      partitionOn_le_partition hN β
        (field_contDiff (mixtureCoefficients μ) J).continuous
        (overlapRegion_measurable u hI)

end
end SlowEquilibration.SphericalTAPHeavyBandPartitionLower
