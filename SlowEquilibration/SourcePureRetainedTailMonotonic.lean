-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLocalMaxActualTailBridge

/-! Ordinary selected critical-point counts are monotone in their value
window; their finite first moments inherit that monotonicity. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PairConditionalDeterminantMoments
open Set MeasureTheory SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalKacRiceGluing
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 450000

theorem sourceRetainedValueWindowCount_mono
    {P : ℕ} (n : ℕ) (c : Degree P → ℝ) (I J : Set ℝ)
    (hIJ : I ⊆ J) (κ C ε η E G : ℝ)
    (A : Disorder (n+1) P) :
    sourceRetainedValueWindowCount n c I κ C ε η E G A ≤
      sourceRetainedValueWindowCount n c J κ C ε η E G A := by
  unfold sourceRetainedValueWindowCount
  rw [actualValueWindowCount_eq_indicator, actualValueWindowCount_eq_indicator]
  unfold actualSphereCount
  apply ENNReal.tsum_le_tsum
  intro u
  dsimp only
  by_cases hu : actualValue c A u ∈ I
  · have hJu : actualValue c A u ∈ J := hIJ hu
    simp only [ite_eq_left hu, ite_eq_left hJu, le_refl]
  · simp only [ite_eq_right hu, zero_le]

theorem sourceRetainedValueWindowMean_mono
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (I J : Set ℝ) (hIJ : I ⊆ J) (κ C ε η E G : ℝ) :
    sourceRetainedValueWindowMean n μ Q I κ C ε η E G ≤
      sourceRetainedValueWindowMean n μ Q J κ C ε η E G := by
  unfold sourceRetainedValueWindowMean
  have hfinite := sourceUnfilteredValueWindowCount_lintegral_lt_top n hn μ hQ J
  have htop : (∫⁻ A, sourceRetainedValueWindowCount n
      (centerCoefficients (mixtureCoefficients μ) Q) J κ C ε η E G A
      ∂disorderLaw (n+1) μ.maxDegree) < ⊤ :=
    (lintegral_mono (sourceRetainedValueWindowCount_le_unfiltered n
      (centerCoefficients (mixtureCoefficients μ) Q) J κ C ε η E G)).trans_lt hfinite
  exact ENNReal.toReal_mono htop.ne
    (lintegral_mono (sourceRetainedValueWindowCount_mono n
      (centerCoefficients (mixtureCoefficients μ) Q) I J hIJ κ C ε η E G))

theorem sourceRetainedValueWindowMean_le_unfiltered
    (n : ℕ) (hn : 1 ≤ n) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (I : Set ℝ) (κ C ε η E G : ℝ) :
    sourceRetainedValueWindowMean n μ Q I κ C ε η E G ≤
      sourceUnfilteredValueWindowMean n μ Q I := by
  unfold sourceRetainedValueWindowMean sourceUnfilteredValueWindowMean
  exact ENNReal.toReal_mono
    (sourceUnfilteredValueWindowCount_lintegral_lt_top n hn μ hQ I).ne
    (lintegral_mono (sourceRetainedValueWindowCount_le_unfiltered n
      (centerCoefficients (mixtureCoefficients μ) Q) I κ C ε η E G))

end SlowEquilibration.PairConditionalDeterminantMoments
