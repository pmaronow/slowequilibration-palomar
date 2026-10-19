-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalLightBandMark

@[expose] public section

/-! The first quantitative step of source Corollary 12.21: the actual
expected number of light critical bands is bounded by a vanishing Palm
factor times the actual expected number of centers in the same score window. -/

namespace SlowEquilibration.SphericalTAPCriticalLightCountBound
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCriticalBandSectionBridge
open SphericalTAPCriticalPalmBandLower
open SphericalTAPCriticalLightBandMark
open SphericalTAPCriticalLightCountTransfer
open SphericalTAPCriticalFixedBandPalmLower
open SphericalTAPCertificate
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Under the manuscript's compact exterior radial window, the actual
original-disorder expected count of centers with a light physical band is
at most `ε` times the actual unweighted center count, for a sufficiently
small fixed lightness threshold and all large dimensions. The energy window
may depend on dimension, which allows the source window `m_N ± L`. -/
theorem mixed_sourceLightBand_count_le_count_eventually
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    {M r L R b : ℝ} (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hb : 0 < b)
    (hBand : Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Icc (-r) r)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L)
    (hU : Icc L R ⊆ Icc (-M) M) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ d : ℕ in atTop,
      ∀ (W : Set ℝ), MeasurableSet W → W ⊆ Icc (-M) M →
      ∀ mN : ℝ,
      (∫⁻ J, actualScoreWindowCount (d+1)
        (centerCoefficients (mixtureCoefficients μ) Q)
        (rectangularScoreWindow W (Ioo L R))
        (sourceLightBandMark d μ h.overlap_range β mN δ
          (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))) J
          ∂disorderLaw (d+2) μ.maxDegree) ≤
      ENNReal.ofReal ε *
        (∫⁻ J, actualScoreWindowCount (d+1)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (rectangularScoreWindow W (Ioo L R))
          (fun _ _ => 1) J
            ∂disorderLaw (d+2) μ.maxDegree) := by
  let g : ℝ := (L-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hg : 0 < g := by dsimp [g]; linarith
  have hFixed := mixed_sourcePalm_band_lower_tight μ h hnp
    hM hr0 hr1 hg (Z := R) _ measurableSet_Icc hBand
  intro ε hε
  obtain ⟨δ,hδ,hPalm⟩ := hFixed ε hε
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hPalm,
    microscopic_interval_eventually_in_fixed_band Q hb]
    with d hd hMicro
  intro W hW hWM mN
  let K := rectangularScoreWindow W (Ioo L R)
  have hK : MeasurableSet K :=
    rectangularScoreWindow_measurable W (Ioo L R) hW measurableSet_Ioo
  apply actual_mixed_marked_count_le_of_uniform_palm d μ h.overlap_range.1
    hnp K hK _
    (sourceLightBandMark_measurable d μ h.overlap_range β mN δ
      (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) measurableSet_Icc)
    ENNReal.ofReal_ne_top
  intro u hu z hz
  have haM : |z 0| ≤ M := abs_le.mpr (hWM hz.1)
  have hkM : |z 1| ≤ M := abs_le.mpr (hU ⟨hz.2.1.le,hz.2.2.le⟩)
  have hkg : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ z 1 := by
    dsimp [g]
    linarith [hz.2.1]
  have hkEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < z 1 := by
    linarith [hz.2.1]
  have hzPair : scorePairEquiv (z 0,z 1) = z := by
    apply PiLp.ext
    intro i
    fin_cases i <;> rfl
  have hRatio := hd u hu (z 0) (z 1) haM hkM hkg hz.2.2.le hMicro mN
  dsimp only at hRatio
  simp only [← scorePairEquiv_apply] at hRatio
  rw [hzPair] at hRatio
  exact sourceLightBandMark_mixed_local_intensity_le d μ h.overlap_range
    hnp u hu z hkEdge β mN δ _ measurableSet_Icc hε.le
      (by simpa only [mul_assoc] using hRatio)

end
end SlowEquilibration.SphericalTAPCriticalLightCountBound
