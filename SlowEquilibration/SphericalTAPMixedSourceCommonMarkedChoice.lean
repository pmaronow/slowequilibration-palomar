-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedSourceMarkedIntegrable

/-! The common source Palm and all-critical envelope choice is narrowed once
more so that the literal determinant-weighted mark and radial Palm ratios are
integrable on that exact same window. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalTAPMixedSourceCommonMarkedChoice

open Set MeasureTheory Filter SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPMixedSourceCommonPalmEnvelope
open SphericalTAPMixedSourceMarkedIntegrable
open SourceMixedAllCriticalIntensityEnvelope
open SphericalTAPCriticalEnergyPalmAverage SphericalTAPMixedBandExponent
open SphericalTAPMixedPalmSourceUpper SphericalTAPMixedBandScaleIdentity
open SphericalTAPCriticalBandSectionBridge
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem source_mixed_palm_allcritical_marked_common_choice
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    ∃ L R ε b C₁ C₂ Cenv Cmark : ℝ,
      0 < ε ∧ 0 < b ∧ 0 < C₁ ∧ 0 < C₂ ∧ 0 < Cenv ∧ 0 < Cmark ∧
      sourceRadialEdge μ Q < L ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧
      Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Ioo (0:ℝ) 1 ∧
      (β*x+β)/2 < β ∧
      ∃ data : SourceMaximumFirstMomentConclusions μ β x Q L R,
        (∀ᶠ d : ℕ in atTop,
          ∀ b' : ℝ, 0 < b' → b' ≤ b →
          ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
          ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
            sourceMixedEnergyPalmBandExpectation d μ Q β e L R
              (Real.sqrt Q) b' u hu ≤
            C₁*sourceCriticalBandScale (d+1) μ h.overlap_range β (data.center d) *
              Real.exp (β*(((d+2:ℕ):ℝ)*e-data.center d)+
                ((d+2:ℕ):ℝ)*C₂*(e-markE μ β x Q)^2)) ∧
        (∀ᶠ d : ℕ in atTop,
          ∀ v ∈ Icc (0 : ℝ)
            (data.center d-((d+2:ℕ):ℝ)*(markE μ β x Q-ε)),
            sourceAllCriticalPhysicalEnergyDensity d μ Q L R (data.center d-v) ≤
              Cenv*Real.exp (((β*x+β)/2)*v)) ∧
        (∀ᶠ d : ℕ in atTop,
          ∀ b' : ℝ, 0 < b' → b' ≤ b → ∀ e : ℝ,
          ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
            (∀ k ∈ Ioo L R,
              Integrable (fun J => intrinsicDet μ Q u J *
                partitionOn β (field (mixtureCoefficients μ) J)
                  (overlapRegion u (Icc (Real.sqrt Q-b') (Real.sqrt Q+b'))))
                (mixedLaw μ Q u hu (scorePairEquiv (e,k))) ∧
              (∫ J, intrinsicDet μ Q u J *
                partitionOn β (field (mixtureCoefficients μ) J)
                  (overlapRegion u (Icc (Real.sqrt Q-b') (Real.sqrt Q+b')))
                ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
                (∫ J, intrinsicDet μ Q u J
                  ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) ≤
                Cmark*(latitudeNormalization (d+1)).toReal *
                  (∫ a in Icc (Real.sqrt Q-b') (Real.sqrt Q+b'),
                    (Real.sqrt (1-a^2))^(d-1) *
                      Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) ∂volume)) ∧
            Integrable (fun k : ℝ =>
              (∫ J, intrinsicDet μ Q u J *
                partitionOn β (field (mixtureCoefficients μ) J)
                  (overlapRegion u (Icc (Real.sqrt Q-b') (Real.sqrt Q+b')))
                ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
                (∫ J, intrinsicDet μ Q u J
                  ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))))
              (sourceAllCriticalRadialLaw d μ Q e L R)) := by
  obtain ⟨L,R,ε,bP,C₁,C₂,hε,hbP,hC₁,hC₂,hEdge,hLK,hKR,
    hbandP,data,hPalm,Cenv,hCenv,hRate,hEnv⟩ :=
    source_mixed_palm_and_allcritical_envelope_common μ h hnp
  obtain ⟨bM,Cmark,hbM,hCmark,hbandM,hMarked⟩ :=
    source_mixed_fixed_mark_and_radial_ratio_integrable μ h hnp
      (by simpa only [sourceRadialEdge] using hEdge) (hLK.trans hKR)
  let b := min bP bM
  have hb : 0 < b := lt_min hbP hbM
  have hband : Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Ioo (0:ℝ) 1 := by
    intro a ha
    apply hbandP
    have hh := min_le_left bP bM
    exact ⟨by dsimp [b] at *; linarith [ha.1],
      by dsimp [b] at *; linarith [ha.2]⟩
  refine ⟨L,R,ε,b,C₁,C₂,Cenv,Cmark,hε,hb,hC₁,hC₂,hCenv,hCmark,
    hEdge,hLK,hKR,hband,hRate,data,?_,hEnv,?_⟩
  · filter_upwards [hPalm] with d hd
    intro b' hb' hbb' e he u hu
    exact hd b' hb' (hbb'.trans (min_le_left bP bM)) e he u hu
  · filter_upwards [hMarked] with d hd
    intro b' hb' hbb' e u hu
    exact hd b' hb' (hbb'.trans (min_le_right bP bM)) e u hu

end SlowEquilibration.SphericalTAPMixedSourceCommonMarkedChoice
