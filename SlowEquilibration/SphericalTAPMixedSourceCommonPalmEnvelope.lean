-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedSourceCommonRatio
public import SlowEquilibration.SphericalTAPMixedSourceUpperSelected
public import SlowEquilibration.SourceMixedAllCriticalIntensityEnvelope

/-! A single original-field coarea window supports both the mixed Palm upper
bound of §12.15 and the all-critical energy intensity envelope of §12.16. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalTAPMixedSourceCommonPalmEnvelope

open Set MeasureTheory Filter SphericalModel SphericalGaussianJet
open SphericalMarkedWindows ConditionedDeterminantMoments
open SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalBandSectionBridge
open SphericalQuadraticLatitudeJetCovariance
open SphericalTAPMixedQuadraticRealTransfer
open SphericalTAPMixedSourceBandShrink
open SphericalTAPMixedPalmSourceUpper SphericalTAPMixedSourceLaplaceRatio
open SphericalTAPMixedBandScaleIdentity SphericalTAPMixedPhysicalRadialLower
open SphericalTAPMixedSourceUpperSelected SphericalTAPMixedSourceCommonRatio
open SourceMixedAllCriticalIntensityEnvelope
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The physical mixed Palm upper bound admits the source score-band
condition on exactly the same selected radial and energy window. -/
theorem source_mixed_energy_palm_upper_shared_score
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    ∃ L R ε b C₂ : ℝ,
      0 < ε ∧ 0 < b ∧ 0 < C₂ ∧
      2*Real.sqrt (Q^2*μ.xi2 Q) < L ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧
      Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Ioo (0:ℝ) 1 ∧
      (∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
        ∀ k ∈ Icc L R,
          β*x/2 ≤ sourceEnergySlope μ Q e k ∧
            sourceEnergySlope μ Q e k ≤ (β*x+β)/2) ∧
      ∀ mN : ℕ → ℝ, ∃ C₁ : ℝ, 0 < C₁ ∧
        ∀ᶠ d : ℕ in atTop,
          ∀ b' : ℝ, 0 < b' → b' ≤ b →
          ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
          ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
            sourceMixedEnergyPalmBandExpectation d μ Q β e L R
              (Real.sqrt Q) b' u hu ≤
            C₁*sourceCriticalBandScale (d+1) μ h.overlap_range β (mN d) *
              Real.exp (β*(((d+2:ℕ):ℝ)*e-mN d)+
                ((d+2:ℕ):ℝ)*C₂*(e-markE μ β x Q)^2) := by
  obtain ⟨L,R,ε₀,b₀,C,C₂,hε₀,hb₀,hC,hC₂,hEdge,hLK,hKR,
    hband₀,hScore₀,hRatio₀⟩ :=
    mixed_source_joint_to_radial_ratio_upper_common μ h hnp
  let g := (L-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hg : 0 < g := by dsimp [g]; linarith
  obtain ⟨bq,Cq,hbq,hbqQ,hCq,hQuad⟩ :=
    source_mb_quadratic_physicalMixedPalm μ hnp h hg
  have hL : sourceRadialEdge μ Q < L := by
    simpa only [sourceRadialEdge] using hEdge
  obtain ⟨εr,cR,hεr,hcR,hRadial⟩ :=
    sourceMixedRadialLaplace_nearby_lower μ h hnp hL ⟨hLK,hKR⟩
  let ε := min ε₀ εr
  let b := min b₀ bq
  have hε : 0 < ε := lt_min hε₀ hεr
  have hb : 0 < b := lt_min hb₀ hbq
  have hLR : L < R := hLK.trans hKR
  have hband : Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Ioo (0:ℝ) 1 := by
    intro a ha
    apply hband₀
    exact ⟨by dsimp [b] at *; linarith [ha.1,min_le_left b₀ bq],
      by dsimp [b] at *; linarith [ha.2,min_le_left b₀ bq]⟩
  have hScore : ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
      ∀ k ∈ Icc L R,
      β*x/2 ≤ sourceEnergySlope μ Q e k ∧
        sourceEnergySlope μ Q e k ≤ (β*x+β)/2 := by
    intro e he k hk
    exact hScore₀ e
      ⟨by dsimp [ε] at *; linarith [he.1,min_le_left ε₀ εr],
        by dsimp [ε] at *; linarith [he.2,min_le_left ε₀ εr]⟩ k hk
  have hRatio : ∀ᶠ d : ℕ in atTop,
      ∀ b' : ℝ, 0 < b' → b' ≤ b →
      ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
      sourceMixedJointLaplace d μ β Q e L R (Real.sqrt Q) b' /
        sourceMixedRadialLaplace d μ Q e L R ≤
        C*Real.exp (((d+2:ℕ):ℝ)*
          (β*e+(Real.log (1-Q)+β^2*residualAtOne μ Q)/2+
            C₂*(e-markE μ β x Q)^2))/Real.sqrt (d+2:ℕ) := by
    filter_upwards [hRatio₀,hRadial] with d hd hr
    intro b' hb' hbb' e he
    have he₀ : e ∈ Icc (markE μ β x Q-ε₀) (markE μ β x Q+ε₀) := by
      exact ⟨by dsimp [ε] at *; linarith [he.1,min_le_left ε₀ εr],
        by dsimp [ε] at *; linarith [he.2,min_le_left ε₀ εr]⟩
    have her : e ∈ Icc (markE μ β x Q-εr) (markE μ β x Q+εr) := by
      exact ⟨by dsimp [ε] at *; linarith [he.1,min_le_right ε₀ εr],
        by dsimp [ε] at *; linarith [he.2,min_le_right ε₀ εr]⟩
    have hI : 0 < sourceMixedRadialLaplace d μ Q e L R :=
      lt_of_lt_of_le (by positivity) (hr e her)
    have hJ := sourceMixedJointLaplace_mono_band
      d μ h.overlap_range.1 β e L R (Real.sqrt Q) b' b₀
      hEdge hLR hb₀ (hbb'.trans (min_le_left b₀ bq)) hband₀
    exact (div_le_div_of_nonneg_right hJ hI.le).trans (hd e he₀)
  have hPalm : ∀ᶠ d : ℕ in atTop,
      ∀ b' : ℝ, 0 < b' → b' ≤ b →
      ∀ e ∈ Icc (markE μ β x Q-ε) (markE μ β x Q+ε),
      ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
        sourceMixedEnergyPalmBandExpectation d μ Q β e L R
          (Real.sqrt Q) b' u hu ≤
          Cq*(latitudeNormalization (d+1)).toReal *
            (sourceMixedJointLaplace d μ β Q e L R (Real.sqrt Q) b' /
              sourceMixedRadialLaplace d μ Q e L R) := by
    filter_upwards [hQuad,Filter.eventually_ge_atTop 1] with d hqd hd
    intro b' hb' hbb' e he u hu
    have hband' : Icc (Real.sqrt Q-b') (Real.sqrt Q+b') ⊆ Ioo (0:ℝ) 1 := by
      intro a ha
      apply hband
      exact ⟨by linarith [ha.1],by linarith [ha.2]⟩
    apply mixed_quadratic_real_sections_to_energy_palm
      d hd μ h.overlap_range.1 hnp β e L R (Real.sqrt Q) b' Cq
      hEdge hLR hb' hCq.le hband' u hu
    intro k hk a ha
    have hkmark : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤
        (scorePairEquiv (e,k)) 1 := by
      simp only [scorePairEquiv_apply]
      dsimp [g]
      linarith [hk.1]
    have hh := hqd u hu (scorePairEquiv (e,k)) hkmark
      b' hb' (hbb'.trans (min_le_right b₀ bq)) a ha
    simpa [scorePairEquiv_apply] using hh
  refine ⟨L,R,ε,b,C₂,hε,hb,hC₂,hEdge,hLK,hKR,hband,hScore,?_⟩
  intro mN
  exact source_mixed_energy_palm_upper_of_selected_coarea
    μ h mN L R ε b Cq C C₂ hCq hC hRatio hPalm

/-- Source Lemmas 12.15 and 12.16 on one literal all-critical mark window,
using the same first-moment centering sequence for both estimates. -/
theorem source_mixed_palm_and_allcritical_envelope_common
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    ∃ L R ε b C₁ C₂ : ℝ,
      0 < ε ∧ 0 < b ∧ 0 < C₁ ∧ 0 < C₂ ∧
      sourceRadialEdge μ Q < L ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧
      Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Ioo (0:ℝ) 1 ∧
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
        ∃ Cenv : ℝ, 0 < Cenv ∧ (β*x+β)/2 < β ∧
          ∀ᶠ d : ℕ in atTop,
            ∀ v ∈ Icc (0 : ℝ)
              (data.center d-((d+2:ℕ):ℝ)*(markE μ β x Q-ε)),
            sourceAllCriticalPhysicalEnergyDensity d μ Q L R (data.center d-v) ≤
              Cenv*Real.exp (((β*x+β)/2)*v) := by
  -- Select the common window first; the Palm scale is then specialized to
  -- the first-moment center constructed on that same window.
  obtain ⟨L,R,ε,b,C₂,hε,hb,hC₂,hEdge,hLK,hKR,
    hband,hScore,hPalm⟩ :=
    source_mixed_energy_palm_upper_shared_score μ h hnp
  have hL : sourceRadialEdge μ Q < L := by
    simpa only [sourceRadialEdge] using hEdge
  obtain ⟨data⟩ := sourceMaximum_first_moments μ h hnp hL
    ⟨hLK,hKR⟩ hε hScore
  obtain ⟨Cenv,hCenv,hEnv⟩ :=
    source_mixed_allcritical_intensity_envelope_from_firstMoments
      μ h hnp (hLK.trans hKR) hε hScore data
  obtain ⟨C₁,hC₁,hPalmData⟩ := hPalm data.center
  exact ⟨L,R,ε,b,C₁,C₂,hε,hb,hC₁,hC₂,hL,hLK,hKR,
    hband,data,hPalmData,Cenv,hCenv,data.lower_density_rate_lt_beta,hEnv⟩

end SlowEquilibration.SphericalTAPMixedSourceCommonPalmEnvelope
