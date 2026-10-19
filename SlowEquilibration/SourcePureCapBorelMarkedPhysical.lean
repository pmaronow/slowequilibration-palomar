-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapBorelMarkedKR
public import SlowEquilibration.SphericalTAPPureMarkedEnergyPalmBound

/-! Physical-energy form of the unconditional arbitrary-Borel marked pure
cap upper bound. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapBorelMarkedPhysical
noncomputable section
open Set Filter MeasureTheory
open SphericalModel SphericalMarkedWindows SphericalGaussianJet
open PureStationarity
open SourcePureCapBorelMarkedValue
open SourcePureCapBorelMarkedKR
open SourcePureCapBorelRadialFirst
open SourcePureLatitudeRadialDisintegration
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_original_borel_band_marked_physical_bound
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hsub : pureResidualCoefficient p β a < 1/2)
    {g : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) 1
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ∀ (J : Set ℝ), MeasurableSet J →
      (∀ H ∈ J, 2*Real.sqrt (μ.xi2 1)+g ≤ (p:ℝ)*(H/(d+2:ℕ))) →
      ∀ (I : Set ℝ), MeasurableSet I → I ⊆ Ico a 1 →
      (∫⁻ K, actualScoreWindowCount (d+1) c
        (physicalEnergyWindow (d+2) J univ)
        (originalBorelBandMark d μ β I) K
        ∂disorderLaw (d+2) μ.maxDegree) ≤
      ∫⁻ H in J, pureCriticalPhysicalIntensity d p hp 1 (by positivity) 1 H *
        (ENNReal.ofReal C *
          ∫⁻ s : Ioi (0:ℝ),
            radialMeanWeight (d+1) p β H I s
            ∂radialLaw (d+1)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp 1 (by positivity)
  let c := centerCoefficients (mixtureCoefficients μ) 1
  obtain ⟨C,hC,hVal⟩ := pure_original_borel_band_marked_value_bound
    p hp β ha hsub hg
  refine ⟨C,hC,?_⟩
  filter_upwards [hVal] with d hd
  intro J hJ hEdge I hI hIcap
  let N : ℝ := (d+2:ℕ)
  let W : Set ℝ := (fun e : ℝ => N*e) ⁻¹' J
  have hW : MeasurableSet W := hJ.preimage (measurable_const_mul _)
  have hWscore : pureScoreWindow p (physicalEnergyWindow (d+2) J univ) = W := by
    ext e
    simp [pureScoreWindow,physicalEnergyWindow,rectangularScoreWindow,
      pureScoreLine,W,N]
  have hWedge : ∀ e ∈ W, 2*Real.sqrt (μ.xi2 1)+g ≤ (p:ℝ)*e := by
    intro e he
    have hscale : (N*e)/(d+2:ℕ) = e := by dsimp [N]; field_simp
    simpa only [hscale] using hEdge (N*e) he
  have hCount (K : Disorder (d+2) μ.maxDegree) :
      actualScoreWindowCount (d+1) c (physicalEnergyWindow (d+2) J univ)
        (originalBorelBandMark d μ β I) K =
      actualValueWindowCount (d+1) c W
        (originalBorelBandMark d μ β I) K := by
    rw [actual_pure_scoreWindowCount_eq_valueWindowCount
      (d+1) p hp 1 (by positivity) 1 _ _ K,hWscore]
  have hCountIntegral := lintegral_congr
    (μ := disorderLaw (d+2) μ.maxDegree) (fun K => hCount K)
  have hKR := hd W hW hWedge I hI hIcap
  rw [hCountIntegral]
  calc
    _ ≤ ∫⁻ e in W, pureCriticalIntensity d p hp 1 (by positivity) 1 e *
        (ENNReal.ofReal C *
          ∫⁻ s : Ioi (0:ℝ),
            radialMeanWeight (d+1) p β (N*e) I s
            ∂radialLaw (d+1)) := hKR
    _ = ∫⁻ H in J, pureCriticalPhysicalIntensity d p hp 1 (by positivity) 1 H *
        (ENNReal.ofReal C *
          ∫⁻ s : Ioi (0:ℝ), radialMeanWeight (d+1) p β H I s
            ∂radialLaw (d+1)) := by
      rw [setLIntegral_positive_rescale N (by dsimp [N]; positivity)]
      apply lintegral_congr
      intro H
      simp only [pureCriticalPhysicalIntensity,N]
      have hresc : ((d+2:ℕ):ℝ)*(H/(d+2:ℕ))=H := by field_simp
      rw [hresc]
      ac_rfl

end
end SlowEquilibration.SourcePureCapBorelMarkedPhysical
