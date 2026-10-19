-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapRadialOutsideSourceMean

/-! The actual marked Kac--Rice estimate with the source's exact raw cap
and disconnected-window conditional means as scalar integrands. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapMarkedSourceIntegral
noncomputable section
open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows
open SphericalGaussianJet PureStationarity
open SourcePureCapBorelMarkedPhysical SourcePureCapBorelMarkedValue
open SourcePureCapBorelRadialFirst SourcePureCapRadialSourceMean
open SourcePureCapRadialOutsideSourceMean
open SourcePureLatitudeRadialDisintegration
open SphericalPureCapSourceRatios
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_original_marked_cap_source_integral
    (p : ℕ) (hp : 4 ≤ p) (β ep cp a : ℝ)
    (ha : a ∈ Ioo (0:ℝ) 1)
    (hsub : pureResidualCoefficient p β a < 1/2)
    {g : ℝ} (hg : 0 < g)
    (u : ∀ d : ℕ, Vector (d+2))
    (hu : ∀ d : ℕ, ‖u d‖^2=(d+2:ℕ)) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) 1
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ∀ J : Set ℝ, MeasurableSet J →
      (∀ H ∈ J, 2*Real.sqrt (μ.xi2 1)+g ≤ (p:ℝ)*(H/(d+2:ℕ))) →
      (∫⁻ K, actualScoreWindowCount (d+1) c
        (physicalEnergyWindow (d+2) J univ)
        (originalBorelBandMark d μ β (Ico a 1)) K
        ∂disorderLaw (d+2) μ.maxDegree) ≤
      ∫⁻ H in J, pureCriticalPhysicalIntensity d p (by omega) 1 (by positivity) 1 H *
        (ENNReal.ofReal C * ENNReal.ofReal
          (sourceCapMean p β ep cp a d
            (H-((d+2:ℕ)*ep-Real.log (d+2:ℕ)/(2*cp))))) := by
  dsimp only
  obtain ⟨C,hC,hMark⟩ := pure_original_borel_band_marked_physical_bound
    p (by omega) β ha hsub hg
  refine ⟨C,hC,?_⟩
  filter_upwards [hMark,Filter.eventually_ge_atTop 2] with d hd hd2
  intro J hJ hEdge
  have hh := hd J hJ hEdge (Ico a 1) measurableSet_Ico (Subset.rfl)
  refine hh.trans ?_
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hJ] with H hH
  have hH0 : ((d+2:ℕ):ℝ)*ep+
      (H-((d+2:ℕ)*ep-Real.log (d+2:ℕ)/(2*cp)))-
      Real.log (d+2:ℕ)/(2*cp)=H := by ring
  have hMean := pure_original_radial_cap_mean_eq_source
    d p hd2 hp β ep cp a
    (H-((d+2:ℕ)*ep-Real.log (d+2:ℕ)/(2*cp))) ha.1 ha.2
    (u d) (hu d)
  rw [hH0] at hMean
  rw [hMean]

end
end SlowEquilibration.SourcePureCapMarkedSourceIntegral
