-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePureCapBorelMarkedValue

/-! Actual marked Kac--Rice upper for arbitrary Borel pure cap bands,
with the physical disorder, critical-point count, and original field. -/

@[expose] public section
namespace SlowEquilibration.SourcePureCapBorelMarkedKR
noncomputable section
open Set Filter MeasureTheory
open SphericalModel SphericalMarkedWindows SphericalGaussianJet
open PureStationarity
open SourcePureCapBorelDeterminantPalm
open SourcePureCapBorelMarkedValue
open SourcePureCapBorelRadialFirst
open SourcePureLatitudeRadialDisintegration
open SphericalTAPPureMarkedValueWeight
open scoped ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem pure_original_borel_band_marked_value_bound
    (p : ℕ) (hp : 2 ≤ p) (β : ℝ)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hsub : pureResidualCoefficient p β a < 1/2)
    {g : ℝ} (hg : 0 < g) :
    let μ := FiniteMixture.pure p hp 1 (by positivity)
    let c := centerCoefficients (mixtureCoefficients μ) 1
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ d : ℕ in atTop,
      ∀ (W : Set ℝ), MeasurableSet W →
      (∀ e ∈ W, 2*Real.sqrt (μ.xi2 1)+g ≤ (p:ℝ)*e) →
      ∀ (I : Set ℝ), MeasurableSet I → I ⊆ Ico a 1 →
      (∫⁻ J, actualValueWindowCount (d+1) c W
        (originalBorelBandMark d μ β I) J
        ∂disorderLaw (d+2) μ.maxDegree) ≤
      ∫⁻ e in W, pureCriticalIntensity d p hp 1 (by positivity) 1 e *
        (ENNReal.ofReal C *
          ∫⁻ s : Ioi (0:ℝ),
            radialMeanWeight (d+1) p β ((d+2:ℕ)*e) I s
            ∂radialLaw (d+1)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp 1 (by positivity)
  let c := centerCoefficients (mixtureCoefficients μ) 1
  obtain ⟨C,hC,hPalm⟩ := pure_original_borel_band_determinant_palm_bound
    p hp β ha hsub hg
  refine ⟨C,hC,?_⟩
  filter_upwards [hPalm,Filter.eventually_ge_atTop 1] with d hdPalm hd
  intro W hW hEdge I hI hIcap
  have hKR := actual_pure_marked_count_le_value_weight
    d p hp 1 (by positivity) (Q := 1) (by positivity) W hW
    (originalBorelBandMark d μ β I)
    (originalBorelBandMark_measurable d μ β hI)
    (fun e => ENNReal.ofReal C *
      ∫⁻ s : Ioi (0:ℝ),
        radialMeanWeight (d+1) p β ((d+2:ℕ)*e) I s
        ∂radialLaw (d+1))
    (by
      intro u hu e he
      have hscale : ((d+2:ℕ)*e)/(d+2:ℕ) = e := by field_simp
      have hpb := hdPalm u hu ((d+2:ℕ)*e)
        (by simpa only [hscale,μ] using hEdge e he) I hI hIcap
      have hLocal := pure_original_borel_band_mark_local_intensity
        d p hd hp β C hC.le u hu e I hI
          (by simpa only [hscale,μ,c] using hpb)
      simpa only [one_pow,one_mul] using hLocal)
  simpa only [μ,c] using hKR

end
end SlowEquilibration.SourcePureCapBorelMarkedKR
