-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedMarkedEnergyPalmBound
public import SlowEquilibration.SphericalTAPMixedSourceCommonMarkedChoice
public import SlowEquilibration.NormalizedRadialMeasureIntegrableTransfer
public import SlowEquilibration.SourceMixedLowSumCenterCorrection

@[expose] public section

/-! Source Corollary 12.17 in the nonpure model: the expected sum of literal
original-field band partitions over low-energy critical centers decays at
the source rate on the exact deterministic D scale. -/

namespace SlowEquilibration.SourceMixedLowSumCorollary
noncomputable section
open MeasureTheory Set Filter SphericalModel SphericalGaussianJet
open SphericalMarkedWindows SphericalTAPCertificate TwoAtomStationarity
open ConditionedDeterminantMoments SphericalTAPCriticalEnergyPalmAverage
open SphericalTAPCriticalBandSectionBridge
open SphericalTAPMixedSourceCommonMarkedChoice
open SphericalTAPMixedPalmSourceUpper
open SphericalTAPMixedMarkedEnergyPalmBound
open SourceMixedAllCriticalIntensityEnvelope
open SourceMixedLowSumENNIntegral SourceMixedLowSumCenterCorrection
open NormalizedRadialMeasureIntegrableTransfer
open scoped Topology ENNReal
set_option autoImplicit false
set_option maxHeartbeats 1400000

/-- The mixed clause of source Corollary 12.17, with one fixed common
choice of physical radial window, latitude width, critical-point centering,
and the exact printed D scale. The upper physical energy endpoint is closed;
the strict manuscript window is contained in it. -/
theorem source_mixed_band_partition_below_window_sum
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    ∃ L R ε b₀ C C₂ Cenv τ₀ a₀ : ℝ,
      0 < ε ∧ 0 < b₀ ∧ 0 < C ∧ 0 < C₂ ∧ 0 < Cenv ∧
      sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧
      markK μ β Q < R ∧
      Icc (Real.sqrt Q-b₀) (Real.sqrt Q+b₀) ⊆ Ioo (0:ℝ) 1 ∧
      τ₀ = min ε ((β-(β*x+β)/2)/(4*C₂)) ∧
      a₀ = (β-(β*x+β)/2)/2 ∧ 0 < τ₀ ∧ 0 < a₀ ∧
      ∃ data : SourceMaximumFirstMomentConclusions μ β x Q L R,
        ∀ τ : ℝ, 0 < τ → τ ≤ τ₀ →
          ∀ᶠ d : ℕ in atTop,
            ∀ b : ℝ, 0 < b → b ≤ b₀ →
            ∀ M : ℝ, 0 ≤ M →
              (∫⁻ J, actualScoreWindowCount (d+1)
                (centerCoefficients (mixtureCoefficients μ) Q)
                (physicalEnergyWindow (d+2)
                  (Icc (((d+2:ℕ):ℝ)*(markE μ β x Q-τ))
                    (data.center d-M)) (Ioo L R))
                (SphericalTAPMixedLowSumMarkedKR.sourceMixedBandMark
                  d μ β (Real.sqrt Q) b) J
                ∂disorderLaw (d+2) μ.maxDegree) ≤
              ENNReal.ofReal
                (C*sourceCriticalBandScale (d+1) μ h.overlap_range β
                  (data.center d)*Real.exp (-a₀*M)) := by
  obtain ⟨L,R,ε,b₀,C₁,C₂,Cenv,Cmark,hε,hb₀,hC₁,hC₂,hCenv,hCmark,
    hEdge,hLK,hKR,hband,hRate,data,hPalm,hEnv,hMarked⟩ :=
      source_mixed_palm_allcritical_marked_common_choice μ h hnp
  let cPlus : ℝ := (β*x+β)/2
  let a₀ : ℝ := (β-cPlus)/2
  let τ₀ : ℝ := min ε ((β-cPlus)/(4*C₂))
  let C : ℝ := Cenv*C₁*Real.exp 1/a₀
  have ha₀ : 0 < a₀ := by dsimp [a₀,cPlus]; linarith
  have hτ₀ : 0 < τ₀ := lt_min hε (div_pos (by dsimp [cPlus]; linarith)
    (by positivity))
  have hC : 0 < C := div_pos (mul_pos (mul_pos hCenv hC₁)
    (Real.exp_pos _)) ha₀
  refine ⟨L,R,ε,b₀,C,C₂,Cenv,τ₀,a₀,hε,hb₀,hC,hC₂,hCenv,
    hEdge,hLK,hKR,hband,rfl,rfl,hτ₀,ha₀,data,?_⟩
  intro τ hτ hτBound
  have hτε : τ ≤ ε := hτBound.trans (min_le_left _ _)
  have hτRate : τ ≤ (β-cPlus)/(4*C₂) :=
    hτBound.trans (min_le_right _ _)
  have hcenter := source_center_quadratic_error_eventually_bounded
    μ h data hτ hC₂
  filter_upwards [hPalm,hEnv,hMarked,hcenter,
    Filter.eventually_ge_atTop 1] with d hp he hm hc hd
  intro b hb hbb M hM
  let N : ℝ := ((d+2:ℕ):ℝ)
  let m := data.center d
  let E₀ := markE μ β x Q
  let D := sourceCriticalBandScale (d+1) μ h.overlap_range β m
  let B := fun H : ℝ => C₁*D*Real.exp
    (β*(H-m)+C₂*(H-N*E₀)^2/N)
  have hN : 0 < N := by dsimp [N]; positivity
  have hD : 0 ≤ D := (sourceCriticalBandScale_pos
    (d+1) (by omega) μ h.overlap_range β m).le
  have hL : 2*Real.sqrt (Q^2*μ.xi2 Q) < L := by
    simpa only [sourceRadialEdge] using hEdge
  have hLR : L < R := hLK.trans hKR
  have hEnergy (H : ℝ) (hH : H ∈ Icc (N*(E₀-τ)) (m-M)) :
      H/N ∈ Icc (E₀-ε) (E₀+ε) := by
    have hLo : E₀-ε ≤ H/N := (le_div_iff₀ hN).mpr (by
      nlinarith [hH.1,hτε])
    have hHi : H/N ≤ E₀+ε := (div_le_iff₀ hN).mpr (by
      have hh := hc.1
      have hτN := mul_le_mul_of_nonneg_right hτε hN.le
      have hOffset := (abs_le.mp (show |m-N*E₀| ≤ τ*N by
        nlinarith [hh])).2
      nlinarith [hH.2,hM])
    exact ⟨hLo,hHi⟩
  have hPalmBound (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
      (H : ℝ) (hH : H ∈ Icc (N*(E₀-τ)) (m-M)) :
      sourceMixedEnergyPalmBandExpectation d μ Q β (H/N) L R
        (Real.sqrt Q) b u hu ≤ B H := by
    have hh := hp b hb hbb (H/N) (hEnergy H hH) u hu
    have harg : β*(N*(H/N)-m)+N*C₂*(H/N-E₀)^2 =
        β*(H-m)+C₂*(H-N*E₀)^2/N := by
      field_simp [hN.ne']
    rw [harg] at hh
    exact hh
  have hCondInt (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
      (H : ℝ) (_hH : H ∈ Icc (N*(E₀-τ)) (m-M))
      (k : ℝ) (hk : k ∈ Ioo L R) :
      Integrable (fun J => intrinsicDet μ Q u J *
        partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))))
        (mixedLaw μ Q u hu (scorePairEquiv (H/N,k))) :=
    (hm b hb hbb (H/N) u hu).1 k hk |>.1
  have hRatioInt (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
      (H : ℝ) (_hH : H ∈ Icc (N*(E₀-τ)) (m-M)) :
      IntegrableOn (fun k =>
        ((∫ J, intrinsicDet μ Q u J *
          partitionOn β (field (mixtureCoefficients μ) J)
            (overlapRegion u (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)))
          ∂mixedLaw μ Q u hu (scorePairEquiv (H/N,k))) /
        (∫ J, intrinsicDet μ Q u J
          ∂mixedLaw μ Q u hu (scorePairEquiv (H/N,k)))) *
        sourceAllCriticalRadialWeight d μ Q (H/N) k) (Ioo L R) := by
    exact integrable_weighted_of_law
      (sourceAllCriticalRadialWeight_measurable d μ Q (H/N))
      (sourceAllCriticalRadialWeight_nonneg d μ Q (H/N))
      (sourceAllCriticalRadialWeight_integral_pos d μ h.overlap_range.1
        (H/N) hL hLR) (hm b hb hbb (H/N) u hu).2
  have hKR := actual_mixed_band_sum_le_energy_palm_envelope
    d μ h.overlap_range.1 hnp β (Real.sqrt Q) b
    (N*(E₀-τ)) (m-M) L R hL hLR B
    hCondInt hRatioInt hPalmBound
  have hDens (H : ℝ) (hH : H ∈ Icc (N*(E₀-τ)) (m-M)) :
      sourceAllCriticalPhysicalEnergyDensity d μ Q L R H ≤
        Cenv*Real.exp (cPlus*(m-H)) := by
    have hv : m-H ∈ Icc (0:ℝ) (m-N*(E₀-ε)) := by
      constructor <;> dsimp [N,m,E₀] at * <;> nlinarith [hH.1,hH.2,hM,hτε]
    have hh := he (m-H) hv
    change sourceAllCriticalPhysicalEnergyDensity d μ Q L R (m-(m-H)) ≤
      Cenv*Real.exp (cPlus*(m-H)) at hh
    have hmeq : m-(m-H)=H := by ring
    rw [hmeq] at hh
    exact hh
  have hB0 (H : ℝ) (_hH : H ∈ Icc (N*(E₀-τ)) (m-M)) :
      0 ≤ B H := by dsimp [B]; positivity
  have hTail := intensity_palm_below_window_lintegral
    (sourceAllCriticalPhysicalEnergyDensity d μ Q L R) B
    hN hM hC₂ hCenv.le hC₁.le hD
    (by dsimp [cPlus]; linarith : 0 < β-cPlus)
    hc.1 hτRate hB0 hDens
    (by intro H hH; exact le_refl _)
  have hFinalReal :
      (Cenv*C₁*D*Real.exp (C₂*(m-N*E₀)^2/N))/a₀*
        Real.exp (-a₀*M) ≤ C*D*Real.exp (-a₀*M) := by
    have hExp : Real.exp (C₂*(m-N*E₀)^2/N) ≤ Real.exp 1 :=
      Real.exp_le_exp.mpr hc.2
    calc
      _ ≤ (Cenv*C₁*D*Real.exp 1)/a₀*Real.exp (-a₀*M) := by
        gcongr
      _ = C*D*Real.exp (-a₀*M) := by dsimp [C]; ring
  exact hKR.trans (hTail.trans
    (ENNReal.ofReal_le_ofReal (by simpa only [D,N,m,E₀,a₀,cPlus] using hFinalReal)))

end
end SlowEquilibration.SourceMixedLowSumCorollary
