-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalLightCountBound
public import SlowEquilibration.SphericalMaximumFirstMoments
public import SlowEquilibration.NatLogSequenceScales

@[expose] public section

/-! Source Corollary 12.21(1) for actual mixed critical points in the
centered physical-energy window. -/

namespace SlowEquilibration.SphericalTAPCriticalFewLightBands
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCriticalLightBandMark SphericalTAPCriticalLightCountBound
open SphericalTAPCertificate
open TwoAtomStationarity
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Any fixed physical window around the actual logarithmically corrected
centering lies in the source's fixed normalized energy interval eventually. -/
theorem centered_physical_window_eventually_in_normalized_interval
    (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : Certificate μ β x Q)
    (data : SourceMaximumFirstMomentConclusions μ β x Q L R)
    {ε0 : ℝ} (hε0 : 0 < ε0) (T : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      (fun a : ℝ => (((d+2:ℕ):ℝ))*a) ⁻¹'
        Icc (data.center d-T) (data.center d+T) ⊆
      Icc (markE μ β x Q-ε0) (markE μ β x Q+ε0) := by
  have hc : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  let E0 := markE μ β x Q
  let σ : ℕ → ℝ := fun d => data.center d-((d+2:ℕ):ℝ)*E0
  have hσ := NatLogWindowScales.normalized_center_log_bounded hc
    data.log_constant_pos.le data.center data.logarithmic_correction
  have hσ0 := NatLogWindowScales.log_bounded_sequence_div_dimension_tendsto_zero
    (show 0 ≤ 1/(2*(β*x))+1 by positivity) σ hσ
  have hCenter : Tendsto (fun d : ℕ => data.center d/((d+2:ℕ):ℝ))
      atTop (𝓝 E0) := by
    have hConst : Tendsto (fun _ : ℕ => E0) atTop (𝓝 E0) := tendsto_const_nhds
    have ht := hConst.add hσ0
    convert ht using 1
    · ext d
      dsimp [σ]
      have hN : (((d+2:ℕ):ℝ)) ≠ 0 := by positivity
      field_simp
      ring
    · simp
  have hT : Tendsto (fun d : ℕ => T/((d+2:ℕ):ℝ))
      atTop (𝓝 (0:ℝ)) := by
    simpa only [Nat.cast_add,Nat.cast_ofNat] using constant_div_dimension_tendsto T
  have hLo : Tendsto (fun d : ℕ => (data.center d-T)/((d+2:ℕ):ℝ))
      atTop (𝓝 E0) := by
    convert hCenter.sub hT using 1
    · ext d
      ring
    · simp
  have hHi : Tendsto (fun d : ℕ => (data.center d+T)/((d+2:ℕ):ℝ))
      atTop (𝓝 E0) := by
    convert hCenter.add hT using 1
    · ext d
      ring
    · simp
  filter_upwards [hLo.eventually (lt_mem_nhds (by linarith : E0-ε0<E0)),
    hHi.eventually (gt_mem_nhds (by linarith : E0<E0+ε0))]
    with d hdLo hdHi
  intro a ha
  have hN : 0 < (((d+2:ℕ):ℝ)) := by positivity
  have haLo : data.center d-T ≤ a*((d+2:ℕ):ℝ) := by
    simpa only [mul_comm] using ha.1
  have haHi : a*((d+2:ℕ):ℝ) ≤ data.center d+T := by
    simpa only [mul_comm] using ha.2
  have hlo : (data.center d-T)/((d+2:ℕ):ℝ) ≤ a :=
    (div_le_iff₀ hN).mpr haLo
  have hhi : a ≤ (data.center d+T)/((d+2:ℕ):ℝ) :=
    (le_div_iff₀ hN).mpr haHi
  exact ⟨by dsimp [E0] at hdLo ⊢; linarith,
    by dsimp [E0] at hdHi ⊢; linarith⟩

/-- Printed Corollary 12.21(1), in its equivalent quantified sequential
form: for every target expected-count error, one fixed lightness threshold
works in all large dimensions. This is the actual original-disorder count
of critical points in the centered physical-energy window. -/
theorem mixed_sourceFewLightBands_centered_window
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    {M r L R b ε0 T : ℝ} (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1) (hb : 0 < b)
    (hBand : Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Icc (-r) r)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L)
    (hU : Icc L R ⊆ Icc (-M) M)
    (hε0 : 0 < ε0)
    (hEM : |markE μ β x Q|+ε0 ≤ M)
    (hT : 0 < T)
    (data : SourceMaximumFirstMomentConclusions μ β x Q L R) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ d : ℕ in atTop,
      (∫⁻ J, actualScoreWindowCount (d+1)
        (centerCoefficients (mixtureCoefficients μ) Q)
        (physicalEnergyWindow (d+2)
          (Icc (data.center d-T) (data.center d+T)) (Ioo L R))
        (sourceLightBandMark d μ h.overlap_range β (data.center d) δ
          (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))) J
          ∂disorderLaw (d+2) μ.maxDegree) ≤ ENNReal.ofReal ε := by
  obtain ⟨C,hC,hBound⟩ := data.uniform_window_bound (-T) T (by linarith)
  intro ε hε
  let η := ε/C
  have hη : 0 < η := div_pos hε hC
  obtain ⟨δ,hδ,hCount⟩ :=
    mixed_sourceLightBand_count_le_count_eventually μ h hnp
      hM hr0 hr1 hb hBand hEdge hU η hη
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hCount,
    centered_physical_window_eventually_in_normalized_interval μ h data hε0 T]
    with d hd hWindow
  let W : Set ℝ :=
    (fun a : ℝ => (((d+2:ℕ):ℝ))*a) ⁻¹'
      Icc (data.center d-T) (data.center d+T)
  have hW : MeasurableSet W :=
    measurableSet_Icc.preimage (measurable_const_mul (((d+2:ℕ):ℝ)))
  have hWM : W ⊆ Icc (-M) M := by
    intro a ha
    obtain ⟨hwlo,hwhi⟩ := hWindow ha
    constructor
    · linarith [neg_abs_le (markE μ β x Q)]
    · linarith [le_abs_self (markE μ β x Q)]
  have hCountD := hd W hW hWM (data.center d)
  let mass := sourceCriticalWindowMass d μ Q (Ioo L R)
    (data.center d-T) (data.center d+T)
  have hCountMass :
      (∫⁻ J, actualScoreWindowCount (d+1)
        (centerCoefficients (mixtureCoefficients μ) Q)
        (rectangularScoreWindow W (Ioo L R)) (fun _ _ => 1) J
        ∂disorderLaw (d+2) μ.maxDegree) = mass := by
    dsimp only [mass]
    rw [sourceCriticalWindowMass_def]
    rfl
  rw [hCountMass] at hCountD
  have hMassFinite : mass < ⊤ := by
    simpa only [mass, sub_eq_add_neg] using
      (data.window_mass_finite d (-T) T).2
  have hMassReal : mass.toReal ≤ C := by
    simpa only [mass,sourceCriticalWindowMean,sub_eq_add_neg] using
      (hBound d).2
  have hMassLe : mass ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal hMassFinite.ne]
    exact ENNReal.ofReal_le_ofReal hMassReal
  change (∫⁻ J, actualScoreWindowCount (d+1)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (rectangularScoreWindow W (Ioo L R))
      (sourceLightBandMark d μ h.overlap_range β (data.center d) δ
        (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))) J
      ∂disorderLaw (d+2) μ.maxDegree) ≤ ENNReal.ofReal ε
  calc
    _ ≤ ENNReal.ofReal η * mass := by simpa only [mass] using hCountD
    _ ≤ ENNReal.ofReal η * ENNReal.ofReal C := by
      simpa only [mul_comm] using
        (mul_le_mul_left hMassLe (ENNReal.ofReal η))
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul hη.le]
      congr 1
      dsimp [η]
      field_simp

end
end SlowEquilibration.SphericalTAPCriticalFewLightBands
