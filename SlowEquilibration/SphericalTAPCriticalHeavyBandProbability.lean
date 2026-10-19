-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairCanonicalGrowingWindow
public import SlowEquilibration.SphericalTAPCriticalFewLightBands
public import SlowEquilibration.SphericalTAPHeavyBandPartitionLower
public import SlowEquilibration.SphericalTAPCriticalSourceGeometry

/-! Source Corollary 12.21(2): one center in a fixed physical window and
few light centers force a lower bound on the original partition function. -/
@[expose] public section
namespace SlowEquilibration.SphericalTAPCriticalHeavyBandProbability
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows SphericalTAPCertificate
open SphericalTAPCriticalLightBandMark SphericalTAPCriticalFewLightBands
open SphericalTAPHeavyBandPartitionLower
open PairConditionalDeterminantMoments TwoAtomStationarity SphericalPairChartKacRice
open SphericalForm SphericalTAPCriticalBandSectionBridge LatitudeGroundTrial
open scoped ENNReal Topology ProbabilityTheory
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- Markov's inequality for the literal marked Kac--Rice count of light
ordinary critical points. -/
theorem source_light_critical_probability_le_marked_count
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : Q ∈ Ioo (0:ℝ) 1)
    (β l r L R m δ b : ℝ) :
    disorderLaw (n+3) μ.maxDegree
      {J | ∃ u ∈ sourceCriticalPhysicalWindowSet n μ Q l r (Ioo L R) J,
        sourceLightBandMark (n+1) μ hQ β m δ
          (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) J u = 1} ≤
    ∫⁻ J, actualScoreWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+3) (Icc l r) (Ioo L R))
      (sourceLightBandMark (n+1) μ hQ β m δ
        (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))) J
      ∂disorderLaw (n+3) μ.maxDegree := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let K := physicalEnergyWindow (n+3) (Icc l r) (Ioo L R)
  let mark := sourceLightBandMark (n+1) μ hQ β m δ
    (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))
  let count := actualScoreWindowCount (n+2) c K mark
  have hK : MeasurableSet K := rectangularScoreWindow_measurable _ _
    (measurableSet_Icc.preimage (measurable_const_mul ((n+3:ℕ):ℝ))) measurableSet_Ioo
  have hCount : AEMeasurable count (disorderLaw (n+3) μ.maxDegree) :=
    actualScoreWindowCount_aemeasurable (n+2) (by omega) μ hQ.1 K hK mark
      (sourceLightBandMark_measurable (n+1) μ hQ β m δ
        (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) measurableSet_Icc)
  have hsub : {J | ∃ u ∈ sourceCriticalPhysicalWindowSet n μ Q l r (Ioo L R) J,
      mark J u = 1} ⊆ {J | 1 ≤ count J} := by
    rintro J ⟨u,hu,hmark⟩
    have hwin : actualScore c J u ∈ K := by
      rw [actualScore_mem_physicalEnergyWindow (by omega) c J u (Icc l r) (Ioo L R)]
      exact ⟨hu.2.2.1,hu.2.2.2⟩
    have hterm := ENNReal.le_tsum (f := fun z : {z : Vector (n+3) |
      ‖z‖^2=(n+3:ℕ) ∧ surfaceGradient (field c J) z=0 ∧
        actualScore c J z ∈ K} => mark J z) ⟨u,hu.1,hu.2.1,hwin⟩
    change 1 ≤ count J
    rw [←hmark]
    exact hterm
  apply (measure_mono hsub).trans
  simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hCount 1

/-- A center in the physical window whose band is not light forces the
printed lower bound with the exact manuscript band scale. -/
theorem source_nonlight_critical_forces_partition_lower
    (n : ℕ) (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (J : Disorder (n+3) μ.maxDegree)
    (u : Vector (n+3)) (m T L R δ b : ℝ)
    (hδ : 0 ≤ δ)
    (hu : u ∈ sourceCriticalPhysicalWindowSet n μ Q (m-T) (m+T) (Ioo L R) J)
    (hheavy : sourceLightBandMark (n+1) μ h.overlap_range β m δ
      (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) J u = 0) :
    δ*Real.exp (-β*T)*sourceCriticalBandScale (n+2) μ h.overlap_range β m ≤
      partition (n+3) β (field (mixtureCoefficients μ) J) := by
  let I := Icc (Real.sqrt Q-b) (Real.sqrt Q+b)
  let D := sourceCriticalBandScale (n+2) μ h.overlap_range β m
  have hD : 0 ≤ D := (sourceCriticalBandScale_pos (n+2) (by omega)
    μ h.overlap_range β m).le
  have henergy : m-T ≤ field
      (centerCoefficients (mixtureCoefficients μ) Q) J u := hu.2.2.1.1
  have hnot : ¬ overlapRestrictedPartition (mixtureCoefficients μ) β I (J,u) <
      δ*D*Real.exp (β*(field
        (centerCoefficients (mixtureCoefficients μ) Q) J u-m)) := by
    unfold sourceLightBandMark at hheavy
    split_ifs at hheavy with hlt
    · simp at hheavy
    · exact hlt
  have hBand : δ*D*Real.exp (β*(field
      (centerCoefficients (mixtureCoefficients μ) Q) J u-m)) ≤
      partitionOn β (field (mixtureCoefficients μ) J) (overlapRegion u I) := by
    simpa only [overlapRestrictedPartition,overlapRegion] using le_of_not_gt hnot
  exact source_heavy_band_implies_partition_lower (by omega) μ Q J u I
    measurableSet_Icc h.beta_pos.le hδ hD henergy hBand

/-- Source 12.21(2)'s probability step: the low-partition event is covered
by a zero retained count or at least one light ordinary critical band. -/
theorem source_partition_low_limsup_of_zero_and_light_bounds
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (m : ℕ → ℝ) (L R κ C ε η E G T δ ρ a b : ℝ)
    (hδ : 0 ≤ δ) (hρ : 0 ≤ ρ)
    (hZero : Filter.limsup (fun n : ℕ =>
      (disorderLaw (n+3) μ.maxDegree).real
        {J | (sourceRetainedScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+3)
            (Icc (m (n+1)-T) (m (n+1)+T)) (Ioo L R))
          κ C ε η E G J).toReal = 0}) atTop ≤ a)
    (hLight : ∀ᶠ n : ℕ in atTop,
      (∫⁻ J, actualScoreWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q)
        (physicalEnergyWindow (n+3)
          (Icc (m (n+1)-T) (m (n+1)+T)) (Ioo L R))
        (sourceLightBandMark (n+1) μ h.overlap_range β (m (n+1)) δ
          (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))) J
          ∂disorderLaw (n+3) μ.maxDegree) ≤ ENNReal.ofReal ρ) :
    Filter.limsup (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
      {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
        δ*Real.exp (-β*T)*
          sourceCriticalBandScale (n+2) μ h.overlap_range β (m (n+1))}) atTop ≤ a+ρ := by
  let zero (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | (sourceRetainedScoreWindowCount (n+2)
      (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+3)
        (Icc (m (n+1)-T) (m (n+1)+T)) (Ioo L R))
      κ C ε η E G J).toReal = 0}
  let light (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | ∃ u ∈ sourceCriticalPhysicalWindowSet n μ Q
      (m (n+1)-T) (m (n+1)+T) (Ioo L R) J,
      sourceLightBandMark (n+1) μ h.overlap_range β (m (n+1)) δ
        (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) J u = 1}
  let low (n : ℕ) := (disorderLaw (n+3) μ.maxDegree).real
    {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
      δ*Real.exp (-β*T)*
        sourceCriticalBandScale (n+2) μ h.overlap_range β (m (n+1))}
  have hpoint : ∀ n, low n ≤ zero n+light n := by
    intro n
    have hsub : {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
        δ*Real.exp (-β*T)*
          sourceCriticalBandScale (n+2) μ h.overlap_range β (m (n+1))} ⊆
        {J | (sourceRetainedScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+3)
            (Icc (m (n+1)-T) (m (n+1)+T)) (Ioo L R))
          κ C ε η E G J).toReal = 0} ∪
        {J | ∃ u ∈ sourceCriticalPhysicalWindowSet n μ Q
          (m (n+1)-T) (m (n+1)+T) (Ioo L R) J,
          sourceLightBandMark (n+1) μ h.overlap_range β (m (n+1)) δ
            (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) J u = 1} := by
      intro J hlow
      by_cases hz : (sourceRetainedScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+3)
            (Icc (m (n+1)-T) (m (n+1)+T)) (Ioo L R))
          κ C ε η E G J).toReal = 0
      · exact Or.inl hz
      · right
        obtain ⟨u,hu⟩ := source_retained_nonzero_critical_window_nonempty
          n μ Q (m (n+1)-T) (m (n+1)+T) κ C ε η E G
          (Ioo L R) J hz
        refine ⟨u,hu,?_⟩
        by_cases hlight : sourceLightBandMark (n+1) μ h.overlap_range β
            (m (n+1)) δ (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) J u = 1
        · exact hlight
        · have hheavy : sourceLightBandMark (n+1) μ h.overlap_range β
              (m (n+1)) δ (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) J u = 0 := by
            unfold sourceLightBandMark at hlight ⊢
            split_ifs at hlight ⊢ <;> simp_all
          have hpartition := source_nonlight_critical_forces_partition_lower
            n μ h J u (m (n+1)) T L R δ b hδ hu hheavy
          exact False.elim ((not_lt.mpr hpartition) hlow)
    calc
      low n ≤ (disorderLaw (n+3) μ.maxDegree).real
        ({J | (sourceRetainedScoreWindowCount (n+2)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+3)
            (Icc (m (n+1)-T) (m (n+1)+T)) (Ioo L R))
          κ C ε η E G J).toReal = 0} ∪
        {J | ∃ u ∈ sourceCriticalPhysicalWindowSet n μ Q
          (m (n+1)-T) (m (n+1)+T) (Ioo L R) J,
          sourceLightBandMark (n+1) μ h.overlap_range β (m (n+1)) δ
            (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) J u = 1}) := by
              exact measureReal_mono hsub (by finiteness)
      _ ≤ zero n+light n := measureReal_union_le _ _
  have hlightEventually : ∀ᶠ n : ℕ in atTop, light n ≤ ρ := by
    filter_upwards [hLight] with n hn
    have hMark := source_light_critical_probability_le_marked_count
      n μ h.overlap_range β (m (n+1)-T) (m (n+1)+T)
      L R (m (n+1)) δ b
    have hEvent := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hMark.trans hn)
    simpa only [light,measureReal_def,ENNReal.toReal_ofReal hρ] using hEvent
  have hEventual : ∀ᶠ n : ℕ in atTop, low n ≤ zero n+ρ := by
    filter_upwards [hlightEventually] with n hn
    exact (hpoint n).trans (add_le_add (le_refl _) hn)
  have hLowCob : IsCoboundedUnder (· ≤ ·) atTop low :=
    isCoboundedUnder_le_of_le atTop (fun n => measureReal_nonneg)
  have hSumB : IsBoundedUnder (· ≤ ·) atTop (fun n => zero n+ρ) :=
    isBoundedUnder_of ⟨1+ρ,fun n => by
      have hz : zero n ≤ 1 := measureReal_le_one
      linarith⟩
  have hLim : Filter.limsup low atTop ≤
      Filter.limsup (fun n => zero n+ρ) atTop :=
    limsup_le_limsup hEventual hLowCob hSumB
  have hzL : IsBoundedUnder (· ≥ ·) atTop zero :=
    isBoundedUnder_of ⟨0,fun n => measureReal_nonneg⟩
  have hzB : IsBoundedUnder (· ≤ ·) atTop zero :=
    isBoundedUnder_of ⟨1,fun n => measureReal_le_one⟩
  have hcL : IsCoboundedUnder (· ≤ ·) atTop (fun _n : ℕ => ρ) :=
    isCoboundedUnder_le_of_le atTop (fun _n => hρ)
  have hcB : IsBoundedUnder (· ≤ ·) atTop (fun _n : ℕ => ρ) :=
    isBoundedUnder_of ⟨ρ,fun _n => le_refl ρ⟩
  have hAdd := limsup_add_le hzL hzB hcL hcB
  simp only [limsup_const] at hAdd
  have hResult := hLim.trans (hAdd.trans (add_le_add hZero (le_refl ρ)))
  simpa only [low,zero,limsup_const] using hResult

/-- Source 12.21(2) from a single fixed-window retained-count zero bound
and the fully formalized Palm estimate for light critical bands. -/
theorem source_mixed_heavy_band_partition_low_probability
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (C cut η ε L R : ℝ)
    (d : SourceMaximumFirstMomentConclusions μ β x Q L R)
    (hZero : ∀ T : ℝ, 0 < T →
      Filter.limsup (fun n : ℕ =>
        (disorderLaw (n+3) μ.maxDegree).real
          {J | (sourceRetainedScoreWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q)
            (physicalEnergyWindow (n+3)
              (Icc (d.center (n+1)-T) (d.center (n+1)+T)) (Ioo L R))
            ((markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/4)
            C ε η (markE μ β x Q)
            (gap μ Q (markY β Q) (markZ x Q) ε η) J).toReal = 0}) atTop ≤
        (1+(1-ε)/(cut^2-ε)) /
          (Real.exp ((β*x)*T)-Real.exp (-(β*x)*T)))
    (M r b ε0 : ℝ) (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hb : 0 < b)
    (hBand : Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Icc (-r) r)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L)
    (hU : Icc L R ⊆ Icc (-M) M)
    (hε0 : 0 < ε0) (hEM : |markE μ β x Q|+ε0 ≤ M) :
    ∀ ρ : ℝ, 0 < ρ →
      ∃ T δ : ℝ, 0 < T ∧ 0 < δ ∧
        Filter.limsup (fun n : ℕ =>
          (disorderLaw (n+3) μ.maxDegree).real
            {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
              δ*Real.exp (-β*T)*
                sourceCriticalBandScale (n+2) μ h.overlap_range β
                  (d.center (n+1))}) atTop ≤ 2*ρ := by
  intro ρ hρ
  let k := 1+(1-ε)/(cut^2-ε)
  have hc0 : 0 < β*x := mul_pos h.beta_pos h.weight_range.1
  have hPos : Tendsto (fun T : ℝ => Real.exp ((β*x)*T)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hc0)
  have hNeg : Tendsto (fun T : ℝ => Real.exp (-(β*x)*T)) atTop (𝓝 (0:ℝ)) :=
    Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc0))
  have hDen : Tendsto (fun T : ℝ =>
      Real.exp ((β*x)*T)-Real.exp (-(β*x)*T)) atTop atTop := by
    simpa only [sub_eq_add_neg] using hPos.atTop_add hNeg.neg
  have hFrac : Tendsto (fun T : ℝ =>
      k/(Real.exp ((β*x)*T)-Real.exp (-(β*x)*T))) atTop (𝓝 (0:ℝ)) :=
    hDen.const_div_atTop k
  have hSmall : ∀ᶠ T : ℝ in atTop,
      0 < T ∧ k/(Real.exp ((β*x)*T)-Real.exp (-(β*x)*T)) < ρ := by
    filter_upwards [eventually_gt_atTop (0:ℝ),
      hFrac.eventually (gt_mem_nhds hρ)] with T ht hs
    exact ⟨ht,hs⟩
  obtain ⟨T,hT,hRatio⟩ := hSmall.exists
  obtain ⟨δ,hδ,hLight⟩ :=
    mixed_sourceFewLightBands_centered_window μ h hnp
      hM hr0 hr1 hb hBand hEdge hU hε0 hEM hT d ρ hρ
  have hLight' : ∀ᶠ n : ℕ in atTop,
      (∫⁻ J, actualScoreWindowCount (n+2)
        (centerCoefficients (mixtureCoefficients μ) Q)
        (physicalEnergyWindow (n+3)
          (Icc (d.center (n+1)-T) (d.center (n+1)+T)) (Ioo L R))
        (sourceLightBandMark (n+1) μ h.overlap_range β (d.center (n+1)) δ
          (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))) J
          ∂disorderLaw (n+3) μ.maxDegree) ≤ ENNReal.ofReal ρ := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (tendsto_add_atTop_nat 1).eventually hLight
  have hBound := source_partition_low_limsup_of_zero_and_light_bounds
    μ h d.center L R
      ((markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/4)
      C ε η (markE μ β x Q)
      (gap μ Q (markY β Q) (markZ x Q) ε η)
      T δ ρ (k/(Real.exp ((β*x)*T)-Real.exp (-(β*x)*T))) b
      hδ.le hρ.le (hZero T hT) hLight'
  refine ⟨T,δ,hT,hδ,?_⟩
  have hSmallBound :
      k/(Real.exp ((β*x)*T)-Real.exp (-(β*x)*T))+ρ ≤ 2*ρ := by
    linarith
  exact hBound.trans hSmallBound

/-- Full mixed-model source 12.21(2), with the radial interval, band width,
critical-point center, and lightness threshold chosen from the certificate.
For each fixed target error and band width, the original-disorder lower
tail of the actual partition function has the printed `2ρ` bound. -/
theorem source_mixed_heavy_band_partition_low_probability_unconditional
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hd : 4 ≤ μ.minDegree) :
    ∃ L R b0 : ℝ,
      sourceRadialEdge μ Q < L ∧ L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b0 ∧ b0 < Real.sqrt Q ∧
      ∃ d : SourceMaximumFirstMomentConclusions μ β x Q L R,
        ∀ b : ℝ, 0 < b → b ≤ b0 →
          ∀ ρ : ℝ, 0 < ρ →
            ∃ T δ : ℝ, 0 < T ∧ 0 < δ ∧
              Filter.limsup (fun n : ℕ =>
                (disorderLaw (n+3) μ.maxDegree).real
                  {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
                    δ*Real.exp (-β*T)*
                      sourceCriticalBandScale (n+2) μ h.overlap_range β
                        (d.center (n+1))}) atTop ≤ 2*ρ := by
  obtain ⟨C,cut,η,ε,L,R,hC,hcut,hcutOne,hcutRad,hη,hηCollar,
    hε,hεCut,hεη,hL,hR,hEdge,d,hMoments,hProb,hMax,hCard,hGround⟩ :=
    source_mixed_actual_canonical_single_witness_with_maximum_tightness
      μ h hnp hd (by norm_num : (0:ℝ) < 1)
  obtain ⟨_M0,r,_L0,_R0,ε0,b0,_hM0,hr0,hr1,hε0,hb0,hb0Q,
    _hEdge0,_hLK0,_hKR0,_hU0,_hE0,hband⟩ :=
    SphericalTAPCriticalSourceGeometry.mixed_fixedBand_source_geometry μ h
  let M := max |markE μ β x Q| (max |L| |R|)+ε0+1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hEM : |markE μ β x Q|+ε0 ≤ M := by
    dsimp [M]
    linarith [le_max_left |markE μ β x Q| (max |L| |R|)]
  have hU : Icc L R ⊆ Icc (-M) M := by
    intro y hy
    have hLAbs : -|L| ≤ L := neg_abs_le L
    have hRAbs : R ≤ |R| := le_abs_self R
    have hLMax : |L| ≤ max |L| |R| := le_max_left _ _
    have hRMax : |R| ≤ max |L| |R| := le_max_right _ _
    have hTop : max |L| |R| ≤ max |markE μ β x Q| (max |L| |R|) :=
      le_max_right _ _
    dsimp [M]
    constructor <;> linarith [hy.1,hy.2]
  obtain ⟨D,_hD,hWin⟩ := hProb (α := (3:ℝ)/8) (by norm_num) (by norm_num)
  have hZero : ∀ T : ℝ, 0 < T →
      Filter.limsup (fun n : ℕ =>
        (disorderLaw (n+3) μ.maxDegree).real
          {J | (sourceRetainedScoreWindowCount (n+2)
            (centerCoefficients (mixtureCoefficients μ) Q)
            (physicalEnergyWindow (n+3)
              (Icc (d.center (n+1)-T) (d.center (n+1)+T)) (Ioo L R))
            ((markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/4)
            C ε η (markE μ β x Q)
            (gap μ Q (markY β Q) (markZ x Q) ε η) J).toReal = 0}) atTop ≤
        (1+(1-ε)/(cut^2-ε)) /
          (Real.exp ((β*x)*T)-Real.exp (-(β*x)*T)) := by
    intro T hT
    have hκ : (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/2/2 =
        (markK μ β Q-2*Real.sqrt (Q^2*μ.xi2 Q))/4 := by ring
    simpa only [hκ] using (hWin T hT).1
  refine ⟨L,R,b0,hEdge,hL,hR,hb0,hb0Q,d,?_⟩
  intro b hb hbb ρ hρ
  exact source_mixed_heavy_band_partition_low_probability μ h hnp
    C cut η ε L R d hZero M r b ε0 hM hr0 hr1 hb
    (hband b hb hbb) (by simpa only [sourceRadialEdge] using hEdge)
    hU hε0 hEM ρ hρ

end
end SlowEquilibration.SphericalTAPCriticalHeavyBandProbability
