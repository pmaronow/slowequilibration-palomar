-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixedHighEnergyBadHessianCount
public import SlowEquilibration.SphericalMaximumGlobalTail
public import SlowEquilibration.SourcePhysicalPairSphereActualJetBounds

/-! The simultaneous all-high event in manuscript `prop:mo-all-high`, for
each prescribed exterior radial interval containing the mixed contact mark.
The original-disorder event combines radial exclusion, the determinant-weighted
bad-Hessian count, an above-contact maximum cutoff, and unconditional tensor
regularity. It controls every high critical point of the center field and its
third derivative on the entire physical sphere. The above-contact count also
gives the separate vanishing upper tail of the center-field maximum. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.MixedHighEnergyAllHigh

open Set Filter MeasureTheory SphericalModel SphericalMarkedWindows SphericalForm
open SphericalGaussianJet SphericalTAPCertificate TwoAtomStationarity
open PairConditionalDeterminantMoments SphericalHessianMarginEvents
open MixedHighEnergyBadHessianCount
open scoped ENNReal Topology

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A maximizer above contact is itself counted in the unrestricted
above-contact critical count. -/
private theorem maximum_upper_tail_exponential
    (μ : FiniteMixture) {β x Q ε : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      (disorderLaw (n+2) μ.maxDegree).real
        {J | (n+2 : ℕ)*(markE μ β x Q+ε) ≤ sourceSphereMaximum n μ Q J} ≤
          Real.exp (-c*(n+2 : ℕ)) := by
  obtain ⟨c, hc, hMean⟩ := sourceAboveContactCountMass_exponential μ h hnp hε
  refine ⟨c, hc, ?_⟩
  filter_upwards [hMean] with n hn
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let K := rectangularScoreWindow (Ici (markE μ β x Q+ε)) univ
  let B := actualScoreWindowCount (n+1) cQ K (fun _ _ => 1)
  have hB : AEMeasurable B (disorderLaw (n+2) μ.maxDegree) :=
    actualScoreWindowCount_aemeasurable (n+1) (by omega) μ h.overlap_range.1 K
      (rectangularScoreWindow_measurable _ _ measurableSet_Ici MeasurableSet.univ)
      _ measurable_const
  have hSub : {J | (n+2 : ℕ)*(markE μ β x Q+ε) ≤ sourceSphereMaximum n μ Q J} ⊆
      {J | 1 ≤ B J} := by
    intro J hJ
    change (n+2 : ℕ)*(markE μ β x Q+ε) ≤ sourceSphereMaximum n μ Q J at hJ
    obtain ⟨u, hu, hCrit, _, hValue⟩ := sourceSphereMaximum_attained n μ Q J
    have hWindow : actualScore cQ J u ∈ K := by
      refine ⟨?_, mem_univ _⟩
      rw [actualScore_value_eq]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (n+2 : ℕ))).mpr
      rw [hValue] at hJ
      simpa only [mul_comm] using hJ
    exact ENNReal.le_tsum
      (f := fun _z : {z : Vector (n+2) | ‖z‖^2 = (n+2 : ℕ) ∧
        surfaceGradient (field cQ J) z = 0 ∧ actualScore cQ J z ∈ K} => (1 : ℝ≥0∞))
      ⟨u, hu, hCrit, hWindow⟩
  have hMass : disorderLaw (n+2) μ.maxDegree
      {J | (n+2 : ℕ)*(markE μ β x Q+ε) ≤ sourceSphereMaximum n μ Q J} ≤
        ENNReal.ofReal (Real.exp (-c*(n+2 : ℕ))) := by
    apply (measure_mono hSub).trans
    calc
      _ ≤ ∫⁻ J, B J ∂disorderLaw (n+2) μ.maxDegree := by
        simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hB 1
      _ ≤ _ := by
        simpa only [sourceMarkedOriginalCountMass_def] using hn
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hMass).trans_eq
    (ENNReal.toReal_ofReal (Real.exp_pos _).le)

/-- Unconditional tensor regularity controls the mixed center field;
no substitution of the original disorder law is required. -/
private theorem original_center_spherical_third_bound (μ : FiniteMixture) (Q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∀ J : Disorder (n+2) μ.maxDegree, J ∈ regularDisorder →
        ∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
          ‖sourceSphereThirdExtension (centerCoefficients (mixtureCoefficients μ) Q) J u‖ ≤
            C / Real.sqrt (n+2 : ℕ) := by
  let K := ∑ q : Degree μ.maxDegree, blockThreshold q
  have hK : 0 ≤ K := Finset.sum_nonneg (fun q _ => (blockThreshold_pos q).le)
  refine ⟨9 * sourcePosteriorDerivativeConstant
    (centerCoefficients (mixtureCoefficients μ) Q) K,
    mul_pos (by norm_num) (sourcePosteriorDerivativeConstant_pos _ hK), ?_⟩
  intro n J hJ u hu
  have hOrdered : J ∈ sourcePosteriorOrderedRegularity K := by
    intro q
    have hq : blockThreshold q ≤ K :=
      Finset.single_le_sum (fun r _ => (blockThreshold_pos r).le) (Finset.mem_univ q)
    have hq0 : 0 ≤ (q.val.val : ℝ) := Nat.cast_nonneg _
    exact (hJ q).trans (by linarith)
  exact (source_ordered_sphere_jet_bounds (by omega)
    (centerCoefficients (mixtureCoefficients μ) Q) hK J hOrdered u hu).2.2

/-- Manuscript `prop:mo-all-high`: on one measurable event with
exponentially small complement, every sufficiently high critical point has
its radial mark in the prescribed interval and a fixed positive Hessian
margin. The third derivative is uniformly bounded on the whole sphere. -/
theorem mixed_all_high_critical_event
    (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hEdge : 2 * Real.sqrt (Q^2 * μ.xi2 Q) < L)
    (hL : L < markK μ β Q) (hR : markK μ β Q < R) :
    ∃ δ κ C c : ℝ, 0 < δ ∧ 0 < κ ∧ 0 < C ∧ 0 < c ∧
      ∃ Ω : ∀ n : ℕ, Set (Disorder (n+2) μ.maxDegree),
        (∀ n, MeasurableSet (Ω n)) ∧
        (∀ n, ∀ J ∈ Ω n,
          (∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
            surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u = 0 →
            (n+2 : ℕ)*(markE μ β x Q-δ) ≤
              field (centerCoefficients (mixtureCoefficients μ) Q) J u →
            actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R ∧
              sourceHessianMargin (centerCoefficients (mixtureCoefficients μ) Q) κ J u) ∧
          (∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
            ‖sourceSphereThirdExtension (centerCoefficients (mixtureCoefficients μ) Q) J u‖ ≤
              C / Real.sqrt (n+2 : ℕ)) ∧
          sSup ((fun u : Vector (n+2) =>
            ‖sourceSphereThirdExtension (centerCoefficients (mixtureCoefficients μ) Q) J u‖) ''
              {u | ‖u‖^2 = (n+2 : ℕ)}) ≤ C / Real.sqrt (n+2 : ℕ)) ∧
        (∀ᶠ n : ℕ in atTop,
          (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤
            C * Real.exp (-c*(n+2 : ℕ))) := by
  classical
  obtain ⟨t, κ, b, B, ht, hκ, hb, hB, hMean⟩ :=
    mixed_high_window_bad_margin_mean μ h hnp hEdge hL hR
  have hm : markK μ β Q ∈ Ioo L R := ⟨hL, hR⟩
  have hCurv := sourceMarkedLeastCurvature_pos μ h.overlap_range.1
    (by have hd := h.min_degree; omega) hnp
  have hClear := sourceRadialClearance_pos μ hm
  let d := sourceMarkedLeastCurvature μ Q *
    (sourceRadialClearance μ β Q (Ioo L R))^2 / (8*(β*x))
  have hd : 0 < d := by dsimp [d]; positivity [h.beta_pos, h.weight_range.1]
  let δ := min t d
  have hδ : 0 < δ := lt_min ht hd
  have hδt : δ ≤ t := min_le_left _ _
  have hA3 : δ ≤ d := min_le_right _ _
  obtain ⟨a, ha, hRadial⟩ := sourceHighCriticalGoodSet_exponential μ h hnp hm hA3
  obtain ⟨e, he, hMaximum⟩ := maximum_upper_tail_exponential μ h hnp hδ
  obtain ⟨T, hT, hThird⟩ := original_center_spherical_third_bound μ Q
  let cQ := centerCoefficients (mixtureCoefficients μ) Q
  let W := rectangularScoreWindow
    (Icc (markE μ β x Q-t) (markE μ β x Q+t)) (Ioo L R)
  let badCount (n : ℕ) := actualScoreWindowCount (n+1) cQ W
    (hessianMarginFailureMark cQ κ)
  let bad (n : ℕ) := toMeasurable (disorderLaw (n+2) μ.maxDegree)
    {J | 1 ≤ badCount n J}
  let radial (n : ℕ) := sourceHighCriticalGoodSet n μ Q (markE μ β x Q-δ) (Ioo L R)
  let cutoff (n : ℕ) : Set (Disorder (n+2) μ.maxDegree) :=
    {J | sourceSphereMaximum n μ Q J ≤ (n+2 : ℕ)*(markE μ β x Q+δ)}
  let Ω (n : ℕ) : Set (Disorder (n+2) μ.maxDegree) :=
    ((regularDisorder ∩ radial n) ∩ (bad n)ᶜ) ∩ cutoff n
  let c := min 1 (min a (min b e))
  have hc : 0 < c := lt_min (by norm_num) (lt_min ha (lt_min hb he))
  have hc1 : c ≤ 1 := min_le_left _ _
  have hca : c ≤ a := (min_le_right _ _).trans (min_le_left _ _)
  have hcb : c ≤ b := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hce : c ≤ e := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  let C := T+B+3
  have hC : 0 < C := by dsimp [C]; positivity
  have hTC : T ≤ C := by dsimp [C]; linarith
  have hCutoffMeas (n : ℕ) : MeasurableSet (cutoff n) :=
    (isClosed_le (sourceSphereMaximum_continuous n μ Q) continuous_const).measurableSet
  refine ⟨δ, κ, C, c, hδ, hκ, hC, hc, Ω, ?_, ?_, ?_⟩
  · intro n
    exact (((regularDisorder_measurable _ _).inter
      (sourceHighCriticalGoodSet_measurable n μ Q _ _)).inter
      (measurableSet_toMeasurable _ _).compl).inter (hCutoffMeas n)
  · intro n J hJ
    obtain ⟨⟨⟨hReg, hRad⟩, hNotBad⟩, hCut⟩ := hJ
    have hUniform : ∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
        ‖sourceSphereThirdExtension cQ J u‖ ≤ C / Real.sqrt (n+2 : ℕ) := by
      intro u hu
      exact (hThird n J hReg u hu).trans
        (div_le_div_of_nonneg_right hTC (Real.sqrt_nonneg _))
    refine ⟨?_, hUniform, ?_⟩
    · intro u hu hCrit hHigh
      have hNr : (0 : ℝ) < (n+2 : ℕ) := by positivity
      have hLow : markE μ β x Q-δ ≤ actualScore cQ J u 0 := by
        rw [actualScore_value_eq]
        exact (le_div_iff₀ hNr).mpr (by simpa only [mul_comm] using hHigh)
      have hRadialMark := sourceHighCriticalGoodSet_radial n μ Q _ _ hRad hu hCrit hLow
      refine ⟨hRadialMark, ?_⟩
      by_contra hBadMargin
      apply hNotBad
      apply subset_toMeasurable _ _
      have hUpper : field cQ J u ≤ (n+2 : ℕ)*(markE μ β x Q+δ) := by
        obtain ⟨v, _, _, hMax, hValue⟩ := sourceSphereMaximum_attained n μ Q J
        exact (show field cQ J u ≤ sourceSphereMaximum n μ Q J by
          rw [hValue]; exact hMax hu).trans hCut
      have hWindow : actualScore cQ J u ∈ W := by
        refine ⟨⟨?_, ?_⟩, hRadialMark⟩
        · exact (by linarith : markE μ β x Q-t ≤ markE μ β x Q-δ).trans hLow
        · rw [actualScore_value_eq]
          apply le_trans (b := markE μ β x Q+δ)
          · exact (div_le_iff₀ hNr).mpr (by simpa only [mul_comm] using hUpper)
          · linarith
      have hOne := ENNReal.le_tsum
        (f := fun z : {z : Vector (n+2) | ‖z‖^2 = (n+2 : ℕ) ∧
          surfaceGradient (field cQ J) z = 0 ∧ actualScore cQ J z ∈ W} =>
            hessianMarginFailureMark cQ κ J z) ⟨u, hu, hCrit, hWindow⟩
      have hBadMargin' : ¬ sourceHessianMargin cQ κ J u := hBadMargin
      simpa only [hessianMarginFailureMark, ite_eq_right hBadMargin',
        badCount, actualScoreWindowCount, mem_ofPred_eq] using hOne
    · obtain ⟨u, hu, _, _, _⟩ := sourceSphereMaximum_attained n μ Q J
      refine csSup_le ⟨_, u, hu, rfl⟩ ?_
      rintro _ ⟨v, hv, rfl⟩
      exact hUniform v hv
  · filter_upwards [hMean, hRadial, hMaximum] with n hn hRad hMax
    have hCountAE : AEMeasurable (badCount n) (disorderLaw (n+2) μ.maxDegree) :=
      actualScoreWindowCount_aemeasurable (n+1) (by omega) μ h.overlap_range.1 W
        (rectangularScoreWindow_measurable _ _ measurableSet_Icc measurableSet_Ioo)
        _ (hessianMarginFailureMark_measurable cQ κ)
    have hBadMass : disorderLaw (n+2) μ.maxDegree (bad n) ≤
        ENNReal.ofReal (B * Real.exp (-b*(n+2 : ℕ))) := by
      rw [show bad n = toMeasurable (disorderLaw (n+2) μ.maxDegree)
        {J | 1 ≤ badCount n J} from rfl, measure_toMeasurable]
      calc
        _ ≤ ∫⁻ J, badCount n J ∂disorderLaw (n+2) μ.maxDegree := by
          simpa only [one_mul] using mul_meas_ge_le_lintegral₀ hCountAE 1
        _ ≤ _ := hn
    have hBadReal : (disorderLaw (n+2) μ.maxDegree).real (bad n) ≤
        B * Real.exp (-b*(n+2 : ℕ)) :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hBadMass).trans_eq
        (ENNReal.toReal_ofReal (by positivity))
    have hRadReal : (disorderLaw (n+2) μ.maxDegree).real (radial n)ᶜ ≤
        Real.exp (-a*(n+2 : ℕ)) :=
      (ENNReal.toReal_mono ENNReal.ofReal_ne_top hRad).trans_eq
        (ENNReal.toReal_ofReal (Real.exp_pos _).le)
    have hCutReal : (disorderLaw (n+2) μ.maxDegree).real (cutoff n)ᶜ ≤
        Real.exp (-e*(n+2 : ℕ)) := by
      apply (measureReal_mono (show (cutoff n)ᶜ ⊆
        {J | (n+2 : ℕ)*(markE μ β x Q+δ) ≤ sourceSphereMaximum n μ Q J} by
          intro J hJ
          change ¬ sourceSphereMaximum n μ Q J ≤
            (n+2 : ℕ)*(markE μ β x Q+δ) at hJ
          exact (lt_of_not_ge hJ).le) (measure_ne_top _ _)).trans hMax
    have hProb : (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤
        Real.exp (-(n+2 : ℕ)) + Real.exp (-a*(n+2 : ℕ)) +
          B * Real.exp (-b*(n+2 : ℕ)) + Real.exp (-e*(n+2 : ℕ)) := by
      have hSub : (Ω n)ᶜ ⊆ ((regularDisorderᶜ ∪ (radial n)ᶜ) ∪ bad n) ∪ (cutoff n)ᶜ := by
        simp only [Ω, compl_inter, compl_compl]
        exact Subset.rfl
      exact (measureReal_mono hSub (measure_ne_top _ _)).trans
        ((measureReal_union_le _ _).trans (add_le_add
          ((measureReal_union_le _ _).trans (add_le_add
            ((measureReal_union_le _ _).trans (add_le_add
              (regularDisorder_failure_probability (by omega)) hRadReal)) hBadReal)) hCutReal))
    have hRate {s : ℝ} (hcs : c ≤ s) :
        Real.exp (-s*(n+2 : ℕ)) ≤ Real.exp (-c*(n+2 : ℕ)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right hcs (show (0 : ℝ) ≤ (n+2 : ℕ) by positivity)]
    apply hProb.trans
    calc
      _ ≤ Real.exp (-c*(n+2 : ℕ)) + Real.exp (-c*(n+2 : ℕ)) +
          B * Real.exp (-c*(n+2 : ℕ)) + Real.exp (-c*(n+2 : ℕ)) :=
        add_le_add (add_le_add (add_le_add (by simpa using hRate hc1) (hRate hca))
          (mul_le_mul_of_nonneg_left (hRate hcb) hB.le)) (hRate hce)
      _ = (B+3) * Real.exp (-c*(n+2 : ℕ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by dsimp [C]; linarith) (Real.exp_pos _).le

/-- The center-field maximum exceeds any fixed normalized energy above
the source contact with probability tending to zero. -/
theorem mixed_center_maximum_above_contact_tendsto_zero
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ =>
      (disorderLaw (n+2) μ.maxDegree).real
        {J | (n+2 : ℕ)*(markE μ β x Q+ε) < sourceSphereMaximum n μ Q J})
      atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨c, hc, hBound⟩ := maximum_upper_tail_exponential μ h hnp hε
  have hExp : Tendsto (fun n : ℕ => Real.exp (-c*(n+2 : ℕ))) atTop (𝓝 (0 : ℝ)) :=
    Real.tendsto_exp_atBot.comp
      ((tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)).const_mul_atTop_of_neg
        (neg_neg_of_pos hc))
  apply squeeze_zero' (.of_forall (fun _ => measureReal_nonneg)) _ hExp
  filter_upwards [hBound] with n hn
  have hSub :
    {J | (n+2 : ℕ)*(markE μ β x Q+ε) < sourceSphereMaximum n μ Q J} ⊆
      {J | (n+2 : ℕ)*(markE μ β x Q+ε) ≤ sourceSphereMaximum n μ Q J} := by
    intro J hJ
    change (n+2 : ℕ)*(markE μ β x Q+ε) < sourceSphereMaximum n μ Q J at hJ
    change (n+2 : ℕ)*(markE μ β x Q+ε) ≤ sourceSphereMaximum n μ Q J
    exact hJ.le
  exact (measureReal_mono hSub (measure_ne_top _ _)).trans hn

end SlowEquilibration.MixedHighEnergyAllHigh
