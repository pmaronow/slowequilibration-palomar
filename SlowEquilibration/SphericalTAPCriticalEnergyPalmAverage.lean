-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPurePalmBandLower
public import SlowEquilibration.SphericalOnePointRadialCurvature
public import SlowEquilibration.SphericalCountRectangles
public import SlowEquilibration.GOECrudeDeterminant
public import SlowEquilibration.NormalizedRadialMeasure

@[expose] public section

/-! The radial mixing measure in the energy-conditioned Palm law uses the
absolute Hessian determinant of every critical point. It is distinct from
the local-maximum radial weight used in center-count asymptotics. -/

namespace SlowEquilibration.SphericalTAPCriticalEnergyPalmAverage
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalGaussianJet SphericalMarkedWindows
open SphericalSequentialRegression GOEPhysicalPotential
open GOEPhysicalNormalizedMoments
open ConditionedDeterminantMoments GOECrudeDeterminant
open WholeFieldRegression
open IntrinsicHessianLaw
open SphericalTAPCriticalBand SphericalTAPCriticalBandSectionBridge
open SphericalTAPCriticalPalmBandLower
open SphericalTAPCertificate
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- The manuscript's `w_N(e,k) = exp(-N q(e,k)/2) d_N(k)`, where `d_N`
is the true ordinary absolute-GOE-determinant mean. -/
def sourceAllCriticalRadialWeight (d : ℕ) (μ : FiniteMixture)
    (Q e k : ℝ) : ℝ :=
  Real.exp (-((d+2:ℕ):ℝ)*
      scoreQuadratic μ Q (scorePairEquiv (e,k))/2) *
    physicalMean d (d+2) (Q^2*μ.xi2 Q) k

theorem sourceAllCriticalRadialWeight_measurable
    (d : ℕ) (μ : FiniteMixture) (Q e : ℝ) :
    Measurable (sourceAllCriticalRadialWeight d μ Q e) := by
  have hq : Continuous (fun k : ℝ =>
      scoreQuadratic μ Q (scorePairEquiv (e,k))) :=
    continuous_iff_continuousAt.mpr
      (fun k => (source_scoreQuadratic_radial_hasDerivAt μ Q e k).continuousAt)
  unfold sourceAllCriticalRadialWeight
  exact (Real.measurable_exp.comp
    ((measurable_const.mul hq.measurable).div_const _)).mul
      (physicalMean_measurable d (d+2) (Q^2*μ.xi2 Q))

theorem sourceAllCriticalRadialWeight_nonneg
    (d : ℕ) (μ : FiniteMixture) (Q e k : ℝ) :
    0 ≤ sourceAllCriticalRadialWeight d μ Q e k := by
  unfold sourceAllCriticalRadialWeight physicalMean
  exact mul_nonneg (Real.exp_pos _).le
    (integral_nonneg (fun _ => abs_nonneg _))

theorem sourceAllCriticalRadialWeight_pos
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (e : ℝ) {k : ℝ}
    (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    0 < sourceAllCriticalRadialWeight d μ Q e k := by
  have hb : 0 < Q^2*μ.xi2 Q :=
    mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  exact mul_pos (Real.exp_pos _)
    (physicalMean_pos d 1 hb hk)

/-- The true all-critical radial density is integrable on every bounded
mark interval; the GOE crude determinant bound supplies a uniform majorant. -/
theorem sourceAllCriticalRadialWeight_integrableOn_Ioo
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (e : ℝ) {L R : ℝ} (hLR : L < R) :
    IntegrableOn (sourceAllCriticalRadialWeight d μ Q e) (Ioo L R) := by
  have hb : 0 < Q^2*μ.xi2 Q :=
    mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hq : Continuous (fun k : ℝ =>
      scoreQuadratic μ Q (scorePairEquiv (e,k))) :=
    continuous_iff_continuousAt.mpr
      (fun k => (source_scoreQuadratic_radial_hasDerivAt μ Q e k).continuousAt)
  obtain ⟨k₀,hk₀,hmin⟩ :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr hLR.le) hq.continuousOn
  let B : ℝ := Real.exp (-((d+2:ℕ):ℝ)*
      scoreQuadratic μ Q (scorePairEquiv (e,k₀))/2) *
    Real.exp (((d+2:ℕ):ℝ)*
      (GaussianCrudeDeterminant.crudeConstant (Q^2*μ.xi2 Q)+max |L| |R|))
  have hbound : ∀ k ∈ Icc L R,
      sourceAllCriticalRadialWeight d μ Q e k ≤ B := by
    intro k hk
    have hqmin : scoreQuadratic μ Q (scorePairEquiv (e,k₀)) ≤
        scoreQuadratic μ Q (scorePairEquiv (e,k)) := hmin hk
    have hExp : Real.exp (-((d+2:ℕ):ℝ)*
        scoreQuadratic μ Q (scorePairEquiv (e,k))/2) ≤
        Real.exp (-((d+2:ℕ):ℝ)*
          scoreQuadratic μ Q (scorePairEquiv (e,k₀))/2) :=
      Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) (d+2)])
    have hkabs : |k| ≤ max |L| |R| := by
      apply abs_le.mpr
      constructor
      · linarith [hk.1, neg_abs_le L, le_max_left |L| |R|]
      · linarith [hk.2, le_abs_self R, le_max_right |L| |R|]
    have hMean := (physical_crude_mean d (d+2) (by omega) hb k).2
    have hMean' : physicalMean d (d+2) (Q^2*μ.xi2 Q) k ≤
        Real.exp (((d+2:ℕ):ℝ)*
          (GaussianCrudeDeterminant.crudeConstant (Q^2*μ.xi2 Q)+max |L| |R|)) :=
      hMean.trans (Real.exp_le_exp.mpr
        (by nlinarith [Nat.cast_nonneg (α := ℝ) (d+2)]))
    unfold sourceAllCriticalRadialWeight B
    exact mul_le_mul hExp hMean'
      (by unfold physicalMean; exact integral_nonneg (fun _ => abs_nonneg _))
      (Real.exp_pos _).le
  have hBint : IntegrableOn (fun _ : ℝ => B) (Ioo L R) :=
    (integrableOn_const isCompact_Icc.measure_ne_top).mono_set Ioo_subset_Icc_self
  apply hBint.mono'
    (sourceAllCriticalRadialWeight_measurable d μ Q e).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with k hk
  rw [Real.norm_of_nonneg (sourceAllCriticalRadialWeight_nonneg d μ Q e k)]
  exact hbound k ⟨hk.1.le,hk.2.le⟩

theorem sourceAllCriticalRadialWeight_integral_pos
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (e : ℝ) {L R : ℝ}
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L) (hLR : L < R) :
    0 < ∫ k in Ioo L R, sourceAllCriticalRadialWeight d μ Q e k := by
  have hint := sourceAllCriticalRadialWeight_integrableOn_Ioo d μ hQ e hLR
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ (fun k => sourceAllCriticalRadialWeight_nonneg d μ Q e k)) hint).mpr
  have hsub : Ioo L R ⊆
      Function.support (sourceAllCriticalRadialWeight d μ Q e) ∩ Ioo L R := by
    intro k hk
    exact ⟨(sourceAllCriticalRadialWeight_pos d μ hQ e
      (hEdge.trans hk.1)).ne',hk⟩
  have hnonempty : (Ioo L R).Nonempty :=
    ⟨(L+R)/2, by constructor <;> linarith⟩
  exact (isOpen_Ioo.measure_pos volume hnonempty).trans_le (measure_mono hsub)

/-- The printed all-critical radial weight defines an honest probability
law on every nondegenerate interval strictly above the GOE edge. -/
def sourceAllCriticalRadialLaw (d : ℕ) (μ : FiniteMixture)
    (Q e L R : ℝ) : Measure ℝ :=
  NormalizedRadialMeasure.law (sourceAllCriticalRadialWeight d μ Q e) (Ioo L R)

theorem sourceAllCriticalRadialLaw_probability
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (e : ℝ) {L R : ℝ}
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L) (hLR : L < R) :
    IsProbabilityMeasure (sourceAllCriticalRadialLaw d μ Q e L R) := by
  unfold sourceAllCriticalRadialLaw
  exact NormalizedRadialMeasure.law_probability
    (sourceAllCriticalRadialWeight_integrableOn_Ioo d μ hQ e hLR)
    (sourceAllCriticalRadialWeight_nonneg d μ Q e)
    (sourceAllCriticalRadialWeight_integral_pos d μ hQ e hEdge hLR)

theorem sourceAllCriticalRadialLaw_ae_mem
    (d : ℕ) (μ : FiniteMixture) (Q e L R : ℝ) :
    ∀ᵐ k ∂sourceAllCriticalRadialLaw d μ Q e L R, k ∈ Ioo L R := by
  unfold sourceAllCriticalRadialLaw
  exact NormalizedRadialMeasure.law_ae_mem measurableSet_Ioo

/-- The determinant-weighted Palm event probability depends measurably on
the radial score. This permits literal integration over the source weight. -/
theorem mixed_markPalm_event_probability_measurable
    (d : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (e : ℝ) (A : Set (Disorder (d+2) μ.maxDegree))
    (hA : MeasurableSet A) :
    Measurable (fun k : ℝ =>
      (∫ J in A, intrinsicDet μ Q u J
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
      (∫ J, intrinsicDet μ Q u J
        ∂mixedLaw μ Q u hu (scorePairEquiv (e,k)))) := by
  let obs := jointCLM (centerCoefficients (mixtureCoefficients μ) Q)
    u (tangentFrame u hu)
  let κ := coefficientKernel obs
  let target := fun k : ℝ => jointScoreTarget (d+1)
    (((d+2:ℕ):ℝ) • scorePairEquiv (e,k))
  have hscore : Measurable (fun k : ℝ => scorePairEquiv (e,k)) :=
    scorePairEquiv.measurable.comp (measurable_const.prodMk measurable_id)
  have hscaled : Measurable (fun k : ℝ =>
      (((d+2:ℕ):ℝ)) • scorePairEquiv (e,k)) :=
    (measurable_const : Measurable (fun _ : ℝ => (((d+2:ℕ):ℝ)))).smul hscore
  have htarget : Measurable target :=
    (jointScoreTarget_continuous (d+1)).measurable.comp hscaled
  have hD : Measurable (intrinsicDet μ Q u) := by
    unfold intrinsicDet
    have hm := (SphericalMarkedWindows.intrinsicDet_measurable
      (centerCoefficients (mixtureCoefficients μ) Q) u hu).ennreal_toReal
    convert hm using 1
    ext J
    exact (ENNReal.toReal_ofReal (abs_nonneg _)).symm
  have hnum : Measurable (fun k : ℝ =>
      ∫ J, A.indicator (intrinsicDet μ Q u) J ∂κ (target k)) :=
    ((hD.stronglyMeasurable.indicator hA).integral_kernel (κ := κ)).measurable.comp htarget
  have hden : Measurable (fun k : ℝ =>
      ∫ J, intrinsicDet μ Q u J ∂κ (target k)) :=
    (hD.stronglyMeasurable.integral_kernel (κ := κ)).measurable.comp htarget
  have hmain := hnum.div hden
  convert hmain using 1
  ext k
  dsimp only [κ,target,obs,mixedLaw]
  rw [← integral_indicator hA]
  rfl

/-- Conditional Palm probability at fixed energy and radial score, with
the actual correlated intrinsic determinant used in numerator and mean. -/
def mixedMarkPalmEventProbability
    (d : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (e : ℝ) (A : Set (Disorder (d+2) μ.maxDegree)) (k : ℝ) : ℝ :=
  (∫ J in A, intrinsicDet μ Q u J
    ∂mixedLaw μ Q u hu (scorePairEquiv (e,k))) /
  (∫ J, intrinsicDet μ Q u J
    ∂mixedLaw μ Q u hu (scorePairEquiv (e,k)))

theorem mixedMarkPalmEventProbability_nonneg
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (e : ℝ) {k : ℝ}
    (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k)
    (A : Set (Disorder (d+2) μ.maxDegree)) :
    0 ≤ mixedMarkPalmEventProbability d μ Q u hu e A k := by
  have hb : 0 < Q^2*μ.xi2 Q :=
    mul_pos (sq_pos_of_pos hQ) (μ.xi2_pos hQ)
  have hMean : 0 < ∫ J, intrinsicDet μ Q u J
      ∂mixedLaw μ Q u hu (scorePairEquiv (e,k)) := by
    rw [determinant_mean_eq_of_law
      (mixed_intrinsicDet_hasLaw μ hQ hnp u hu (scorePairEquiv (e,k)))]
    have hb1 : (scorePairEquiv (e,k)) 1 = k := by
      simp [scorePairEquiv_apply]
    rw [hb1]
    exact physicalMean_pos d 1 hb hk
  unfold mixedMarkPalmEventProbability
  exact div_nonneg (integral_nonneg (fun _ => abs_nonneg _)) hMean.le

/-- The source's Palm law at energy `Ne`, as the exact all-critical radial
average of the determinant-weighted fixed-mark Palm probabilities. -/
def mixedEnergyPalmEventProbability
    (d : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (e L R : ℝ) (A : Set (Disorder (d+2) μ.maxDegree)) : ℝ :=
  ∫ k, mixedMarkPalmEventProbability d μ Q u hu e A k
    ∂sourceAllCriticalRadialLaw d μ Q e L R

/-- The energy-Palm probability is literally the ratio of the two radial
integrals printed in §12, with `w_N(e,k)` including the unrestricted
absolute-determinant mean. -/
theorem mixedEnergyPalmEventProbability_eq_source_ratio
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (e : ℝ) {L R : ℝ}
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L) (hLR : L < R)
    (A : Set (Disorder (d+2) μ.maxDegree)) :
    mixedEnergyPalmEventProbability d μ Q u hu e L R A =
      (∫ k in Ioo L R,
        mixedMarkPalmEventProbability d μ Q u hu e A k *
          sourceAllCriticalRadialWeight d μ Q e k) /
      (∫ k in Ioo L R, sourceAllCriticalRadialWeight d μ Q e k) := by
  unfold mixedEnergyPalmEventProbability sourceAllCriticalRadialLaw
  exact NormalizedRadialMeasure.law_integral
    (sourceAllCriticalRadialWeight_measurable d μ Q e)
    (sourceAllCriticalRadialWeight_nonneg d μ Q e)
    (sourceAllCriticalRadialWeight_integral_pos d μ hQ e hEdge hLR)
    (mixedMarkPalmEventProbability d μ Q u hu e A)

/-- Any bound uniform over all radial marks in the source interval passes
to the exact energy-Palm radial mixture. -/
theorem mixedEnergyPalmEventProbability_le_of_uniform
    (d : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (e : ℝ) {L R : ℝ}
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L) (hLR : L < R)
    (A : Set (Disorder (d+2) μ.maxDegree)) (hA : MeasurableSet A)
    {ε : ℝ}
    (hlo : ∀ k ∈ Ioo L R,
      0 ≤ mixedMarkPalmEventProbability d μ Q u hu e A k)
    (hhi : ∀ k ∈ Ioo L R,
      mixedMarkPalmEventProbability d μ Q u hu e A k ≤ ε) :
    mixedEnergyPalmEventProbability d μ Q u hu e L R A ≤ ε := by
  let ρ := sourceAllCriticalRadialLaw d μ Q e L R
  let : IsProbabilityMeasure ρ :=
    sourceAllCriticalRadialLaw_probability d μ hQ e hEdge hLR
  have hmeas : Measurable (mixedMarkPalmEventProbability d μ Q u hu e A) :=
    mixed_markPalm_event_probability_measurable d μ Q u hu e A hA
  have hsupp : ∀ᵐ k ∂ρ, k ∈ Ioo L R :=
    sourceAllCriticalRadialLaw_ae_mem d μ Q e L R
  have hint : Integrable
      (mixedMarkPalmEventProbability d μ Q u hu e A) ρ := by
    apply (integrable_const ε).mono' hmeas.aestronglyMeasurable
    filter_upwards [hsupp] with k hk
    rw [Real.norm_of_nonneg (hlo k hk)]
    exact hhi k hk
  have hineq : (∫ k, mixedMarkPalmEventProbability d μ Q u hu e A k ∂ρ) ≤
      ∫ _ : ℝ, ε ∂ρ :=
    integral_mono_ae hint (integrable_const ε)
      (hsupp.mono (fun k hk => hhi k hk))
  simpa only [mixedEnergyPalmEventProbability,ρ,integral_const,
    probReal_univ,smul_eq_mul,one_mul] using hineq

/-- Source Proposition 12.20 at fixed energy: the exact unrestricted
all-critical radial Palm average inherits the uniform fixed-`(e,k)` lower
tail. The radial density is the printed `w_N(e,k)`, and the band threshold
uses the exact printed `D_N`. -/
theorem mixed_sourceEnergyPalm_band_lower_tight
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    {M r L R : ℝ} (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hEdge : 2*Real.sqrt (Q^2*μ.xi2 Q) < L)
    (hLR : L < R)
    (hU : Icc L R ⊆ Icc (-M) M)
    (I : Set ℝ) (hImeas : MeasurableSet I)
    (hI : I ⊆ Icc (-r) r) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ d : ℕ in atTop,
      ∀ (u : Vector (d+2)) (hu : ‖u‖^2=((d+2:ℕ):ℝ)),
      ∀ a : ℝ, |a| ≤ M →
      Icc
        (Real.sqrt Q-1/Real.sqrt (((d+2:ℕ):ℝ)))
        (Real.sqrt Q+1/Real.sqrt (((d+2:ℕ):ℝ))) ⊆ I →
      ∀ mN : ℝ,
      let scale := sourceCriticalBandScale (d+1) μ h.overlap_range β mN *
        Real.exp (β*(((d+2:ℕ):ℝ)*a-mN))
      mixedEnergyPalmEventProbability d μ Q u hu a L R
        {J | partitionOn β (field (mixtureCoefficients μ) J)
          (overlapRegion u I) < δ*scale} ≤ ε := by
  intro ε hε
  let g : ℝ := (L-2*Real.sqrt (Q^2*μ.xi2 Q))/2
  have hg : 0 < g := by dsimp [g]; linarith
  obtain ⟨δ,hδ,hFinite⟩ :=
    mixed_sourcePalm_band_lower_tight μ h hnp hM hr0 hr1 hg
      (Z := R) I hImeas hI ε hε
  -- The fixed-mark theorem is applied at the same error tolerance.
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hFinite] with d hd
  intro u hu a ha hband mN
  let scale := sourceCriticalBandScale (d+1) μ h.overlap_range β mN *
    Real.exp (β*(((d+2:ℕ):ℝ)*a-mN))
  let A : Set (Disorder (d+2) μ.maxDegree) :=
    {J | partitionOn β (field (mixtureCoefficients μ) J)
      (overlapRegion u I) < δ*scale}
  have hA : MeasurableSet A :=
    measurableSet_lt
      (sourceBandPartition_measurable (d+1) μ u I hImeas β)
      measurable_const
  apply mixedEnergyPalmEventProbability_le_of_uniform d μ h.overlap_range.1
    u hu a hEdge hLR A hA
  · intro k hk
    exact mixedMarkPalmEventProbability_nonneg d μ h.overlap_range.1 hnp
      u hu a (hEdge.trans hk.1) A
  · intro k hk
    have hkM : |k| ≤ M := abs_le.mpr (hU ⟨hk.1.le,hk.2.le⟩)
    have hkg : 2*Real.sqrt (Q^2*μ.xi2 Q)+g ≤ k := by
      dsimp [g]
      linarith [hk.1]
    have hfixed := hd u hu a k ha hkM hkg hk.2.le hband mN
    dsimp only at hfixed
    simpa only [A,scale,mixedMarkPalmEventProbability,
      scorePairEquiv_apply] using hfixed

end
end SlowEquilibration.SphericalTAPCriticalEnergyPalmAverage
