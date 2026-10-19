-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixedCapturePhysicalCoarseDiniAssembly
public import SlowEquilibration.SourceReductionFiniteWindowCapture
public import SlowEquilibration.SourceLiteraturePhysicalNormQ
public import SlowEquilibration.SourceMixedLowSumBorelIndicator
public import SlowEquilibration.SourceMixedCriticalCenteredWindowCount
public import SlowEquilibration.SphericalTAPCriticalHeavyBandProbability

/-! The common witness for source `thm:mb-capture`. A compact radial
interval inside the low-sum interval supports the ordinary counts and the
coarse cover. The independently constructed heavy-band center differs by
a bounded amount, so its partition lower tail transfers to the same scale.
The final theorem applies the fixed-window reduction to these witnesses. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceMixedCaptureCommonWitness

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalTAPCertificate TwoAtomStationarity PairConditionalDeterminantMoments
open SphericalTAPCriticalBandSectionBridge SphericalTAPMixedLowSumMarkedKR
open SourceMixedLowSumBorelIndicator SourceMixedCriticalCenteredWindowCount
open SphericalTAPCriticalHeavyBandProbability SourceReductionConsumerAsymptoticCounts
open SourceReductionConsumerAsymptotic SourceReductionClosedBandGraph
open SourceReductionFiniteWindowCapture MixedHighEnergyRelocation
open MixedReplicaMeanEnergyAssembly
open SourceLiteratureParisi SourceLiteratureGroundState SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open scoped Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

/-- The common logarithmic correction bounds the difference of centers,
even when their radial intervals and finite prefixes differ. -/
theorem source_centers_eventually_bounded_difference
    {μ : FiniteMixture} {β x Q L₁ R₁ L₂ R₂ : ℝ}
    (d₁ : SourceMaximumFirstMomentConclusions μ β x Q L₁ R₁)
    (d₂ : SourceMaximumFirstMomentConclusions μ β x Q L₂ R₂) :
    ∀ᶠ n : ℕ in atTop,
      |d₁.center n - d₂.center n| ≤ d₁.log_constant + d₂.log_constant := by
  filter_upwards [d₁.logarithmic_correction, d₂.logarithmic_correction] with n h₁ h₂
  have h₂' : |((n+2 : ℕ)*markE μ β x Q-
      Real.log (n+2 : ℕ)/(2*(β*x))) - d₂.center n| ≤ d₂.log_constant := by
    rwa [abs_sub_comm]
  exact (abs_sub_le (d₁.center n)
    ((n+2 : ℕ)*markE μ β x Q-Real.log (n+2 : ℕ)/(2*(β*x))) (d₂.center n)).trans
      (add_le_add h₁ h₂')

/-- The closed consumer interval is chosen strictly inside the analytic
open interval; its boundary points are therefore covered as well. -/
private theorem closed_radial_window_subset_open {L₀ L R R₀ : ℝ}
    (hL : L₀ < L) (hR : R < R₀) : Icc L R ⊆ Ioo L₀ R₀ := by
  intro k hk
  exact ⟨hL.trans_le hk.1, hk.2.trans_lt hR⟩

/-- The two fixed radial boundary points contribute zero to the expected
ordinary count, by the physical Kac--Rice density. -/
theorem originalWindowExpectedCount_closed_eq_open
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (m : ℕ → ℝ) (M L R : ℝ) (n : ℕ) :
    originalWindowExpectedCount μ Q m M (Icc L R) n =
      originalWindowExpectedCount μ Q m M (Ioo L R) n := by
  unfold originalWindowExpectedCount
  rw [actual_mixed_critical_physical_intensity n μ hQ hnp _ _
    measurableSet_Icc measurableSet_Icc,
    actual_mixed_critical_physical_intensity n μ hQ hnp _ _
      measurableSet_Icc measurableSet_Ioo]
  simp only [restrict_Ioo_eq_restrict_Icc]


private theorem score_window_count_mono {P : ℕ} (n : ℕ) (c : Degree P → ℝ)
    (K₁ K₂ : Set (EuclideanSpace ℝ (Fin 2))) (hK : K₁ ⊆ K₂)
    (ψ : Disorder (n+1) P → Vector (n+1) → ℝ≥0∞) (J : Disorder (n+1) P) :
    actualScoreWindowCount n c K₁ ψ J ≤ actualScoreWindowCount n c K₂ ψ J := by
  classical
  rw [actualScoreWindowCount_eq_indicator, actualScoreWindowCount_eq_indicator]
  unfold SphericalKacRiceGluing.actualSphereCount
  apply ENNReal.tsum_le_tsum
  intro u
  dsimp only
  by_cases h₁ : actualScore c J u ∈ K₁
  · simp only [h₁, hK h₁, ↓reduceIte, le_refl]
  · by_cases h₂ : actualScore c J u ∈ K₂ <;>
      simp only [h₁, h₂, ↓reduceIte, zero_le, le_refl]


private theorem physical_window_count_mono_radial (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (I U V : Set ℝ) (hUV : U ⊆ V)
    (ψ : Disorder (n+2) μ.maxDegree → Vector (n+2) → ℝ≥0∞)
    (J : Disorder (n+2) μ.maxDegree) :
    actualScoreWindowCount (n+1) (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+2) I U) ψ J ≤
    actualScoreWindowCount (n+1) (centerCoefficients (mixtureCoefficients μ) Q)
      (physicalEnergyWindow (n+2) I V) ψ J :=
  score_window_count_mono (n+1) (centerCoefficients (mixtureCoefficients μ) Q)
    (physicalEnergyWindow (n+2) I U) (physicalEnergyWindow (n+2) I V)
    (fun _ hz => ⟨hz.1,hUV hz.2⟩) ψ J

/-- One choice of all inputs to the mixed fixed-window reduction. The
scale has a positive finite prefix and equals the exact source band scale
eventually. The low-sum estimate is uniform in the window width. -/
structure CommonWitness (μ : FiniteMixture) (β Q E L R b₀ : ℝ)
    (m : ℕ → ℝ) (τ : ℝ) (D : ℕ → ℝ) where
  overlap_range : Q ∈ Ioo (0 : ℝ) 1
  scale_pos : ∀ n, 0 < D n
  scale_eventually_eq : ∀ᶠ n : ℕ in atTop,
    D n = sourceCriticalBandScale (n+1) μ overlap_range β (m n)
  normalized_center : Tendsto (fun n => m n / ((n+2 : ℕ) : ℝ)) atTop (𝓝 E)
  uniform_count : ∀ M : ℝ, 0 < M → ∃ B : ℝ, 0 < B ∧
    ∀ n : ℕ, originalWindowExpectedCount μ Q m M (Icc L R) n ≤ ENNReal.ofReal B
  count : ∀ M : ℝ, 0 < M →
    limsup (originalWindowExpectedCount μ Q m M (Icc L R)) atTop < ⊤
  upper : Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
    (disorderLaw (n+2) μ.maxDegree).real
      {J | m n+M < sourceSphereMaximum n μ Q J}) atTop) atTop (𝓝 0)
  coarse : ∀ b : ℝ, 0 < b → Tendsto (fun n =>
    ∫ J, originalCoarseBandComplementMass n μ Q E τ b β (Icc L R) J
      ∂disorderLaw (n+2) μ.maxDegree) atTop (𝓝 0)
  C : ℝ
  a : ℝ
  C_pos : 0 < C
  a_pos : 0 < a
  low_sum : ∀ᶠ n : ℕ in atTop, ∀ b : ℝ, 0 < b → b ≤ b₀ →
    ∀ M : ℝ, 0 ≤ M →
      (∫⁻ J, originalLowBandPartitionSum n μ Q E τ (m n) M b β (Icc L R) J
        ∂disorderLaw (n+2) μ.maxDegree) ≤
        ENNReal.ofReal (C * D n * Real.exp (-a*M))
  denominator : Tendsto (fun s : ℝ => limsup (fun n : ℕ =>
    (disorderLaw (n+2) μ.maxDegree).real
      {J | mixturePartition μ β J < s*D n}) atTop) (𝓝[>] 0) (𝓝 0)

private theorem source_center_normalized
    {μ : FiniteMixture} {β x Q L R : ℝ} (h : Certificate μ β x Q)
    (d : SourceMaximumFirstMomentConclusions μ β x Q L R) :
    Tendsto (fun n => d.center n / ((n+2 : ℕ) : ℝ)) atTop
      (𝓝 (markE μ β x Q)) := by
  have hc := mul_pos h.beta_pos h.weight_range.1
  have hlog := NatLogWindowScales.normalized_center_log_bounded hc
    d.log_constant_pos.le d.center d.logarithmic_correction
  have hr := NatLogWindowScales.log_bounded_sequence_div_dimension_tendsto_zero
    (show 0 ≤ 1/(2*(β*x))+1 by positivity)
    (fun n => d.center n-(n+2 : ℕ)*markE μ β x Q) hlog
  convert hr.add_const (markE μ β x Q) using 1
  · funext n
    have hn : ((n+2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  · simp

private theorem source_center_upper_tight
    {μ : FiniteMixture} {β x Q L R : ℝ} (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree) (hEdge : sourceRadialEdge μ Q < L)
    (hL : L < markK μ β Q) (hR : markK μ β Q < R)
    (d : SourceMaximumFirstMomentConclusions μ β x Q L R) :
    Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
      (disorderLaw (n+2) μ.maxDegree).real
        {J | d.center n+M < sourceSphereMaximum n μ Q J}) atTop) atTop (𝓝 0) := by
  have hc := mul_pos h.beta_pos h.weight_range.1
  have hκ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1
    (by have hd := h.min_degree; omega) hnp
  have hu := sourceRadialClearance_pos μ (show markK μ β Q ∈ Ioo L R from ⟨hL,hR⟩)
  let δ := sourceMarkedLeastCurvature μ Q *
    (sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hexp : Tendsto (fun M : ℝ => Real.exp (-(β*x)*M)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (neg_neg_of_pos hc))
  apply squeeze_zero (fun M => ?_) (fun M => ?_) hexp
  · have hh := limsup_le_limsup
      (.of_forall fun n : ℕ => (measureReal_nonneg :
        0 ≤ (disorderLaw (n+2) μ.maxDegree).real
          {J | d.center n+M < sourceSphereMaximum n μ Q J}))
      (isCoboundedUnder_le_of_le atTop fun _ : ℕ => le_rfl (a := (0 : ℝ)))
      (isBoundedUnder_of ⟨1,fun _ => measureReal_le_one⟩)
    simpa only [limsup_const] using hh
  · apply le_trans ?_ (sourceSphereMaximum_centered_probability_limsup
      μ h hnp hEdge ⟨hL,hR⟩ hδ (le_refl δ) d M)
    apply limsup_le_limsup (.of_forall fun n => ?_)
      (isCoboundedUnder_le_of_le atTop fun _ => measureReal_nonneg)
      (isBoundedUnder_of ⟨1,fun _ => measureReal_le_one⟩)
    exact measureReal_mono (fun _ hJ => (show d.center n+M < _ from hJ).le)
      (measure_ne_top _ _)

private theorem band_scale_shift (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : Q ∈ Ioo (0 : ℝ) 1) (β m t : ℝ) :
    sourceCriticalBandScale n μ hQ β (m+t) =
      Real.exp (β*t) * sourceCriticalBandScale n μ hQ β m := by
  unfold sourceCriticalBandScale
  rw [mul_add, Real.exp_add]
  ring

private theorem denominator_transfer
    {μ : FiniteMixture} {β x Q L₁ R₁ L₂ R₂ : ℝ}
    (h : Certificate μ β x Q)
    (d₁ : SourceMaximumFirstMomentConclusions μ β x Q L₁ R₁)
    (d₂ : SourceMaximumFirstMomentConclusions μ β x Q L₂ R₂)
    (D : ℕ → ℝ)
    (hD : ∀ᶠ n : ℕ in atTop,
      D n = sourceCriticalBandScale (n+1) μ h.overlap_range β (d₁.center n))
    (hheavy : ∀ ρ : ℝ, 0 < ρ → ∃ T δ : ℝ, 0 < T ∧ 0 < δ ∧
      limsup (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
        {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
          δ*Real.exp (-β*T)*sourceCriticalBandScale (n+2) μ h.overlap_range β
            (d₂.center (n+1))}) atTop ≤ 2*ρ) :
    Tendsto (fun s : ℝ => limsup (fun n : ℕ =>
      (disorderLaw (n+2) μ.maxDegree).real
        {J | mixturePartition μ β J < s*D n}) atTop) (𝓝[>] 0) (𝓝 0) := by
  let B := d₁.log_constant + d₂.log_constant
  have hscale : ∀ᶠ n : ℕ in atTop,
      Real.exp (-β*B)*D n ≤
        sourceCriticalBandScale (n+1) μ h.overlap_range β (d₂.center n) := by
    filter_upwards [hD, source_centers_eventually_bounded_difference d₁ d₂,
      eventually_ge_atTop 1] with n hn hcent hn1
    rw [hn]
    have hd : -B ≤ d₂.center n-d₁.center n := by
      have hh := (abs_le.mp hcent).2
      dsimp [B]
      linarith
    have he : Real.exp (-β*B) ≤ Real.exp (β*(d₂.center n-d₁.center n)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [h.beta_pos]
    have hshift := band_scale_shift (n+1) μ h.overlap_range β (d₁.center n)
      (d₂.center n-d₁.center n)
    rw [add_sub_cancel] at hshift
    rw [hshift]
    exact mul_le_mul_of_nonneg_right he
      (sourceCriticalBandScale_pos (n+1) (by omega) μ h.overlap_range β _).le
  apply tendsto_order.mpr
  constructor
  · intro z hz
    refine .of_forall fun s => hz.trans_le ?_
    have hh := limsup_le_limsup
      (.of_forall fun n : ℕ => (measureReal_nonneg :
        0 ≤ (disorderLaw (n+2) μ.maxDegree).real
          {J | mixturePartition μ β J < s*D n}))
      (isCoboundedUnder_le_of_le atTop fun _ : ℕ => le_rfl (a := (0 : ℝ)))
      (isBoundedUnder_of ⟨1,fun _ => measureReal_le_one⟩)
    simpa only [limsup_const] using hh
  · intro ε hε
    obtain ⟨T,δ,_hT,hδ,hprob⟩ := hheavy (ε/4) (by positivity)
    let s₀ := δ*Real.exp (-β*T)*Real.exp (-β*B)
    have hs₀ : 0 < s₀ := by dsimp [s₀]; positivity
    have hprob' : limsup (fun n : ℕ => (disorderLaw (n+2) μ.maxDegree).real
        {J | mixturePartition μ β J < δ*Real.exp (-β*T)*
          sourceCriticalBandScale (n+1) μ h.overlap_range β (d₂.center n)}) atTop ≤
        2*(ε/4) := by
      let f := fun n : ℕ => (disorderLaw (n+2) μ.maxDegree).real
        {J | mixturePartition μ β J < δ*Real.exp (-β*T)*
          sourceCriticalBandScale (n+1) μ h.overlap_range β (d₂.center n)}
      have heq : limsup (fun n => f (n+1)) atTop = limsup f atTop := by
        rw [← Function.comp_def, limsup_comp, map_add_atTop_eq_nat]
      rw [← heq]
      exact hprob
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (gt_mem_nhds hs₀)] with s hs hss
    apply lt_of_le_of_lt (b := 2*(ε/4)) ?_ (by linarith)
    apply le_trans ?_ hprob'
    apply limsup_le_limsup ?_
      (isCoboundedUnder_le_of_le atTop fun _ => measureReal_nonneg)
      (isBoundedUnder_of ⟨1,fun _ => measureReal_le_one⟩)
    filter_upwards [hscale, hD, eventually_ge_atTop 1] with n hn hnD hn1
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro J hJ
    have hDn : 0 ≤ D n := by
      rw [hnD]
      exact (sourceCriticalBandScale_pos (n+1) (by omega) μ h.overlap_range β _).le
    have hh := mul_le_mul_of_nonneg_left hn
      (show 0 ≤ δ*Real.exp (-β*T) by positivity)
    have hsD := mul_le_mul_of_nonneg_right hss.le hDn
    change mixturePartition μ β J < _ at hJ ⊢
    dsimp [s₀] at hsD
    nlinarith

private theorem common_witness_of_estimates
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β) (h24 : Proposition24 μ β Q)
    {L₀ R₀ bLow C τ a Lh Rh : ℝ}
    (hEdge : sourceRadialEdge μ Q < L₀)
    (hLK : L₀ < markK μ β Q) (hKR : markK μ β Q < R₀)
    (hbLow : 0 < bLow) (hC : 0 < C) (hτ : 0 < τ) (ha : 0 < a)
    (d : SourceMaximumFirstMomentConclusions μ β x Q L₀ R₀)
    (hLow : ∀ᶠ n : ℕ in atTop, ∀ b : ℝ, 0 < b → b ≤ bLow →
      ∀ M : ℝ, 0 ≤ M →
        (∫⁻ J, actualScoreWindowCount (n+1)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+2)
            (Ico (((n+2 : ℕ) : ℝ)*(markE μ β x Q-τ)) (d.center n-M)) (Ioo L₀ R₀))
          (sourceMixedBandMark n μ β (Real.sqrt Q) b) J
          ∂disorderLaw (n+2) μ.maxDegree) ≤
          ENNReal.ofReal (C*sourceCriticalBandScale (n+1) μ h.overlap_range β
            (d.center n)*Real.exp (-a*M)))
    (dh : SourceMaximumFirstMomentConclusions μ β x Q Lh Rh)
    (hHeavy : ∀ ρ : ℝ, 0 < ρ → ∃ T δ : ℝ, 0 < T ∧ 0 < δ ∧
      limsup (fun n : ℕ => (disorderLaw (n+3) μ.maxDegree).real
        {J | partition (n+3) β (field (mixtureCoefficients μ) J) <
          δ*Real.exp (-β*T)*sourceCriticalBandScale (n+2) μ h.overlap_range β
            (dh.center (n+1))}) atTop ≤ 2*ρ) :
    ∃ L R b₀ : ℝ,
      2 * Real.sqrt (Q^2 * μ.xi2 Q) < L ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ (m : ℕ → ℝ) (τ : ℝ) (D : ℕ → ℝ), 0 < τ ∧
        Nonempty (CommonWitness μ β Q (markE μ β x Q) L R b₀ m τ D) := by
  let L := (L₀+markK μ β Q)/2
  let R := (markK μ β Q+R₀)/2
  have hL₀ : L₀ < L := by dsimp [L]; linarith
  have hL : L < markK μ β Q := by dsimp [L]; linarith
  have hR : markK μ β Q < R := by dsimp [R]; linarith
  have hR₀ : R < R₀ := by dsimp [R]; linarith
  have hInside := closed_radial_window_subset_open hL₀ hR₀
  have hEdge' : 2 * Real.sqrt (Q^2*μ.xi2 Q) < L := by
    exact (show 2 * Real.sqrt (Q^2*μ.xi2 Q) < L₀ from hEdge).trans hL₀
  let b₀ := min bLow (Real.sqrt Q/2)
  have hsqrt : 0 < Real.sqrt Q := Real.sqrt_pos.mpr h.overlap_range.1
  have hb₀ : 0 < b₀ := lt_min hbLow (by positivity)
  have hb₀Q : b₀ < Real.sqrt Q :=
    (min_le_right _ _).trans_lt (by linarith)
  let D := fun n : ℕ => if n = 0 then 1 else
    sourceCriticalBandScale (n+1) μ h.overlap_range β (d.center n)
  have hD : ∀ n, 0 < D n := by
    intro n
    dsimp [D]
    split_ifs with hn
    · norm_num
    · exact sourceCriticalBandScale_pos (n+1) (by omega) μ h.overlap_range β _
  have hDeq : ∀ᶠ n : ℕ in atTop,
      D n = sourceCriticalBandScale (n+1) μ h.overlap_range β (d.center n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact ite_eq_right (by omega)
  have hNorm := SourceLiteraturePhysicalNormQ.physicalDirectingNormQ_of_cited_theorems
    hChen hChenSen h h5 h25
  have hMean := mixed_contactReplicaMeanEnergy_of_literature μ h hChen h24
  have hRel : CenterFieldRelocation μ Q (markE μ β x Q) (Icc L R) := by
    intro r hr
    obtain ⟨ε₀,hε₀,Ω,hΩ,hmove,hprob⟩ :=
      mixed_centerFieldRelocation μ h hnp hEdge' hL hR r hr
    refine ⟨ε₀,hε₀,Ω,hΩ,?_,hprob⟩
    intro n J hJ w hw he
    obtain ⟨u,hu,hcrit,hk,hdist,henergy⟩ := hmove n J hJ w hw he
    exact ⟨u,hu,hcrit,Ioo_subset_Icc_self hk,hdist,henergy⟩
  have hCount : ∀ M : ℝ, 0 < M → ∃ B : ℝ, 0 < B ∧
      ∀ n : ℕ, originalWindowExpectedCount μ Q d.center M (Icc L R) n ≤
        ENNReal.ofReal B := by
    intro M hM
    obtain ⟨B,hB,hbound⟩ :=
      original_mixed_centered_critical_window_count_bounded μ h.overlap_range.1 d hM
    refine ⟨B,hB,fun n => ?_⟩
    exact (lintegral_mono fun J =>
      physical_window_count_mono_radial n μ Q
        (Icc (d.center n-M) (d.center n+M)) _ _ hInside (fun _ _ => 1) J).trans (hbound n)
  refine ⟨L,R,b₀,hEdge',hL,hR,hb₀,hb₀Q,d.center,τ,D,hτ,⟨{
    overlap_range := h.overlap_range
    scale_pos := hD
    scale_eventually_eq := hDeq
    normalized_center := source_center_normalized h d
    uniform_count := hCount
    count := ?_
    upper := source_center_upper_tight h hnp hEdge hLK hKR d
    coarse := ?_
    C := C
    a := a
    C_pos := hC
    a_pos := ha
    low_sum := ?_
    denominator := denominator_transfer h d dh D hDeq hHeavy }⟩⟩
  · intro M hM
    obtain ⟨B,_hB,hbound⟩ := hCount M hM
    exact (limsup_le_of_le (by isBoundedDefault) (.of_forall hbound)).trans_lt
      ENNReal.ofReal_lt_top
  · intro b hb
    exact MixedCapturePhysicalCoarseDiniAssembly.physical_coarse_cover_of_three_physical_inputs
      μ β (Icc L R) hNorm hMean hRel b hb τ hτ
  · filter_upwards [hLow, hDeq] with n hn hnD
    intro b hb hbb M hM
    rw [hnD]
    have hh := hn b hb (hbb.trans (min_le_left _ _)) M hM
    apply le_trans ?_ hh
    apply lintegral_mono
    intro J
    exact physical_window_count_mono_radial n μ Q
      (Ico (((n+2 : ℕ) : ℝ)*(markE μ β x Q-τ)) (d.center n-M)) _ _
      hInside (sourceMixedBandMark n μ β (Real.sqrt Q) b) J


private theorem capture_of_common_witness
    (μ : FiniteMixture) {β Q E L R b₀ τ : ℝ} {m D : ℕ → ℝ}
    (hQ : 0 < Q) (w : CommonWitness μ β Q E L R b₀ m τ D)
    {b : ℝ} (hb : 0 < b) (hbb : b ≤ b₀) :
    Tendsto (fun M : ℝ => limsup (fun n => ∫ J,
      originalBandComplementMass μ Q (m n) M b β (Icc L R) J
        ∂disorderLaw (n+2) μ.maxDegree) atTop) atTop (𝓝 0) := by
  apply original_fixed_window_capture_of_inputs μ hQ E τ b β isClosed_Icc m D w.scale_pos
    (w.coarse b hb) w.upper w.denominator w.C w.a w.a_pos
  intro M hM
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [w.low_sum] with n hn
  have hh := ENNReal.div_le_div_right (hn b hb hbb M hM.le) (ENNReal.ofReal (D n))
  apply hh.trans_eq
  rw [← ENNReal.ofReal_div_of_pos (w.scale_pos n)]
  congr 1
  field_simp [(w.scale_pos n).ne']

/-- Module 7: one compact radial interval, center, band width, coarse
threshold and positive scale satisfy all six source capture inputs. -/
theorem mixed_capture_common_witness_of_literature
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hChen : Chen2013FiniteParisi) (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5 (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β) (h24 : Proposition24 μ β Q) :
    ∃ L R b₀ : ℝ,
      2 * Real.sqrt (Q^2 * μ.xi2 Q) < L ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ (m : ℕ → ℝ) (τ : ℝ) (D : ℕ → ℝ), 0 < τ ∧
        Nonempty (CommonWitness μ β Q (markE μ β x Q) L R b₀ m τ D) := by
  obtain ⟨L₀,R₀,ε,bLow,C,C₂,Cenv,τ,a,_hε,hbLow,hC,_hC₂,_hCenv,
    hEdge,hLK,hKR,_hband,_hτdef,_hadef,hτ,ha,d,hLow⟩ :=
    source_mixed_band_partition_below_window_sum_borel μ h hnp
  obtain ⟨Lh,Rh,bh,_hEdgeh,_hLh,_hRh,hbh,_hbhQ,dh,hHeavy⟩ :=
    source_mixed_heavy_band_partition_low_probability_unconditional μ h hnp h.min_degree
  have hLow' := hLow τ hτ le_rfl
  have hLow'' : ∀ᶠ n : ℕ in atTop, ∀ b : ℝ, 0 < b → b ≤ bLow →
      ∀ M : ℝ, 0 ≤ M →
        (∫⁻ J, actualScoreWindowCount (n+1)
          (centerCoefficients (mixtureCoefficients μ) Q)
          (physicalEnergyWindow (n+2)
            (Ico (((n+2 : ℕ) : ℝ)*(markE μ β x Q-τ)) (d.center n-M)) (Ioo L₀ R₀))
          (sourceMixedBandMark n μ β (Real.sqrt Q) b) J
          ∂disorderLaw (n+2) μ.maxDegree) ≤
          ENNReal.ofReal (C*sourceCriticalBandScale (n+1) μ h.overlap_range β
            (d.center n)*Real.exp (-a*M)) := by
    filter_upwards [hLow'] with n hn
    intro b hb hbb M hM
    simpa only [mem_univ, ↓reduceIte] using hn b hb hbb M hM univ MeasurableSet.univ
  exact common_witness_of_estimates μ h hnp hChen hChenSen h5 h25 h24
    hEdge hLK hKR hbLow hC hτ ha d hLow'' dh (hHeavy bh hbh le_rfl)

/-- Source `thm:mb-capture` for a genuine finite mixture, conditional
only on the certificate and the named literature interfaces. -/
theorem mixed_original_fixed_window_capture_of_literature
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (hChen : Chen2013FiniteParisi)
    (hChenSen : ChenSenFiniteGround)
    (h5 : Theorem5
      (literatureThermodynamicData hChen hChenSen μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β)
    (h24 : Proposition24 μ β Q) :
    ∃ L R b₀ : ℝ,
      2 * Real.sqrt (Q^2 * μ.xi2 Q) < L ∧
      L < markK μ β Q ∧ markK μ β Q < R ∧
      0 < b₀ ∧ b₀ < Real.sqrt Q ∧
      ∃ m : ℕ → ℝ,
        Tendsto (fun n => m n / ((n+2 : ℕ) : ℝ))
          atTop (𝓝 (markE μ β x Q)) ∧
        (∀ M : ℝ, 0 < M →
          limsup (originalWindowExpectedCount μ Q m M (Icc L R))
            atTop < ⊤) ∧
        ∀ b : ℝ, 0 < b → b ≤ b₀ →
          Tendsto (fun M : ℝ => limsup (fun n =>
            ∫ J, originalBandComplementMass μ Q (m n) M b β
              (Icc L R) J ∂disorderLaw (n+2) μ.maxDegree) atTop)
            atTop (𝓝 0) := by
  obtain ⟨L,R,b₀,hEdge,hL,hR,hb₀,hb₀Q,m,τ,D,_hτ,⟨w⟩⟩ :=
    mixed_capture_common_witness_of_literature μ h hnp hChen hChenSen h5 h25 h24
  refine ⟨L,R,b₀,hEdge,hL,hR,hb₀,hb₀Q,m,w.normalized_center,w.count,?_⟩
  intro b hb hbb
  exact capture_of_common_witness μ h.overlap_range.1 w hb hbb

end SlowEquilibration.SourceMixedCaptureCommonWitness
