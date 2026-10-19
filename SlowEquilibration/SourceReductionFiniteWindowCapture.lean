-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionConsumerAsymptoticCounts
public import SlowEquilibration.SphericalMarkedMaximumEvents
public import SlowEquilibration.SphericalTAPMixedLowSumMarkedKR

/-! The reduction in source `prop:red-capture` and `thm:mb-capture`:
coarse critical-center bands, upper tightness of the center-field maximum,
a lower-tail bound for the original partition function, and a small expected
below-window partition sum imply fixed-window Gibbs capture. All analytic
inputs are hypotheses; no mixed coarse-cover or common-witness theorem is
assumed to have been constructed. The Gibbs law and all partition marks use
the original mixture, while critical points use its radius-Q center field.
The extended-valued version preserves infinite nonnegative expectations. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceReductionFiniteWindowCapture

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open SphericalMorse SphericalKacRiceGluing PairConditionalDeterminantMoments
open SourceReductionClosedBandGraph SourceReductionConsumerBandBound
open SourceReductionConsumerAsymptotic SourceReductionConsumerAsymptoticCounts
open SphericalTAPMixedLowSumMarkedKR
open scoped Topology ENNReal

set_option autoImplicit false

/-- The coarse union of the same physical bands as the literal consumer,
over center-field critical points above `N * (E - τ)` with radial mark in `U`. -/
def originalCoarseBandUnion (n : ℕ) (μ : FiniteMixture) (Q E τ b : ℝ)
    (U : Set ℝ) (J : Disorder (n+2) μ.maxDegree) : Set (Vector (n+2)) :=
  {σ | ‖σ‖^2 = ((n+2 : ℕ) : ℝ) ∧ ∃ u : Vector (n+2),
    ‖u‖^2 = ((n+2 : ℕ) : ℝ) ∧
    surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u = 0 ∧
    ((n+2 : ℕ) : ℝ) * (E-τ) ≤
      field (centerCoefficients (mixtureCoefficients μ) Q) J u ∧
    actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ U ∧
    |overlap σ u - Real.sqrt Q| ≤ b}

/-- Original Gibbs mass outside the coarse center-field band union. -/
def originalCoarseBandComplementMass (n : ℕ) (μ : FiniteMixture)
    (Q E τ b β : ℝ) (U : Set ℝ) (J : Disorder (n+2) μ.maxDegree) : ℝ :=
  (mixtureGibbsLaw μ β J).real (originalCoarseBandUnion n μ Q E τ b U J)ᶜ

/-- The genuine nonnegative partition sum over the half-open low-energy
window, with the same radial window and original-field band partition mark. -/
def originalLowBandPartitionSum (n : ℕ) (μ : FiniteMixture)
    (Q E τ m M b β : ℝ) (U : Set ℝ)
    (J : Disorder (n+2) μ.maxDegree) : ℝ≥0∞ :=
  actualScoreWindowCount (n+1) (centerCoefficients (mixtureCoefficients μ) Q)
    (physicalEnergyWindow (n+2) (Ico (((n+2 : ℕ) : ℝ)*(E-τ)) (m-M)) U)
    (sourceMixedBandMark n μ β (Real.sqrt Q) b) J

private theorem coarse_graph_closed (n : ℕ) (μ : FiniteMixture)
    (Q E τ b : ℝ) {U : Set ℝ} (hU : IsClosed U) :
    IsClosed {z : Disorder (n+2) μ.maxDegree × Vector (n+2) |
      z.2 ∈ originalCoarseBandUnion n μ Q E τ b U z.1} := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let S := {u : Vector (n+2) | ‖u‖^2 = ((n+2 : ℕ) : ℝ)}
  let : CompactSpace S := isCompact_iff_compactSpace.mp (sourceSphere_compact (n+2))
  let C : Set (Disorder (n+2) μ.maxDegree × S) :=
    {z | surfaceGradient (field c z.1) z.2.1 = 0 ∧
      ((n+2 : ℕ) : ℝ)*(E-τ) ≤ field c z.1 z.2.1 ∧
      actualScore c z.1 z.2.1 1 ∈ U}
  let B : Set (Vector (n+2) × S) :=
    {z | |overlap z.1 z.2.1 - Real.sqrt Q| ≤ b}
  have hmap : Continuous (fun z : Disorder (n+2) μ.maxDegree × S => (z.1,z.2.1)) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  have hC : IsClosed C := by
    exact (isClosed_eq ((source_surfaceGradient_joint_contDiff c).continuous.comp hmap)
      continuous_const).inter
      ((isClosed_le continuous_const ((field_jointContinuous c).comp hmap)).inter
        (hU.preimage (((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
          (actualScore_jointContinuous c)).comp hmap)))
  have hB : IsClosed B :=
    (physicalBandRelation_isClosed Q b).preimage
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hp := (SourceReductionCompactBandProjection.bandUnionGraph_isClosed hC hB).inter
    (isClosed_eq (continuous_snd.norm.pow 2)
      (continuous_const (y := ((n+2 : ℕ) : ℝ))))
  convert hp using 1
  ext z
  constructor
  · rintro ⟨hσ,u,hu,hg,he,hr,hb⟩
    exact ⟨⟨⟨u,hu⟩,⟨hg,he,hr⟩,hb⟩,hσ⟩
  · rintro ⟨⟨u,⟨hg,he,hr⟩,hb⟩,hσ⟩
    exact ⟨hσ,u.1,u.2,hg,he,hr,hb⟩

private theorem coarse_measurable (n : ℕ) (μ : FiniteMixture)
    (Q E τ b β : ℝ) {U : Set ℝ} (hU : IsClosed U) :
    Measurable (originalCoarseBandComplementMass n μ Q E τ b β U) := by
  have hm := (Kernel.measurable_kernel_prodMk_left
    (κ := disorderGibbsKernel (by omega : 1 ≤ n+2) (mixtureCoefficients μ) β)
    (coarse_graph_closed n μ Q E τ b hU).measurableSet.compl).ennreal_toReal
  convert hm using 1
  funext J
  rw [disorderGibbsKernel_apply]
  rfl

private theorem coarse_integrable (n : ℕ) (μ : FiniteMixture)
    (Q E τ b β : ℝ) {U : Set ℝ} (hU : IsClosed U) :
    Integrable (originalCoarseBandComplementMass n μ Q E τ b β U)
      (disorderLaw (n+2) μ.maxDegree) := by
  apply Integrable.of_bound (coarse_measurable n μ Q E τ b β hU).aestronglyMeasurable 1
  refine .of_forall fun J => ?_
  let := mixtureGibbsLaw_probability (by omega : 1 ≤ n+2) μ β J
  unfold originalCoarseBandComplementMass
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

private theorem low_aemeasurable (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (E τ m M b β : ℝ) {U : Set ℝ} (hU : IsClosed U) :
    AEMeasurable (originalLowBandPartitionSum n μ Q E τ m M b β U)
      (disorderLaw (n+2) μ.maxDegree) := by
  exact actualScoreWindowCount_aemeasurable (n+1) (by omega) μ hQ _
    (rectangularScoreWindow_measurable _ _
      (measurableSet_Ico.preimage (measurable_const_mul _)) hU.measurableSet)
    _ (sourceMixedBandMark_measurable n μ β (Real.sqrt Q) b)

private theorem good_field_bound (n : ℕ) (μ : FiniteMixture)
    (Q E τ m M b β : ℝ) (U : Set ℝ) (J : Disorder (n+2) μ.maxDegree)
    (hf : (sphereCriticalSet (n+1)
      (centerCoefficients (mixtureCoefficients μ) Q) J).Finite)
    (hmax : sourceSphereMaximum n μ Q J ≤ m+M) :
    originalBandComplementMass μ Q m M b β U J ≤
      originalCoarseBandComplementMass n μ Q E τ b β U J +
      (originalLowBandPartitionSum n μ Q E τ m M b β U J).toReal /
        mixturePartition μ β J := by
  classical
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let K := physicalEnergyWindow (n+2) (Ico (((n+2 : ℕ) : ℝ)*(E-τ)) (m-M)) U
  let L := {u : Vector (n+2) | ‖u‖^2 = ((n+2 : ℕ) : ℝ) ∧
    surfaceGradient (field c J) u = 0 ∧ actualScore c J u ∈ K}
  have hL : L.Finite := hf.subset fun _ hu => ⟨hu.1,hu.2.1⟩
  let : Fintype L := hL.fintype
  let π := mixtureGibbsLaw μ β J
  let := mixtureGibbsLaw_probability (by omega : 1 ≤ n+2) μ β J
  let A := ⋃ u : L, overlapRegion (u : Vector (n+2))
    (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))
  obtain ⟨v,hv,_,hvm,heq⟩ := sourceSphereMaximum_attained n μ Q J
  have hupper (u : Vector (n+2)) (hu : ‖u‖^2 = ((n+2 : ℕ) : ℝ)) :
      field c J u ≤ m+M := by
    have hh := hvm hu
    rw [← heq] at hh
    exact hh.trans hmax
  have hsub : (ambientWindowBandUnion μ Q m M b U J)ᶜ ⊆
      (originalCoarseBandUnion n μ Q E τ b U J)ᶜ ∪ A := by
    intro σ hσ
    by_cases hc : σ ∈ originalCoarseBandUnion n μ Q E τ b U J
    · obtain ⟨hs,u,hu,hg,he,hr,hb⟩ := hc
      have hlo : field c J u < m-M := by
        by_contra hn
        apply hσ
        change (∃ u, (J,u) ∈ windowCenterGraph μ Q m M U ∧
          (σ,u) ∈ physicalBandRelation Q b) ∧ ‖σ‖^2 = ((n+2 : ℕ) : ℝ)
        exact ⟨⟨u,⟨⟨⟨hu,hg⟩,le_of_not_gt hn,hupper u hu⟩,hr⟩,hb⟩,hs⟩
      have hk : actualScore c J u ∈ K :=
        (actualScore_mem_physicalEnergyWindow (by omega) c J u _ _).2 ⟨⟨he,hlo⟩,hr⟩
      right
      apply mem_iUnion.mpr
      refine ⟨⟨u,hu,hg,hk⟩,?_⟩
      change overlap σ u ∈ Icc (Real.sqrt Q-b) (Real.sqrt Q+b)
      obtain ⟨hl,hh⟩ := abs_le.mp hb
      exact ⟨by linarith,by linarith⟩
    · exact Or.inl hc
  have hsum : (∑ u : L, π.real (overlapRegion (u : Vector (n+2))
      (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)))) =
      (originalLowBandPartitionSum n μ Q E τ m M b β U J).toReal /
        mixturePartition μ β J := by
    unfold originalLowBandPartitionSum actualScoreWindowCount sourceMixedBandMark
    rw [tsum_fintype, ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
    simp_rw [ENNReal.toReal_ofReal (partitionOn_nonneg _ _ _)]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _
    exact gibbsLaw_real_eq_partitionOn_div (by omega) β
      (field_contDiff (mixtureCoefficients μ) J).continuous
      (overlapRegion_measurable _ measurableSet_Icc)
  have hA : π.real A ≤ ∑ u : L, π.real (overlapRegion (u : Vector (n+2))
      (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))) := measureReal_iUnion_fintype_le _
  rw [hsum] at hA
  exact (measureReal_mono (μ := π) hsub).trans
    ((measureReal_union_le _ _).trans (add_le_add le_rfl hA))

/-- Source reduction inequality in real form. Finiteness is stated only
for the nonnegative low-center expectation, so `.toReal` is legitimate. -/
theorem original_expected_band_complement_le (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (E τ m M b β s D : ℝ)
    {U : Set ℝ} (hU : IsClosed U) (hs : 0 < s) (hD : 0 < D)
    (hlow : (∫⁻ J, originalLowBandPartitionSum n μ Q E τ m M b β U J
      ∂disorderLaw (n+2) μ.maxDegree) ≠ ⊤) :
    (∫ J, originalBandComplementMass μ Q m M b β U J
      ∂disorderLaw (n+2) μ.maxDegree) ≤
    (∫ J, originalCoarseBandComplementMass n μ Q E τ b β U J
      ∂disorderLaw (n+2) μ.maxDegree) +
    (disorderLaw (n+2) μ.maxDegree).real {J | m+M < sourceSphereMaximum n μ Q J} +
    (disorderLaw (n+2) μ.maxDegree).real {J | mixturePartition μ β J < s*D} +
    (∫⁻ J, originalLowBandPartitionSum n μ Q E τ m M b β U J
      ∂disorderLaw (n+2) μ.maxDegree).toReal / (s*D) := by
  let P := disorderLaw (n+2) μ.maxDegree
  let X := originalBandComplementMass (N := n+2) μ Q m M b β U
  let C := originalCoarseBandComplementMass n μ Q E τ b β U
  let W := originalLowBandPartitionSum n μ Q E τ m M b β U
  let A := {J : Disorder (n+2) μ.maxDegree | m+M < sourceSphereMaximum n μ Q J}
  let B := {J : Disorder (n+2) μ.maxDegree | mixturePartition μ β J < s*D}
  have hA : MeasurableSet A :=
    measurableSet_lt measurable_const (sourceSphereMaximum_continuous n μ Q).measurable
  have hB : MeasurableSet B :=
    measurableSet_lt (partition_measurable (mixtureCoefficients μ) β) measurable_const
  have hm : AEMeasurable W P := low_aemeasurable n μ hQ E τ m M b β hU
  have hi := integrable_toReal_of_lintegral_ne_top hm hlow
  have hC := coarse_integrable n μ Q E τ b β hU
  have hAi : Integrable (A.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator hA
  have hBi : Integrable (B.indicator (fun _ => (1 : ℝ))) P :=
    (integrable_const 1).indicator hB
  have hpoint : ∀ᵐ J ∂P, X J ≤ C J + A.indicator (fun _ => (1 : ℝ)) J +
      B.indicator (fun _ => (1 : ℝ)) J + (W J).toReal/(s*D) := by
    filter_upwards [actual_sphere_criticalSet_finite_ae (n+1) (by omega) μ hQ] with J hJ
    let := mixtureGibbsLaw_probability (by omega : 1 ≤ n+2) μ β J
    have hX : X J ≤ 1 := measureReal_le_one
    have hC0 : 0 ≤ C J := measureReal_nonneg
    have hA0 : 0 ≤ A.indicator (fun _ => (1 : ℝ)) J :=
      indicator_nonneg (fun _ _ => zero_le_one) _
    have hB0 : 0 ≤ B.indicator (fun _ => (1 : ℝ)) J :=
      indicator_nonneg (fun _ _ => zero_le_one) _
    have hW0 : 0 ≤ (W J).toReal/(s*D) := by positivity
    by_cases hJA : J ∈ A
    · rw [indicator_of_mem hJA]
      linarith
    by_cases hJB : J ∈ B
    · rw [indicator_of_mem hJB]
      linarith
    have hb := good_field_bound n μ Q E τ m M b β U J hJ (le_of_not_gt hJA)
    have hz : s*D ≤ mixturePartition μ β J := le_of_not_gt hJB
    have hdiv := div_le_div_of_nonneg_left (ENNReal.toReal_nonneg (a := W J))
      (mul_pos hs hD) hz
    exact hb.trans (by dsimp only [C,W]; linarith)
  have hbound := integral_mono_ae
    (originalBandComplementMass_integrable (by omega : 1 ≤ n+2) μ Q m M b β hU)
    (((hC.add hAi).add hBi).add (hi.div_const (s*D))) hpoint
  rw [integral_add' ((hC.add hAi).add hBi) (hi.div_const (s*D)),
    integral_add' (hC.add hAi) hBi, integral_add' hC hAi,
    integral_indicator_const 1 hA, integral_indicator_const 1 hB, integral_div,
    integral_toReal hm (ae_lt_top' hm hlow)] at hbound
  simpa only [smul_eq_mul,mul_one] using hbound

/-- The same reduction without any finiteness hypothesis on the low-center
expectation. In particular, an infinite expectation remains `⊤`. -/
theorem original_expected_band_complement_le_ennreal (n : ℕ) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (E τ m M b β s D : ℝ)
    {U : Set ℝ} (hU : IsClosed U) (hs : 0 < s) (hD : 0 < D) :
    ENNReal.ofReal (∫ J, originalBandComplementMass μ Q m M b β U J
      ∂disorderLaw (n+2) μ.maxDegree) ≤
    ENNReal.ofReal (∫ J, originalCoarseBandComplementMass n μ Q E τ b β U J
      ∂disorderLaw (n+2) μ.maxDegree) +
    disorderLaw (n+2) μ.maxDegree {J | m+M < sourceSphereMaximum n μ Q J} +
    disorderLaw (n+2) μ.maxDegree {J | mixturePartition μ β J < s*D} +
    (∫⁻ J, originalLowBandPartitionSum n μ Q E τ m M b β U J
      ∂disorderLaw (n+2) μ.maxDegree) / ENNReal.ofReal (s*D) := by
  by_cases ht : (∫⁻ J, originalLowBandPartitionSum n μ Q E τ m M b β U J
      ∂disorderLaw (n+2) μ.maxDegree) = ⊤
  · simp [ht, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
  have hc : 0 ≤ ∫ J, originalCoarseBandComplementMass n μ Q E τ b β U J
      ∂disorderLaw (n+2) μ.maxDegree := integral_nonneg fun _ => measureReal_nonneg
  have hh := ENNReal.ofReal_le_ofReal
    (original_expected_band_complement_le n μ hQ E τ m M b β s D hU hs hD ht)
  rw [ENNReal.ofReal_add (add_nonneg (add_nonneg hc measureReal_nonneg) measureReal_nonneg)
      (div_nonneg ENNReal.toReal_nonneg (mul_pos hs hD).le),
    ENNReal.ofReal_add (add_nonneg hc measureReal_nonneg) measureReal_nonneg,
    ENNReal.ofReal_add hc measureReal_nonneg,
    ofReal_measureReal, ofReal_measureReal, ENNReal.ofReal_div_of_pos (mul_pos hs hD),
    ENNReal.ofReal_toReal ht] at hh
  exact hh

private theorem iterated_limit
    (f : ℝ → ℕ → ℝ) (c : ℕ → ℝ) (p : ℝ → ℕ → ℝ)
    (q : ℝ → ℕ → ℝ) (w : ℝ → ℕ → ℝ≥0∞)
    (hf : ∀ M n, f M n ∈ Icc 0 1)
    (hp : ∀ M n, p M n ≤ 1) (hq : ∀ s n, q s n ≤ 1)
    (hbound : ∀ M s : ℝ, 0 < M → 0 < s → ∀ n,
      ENNReal.ofReal (f M n) ≤ ENNReal.ofReal (c n) + ENNReal.ofReal (p M n) +
        ENNReal.ofReal (q s n) + w M n / ENNReal.ofReal s)
    (hc : Tendsto c atTop (𝓝 0))
    (hupper : Tendsto (fun M => limsup (p M) atTop) atTop (𝓝 0))
    (hden : Tendsto (fun s => limsup (q s) atTop) (𝓝[>] 0) (𝓝 0))
    (C a : ℝ) (ha : 0 < a)
    (hlow : ∀ M : ℝ, 0 < M →
      limsup (w M) atTop ≤ ENNReal.ofReal (C * Real.exp (-a*M))) :
    Tendsto (fun M => limsup (f M) atTop) atTop (𝓝 0) := by
  have hnonneg (M : ℝ) : 0 ≤ limsup (f M) atTop := by
    have hh := limsup_le_limsup (.of_forall fun n => (hf M n).1)
      (isCoboundedUnder_le_of_le atTop fun _ : ℕ => le_rfl (a := (0 : ℝ)))
      (isBoundedUnder_of ⟨1,fun n => (hf M n).2⟩)
    simpa only [limsup_const] using hh
  apply tendsto_order.mpr
  constructor
  · intro z hz
    exact .of_forall fun M => hz.trans_le (hnonneg M)
  · intro ε hε
    have hpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < s := self_mem_nhdsWithin
    obtain ⟨s,hs,hqs⟩ := (hpos.and
      (hden.eventually (gt_mem_nhds (show 0 < ε/16 by positivity)))).exists
    have hqe : ∀ᶠ n : ℕ in atTop, q s n < ε/8 :=
      eventually_lt_of_limsup_lt (hqs.trans (by linarith))
        (isBoundedUnder_of ⟨1,hq s⟩)
    have hexp : Tendsto (fun M : ℝ => C * Real.exp (-a*M)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,id_eq,mul_zero,neg_mul] using
        (Real.tendsto_exp_neg_atTop_nhds_zero.comp
          (tendsto_id.const_mul_atTop ha)).const_mul C
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      hupper.eventually (gt_mem_nhds (show 0 < ε/16 by positivity)),
      hexp.eventually (gt_mem_nhds (show 0 < s*(ε/16) by positivity))] with M hM hpm hwm
    have hpe : ∀ᶠ n : ℕ in atTop, p M n < ε/8 :=
      eventually_lt_of_limsup_lt (hpm.trans (by linarith))
        (isBoundedUnder_of ⟨1,hp M⟩)
    have hwe : ∀ᶠ n : ℕ in atTop, w M n < ENNReal.ofReal (s*(ε/8)) := by
      refine eventually_lt_of_limsup_lt ?_ (isBoundedUnder_of ⟨⊤,fun _ => le_top⟩)
      apply (hlow M hM).trans_lt
      apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
      exact hwm.trans (by nlinarith)
    have hfe : ∀ᶠ n : ℕ in atTop, f M n ≤ ε/2 := by
      filter_upwards [hc.eventually (gt_mem_nhds (show 0 < ε/8 by positivity)),
        hpe,hqe,hwe] with n hcn hpn hqn hwn
      have hwdiv : w M n / ENNReal.ofReal s ≤ ENNReal.ofReal (ε/8) := by
        calc
          _ ≤ ENNReal.ofReal (s*(ε/8)) / ENNReal.ofReal s :=
            ENNReal.div_le_div_right hwn.le _
          _ = _ := by rw [← ENNReal.ofReal_div_of_pos hs, mul_div_cancel_left₀ _ hs.ne']
      have hh := (hbound M s hM hs n).trans
        (add_le_add (add_le_add (add_le_add (ENNReal.ofReal_le_ofReal hcn.le)
          (ENNReal.ofReal_le_ofReal hpn.le)) (ENNReal.ofReal_le_ofReal hqn.le)) hwdiv)
      have heq : ENNReal.ofReal (ε/8) + ENNReal.ofReal (ε/8) +
          ENNReal.ofReal (ε/8) + ENNReal.ofReal (ε/8) = ENNReal.ofReal (ε/2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
      rw [heq] at hh
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hh
    exact (limsup_le_of_le
      (isCoboundedUnder_le_of_le atTop fun n => (hf M n).1) hfe).trans_lt (by linarith)

/-- Source fixed-window capture from general common-witness inputs. The
normalized low-sum estimate is an extended limsup, allowing exceptional
infinite expectations at finitely many dimensions. The limits are taken in
the source order: dimension, window width, then positive denominator cutoff. -/
theorem original_fixed_window_capture_of_inputs
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (E τ b β : ℝ)
    {U : Set ℝ} (hU : IsClosed U) (m D : ℕ → ℝ) (hD : ∀ n, 0 < D n)
    (hcoarse : Tendsto (fun n =>
      ∫ J, originalCoarseBandComplementMass n μ Q E τ b β U J
        ∂disorderLaw (n+2) μ.maxDegree) atTop (𝓝 0))
    (hupper : Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
      (disorderLaw (n+2) μ.maxDegree).real
        {J | m n+M < sourceSphereMaximum n μ Q J}) atTop) atTop (𝓝 0))
    (hden : Tendsto (fun s : ℝ => limsup (fun n : ℕ =>
      (disorderLaw (n+2) μ.maxDegree).real
        {J | mixturePartition μ β J < s*D n}) atTop) (𝓝[>] 0) (𝓝 0))
    (C a : ℝ) (ha : 0 < a)
    (hlow : ∀ M : ℝ, 0 < M → limsup (fun n : ℕ =>
      (∫⁻ J, originalLowBandPartitionSum n μ Q E τ (m n) M b β U J
        ∂disorderLaw (n+2) μ.maxDegree) / ENNReal.ofReal (D n)) atTop ≤
      ENNReal.ofReal (C * Real.exp (-a*M))) :
    Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
      ∫ J, originalBandComplementMass μ Q (m n) M b β U J
        ∂disorderLaw (n+2) μ.maxDegree) atTop) atTop (𝓝 0) := by
  apply iterated_limit _ _ _ _ _ _ _ _ _ hcoarse hupper hden C a ha hlow
  · intro M n
    constructor
    · exact integral_nonneg fun J =>
        (originalBandComplementMass_mem_unit (by omega : 1 ≤ n+2) μ Q (m n) M b β U J).1
    · exact (integral_mono
        (originalBandComplementMass_integrable (by omega : 1 ≤ n+2) μ Q (m n) M b β hU)
        (integrable_const 1) fun J =>
          (originalBandComplementMass_mem_unit (by omega : 1 ≤ n+2) μ Q (m n) M b β U J).2).trans
        (by simp)
  · intro M n
    exact measureReal_le_one
  · intro s n
    exact measureReal_le_one
  · intro M s _hM hs n
    have hh := original_expected_band_complement_le_ennreal
      n μ hQ E τ (m n) M b β s (D n) hU hs (hD n)
    rw [← ofReal_measureReal, ← ofReal_measureReal] at hh
    convert hh using 1
    rw [ENNReal.ofReal_mul hs.le]
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_inv (.inr ENNReal.ofReal_ne_top) (.inl ENNReal.ofReal_ne_top)]
    ac_rfl

/-- The conditional count-and-capture interface for the later common-witness
assembly. Counts are carried on exactly `U`; no radial enlargement is used. -/
theorem original_fixed_window_counts_and_capture_of_inputs
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (E τ b β : ℝ)
    {U : Set ℝ} (hU : IsClosed U) (m D : ℕ → ℝ) (hD : ∀ n, 0 < D n)
    (hcount : ∀ M : ℝ, 0 < M →
      limsup (originalWindowExpectedCount μ Q m M U) atTop < ⊤)
    (hcoarse : Tendsto (fun n =>
      ∫ J, originalCoarseBandComplementMass n μ Q E τ b β U J
        ∂disorderLaw (n+2) μ.maxDegree) atTop (𝓝 0))
    (hupper : Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
      (disorderLaw (n+2) μ.maxDegree).real
        {J | m n+M < sourceSphereMaximum n μ Q J}) atTop) atTop (𝓝 0))
    (hden : Tendsto (fun s : ℝ => limsup (fun n : ℕ =>
      (disorderLaw (n+2) μ.maxDegree).real
        {J | mixturePartition μ β J < s*D n}) atTop) (𝓝[>] 0) (𝓝 0))
    (C a : ℝ) (ha : 0 < a)
    (hlow : ∀ M : ℝ, 0 < M → limsup (fun n : ℕ =>
      (∫⁻ J, originalLowBandPartitionSum n μ Q E τ (m n) M b β U J
        ∂disorderLaw (n+2) μ.maxDegree) / ENNReal.ofReal (D n)) atTop ≤
      ENNReal.ofReal (C * Real.exp (-a*M))) :
    (∀ M : ℝ, 0 < M →
      limsup (originalWindowExpectedCount μ Q m M U) atTop < ⊤) ∧
    Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
      ∫ J, originalBandComplementMass μ Q (m n) M b β U J
        ∂disorderLaw (n+2) μ.maxDegree) atTop) atTop (𝓝 0) := by
  exact ⟨hcount, original_fixed_window_capture_of_inputs
    μ hQ E τ b β hU m D hD hcoarse hupper hden C a ha hlow⟩

end SlowEquilibration.SourceReductionFiniteWindowCapture
