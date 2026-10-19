-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LiteratureSubagTheorem10Proof
public import SlowEquilibration.SphericalGeneralReplicaBound

/-!
Further, partial reduction of Subag's Theorem 10. The bounded quenched
block cost is reduced to a precise lower-tail statement for the original
conditional Gibbs probabilities. Below the static threshold the existing
two-replica estimates prove this statement for every finite block, including
zero overlap, and hence prove the full forward interface in that range.

The low-temperature contact lower-tail statement remains a hypothesis of
the final reductions. This file does not claim to prove the full Theorem 10
or the physical TAP lower bound used in its published proof.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.LiteratureSubagTheorem10Final

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel CrisantiSommers CSParisiMeasure
open LiteratureSubagPhysicalDefinitions LiteratureSubagContact
open LiteratureSubagTheorem10Proof
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem block_measurable {N k : ℕ} (q ρ : ℝ) :
    MeasurableSet (overlapBlock (N := N) (k := k) q ρ) := by
  simp only [overlapBlock, Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    MeasurableSet.iInter fun _ => ?_
  exact (isOpen_lt (by unfold overlap; fun_prop) continuous_const).measurableSet

private theorem blockProbability_measurable (N k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) : Measurable (conditionalBlockProbability N k μ β q ρ) :=
  (Kernel.measurable_coe _ (block_measurable q ρ)).ennreal_toReal

private def normalizedBlockLog (N k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) (J : Disorder N μ.maxDegree) : ℝ :=
  Real.log (max (conditionalBlockProbability N k μ β q ρ J)
    (Real.exp (-(N : ℝ)))) / (N : ℝ)

private theorem normalizedBlockLog_bounds (N k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) (J : Disorder N μ.maxDegree) :
    -1 ≤ normalizedBlockLog N k μ β q ρ J ∧
      normalizedBlockLog N k μ β q ρ J ≤ 0 := by
  have ha := Real.exp_pos (-(N : ℝ))
  have ha1 : Real.exp (-(N : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N))
  have hlo := Real.log_le_log ha
    (le_max_right (conditionalBlockProbability N k μ β q ρ J) _)
  rw [Real.log_exp] at hlo
  have hhi : Real.log (max (conditionalBlockProbability N k μ β q ρ J)
      (Real.exp (-(N : ℝ)))) ≤ 0 :=
    Real.log_nonpos (ha.le.trans (le_max_right _ _))
      (max_le measureReal_le_one ha1)
  by_cases hN : N = 0
  · simp [normalizedBlockLog, hN]
  · have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    exact ⟨(le_div_iff₀ hNr).mpr (by simpa using hlo),
      div_nonpos_of_nonpos_of_nonneg hhi hNr.le⟩

private theorem normalizedBlockLog_integrable (N k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) :
    Integrable (normalizedBlockLog N k μ β q ρ) (disorderLaw N μ.maxDegree) := by
  refine (integrable_const (1 : ℝ)).mono' ?_ (.of_forall fun J => ?_)
  · exact ((((blockProbability_measurable N k μ β q ρ).max measurable_const).log).div_const
      (N : ℝ)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]
    exact abs_le.mpr (by
      have h := normalizedBlockLog_bounds N k μ β q ρ J
      constructor <;> linarith [h.1, h.2])

private theorem rate_eq_integral (N k : ℕ) (μ : FiniteMixture) (β q ρ : ℝ) :
    truncatedQuenchedBlockRate N k μ β q ρ =
      ∫ J, normalizedBlockLog N k μ β q ρ J ∂disorderLaw N μ.maxDegree := by
  simp only [normalizedBlockLog, integral_div, truncatedQuenchedBlockRate]

/-- The exponential floor makes the actual normalized quenched cost lie
in `[-1,0]`, in every dimension, without a contact assumption. -/
theorem truncatedQuenchedBlockRate_bounds (N k : ℕ) (μ : FiniteMixture)
    (β q ρ : ℝ) :
    -1 ≤ truncatedQuenchedBlockRate N k μ β q ρ ∧
      truncatedQuenchedBlockRate N k μ β q ρ ≤ 0 := by
  rw [rate_eq_integral]
  constructor
  · simpa using integral_mono (integrable_const (-1 : ℝ))
      (normalizedBlockLog_integrable N k μ β q ρ)
      (fun J => (normalizedBlockLog_bounds N k μ β q ρ J).1)
  · simpa using integral_nonpos (fun J => (normalizedBlockLog_bounds N k μ β q ρ J).2)

/-- The precise physical lower-tail probability still needed in the
low-temperature part of the published TAP argument. -/
def blockLowerTailProbability (N k : ℕ) (μ : FiniteMixture)
    (β q ρ ε : ℝ) : ℝ :=
  (disorderLaw N μ.maxDegree).real
    {J | conditionalBlockProbability N k μ β q ρ J < Real.exp (-ε * (N : ℝ))}

private theorem blockLowerTail_measurable (N k : ℕ) (μ : FiniteMixture)
    (β q ρ ε : ℝ) :
    MeasurableSet {J | conditionalBlockProbability N k μ β q ρ J <
      Real.exp (-ε * (N : ℝ))} :=
  measurableSet_lt (blockProbability_measurable N k μ β q ρ) measurable_const

/-- A finite-dimensional lower bound: a block with probability at least
`exp (-ε N)` outside a small disorder event has small truncated cost. -/
theorem truncatedQuenchedBlockRate_lower_bound {N : ℕ} (hN : 0 < N)
    (k : ℕ) (μ : FiniteMixture) (β q ρ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    -ε - blockLowerTailProbability N k μ β q ρ ε ≤
      truncatedQuenchedBlockRate N k μ β q ρ := by
  let d := disorderLaw N μ.maxDegree
  let B := {J | conditionalBlockProbability N k μ β q ρ J < Real.exp (-ε * (N : ℝ))}
  have hB : MeasurableSet B := blockLowerTail_measurable N k μ β q ρ ε
  have hi : Integrable (B.indicator (fun _ => (1 : ℝ))) d :=
    (integrable_const (1 : ℝ)).indicator hB
  have hp : ∀ J, -ε - B.indicator (fun _ => (1 : ℝ)) J ≤
      normalizedBlockLog N k μ β q ρ J := by
    intro J
    by_cases hJ : J ∈ B
    · rw [indicator_of_mem hJ]
      linarith [(normalizedBlockLog_bounds N k μ β q ρ J).1]
    · rw [indicator_of_notMem hJ, sub_zero]
      have hp : Real.exp (-ε * (N : ℝ)) ≤
          conditionalBlockProbability N k μ β q ρ J := le_of_not_gt hJ
      have hl := Real.log_le_log (Real.exp_pos (-ε * (N : ℝ)))
        (hp.trans (le_max_left _ (Real.exp (-(N : ℝ)))))
      rw [Real.log_exp] at hl
      exact (le_div_iff₀ (Nat.cast_pos.mpr hN)).mpr hl
  have hh := integral_mono ((integrable_const (-ε)).sub hi)
    (normalizedBlockLog_integrable N k μ β q ρ) hp
  change (∫ J, -ε - B.indicator (fun _ => (1 : ℝ)) J ∂d) ≤ _ at hh
  rw [integral_sub (integrable_const (-ε)) hi, integral_const,
    integral_indicator hB, setIntegral_const, probReal_univ, one_smul, smul_eq_mul,
    mul_one] at hh
  simpa only [rate_eq_integral, blockLowerTailProbability, d, B] using hh

/-- Vanishing physical lower tails imply the exact quenched limit in the
previous reduction, with no integrability or positivity premises omitted. -/
theorem truncatedQuenchedBlockRate_tendsto_of_lowerTail
    (k : ℕ) (μ : FiniteMixture) (β q ρ : ℝ)
    (hTail : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun N => blockLowerTailProbability N k μ β q ρ ε) atTop (𝓝 0)) :
    Tendsto (fun N => truncatedQuenchedBlockRate N k μ β q ρ) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have ht := (hTail (ε / 2) (half_pos hε)).eventually
    (gt_mem_nhds (half_pos hε))
  filter_upwards [ht, eventually_gt_atTop (0 : ℕ)] with N hNt hN
  have hlo := truncatedQuenchedBlockRate_lower_bound hN k μ β q ρ (half_pos hε).le
  have hhi := (truncatedQuenchedBlockRate_bounds N k μ β q ρ).2
  rw [Real.dist_eq, sub_zero, abs_of_nonpos hhi]
  linarith

/-- A single replica has no pair constraints; its cost vanishes identically. -/
theorem truncatedQuenchedBlockRate_one (N : ℕ) (μ : FiniteMixture) (β q ρ : ℝ) :
    truncatedQuenchedBlockRate N 1 μ β q ρ = 0 := by
  have hb : overlapBlock (N := N) (k := 1) q ρ = univ := by
    ext σ
    simp only [overlapBlock, mem_ofPred_eq, mem_univ, iff_true]
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  have hp (J : Disorder N μ.maxDegree) : conditionalBlockProbability N 1 μ β q ρ J = 1 := by
    simp only [conditionalBlockProbability, hb, probReal_univ]
  simp only [truncatedQuenchedBlockRate, hp,
    max_eq_left (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg N))),
    Real.log_one, integral_zero, zero_div]

private theorem overlapBlock_compl_le_pair {N k : ℕ}
    (ν : Measure (Vector N)) [IsProbabilityMeasure ν]
    {δ ρ : ℝ} (hδρ : δ ≤ ρ) :
    (Measure.pi (fun _ : Fin k => ν)).real (overlapBlock (N := N) (k := k) 0 ρ)ᶜ ≤
      (k : ℝ) ^ 2 * (ν.prod ν).real (absoluteReplicaOverlapEvent δ) := by
  classical
  let P := Measure.pi (fun _ : Fin k => ν)
  let B (ij : Fin k × Fin k) : Set (Fin k → Vector N) :=
    {σ | ij.1 ≠ ij.2 ∧ δ ≤ |overlap (σ ij.1) (σ ij.2)|}
  have hs : (overlapBlock (N := N) (k := k) 0 ρ)ᶜ ⊆ ⋃ ij, B ij := by
    intro σ hσ
    have hn : ¬ ∀ i j : Fin k, i ≠ j → |overlap (σ i) (σ j)| < ρ := by
      simpa only [overlapBlock, mem_compl_iff, mem_ofPred_eq, sub_zero] using hσ
    push Not at hn
    obtain ⟨i, j, hij, hbad⟩ := hn
    exact mem_iUnion.mpr ⟨(i, j), hij, hδρ.trans hbad⟩
  have hb (ij : Fin k × Fin k) :
      P.real (B ij) ≤ (ν.prod ν).real (absoluteReplicaOverlapEvent δ) := by
    by_cases hij : ij.1 = ij.2
    · have he : B ij = ∅ := by ext σ; simp [B, hij]
      rw [he, measureReal_empty]
      exact measureReal_nonneg
    · have hl := (GaussianReplicaKernel.pair_pi_hasLaw ν ij.1 ij.2 hij).measureReal_eq
        (absoluteReplicaOverlapEvent_measurable δ)
      have he : P.real (B ij) = (ν.prod ν).real (absoluteReplicaOverlapEvent δ) := by
        simpa [P, B, absoluteReplicaOverlapEvent, hij] using hl
      exact he.le
  calc
    _ ≤ P.real (⋃ ij, B ij) := measureReal_mono hs
    _ ≤ ∑ ij, P.real (B ij) := measureReal_iUnion_fintype_le B
    _ ≤ ∑ _ij : Fin k × Fin k, (ν.prod ν).real (absoluteReplicaOverlapEvent δ) :=
      Finset.sum_le_sum fun ij _ => hb ij
    _ = _ := by simp [pow_two]

private theorem exp_decay {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.exp (-c * (N : ℝ))) atTop (𝓝 0) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp (hcast.const_mul_atTop hc)
  exact hh.congr fun N => by simp only [Function.comp_apply, neg_mul]

/-- Below the static threshold all finite zero-overlap Gibbs blocks have
vanishing lower tails. This uses the literal two-replica estimate and a
finite union bound, without Chen or a TAP interface. -/
theorem zero_blockLowerTail_tendsto_of_lt_staticThreshold
    {μ : FiniteMixture} {β : ℝ} (hβ : 0 < β)
    (hβs : β < Thresholds.staticThreshold μ.xi)
    (k : ℕ) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    Tendsto (fun N => blockLowerTailProbability N k μ β 0 ρ ε) atTop (𝓝 0) := by
  let δ := min (ρ / 2) (1 / 2)
  have hδ : δ ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_min (half_pos hρ) (by norm_num),
      (min_le_right _ _).trans_lt (by norm_num)⟩
  have hδρ : δ ≤ ρ := (min_le_left _ _).trans (by linarith)
  obtain ⟨c, hc, hev⟩ := general_replica_overlap_eventually μ hβ hβs hδ
  have ht : Tendsto (fun N : ℕ => (k : ℝ) ^ 2 * (2 * Real.exp (-c * (N : ℝ))))
      atTop (𝓝 0) := by simpa using ((exp_decay hc).const_mul 2).const_mul ((k : ℝ) ^ 2)
  have hsmall := ht.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have heps := (exp_decay hε).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hbound : ∀ᶠ N : ℕ in atTop,
      blockLowerTailProbability N k μ β 0 ρ ε ≤ Real.exp (-c * (N : ℝ)) := by
    filter_upwards [hev, hsmall, heps, eventually_gt_atTop (0 : ℕ)] with N hN hs he hNp
    obtain ⟨Ω, _hΩ, hfail, hgood⟩ := hN
    apply le_trans ?_ hfail
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    intro J hJ hJΩ
    have hH := (fieldOfMixture_contDiff μ J).continuous
    let _ := gibbsLaw_probability (by omega : 1 ≤ N) β hH
    let ν := gibbsLaw N β (fieldOfMixture μ J)
    have hp := (overlapBlock_compl_le_pair (k := k) ν hδρ).trans
      (mul_le_mul_of_nonneg_left (hgood J hJΩ) (sq_nonneg (k : ℝ)))
    have hadd := measureReal_add_measureReal_compl (μ := Measure.pi (fun _ : Fin k => ν))
      (block_measurable (N := N) (k := k) 0 ρ)
    rw [probReal_univ] at hadd
    have hcond : conditionalBlockProbability N k μ β 0 ρ J =
        (Measure.pi (fun _ : Fin k => ν)).real (overlapBlock 0 ρ) := by
      rw [conditionalBlockProbability, GaussianReplicaKernel.iid_apply,
        allDimensionGibbsKernel_apply]
      rfl
    change conditionalBlockProbability N k μ β 0 ρ J < Real.exp (-ε * (N : ℝ)) at hJ
    rw [hcond] at hJ
    linarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (exp_decay hc)
    (.of_forall fun _ => measureReal_nonneg) hbound

/-- The exact previously outstanding rate, for every finite block and
every positive tolerance, throughout the strict high-temperature range. -/
theorem zero_truncatedQuenchedBlockRate_tendsto_of_lt_staticThreshold
    {μ : FiniteMixture} {β : ℝ} (hβ : 0 < β)
    (hβs : β < Thresholds.staticThreshold μ.xi)
    (k : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    Tendsto (fun N => truncatedQuenchedBlockRate N k μ β 0 ρ) atTop (𝓝 0) :=
  truncatedQuenchedBlockRate_tendsto_of_lowerTail k μ β 0 ρ
    (fun _ hε => zero_blockLowerTail_tendsto_of_lt_staticThreshold hβ hβs k hρ hε)

/-- In the strict high-temperature range the zero-overlap replicas are
multisamplable in exactly the repository's positivity-aware definition. -/
theorem zero_multiSamplable_of_lt_staticThreshold
    {μ : FiniteMixture} {β : ℝ} (hβ : 0 < β)
    (hβs : β < Thresholds.staticThreshold μ.xi) : MultiSamplable μ β 0 :=
  multiSamplable_of_truncatedQuenchedBlockRate (by norm_num)
    (fun k _ _ hρ => zero_truncatedQuenchedBlockRate_tendsto_of_lt_staticThreshold hβ hβs k hρ)

/-- Below the static threshold the only canonical contact is zero. -/
theorem contact_eq_zero_of_lt_staticThreshold
    {μ : FiniteMixture} {β q : ℝ} (hβ : 0 ≤ β)
    (hβs : β < Thresholds.staticThreshold μ.xi) (hc : Contact μ β q) : q = 0 := by
  have hz := (contact_iff_firstVariation_zero μ β q).mp hc
  rw [(canonicalMinimizer_law_eq_diracZero_iff μ hβ).mpr hβs.le] at hz
  by_contra hq
  have hqpos : 0 < q := lt_of_le_of_ne hc.1.1 (Ne.symm hq)
  exact (CSReplicaSymmetric.firstVariation_diracZero_neg_of_lt_staticThreshold
    μ hβ hβs ⟨hqpos, hc.1.2⟩).ne hz.2

/-- The full, unchanged forward Theorem 10 interface is proved below the
static threshold, including its zero contact. No literature premise remains. -/
theorem theorem10Forward_of_lt_staticThreshold
    {μ : FiniteMixture} {β : ℝ} (hβ : 0 < β)
    (hβs : β < Thresholds.staticThreshold μ.xi) : Theorem10Forward μ β := by
  refine ⟨hβ, ?_⟩
  intro q hc
  rw [contact_eq_zero_of_lt_staticThreshold hβ.le hβs hc]
  exact zero_multiSamplable_of_lt_staticThreshold hβ hβs

private theorem lowerTail_mul_le_neg_rate {N : ℕ} (hN : 0 < N)
    (k : ℕ) (μ : FiniteMixture) (β q ρ : ℝ) {ε : ℝ}
    (hε : ε ∈ Ioc (0 : ℝ) 1) :
    blockLowerTailProbability N k μ β q ρ ε * ε ≤
      -truncatedQuenchedBlockRate N k μ β q ρ := by
  let d := disorderLaw N μ.maxDegree
  let B := {J | conditionalBlockProbability N k μ β q ρ J < Real.exp (-ε * (N : ℝ))}
  have hB : MeasurableSet B := blockLowerTail_measurable N k μ β q ρ ε
  have hi : Integrable (B.indicator (fun _ => ε)) d :=
    (integrable_const ε).indicator hB
  have hp : ∀ J, B.indicator (fun _ => ε) J ≤ -normalizedBlockLog N k μ β q ρ J := by
    intro J
    by_cases hJ : J ∈ B
    · rw [indicator_of_mem hJ]
      have hf : Real.exp (-(N : ℝ)) ≤ Real.exp (-ε * (N : ℝ)) :=
        Real.exp_le_exp.mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) N, hε.2])
      have hmax : max (conditionalBlockProbability N k μ β q ρ J)
          (Real.exp (-(N : ℝ))) ≤ Real.exp (-ε * (N : ℝ)) := max_le (le_of_lt hJ) hf
      have hl := Real.log_le_log
        ((Real.exp_pos (-(N : ℝ))).trans_le (le_max_right
          (conditionalBlockProbability N k μ β q ρ J) _)) hmax
      rw [Real.log_exp] at hl
      have hd := (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr hl
      change Real.log _ / (N : ℝ) ≤ -ε at hd
      dsimp only [normalizedBlockLog]
      linarith
    · rw [indicator_of_notMem hJ]
      exact neg_nonneg.mpr (normalizedBlockLog_bounds N k μ β q ρ J).2
  have hh := integral_mono hi (normalizedBlockLog_integrable N k μ β q ρ).neg hp
  change (∫ J, B.indicator (fun _ => ε) J ∂d) ≤
    ∫ J, -normalizedBlockLog N k μ β q ρ J ∂d at hh
  rw [integral_indicator hB, setIntegral_const, smul_eq_mul, integral_neg] at hh
  simpa only [blockLowerTailProbability, rate_eq_integral, B, d] using hh

/-- The remaining lower-tail statement is equivalent to the exact rate
limit, rather than a weakening caused by truncating the logarithm. -/
theorem truncatedQuenchedBlockRate_tendsto_iff_lowerTail
    (k : ℕ) (μ : FiniteMixture) (β q ρ : ℝ) :
    Tendsto (fun N => truncatedQuenchedBlockRate N k μ β q ρ) atTop (𝓝 0) ↔
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun N => blockLowerTailProbability N k μ β q ρ ε) atTop (𝓝 0) := by
  constructor
  · intro hRate ε hε
    let η := min ε (1 / 2)
    have hη : η ∈ Ioc (0 : ℝ) 1 :=
      ⟨lt_min hε (by norm_num), (min_le_right _ _).trans (by norm_num)⟩
    have hb : ∀ᶠ N : ℕ in atTop, blockLowerTailProbability N k μ β q ρ ε ≤
        -truncatedQuenchedBlockRate N k μ β q ρ / η := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
      have hm : blockLowerTailProbability N k μ β q ρ ε ≤
          blockLowerTailProbability N k μ β q ρ η := by
        apply measureReal_mono (h₂ := measure_ne_top _ _)
        intro J hJ
        exact hJ.trans_le (Real.exp_le_exp.mpr (by
          have hηε : η ≤ ε := min_le_left _ _
          nlinarith [Nat.cast_nonneg (α := ℝ) N]))
      exact hm.trans ((le_div_iff₀ hη.1).mpr
        (lowerTail_mul_le_neg_rate hN k μ β q ρ hη))
    have hu : Tendsto (fun N => -truncatedQuenchedBlockRate N k μ β q ρ / η)
        atTop (𝓝 0) := by simpa using hRate.neg.div_const η
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (.of_forall fun _ => measureReal_nonneg) hb
  · exact truncatedQuenchedBlockRate_tendsto_of_lowerTail k μ β q ρ

/-- Further reduction of the unchanged forward interface. Only blocks
with at least two replicas, at or above the static threshold, remain.
The hypothesis still includes zero and all other canonical contacts. -/
theorem theorem10Forward_reduced2 {μ : FiniteMixture} {β : ℝ} (hβ : 0 < β)
    (hTail : Thresholds.staticThreshold μ.xi ≤ β →
      ∀ q : ℝ, Contact μ β q → ∀ k : ℕ, 2 ≤ k →
        ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε →
          Tendsto (fun N => blockLowerTailProbability N k μ β q ρ ε) atTop (𝓝 0)) :
    Theorem10Forward μ β := by
  by_cases hβs : β < Thresholds.staticThreshold μ.xi
  · exact theorem10Forward_of_lt_staticThreshold hβ hβs
  · apply theorem10Forward_of_contact_block_rate hβ
    intro q hc k hk ρ hρ
    by_cases hk1 : k = 1
    · simpa only [hk1, truncatedQuenchedBlockRate_one] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · exact truncatedQuenchedBlockRate_tendsto_of_lowerTail k μ β q ρ
        (hTail (le_of_not_gt hβs) q hc k (by omega) ρ hρ)

private theorem zero_rate_reduced2 {μ : FiniteMixture} {β : ℝ} (hβ : 0 < β)
    (hTail : Thresholds.staticThreshold μ.xi ≤ β →
      ∀ k : ℕ, 2 ≤ k → ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε →
        Tendsto (fun N => blockLowerTailProbability N k μ β 0 ρ ε) atTop (𝓝 0)) :
    ∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
      Tendsto (fun N => truncatedQuenchedBlockRate N k μ β 0 ρ) atTop (𝓝 0) := by
  intro k hk ρ hρ
  by_cases hβs : β < Thresholds.staticThreshold μ.xi
  · exact zero_truncatedQuenchedBlockRate_tendsto_of_lt_staticThreshold hβ hβs k hρ
  · by_cases hk1 : k = 1
    · simpa only [hk1, truncatedQuenchedBlockRate_one] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    · exact truncatedQuenchedBlockRate_tendsto_of_lowerTail k μ β 0 ρ
        (hTail (le_of_not_gt hβs) k (by omega) ρ hρ)

/-- The source TAP endpoint with the zero-rate premise discharged below
the static threshold and otherwise replaced by its exact physical lower tail. -/
theorem source_subag_tap_reduced2 {μ : FiniteMixture} {β : ℝ}
    (D : LiteratureSubagTAP.ThermodynamicData μ β)
    (h5 : LiteratureSubagTAP.Theorem5 D)
    (hTail : Thresholds.staticThreshold μ.xi ≤ β →
      ∀ k : ℕ, 2 ≤ k → ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε →
        Tendsto (fun N => blockLowerTailProbability N k μ β 0 ρ ε) atTop (𝓝 0))
    {q : ℝ} (hq : q ∈ Ico (0 : ℝ) 1) :
    SourceSubagReplicaCriterion.sourceTAPValue D q ≤ D.pressure ∧
      (D.pressure = SourceSubagReplicaCriterion.sourceTAPValue D q ↔
        MultiSamplable μ β q) :=
  source_subag_tap_reduced D h5 (zero_rate_reduced2 h5.1 hTail) hq

/-- The source replica criterion with only the low-temperature zero-block
lower tail remaining in place of the earlier zero-rate hypothesis. -/
theorem source_replica_criterion_reduced2 {μ : FiniteMixture} {β q : ℝ}
    (h25 : LiteratureSubagReplicaExclusion.Remark25Contrapositive μ β)
    (hTail : Thresholds.staticThreshold μ.xi ≤ β →
      ∀ k : ℕ, 2 ≤ k → ∀ ρ : ℝ, 0 < ρ → ∀ ε : ℝ, 0 < ε →
        Tendsto (fun N => blockLowerTailProbability N k μ β 0 ρ ε) atTop (𝓝 0))
    (hq : q ∈ Ico (0 : ℝ) 1) :
    (∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ →
      limsup (fun N : ℕ => SourceSubagReplicaCriterion.replicaLogRate N k μ β q ρ)
        atTop = 0) ↔ MultiSamplable μ β q :=
  source_replica_criterion_reduced h25 (zero_rate_reduced2 h25.1 hTail) hq

end SlowEquilibration.LiteratureSubagTheorem10Final
