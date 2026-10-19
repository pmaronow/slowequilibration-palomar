-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionConsumerTVBound
public import SlowEquilibration.SourceReductionWeightedFiberBorel
public import SlowEquilibration.SourceReductionOpenWindowPathMeasurable
public import SlowEquilibration.SphericalGibbsKernel
public import SlowEquilibration.SphericalInitialRotation
public import SlowEquilibration.SphericalHaarTransfer
public import SlowEquilibration.VaryingSeparation
public import SlowEquilibration.VaryingProbability

/-! The literal original-disorder consumer implication. The bounded true
path probability transfers the extended weighted-score limit to the physical
all-time total-variation conclusion, with the source iterated capture limit. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceReductionConsumerAsymptotic

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalRotationCovariance
open SourceReductionClosedBandGraph SourceReductionClosedPathUnionGraph
open SourceReductionConsumerBandBound SourceReductionBandCapGeometry
open SourceReductionEvolvedCapMass SourceReductionPathMarginal
open SourceReductionWeightedCenterScore SourceReductionClosedScoreBound
open SourceReductionOpenWindowPathMeasurable
open SphericalKacRiceHittingSource SphericalRealTimePathKernel SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

variable {N : ℕ}

/-- Actual Gibbs mass missed by the original critical-center band union. -/
def originalBandComplementMass (μ : FiniteMixture) (Q m M b β : ℝ)
    (U : Set ℝ) (J : Disorder N μ.maxDegree) : ℝ :=
  (mixtureGibbsLaw μ β J).real (ambientWindowBandUnion μ Q m M b U J)ᶜ

theorem originalBandComplementMass_measurable (hN : 1 ≤ N)
    (μ : FiniteMixture) (Q m M b β : ℝ) {U : Set ℝ} (hU : IsClosed U) :
    Measurable (originalBandComplementMass (N := N) μ Q m M b β U) := by
  have hgraph := (physicalSphereBandUnionGraph_isClosed
    (N := N) μ Q m M b hU).measurableSet.compl
  have hm := (Kernel.measurable_kernel_prodMk_left
    (κ := disorderGibbsKernel hN (mixtureCoefficients μ) β) hgraph).ennreal_toReal
  convert hm using 1
  funext J
  rw [disorderGibbsKernel_apply]
  rfl

theorem originalBandComplementMass_mem_unit (hN : 1 ≤ N)
    (μ : FiniteMixture) (Q m M b β : ℝ) (U : Set ℝ)
    (J : Disorder N μ.maxDegree) :
    originalBandComplementMass μ Q m M b β U J ∈ Icc 0 1 := by
  let := mixtureGibbsLaw_probability hN μ β J
  exact ⟨measureReal_nonneg, measureReal_le_one⟩

theorem originalBandComplementMass_integrable (hN : 1 ≤ N)
    (μ : FiniteMixture) (Q m M b β : ℝ) {U : Set ℝ} (hU : IsClosed U) :
    Integrable (originalBandComplementMass (N := N) μ Q m M b β U)
      (disorderLaw N μ.maxDegree) := by
  apply Integrable.of_bound
    (originalBandComplementMass_measurable hN μ Q m M b β hU).aestronglyMeasurable 1
  exact .of_forall fun J => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (originalBandComplementMass_mem_unit hN μ Q m M b β U J).1]
    exact (originalBandComplementMass_mem_unit hN μ Q m M b β U J).2

theorem original_path_probability_integrable (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M a β : ℝ) {U : Set ℝ}
    (hU : IsClosed U) (T : ℝ≥0) :
    Integrable (actualWindowPathHitProbability hN μ Q m M a β U T)
      (disorderLaw N μ.maxDegree) := by
  apply Integrable.of_bound
    (actualWindowPathHitProbability_measurable hN μ Q m M a β hU T).aestronglyMeasurable 1
  exact .of_forall fun J => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (actualWindowPathHitProbability_mem_unit hN μ Q m M a β U T J).1]
    exact (actualWindowPathHitProbability_mem_unit hN μ Q m M a β U T J).2

theorem original_path_mean_le_weighted_score (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M a β : ℝ) {U : Set ℝ}
    (hU : IsClosed U) (T : ℝ≥0) :
    ENNReal.ofReal (∫ J, actualWindowPathHitProbability hN μ Q m M a β U T J
      ∂disorderLaw N μ.maxDegree) ≤
      ∫⁻ J, actualWindowCenterWeightedHitSum μ Q m M a β U T J
        ∂disorderLaw N μ.maxDegree := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (original_path_probability_integrable hN μ Q m M a β hU T)
    (.of_forall fun J =>
      (actualWindowPathHitProbability_mem_unit hN μ Q m M a β U T J).1)]
  exact lintegral_mono fun J =>
    actualWindowPathHitProbability_le_weightedScore hN μ Q m M a β U T J

/-- All fields, including infinite critical fibers, satisfy this finite
path-probability version of the consumer test. -/
theorem original_consumer_tv_lower_path (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M b a β : ℝ) {U : Set ℝ}
    (hU : IsClosed U) (T : ℝ≥0) (J : Disorder N μ.maxDegree)
    (t : RealPathTime T) (ha : a < Real.sqrt Q-b) :
    1-originalBandComplementMass μ Q m M b β U J-
      actualWindowPathHitProbability hN μ Q m M a β U T J ≤
      totalVariation (mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N)
        (mixtureGibbsLaw μ β J) := by
  let := sphereLaw_probability N
  let := mixtureGibbsLaw_probability (by omega : 1 ≤ N) μ β J
  have hband := measureReal_mono
    (μ := mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N)
    (physicalSphereBandUnion_subset_pointCapUnion μ Q m M b a U J ha)
  change (mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N).real
      (ambientWindowBandUnion μ Q m M b U J) ≤ _ at hband
  have hpath := evolved_pointCap_le_pathHit hN μ Q m M a β hU T J t
  have hsep := separation_from_event
    (mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N)
    (mixtureGibbsLaw μ β J)
    (ambientWindowBandUnion_isClosed μ Q m M b hU J).measurableSet
  change 1-(mixtureGibbsLaw μ β J).real
    (ambientWindowBandUnion μ Q m M b U J)ᶜ- _ ≤ _
  linarith

/-- The literal infimum over the complete physical time interval. -/
def originalUniformIntervalDistance (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) : ℝ :=
  sInf ((fun t : ℝ => totalVariation
    (mixedTransitionKernel μ J β t.toNNReal ∘ₘ sphereLaw N)
    (mixtureGibbsLaw μ β J)) '' Icc 0 (T : ℝ))

theorem originalUniformIntervalDistance_eq_endpoint (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) (J : Disorder N μ.maxDegree) :
    originalUniformIntervalDistance μ β T J =
      totalVariation (mixedTransitionKernel μ J β T ∘ₘ sphereLaw N)
        (mixtureGibbsLaw μ β J) := by
  let := sphereLaw_probability N
  simpa only [originalUniformIntervalDistance, Real.toNNReal_coe] using
    mixed_totalVariation_endpoint_infimum hN μ J β (sphereLaw N) T.coe_nonneg

theorem originalUniformIntervalDistance_measurable (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0) :
    Measurable (originalUniformIntervalDistance (N := N) μ β T) := by
  have heq : originalUniformIntervalDistance (N := N) μ β T =
      fun J => SphericalOrthogonalHaar.distance μ β T J
        (SphericalOrthogonalHaar.uniformInitialProbability N) := by
    funext J
    rw [originalUniformIntervalDistance_eq_endpoint hN]
    unfold SphericalOrthogonalHaar.distance SphericalOrthogonalHaar.uniformInitialProbability
    rfl
  rw [heq]
  exact SphericalOrthogonalHaar.distance_field_measurable hN μ β T _

/-- The exact time supremum of the original evolved band mass. -/
def originalBandTimeSup (μ : FiniteMixture) (Q m M b β : ℝ)
    (U : Set ℝ) (T : ℝ≥0) (J : Disorder N μ.maxDegree) : ℝ :=
  sSup {r : ℝ | ∃ t : RealPathTime T,
    r = (mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N).real
      (ambientWindowBandUnion μ Q m M b U J)}

theorem originalBandTimeSup_le_path_probability (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M b a β : ℝ) {U : Set ℝ}
    (hU : IsClosed U) (T : ℝ≥0) (J : Disorder N μ.maxDegree)
    (ha : a < Real.sqrt Q-b) :
    originalBandTimeSup μ Q m M b β U T J ≤
      actualWindowPathHitProbability hN μ Q m M a β U T J := by
  apply csSup_le
  · let t₀ : RealPathTime T := ⟨0,⟨le_rfl,T.coe_nonneg⟩⟩
    exact ⟨_,t₀,rfl⟩
  · rintro r ⟨t,rfl⟩
    exact (measureReal_mono
      (μ := mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N)
      (physicalSphereBandUnion_subset_pointCapUnion μ Q m M b a U J ha)).trans
      (evolved_pointCap_le_pathHit hN μ Q m M a β hU T J t)

/-- First all-disorder inequality in source `red-path-bound`. -/
theorem originalBandTimeSup_le_weighted_score (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M b a β : ℝ) {U : Set ℝ}
    (hU : IsClosed U) (T : ℝ≥0) (J : Disorder N μ.maxDegree)
    (ha : a < Real.sqrt Q-b) :
    ENNReal.ofReal (originalBandTimeSup μ Q m M b β U T J) ≤
      actualWindowCenterWeightedHitSum μ Q m M a β U T J :=
  (ENNReal.ofReal_le_ofReal
    (originalBandTimeSup_le_path_probability hN μ Q m M b a β hU T J ha)).trans
    (actualWindowPathHitProbability_le_weightedScore hN μ Q m M a β U T J)

/-- Second all-disorder source inequality, explicitly retaining the
infinite-score convention on exceptional critical fibers. -/
theorem original_consumer_interval_lower (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M b a β : ℝ) {U : Set ℝ}
    (hU : IsClosed U) (T : ℝ≥0) (J : Disorder N μ.maxDegree)
    (ha : a < Real.sqrt Q-b) :
    actualWindowCenterWeightedHitSum μ Q m M a β U T J = ⊤ ∨
      1-originalBandComplementMass μ Q m M b β U J-
        (actualWindowCenterWeightedHitSum μ Q m M a β U T J).toReal ≤
        originalUniformIntervalDistance μ β T J := by
  rw [originalUniformIntervalDistance_eq_endpoint (by omega)]
  let t : RealPathTime T := ⟨T,⟨T.coe_nonneg,le_rfl⟩⟩
  have ht : nnrealTime t = T := Subtype.ext rfl
  simpa only [originalBandComplementMass, ht] using
    SourceReductionConsumerTVBound.original_consumer_tv_lower
      hN μ Q m M b a β hU T J t ha

/-- Source `red-consumer` with its weighted-score conclusion as input.
The capture limit is the actual iterated source limit, and the same horizon
is used for every fixed window. -/
theorem source_red_consumer_of_expected_score_tendsto_zero
    (μ : FiniteMixture) (Q b a β : ℝ) {U : Set ℝ}
    (hU : IsClosed U) (m : ℕ → ℝ) (T : ℕ → ℝ≥0)
    (ha : a < Real.sqrt Q-b)
    (hcapture : Tendsto (fun M : ℝ => limsup (fun n : ℕ =>
      ∫ J, originalBandComplementMass μ Q (m n) M b β U J
        ∂disorderLaw (n+2) μ.maxDegree) atTop) atTop (𝓝 0))
    (hscore : ∀ M : ℝ, 0 < M → Tendsto (fun n : ℕ =>
      ∫⁻ J, actualWindowCenterWeightedHitSum μ Q (m n) M a β U (T n) J
        ∂disorderLaw (n+2) μ.maxDegree) atTop (𝓝 0)) :
    VaryingConvergesInProbability (fun n => disorderLaw (n+2) μ.maxDegree)
      (fun n => originalUniformIntervalDistance μ β (T n)) (fun _ _ => 1) := by
  let C (n : ℕ) (M : ℝ) := originalBandComplementMass
    (N := n+2) μ Q (m n) M b β U
  let E (n : ℕ) (M : ℝ) := actualWindowPathHitProbability
    (by omega : 2 ≤ n+2) μ Q (m n) M a β U (T n)
  have herr (M : ℝ) (hM : 0 < M) :
      VaryingConvergesInProbability (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => E n M) (fun _ _ => 0) := by
    have hmeanENN : Tendsto (fun n => ENNReal.ofReal
        (∫ J, E n M J ∂disorderLaw (n+2) μ.maxDegree)) atTop (𝓝 0) := by
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (hscore M hM) (.of_forall fun _ => zero_le)
        (.of_forall fun n => original_path_mean_le_weighted_score
          (by omega) μ Q (m n) M a β hU (T n))
    have hmean : Tendsto (fun n => ∫ J, E n M J
        ∂disorderLaw (n+2) μ.maxDegree) atTop (𝓝 0) := by
      have hh := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hmeanENN
      have hnonneg (n : ℕ) : 0 ≤ ∫ J, E n M J
          ∂disorderLaw (n+2) μ.maxDegree := integral_nonneg fun J =>
        (actualWindowPathHitProbability_mem_unit
          (by omega) μ Q (m n) M a β U (T n) J).1
      simpa only [Function.comp_def, ENNReal.toReal_zero,
        ENNReal.toReal_ofReal (hnonneg _)] using hh
    exact VaryingProbability.inProbability_zero_of_integral_tendsto_zero
      (fun n => disorderLaw (n+2) μ.maxDegree) (fun n => E n M)
      (fun n J => (actualWindowPathHitProbability_mem_unit
        (by omega) μ Q (m n) M a β U (T n) J).1)
      (fun n => original_path_probability_integrable
        (by omega) μ Q (m n) M a β hU (T n)) hmean
  apply varying_testing_band_union_of_iterated_limsup
    (fun n => disorderLaw (n+2) μ.maxDegree)
    (fun n => originalUniformIntervalDistance μ β (T n)) C E
  · intro n J
    rw [originalUniformIntervalDistance_eq_endpoint (by omega)]
    let := sphereLaw_probability (n+2)
    let := mixtureGibbsLaw_probability (by omega : 1 ≤ n+2) μ β J
    exact totalVariation_le_one _ _
  · intro n M hM J
    exact (originalBandComplementMass_mem_unit (by omega) μ Q (m n) M b β U J).1
  · intro n M hM J
    exact (originalBandComplementMass_mem_unit (by omega) μ Q (m n) M b β U J).2
  · intro n M hM J
    exact (actualWindowPathHitProbability_mem_unit
      (by omega) μ Q (m n) M a β U (T n) J).1
  · intro n M hM
    exact originalBandComplementMass_integrable (by omega) μ Q (m n) M b β hU
  · exact hcapture
  · exact herr
  · intro n M hM J
    rw [originalUniformIntervalDistance_eq_endpoint (by omega)]
    let t : RealPathTime (T n) := ⟨T n, ⟨(T n).coe_nonneg, le_rfl⟩⟩
    have ht : nnrealTime t = T n := Subtype.ext rfl
    simpa only [C, E, ht] using
      original_consumer_tv_lower_path (by omega) μ Q (m n) M b a β hU (T n) J t ha

end SlowEquilibration.SourceReductionConsumerAsymptotic
