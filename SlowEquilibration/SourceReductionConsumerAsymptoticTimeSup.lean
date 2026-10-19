-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceReductionConsumerAsymptotic
public import SlowEquilibration.SphericalL2Semigroup
public import SlowEquilibration.SphericalEqualMass

/-! Borel measurability and integrability of the exact physical time
supremum in source `cp-transfer`. Strong continuity of the constructed
Gibbs L² semigroup gives continuity of evolved masses from the uniform
initial law, including time zero. A countable dense set of times then
computes the literal supremum over the full time interval. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SourceReductionConsumerAsymptoticTimeSup

open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalReversibility
open SphericalRotationCovariance SphericalForm SphericalL2Semigroup
open SourceReductionConsumerAsymptotic SourceReductionPathMarginal
open SourceReductionConsumerBandBound SphericalRealTimePathKernel
open SourceReductionClosedBandGraph SourceReductionWeightedCenterScore
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1800000

variable {N : ℕ}

/-- Uniform sphere initialization is an L² density relative to actual
Gibbs measure. Therefore every Borel event has continuous evolved mass. -/
theorem uniform_evolved_mass_continuous (hN : 1 ≤ N)
    (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    {B : Set (Vector N)} (hB : MeasurableSet B) :
    Continuous (fun t : ℝ≥0 =>
      (mixedTransitionKernel μ J β t ∘ₘ sphereLaw N).real B) := by
  let := mixtureGibbsLaw_probability hN μ β J
  let H := fieldOfMixture μ J
  have hH : Continuous H := (fieldOfMixture_contDiff μ J).continuous
  let f : Vector N → ℝ := B.indicator (fun _ => 1)
  have hf : StronglyMeasurable f :=
    (measurable_const.indicator hB).stronglyMeasurable
  have hfLp : MemLp f 2 (mixtureGibbsLaw μ β J) :=
    MemLp.indicator hB (memLp_const (1 : ℝ))
  let F : Space μ J β := hfLp.toLp f
  let w : Vector N → ℝ := fun x => (gibbsDensity N β H x)⁻¹
  have hw : Continuous w := (gibbsDensity_continuous β hH).inv₀
    (fun x => ne_of_gt (gibbsDensity_pos hN β hH x))
  have hwLp : MemLp w 2 (mixtureGibbsLaw μ β J) :=
    (memLp_two_iff_integrable_sq hw.aestronglyMeasurable).mpr
      (integrable_gibbs_of_continuous hN β hH (hw.pow 2))
  let W : Space μ J β := hwLp.toLp w
  have heq (t : ℝ≥0) : inner ℝ W (P hN μ J β t F) =
      (mixedTransitionKernel μ J β t ∘ₘ sphereLaw N).real B := by
    calc
      _ = ∫ x, w x * mixedExpectation μ J β t f x
          ∂mixtureGibbsLaw μ β J := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hwLp.coeFn_toLp,
          P_ae_expectation hN μ J β t F hf hfLp.coeFn_toLp] with x hx hy
        simp only [W,hx,hy,RCLike.inner_apply,conj_trivial,mul_comm]
      _ = ∫ x, mixedExpectation μ J β t f x ∂sphereLaw N := by
        change (∫ x, w x * mixedExpectation μ J β t f x ∂gibbsLaw N β H) = _
        rw [integral_gibbsLaw hN β hH]
        apply integral_congr_ae
        exact .of_forall fun x => by
          dsimp only [w]
          rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt (gibbsDensity_pos hN β hH x)),one_mul]
      _ = ∫ x, eventMass μ β t (fun _ => B) (J,x) ∂sphereLaw N := by
        apply integral_congr_ae
        exact .of_forall fun x => by
          rw [mixedExpectation_eq_kernel μ J β t f hf x]
          simp only [f,integral_indicator_const (1 : ℝ) hB,smul_eq_mul,mul_one,eventMass]
      _ = _ := (evolved_eventMass_eq_integral μ β t (fun _ => B)
        (hB.preimage measurable_snd) J (sphereLaw N)).symm
  exact (continuous_const.inner (P_apply_continuous hN μ J β F)).congr heq

/-- At a fixed time the original disorder-dependent event mass is Borel. -/
theorem uniform_evolved_mass_measurable (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (B : Disorder N μ.maxDegree → Set (Vector N))
    (hB : MeasurableSet {q : Disorder N μ.maxDegree × Vector N | q.2 ∈ B q.1}) :
    Measurable (fun J : Disorder N μ.maxDegree =>
      (mixedTransitionKernel μ J β t ∘ₘ sphereLaw N).real (B J)) := by
  have hm : StronglyMeasurable (fun J : Disorder N μ.maxDegree =>
      ∫ x, eventMass μ β t B (J,x) ∂sphereLaw N) :=
    (eventMass_joint_measurable μ β t B hB).stronglyMeasurable.integral_prod_right'
  convert hm.measurable using 1
  funext J
  exact evolved_eventMass_eq_integral μ β t B hB J (sphereLaw N)

/-- A dense countable set computes the supremum of a bounded continuous
real function; this applies even when the time interval is a singleton. -/
theorem sSup_range_eq_dense_iSup {X : Type*} [TopologicalSpace X]
    (d : ℕ → X) (hd : DenseRange d) (f : X → ℝ) (hf : Continuous f)
    (hbound : BddAbove (range f)) :
    sSup (range f) = ⨆ k : ℕ, f (d k) := by
  have hdbound : BddAbove (range (fun k => f (d k))) :=
    hbound.mono (by rintro _ ⟨k,rfl⟩; exact ⟨d k,rfl⟩)
  apply le_antisymm
  · apply csSup_le (show (range f).Nonempty from ⟨f (d 0),d 0,rfl⟩)
    rintro _ ⟨t,rfl⟩
    exact hd.induction_on t (isClosed_le hf continuous_const)
      (fun k => le_ciSup hdbound k)
  · exact ciSup_le fun k => le_csSup hbound ⟨d k,rfl⟩

theorem originalBandTimeSup_mem_unit (μ : FiniteMixture)
    (Q m M b β : ℝ) (U : Set ℝ) (T : ℝ≥0) (J : Disorder N μ.maxDegree) :
    originalBandTimeSup μ Q m M b β U T J ∈ Icc 0 1 := by
  let := sphereLaw_probability N
  let t₀ : RealPathTime T := ⟨0,⟨le_rfl,T.coe_nonneg⟩⟩
  have hbounded : BddAbove {r : ℝ | ∃ t : RealPathTime T,
      r = (mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N).real
        (ambientWindowBandUnion μ Q m M b U J)} := by
    refine ⟨1,?_⟩
    rintro _ ⟨t,rfl⟩
    exact measureReal_le_one
  constructor
  · exact (measureReal_nonneg (μ := mixedTransitionKernel μ J β (nnrealTime t₀) ∘ₘ
      sphereLaw N)).trans (le_csSup hbounded ⟨t₀,rfl⟩)
  · exact csSup_le ⟨_,t₀,rfl⟩ (by rintro _ ⟨t,rfl⟩; exact measureReal_le_one)

theorem originalBandTimeSup_measurable (hN : 1 ≤ N)
    (μ : FiniteMixture) (Q m M b β : ℝ) {U : Set ℝ}
    (hU : IsClosed U) (T : ℝ≥0) :
    Measurable (originalBandTimeSup (N := N) μ Q m M b β U T) := by
  let : Nonempty (RealPathTime T) := ⟨⟨0,⟨le_rfl,T.coe_nonneg⟩⟩⟩
  let := sphereLaw_probability N
  let d := TopologicalSpace.denseSeq (RealPathTime T)
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq _
  let F (J : Disorder N μ.maxDegree) (t : RealPathTime T) :=
    (mixedTransitionKernel μ J β (nnrealTime t) ∘ₘ sphereLaw N).real
      (ambientWindowBandUnion μ Q m M b U J)
  have ht : Continuous (nnrealTime (T := T)) := by
    exact continuous_subtype_val.subtype_mk (fun t => t.property.1)
  have hF (J : Disorder N μ.maxDegree) : Continuous (F J) :=
    (uniform_evolved_mass_continuous hN μ J β
      (ambientWindowBandUnion_isClosed μ Q m M b hU J).measurableSet).comp ht
  have heq (J : Disorder N μ.maxDegree) :
      originalBandTimeSup μ Q m M b β U T J = ⨆ k : ℕ, F J (d k) := by
    have hset : {r : ℝ | ∃ t : RealPathTime T, r = F J t} = range (F J) := by
      ext r
      simp only [mem_ofPred_eq,mem_range,eq_comm]
    change sSup {r : ℝ | ∃ t : RealPathTime T, r = F J t} = _
    rw [hset]
    exact sSup_range_eq_dense_iSup d hd (F J) (hF J)
      ⟨1,by rintro _ ⟨t,rfl⟩; exact measureReal_le_one⟩
  have hm : Measurable (fun J : Disorder N μ.maxDegree => ⨆ k : ℕ, F J (d k)) := by
    apply Measurable.iSup
    intro k
    exact uniform_evolved_mass_measurable μ β (nnrealTime (d k))
      (ambientWindowBandUnion μ Q m M b U)
      (physicalSphereBandUnionGraph_isClosed (N := N) μ Q m M b hU).measurableSet
  convert hm using 1
  exact funext heq

theorem originalBandTimeSup_integrable (hN : 1 ≤ N)
    (μ : FiniteMixture) (Q m M b β : ℝ) {U : Set ℝ}
    (hU : IsClosed U) (T : ℝ≥0) :
    Integrable (originalBandTimeSup (N := N) μ Q m M b β U T)
      (disorderLaw N μ.maxDegree) := by
  apply Integrable.of_bound
    (originalBandTimeSup_measurable hN μ Q m M b β hU T).aestronglyMeasurable 1
  exact .of_forall fun J => by
    rw [Real.norm_eq_abs,abs_of_nonneg
      (originalBandTimeSup_mem_unit μ Q m M b β U T J).1]
    exact (originalBandTimeSup_mem_unit μ Q m M b β U T J).2

/-- The first displayed source CP inequality is an ordinary expectation
of the literal time supremum, with its measurability now proved. -/
theorem originalBandTimeSup_mean_le_weighted_score (hN : 2 ≤ N)
    (μ : FiniteMixture) (Q m M b a β : ℝ) {U : Set ℝ}
    (hU : IsClosed U) (T : ℝ≥0) (ha : a < Real.sqrt Q-b) :
    ENNReal.ofReal (∫ J, originalBandTimeSup μ Q m M b β U T J
      ∂disorderLaw N μ.maxDegree) ≤
      ∫⁻ J, actualWindowCenterWeightedHitSum μ Q m M a β U T J
        ∂disorderLaw N μ.maxDegree := by
  rw [ofReal_integral_eq_lintegral_ofReal
    (originalBandTimeSup_integrable (by omega) μ Q m M b β hU T)
    (.of_forall fun J => (originalBandTimeSup_mem_unit μ Q m M b β U T J).1)]
  exact lintegral_mono fun J =>
    originalBandTimeSup_le_weighted_score hN μ Q m M b a β hU T J ha

end SlowEquilibration.SourceReductionConsumerAsymptoticTimeSup
