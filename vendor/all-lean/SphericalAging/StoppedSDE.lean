module

public import SphericalAging.ClosedHitStopping

public section

/-! Actual integral-equation preservation under bounded stopping.
Fixed-time equations are first upgraded on a common full-measure event by
countable past sampling and continuity, so they may be evaluated at the
random stopping time. The stopped Brownian term is the proved operator.
-/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.StoppedSDE
open HardSphereDynamics VectorIto WeightedDriftSums StoppedVectorIto AdaptedContinuous
set_option maxHeartbeats 1200000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] in
theorem continuous_agreement_on_common_event (X Y : ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hX : ∀ᵐ ω ∂P, Continuous (fun t => X (min t T) ω))
    (hY : ∀ᵐ ω ∂P, Continuous (fun t => Y (min t T) ω))
    (hfixed : ∀ t, t ≤ T → X t =ᵐ[P] Y t) :
    ∀ᵐ ω ∂P, ∀ t, t ≤ T → X t ω = Y t ω := by
  have hg : ∀ᵐ ω ∂P, ∀ n k : ℕ, X (min (gridTime n k) T) ω = Y (min (gridTime n k) T) ω :=
    ae_all_iff.mpr (fun n => ae_all_iff.mpr (fun k => hfixed _ (min_le_right _ _)))
  filter_upwards [hX, hY, hg] with ω hcX hcY hg
  intro t ht
  have hlimX := hcX.continuousAt.tendsto.comp (tendsto_pastGrid t)
  have hlimY := hcY.continuousAt.tendsto.comp (tendsto_pastGrid t)
  have he : (fun n => X (min (pastGrid t n) T) ω) = fun n => Y (min (pastGrid t n) T) ω := by
    funext n
    exact hg n ⌊t * (n+1)⌋₊
  have hlimX' : Tendsto (fun n => X (min (pastGrid t n) T) ω) atTop (𝓝 (X t ω)) := by
    simpa only [Function.comp_def, min_eq_left ht] using hlimX
  have hlimY' : Tendsto (fun n => Y (min (pastGrid t n) T) ω) atTop (𝓝 (Y t ω)) := by
    simpa only [Function.comp_def, min_eq_left ht] using hlimY
  rw [he] at hlimX'
  exact tendsto_nhds_unique hlimX' hlimY'

omit [MeasurableSpace Ω] in
lemma continuous_integratedDrift_clipped (μ : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω)
    (hμ : IntegrableOn (fun s => μ s ω) (Ioc 0 T) nonnegativeLebesgueMeasure) :
    Continuous (fun t => integratedDrift μ (min t T) ω) := by
  have hi := continuousOn_nnrealIntegralPrimitive
    ((integrableOn_nonnegative_iff_real (fun s => μ s ω) T).mp hμ)
  have hc := hi.comp_continuous (continuous_id.min continuous_const)
    (fun t => (show min t T ∈ Icc (0 : ℝ≥0) T from ⟨bot_le, min_le_right _ _⟩))
  exact hc

omit [IsProbabilityMeasure P] in
lemma stoppedIntegrand_timeRestrict {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0))) (T : ℝ≥0)
    (U : PredictableProcessL2 𝓕 P) (t : ℝ≥0) :
    FourPapersCommon.FilteredBrownian.predictableTimeRestrict 𝓕 t (stoppedIntegrand hτ T U) =
      stoppedIntegrand (τ := fun ω => min t (τ ω)) (by
        simpa only [← WithTop.coe_min] using (isStoppingTime_const 𝓕 t).min hτ) T U := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn 𝓕 t
      (stoppedIntegrand hτ T U), stoppedIntegrand_coe hτ T U,
    stoppedIntegrand_coe (τ := fun ω => min t (τ ω)) (by simpa only [← WithTop.coe_min] using (isStoppingTime_const 𝓕 t).min hτ) T U]
    with p hcut hstop hnew
  rw [hcut, hnew]
  unfold FourPapersCommon.FilteredBrownian.predictableTimeFrame
  by_cases ht : p.1 ∈ Ioc (0 : ℝ≥0) t
  · rw [indicator_of_mem (show p ∈ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) from ⟨ht, mem_univ _⟩), hstop]
    unfold stoppedTimeCoefficient
    have he : p.1 ∈ Ioc 0 T ∧ p.1 ≤ min t (τ p.2) ↔ p.1 ∈ Ioc 0 T ∧ p.1 ≤ τ p.2 := by
      simp only [le_min_iff, ht.2, true_and]
    simp only [he]
  · rw [indicator_of_notMem (show p ∉ Ioc (0 : ℝ≥0) t ×ˢ (univ : Set Ω) from fun h => ht h.1)]
    have hnew0 : ¬(p.1 ∈ Ioc (0 : ℝ≥0) T ∧ p.1 ≤ min t (τ p.2)) := by
      rintro ⟨hp, hh⟩
      exact ht ⟨hp.1, hh.trans (min_le_left _ _)⟩
    simp only [stoppedTimeCoefficient, hnew0, ite_false, zero_mul]

@[expose] def stoppedDrift (μ : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun s ω => if s ≤ τ ω then μ s ω else 0

lemma stoppedDrift_integral (μ : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0) (t : ℝ≥0) (ω : Ω) :
    integratedDrift (stoppedDrift μ τ) t ω = integratedDrift μ (min t (τ ω)) ω := by
  rw [← driftPrimitive_eq_integratedDrift, ← driftPrimitive_eq_integratedDrift]
  unfold driftPrimitive
  rw [← integral_indicator measurableSet_Ioc, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  exact .of_forall (fun s => by
    have he : s ∈ Ioc (0 : ℝ≥0) t ∧ s ≤ τ ω ↔ s ∈ Ioc 0 (min t (τ ω)) := by
      simp only [mem_Ioc, le_min_iff, and_assoc]
    by_cases hs : s ∈ Ioc (0 : ℝ≥0) t
    · by_cases hτs : s ≤ τ ω
      · simp only [indicator_of_mem hs, indicator_of_mem (he.mp ⟨hs, hτs⟩), stoppedDrift, hτs, ite_true]
      · have hm : s ∉ Ioc (0 : ℝ≥0) (min t (τ ω)) := fun hm => hτs (he.mpr hm).2
        simp only [indicator_of_mem hs, indicator_of_notMem hm, stoppedDrift, hτs, ite_false]
    · have hm : s ∉ Ioc (0 : ℝ≥0) (min t (τ ω)) := fun hm => hs (he.mpr hm).1
      simp only [indicator_of_notMem hs, indicator_of_notMem hm])

theorem vector_stopped_process_ae (D : BrownianDriver N P 𝓕)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) (U : Fin N → PredictableProcessL2 𝓕 P)
    (M : ℝ≥0 → Ω → ℝ) (hM : ∀ s, vectorProcess D U s =ᵐ[P] M s)
    (hcts : ∀ᵐ ω ∂P, Continuous (fun s => M s ω)) (t : ℝ≥0) :
    vectorProcess D (fun i => stoppedIntegrand hτ T (U i)) t =ᵐ[P]
      fun ω => M (min t (τ ω)) ω - M 0 ω := by
  have hτ' : IsStoppingTime 𝓕 (fun ω => (min t (τ ω) : WithTop ℝ≥0)) := by
    simpa only [← WithTop.coe_min] using (isStoppingTime_const 𝓕 t).min hτ
  have hcoef : vectorProcessLp D (fun i => stoppedIntegrand hτ T (U i)) t =
      vectorIto D (fun i => stoppedIntegrand hτ' T (U i)) := by
    unfold vectorProcessLp
    congr 1
    funext i
    exact stoppedIntegrand_timeRestrict hτ T (U i) t
  have hstop := vector_stopped_integral D hτ' T
    (fun ω => (min_le_right t (τ ω)).trans (hbound ω)) U M hM hcts
  rw [← hcoef] at hstop
  exact (vectorProcessLp_ae_eq D (fun i => stoppedIntegrand hτ T (U i)) t).symm.trans hstop

/-- A faithful fixed-time SDE equation with a genuinely realized
continuous noise modification yields the actual stopped SDE equation.
The random-time substitution is proved from continuity and countable past
agreement; it is not a premise. -/
theorem stopped_equation (D : BrownianDriver N P 𝓕)
    {τ : Ω → ℝ≥0} (hτ : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbound : ∀ ω, τ ω ≤ T) (U : Fin N → PredictableProcessL2 𝓕 P)
    (X μ M : ℝ≥0 → Ω → ℝ)
    (hXc : ∀ ω, Continuous (fun s => X s ω))
    (hμint : ∀ ω, IntegrableOn (fun s => μ s ω) (Ioc 0 T) nonnegativeLebesgueMeasure)
    (hM : ∀ s, vectorProcess D U s =ᵐ[P] M s)
    (hMc : ∀ᵐ ω ∂P, Continuous (fun s => M s ω))
    (hfixed : ∀ s, s ≤ T → X s =ᵐ[P] fun ω => X 0 ω + integratedDrift μ s ω + M s ω)
    (t : ℝ≥0) :
    (fun ω => X (min t (τ ω)) ω) =ᵐ[P] fun ω => X 0 ω +
      integratedDrift (stoppedDrift μ τ) t ω +
      vectorProcess D (fun i => stoppedIntegrand hτ T (U i)) t ω := by
  have hYc : ∀ᵐ ω ∂P, Continuous (fun s =>
      X 0 ω + integratedDrift μ (min s T) ω + M (min s T) ω) := by
    filter_upwards [hMc] with ω hc
    exact (continuous_const.add (continuous_integratedDrift_clipped μ T ω (hμint ω))).add
      (hc.comp (continuous_id.min continuous_const))
  have hcommon := continuous_agreement_on_common_event X
    (fun s ω => X 0 ω + integratedDrift μ s ω + M s ω) T
    (.of_forall (fun ω => (hXc ω).comp (continuous_id.min continuous_const))) hYc hfixed
  have hnoise := vector_stopped_process_ae D hτ T hbound U M hM hMc t
  have hM0 : M 0 =ᵐ[P] fun _ => 0 := by
    filter_upwards [hfixed 0 bot_le] with ω hω
    have hzero : integratedDrift μ 0 ω = 0 := by
      rw [← driftPrimitive_eq_integratedDrift]
      simp only [driftPrimitive, Ioc_self, Measure.restrict_empty, integral_zero_measure]
    rw [hzero] at hω
    linarith
  filter_upwards [hcommon, hnoise, hM0] with ω hω hN h0
  rw [stoppedDrift_integral, hN, h0, sub_zero]
  exact hω (min t (τ ω)) ((min_le_right _ _).trans (hbound ω))

end SphericalAging.StoppedSDE
