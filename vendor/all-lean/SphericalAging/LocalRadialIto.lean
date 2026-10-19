module

public import SphericalAging.RadialProcess

public section

/-! Local-in-time quadratic Itô representation for an actual vector driver.
Only the integral equation up to the requested horizon is required. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.LocalRadialIto
open HardSphereDynamics VectorIto VectorItoFormula VectorQuadraticVariation
  WeightedItoSums WeightedDriftSums RadialItoRepresentation
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

omit [IsProbabilityMeasure P] in
lemma quadraticVariationApprox_congr_on {X Y : ℝ≥0 → Ω → ℝ} (t : ℝ≥0)
    (h : ∀ s,s ≤ t → X s =ᵐ[P] Y s) (n : ℕ) (hn : 0 < n) :
    quadraticVariationApprox X t n =ᵐ[P] quadraticVariationApprox Y t n := by
  have hnext : ∀ᵐ ω ∂P,∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n (i+1)) ω=Y (uniformPartitionTime t n (i+1)) ω :=
    (Finset.range n).eventually_all.mpr (fun i hi => h _
      (uniformPartitionTime_mem_Icc_of_le t hn (Nat.succ_le_of_lt (Finset.mem_range.mp hi))).2)
  have hprev : ∀ᵐ ω ∂P,∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n i) ω=Y (uniformPartitionTime t n i) ω :=
    (Finset.range n).eventually_all.mpr (fun i hi => h _
      (uniformPartitionTime_mem_Icc_of_le t hn (Finset.mem_range.mp hi).le).2)
  filter_upwards [hnext,hprev] with ω hn hp
  unfold quadraticVariationApprox
  exact Finset.sum_congr rfl (fun i hi => by rw [hn i hi,hp i hi])

omit [IsProbabilityMeasure P] in
lemma weightedLeftSum_congr_on {X Y : ℝ≥0 → Ω → ℝ} (H : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (h : ∀ s,s ≤ t → X s =ᵐ[P] Y s) (n : ℕ) (hn : 0 < n) :
    weightedLeftSum H X t n =ᵐ[P] weightedLeftSum H Y t n := by
  have hnext : ∀ᵐ ω ∂P,∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n (i+1)) ω=Y (uniformPartitionTime t n (i+1)) ω :=
    (Finset.range n).eventually_all.mpr (fun i hi => h _
      (uniformPartitionTime_mem_Icc_of_le t hn (Nat.succ_le_of_lt (Finset.mem_range.mp hi))).2)
  have hprev : ∀ᵐ ω ∂P,∀ i ∈ Finset.range n,
      X (uniformPartitionTime t n i) ω=Y (uniformPartitionTime t n i) ω :=
    (Finset.range n).eventually_all.mpr (fun i hi => h _
      (uniformPartitionTime_mem_Icc_of_le t hn (Finset.mem_range.mp hi).le).2)
  filter_upwards [hnext,hprev] with ω hn hp
  unfold weightedLeftSum
  exact Finset.sum_congr rfl (fun i hi => by rw [hn i hi,hp i hi])

theorem quadratic_ito_formula_ae_on (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (X μ : ℝ≥0 → Ω → ℝ)
    (hX : ∀ s, AEStronglyMeasurable (X s) P)
    (hμ : Measurable (Function.uncurry μ))
    (hμint : ∀ t, ∀ᵐ ω ∂P, IntegrableOn (fun s => μ s ω) (Ioc 0 t) nonnegativeLebesgueMeasure)
    (T : ℝ≥0) (hdecomp : ∀ s,s ≤ T → X s =ᵐ[P] fun ω => X 0 ω + integratedDrift μ s ω + vectorProcess D U s ω)
    (t : ℝ≥0) (ht : t ≤ T) : TendstoInMeasure P (fun n => quadraticLeftSum X t (n + 1)) atTop
      (fun ω => X t ω ^ 2 - X 0 ω ^ 2 -
        ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U i) t ω) := by
  have hA : HasQuadraticVariationInProbabilityAt (integratedDrift μ) P t (fun _ => 0) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      exact (stronglyMeasurable_quadraticVariationApprox_integratedDrift hμ t (n+1)).aestronglyMeasurable
    · filter_upwards [hμint t] with ω hω
      exact tendsto_quadraticVariationApprox_integratedDrift_zero μ t ω
        ((integrableOn_nonnegative_iff_real (fun s => μ s ω) t).mp hω)
  have hM := vectorProcess_quadraticVariation D U t
  have hAM := hA.add_of_left_zero_of_aestronglyMeasurable hM
    (fun s => (StochasticCalculus.stronglyMeasurable_integratedDrift hμ s).aestronglyMeasurable)
    (fun s => (vectorProcess_memLp_two D U s).aestronglyMeasurable)
  have hconstant := hAM.add_timeConstant (X 0)
  have hQ : HasQuadraticVariationInProbabilityAt X P t
      (fun ω => ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U i) t ω) := by
    unfold HasQuadraticVariationInProbabilityAt at hconstant ⊢
    apply hconstant.congr
    · intro n
      apply quadraticVariationApprox_congr_on t _ (n+1) (Nat.zero_lt_succ n)
      intro s hs
      simpa only [add_assoc] using (hdecomp s (hs.trans ht)).symm
    · exact EventuallyEq.rfl
  have hc : TendstoInMeasure P (fun _ : ℕ => fun ω => X t ω ^ 2 - X 0 ω ^ 2) atTop
      (fun ω => X t ω ^ 2 - X 0 ω ^ 2) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      convert ((hX t).pow 2).sub ((hX 0).pow 2) using 1
    · exact .of_forall (fun _ => tendsto_const_nhds)
  apply (hc.sub_real_noMeas hQ).congr
  · intro n
    exact .of_forall (fun ω => (quadraticLeftSum_identity X t (Nat.zero_lt_succ n) ω).symm)
  · exact EventuallyEq.rfl

omit [IsProbabilityMeasure P] in
lemma weightedLeftSum_decomp_on {X A M : ℝ≥0 → Ω → ℝ}
    (T : ℝ≥0) (hdecomp : ∀ s,s ≤ T → X s =ᵐ[P] fun ω => X 0 ω + A s ω + M s ω)
    (H : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ht : t ≤ T) (n : ℕ) (hn : 0 < n) :
    weightedLeftSum H X t n =ᵐ[P]
      fun ω => weightedLeftSum H A t n ω + weightedLeftSum H M t n ω := by
  have h := weightedLeftSum_congr_on H t (fun s hs => hdecomp s (hs.trans ht)) n hn
  filter_upwards [h] with ω hω
  rw [hω]
  unfold weightedLeftSum
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem quadratic_ito_representation_on (D : BrownianDriver N P 𝓕)
    (U : Fin N → PredictableProcessL2 𝓕 P) (X μ : ℝ≥0 → Ω → ℝ)
    (hX : StronglyAdapted 𝓕 X) (hcts : ∀ᵐ ω ∂P, Continuous (fun s => X s ω))
    (K : ℝ≥0) (hK : ∀ s ω, ‖X s ω‖ ≤ K)
    (hμ : Measurable (Function.uncurry μ))
    (hμint : ∀ t, ∀ᵐ ω ∂P, IntegrableOn (fun s => μ s ω) (Ioc 0 t) nonnegativeLebesgueMeasure)
    (T : ℝ≥0) (hdecomp : ∀ s,s ≤ T → X s =ᵐ[P] fun ω => X 0 ω + integratedDrift μ s ω + vectorProcess D U s ω)
    (t : ℝ≥0) (ht : t ≤ T) : ∀ᵐ ω ∂P, X t ω ^ 2 = X 0 ω ^ 2 +
      (∫ s in Ioc 0 t, 2 * X s ω * μ s ω ∂nonnegativeLebesgueMeasure) +
      (quadraticNoise D U X hX hcts K hK t : Ω → ℝ) ω +
      ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U i) t ω := by
  have hQ := quadratic_ito_formula_ae_on D U X μ
    (fun s => ((hX s).mono (𝓕.le s)).aestronglyMeasurable) hμ hμint T hdecomp t ht
  have hDrift := adapted_weightedDrift_tendsto (twiceState X) μ (stronglyAdapted_twiceState hX)
    (continuous_twiceState hcts) (2 * K) (bound_twiceState hK) t hμ (hμint t)
  have hNoise := vector_weightedLeftSum_tendsto D (twiceState X) (stronglyAdapted_twiceState hX)
    (continuous_twiceState hcts) (2 * K) (bound_twiceState hK) t U
  have hTotal := hDrift.add_real_noMeas hNoise
  have hTotal' : TendstoInMeasure P (fun n => quadraticLeftSum X t (n+1)) atTop
      (fun ω => (∫ s in Ioc 0 t, 2 * X s ω * μ s ω ∂nonnegativeLebesgueMeasure) +
        (quadraticNoise D U X hX hcts K hK t : Ω → ℝ) ω) := by
    apply hTotal.congr
    · intro n
      exact (weightedLeftSum_decomp_on T hdecomp (twiceState X) t ht (n+1) (Nat.zero_lt_succ n)).symm
    · exact EventuallyEq.rfl
  have heq := tendstoInMeasure_ae_unique hQ hTotal'
  filter_upwards [heq] with ω hω
  linarith

theorem quadratic_norm_ito_representation_on {L : ℕ} (D : BrownianDriver N P 𝓕)
    (U : Fin L → Fin N → PredictableProcessL2 𝓕 P) (X μ : Fin L → ℝ≥0 → Ω → ℝ)
    (hX : ∀ k, StronglyAdapted 𝓕 (X k))
    (hcts : ∀ k, ∀ᵐ ω ∂P, Continuous (fun s => X k s ω))
    (K : ℝ≥0) (hK : ∀ k s ω, ‖X k s ω‖ ≤ K)
    (hμ : ∀ k, Measurable (Function.uncurry (μ k)))
    (hμint : ∀ k t, ∀ᵐ ω ∂P, IntegrableOn (fun s => μ k s ω) (Ioc 0 t) nonnegativeLebesgueMeasure)
    (T : ℝ≥0) (hdecomp : ∀ k s,s ≤ T → X k s =ᵐ[P] fun ω =>
      X k 0 ω + integratedDrift (μ k) s ω + vectorProcess D (U k) s ω)
    (t : ℝ≥0) (ht : t ≤ T) : ∀ᵐ ω ∂P,
      (∑ k, X k t ω ^ 2) = (∑ k, X k 0 ω ^ 2) +
        (∑ k, ∫ s in Ioc 0 t, 2 * X k s ω * μ k s ω ∂nonnegativeLebesgueMeasure) +
        (∑ k, (quadraticNoise D (U k) (X k) (hX k) (hcts k) K (hK k) t : Ω → ℝ) ω) +
        ∑ k, ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U k i) t ω := by
  have hall := ae_all_iff.mpr (fun k : Fin L => quadratic_ito_representation_on D (U k) (X k) (μ k)
    (hX k) (hcts k) K (hK k) (hμ k) (hμint k) T (hdecomp k) t ht)
  filter_upwards [hall] with ω hω
  calc
    (∑ k, X k t ω ^ 2) = ∑ k, (X k 0 ω ^ 2 +
      (∫ s in Ioc 0 t, 2 * X k s ω * μ k s ω ∂nonnegativeLebesgueMeasure) +
      (quadraticNoise D (U k) (X k) (hX k) (hcts k) K (hK k) t : Ω → ℝ) ω +
      ∑ i, FilteredQuadraticVariation.predictableQuadraticVariation (U k i) t ω) :=
      Finset.sum_congr rfl (fun k _ => hω k)
    _ = _ := by simp only [Finset.sum_add_distrib]

theorem quadratic_class_equation_on {L : ℕ} (D : BrownianDriver N P 𝓕)
    (A : Fin L → PredictableProcessL2 𝓕 P)
    (U : Fin L → Fin N → PredictableProcessL2 𝓕 P)
    (X μ : Fin L → ℝ≥0 → Ω → ℝ) (hX : ∀ k, StronglyAdapted 𝓕 (X k))
    (hc : ∀ k, ∀ᵐ ω ∂P, Continuous (fun s => X k s ω))
    (K : ℝ≥0) (hK : ∀ k s ω, ‖X k s ω‖ ≤ K) (S : ℝ≥0)
    (hS : ∀ k i, ∀ᵐ p ∂nonnegativeLebesgueMeasure.prod P, ‖(U k i : ℝ≥0 × Ω → ℝ) p‖ ≤ S)
    (T t : ℝ≥0) (ht : t ≤ T)
    (hA : ∀ k, (A k : ℝ≥0 × Ω → ℝ) =ᵐ[nonnegativeLebesgueMeasure.prod P] fun p => μ k p.1 p.2)
    (hμ : ∀ k, Measurable (Function.uncurry (μ k)))
    (hμint : ∀ k s, ∀ᵐ ω ∂P, IntegrableOn (fun r => μ k r ω) (Ioc 0 s) nonnegativeLebesgueMeasure)
    (hdecomp : ∀ k s,s ≤ T → X k s =ᵐ[P] fun ω => X k 0 ω + integratedDrift (μ k) s ω + vectorProcess D (U k) s ω) :
    (fun ω => (∑ k, X k t ω ^ 2) - ∑ k, X k 0 ω ^ 2) =ᵐ[P]
      fun ω => PredictableDriftTime.driftVersion (RadialProcess.radialDrift A U X hX hc K hK S hS T) t t ω +
        (vectorProcessLp D (RadialProcess.radialNoise U X hX hc K hK T) t : Ω → ℝ) ω := by
  have hn := quadratic_norm_ito_representation_on D U X μ hX hc K hK hμ hμint T hdecomp t ht
  have hd := RadialProcess.radialDrift_version A U X μ hX hc K hK S hS T t ht hA (fun k => hμint k t)
  have heq := Lp.coeFn_fun_finsetSum Finset.univ
    (fun k => quadraticNoise D (U k) (X k) (hX k) (hc k) K (hK k) t)
  rw [RadialProcess.sum_quadraticNoise D U X hX hc K hK T t ht] at heq
  filter_upwards [hn, hd, heq] with ω hn hd heq
  linarith

end SphericalAging.LocalRadialIto
