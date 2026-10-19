module

public import SphericalAging.WeightedVectorQuadratic
public import SphericalAging.LocalRadialIto
public import SphericalAging.AnnealedSDECore

public section

/-! Arbitrary continuous weighted brackets of genuine local strong SDE
coordinates. Drift removal uses the actual finite-variation drift version,
and all coefficient classes remain full-filtration predictable classes. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.LocalWeightedQuadratic
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open VectorIto VectorItoFormula VectorQuadraticVariation WeightedVectorQuadratic WeightedDriftSums
open AnnealedSDECore
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Every actual predictable drift version has zero quadratic variation,
pathwise on almost every sample and on every requested finite horizon. -/
theorem driftVersion_quadratic_zero (A : PredictableProcessL2 F P) (T t : ℝ≥0) :
    ∀ᵐ ω ∂P,Tendsto (fun n => quadraticVariationApprox (driftVersion A T) t (n+1) ω) atTop (𝓝 0) := by
  let μ : ℝ≥0 → Ω → ℝ := fun s ω => cutRepresentative A T (s,ω)
  have he (s : ℝ≥0) (ω : Ω) : driftVersion A T s ω = integratedDrift μ s ω :=
    driftPrimitive_eq_integratedDrift μ s ω
  filter_upwards [(cutRepresentative_integrable A T).prod_left_ae] with ω hω
  have hi : IntegrableOn (fun s => μ s ω) (Ioc 0 t) nonnegativeLebesgueMeasure := hω.integrableOn
  have hq := tendsto_quadraticVariationApprox_integratedDrift_zero μ t ω
    ((integrableOn_nonnegative_iff_real _ _).mp hi)
  simpa only [quadraticVariationApprox,he] using hq

/-- Arbitrary continuous weights see precisely the true stochastic bracket;
the genuine finite-variation Picard drift contributes no quadratic term. -/
theorem drift_ito_weightedQuadratic_tendsto (D : BrownianDriver N P F)
    (A : PredictableProcessL2 F P) (U : Fin N → PredictableProcessL2 F P)
    (T t : ℝ≥0) (H : ℝ≥0 → Ω → ℝ)
    (hH : ∀ s,AEStronglyMeasurable (H s) P)
    (hHc : ∀ᵐ ω ∂P,Continuous (fun s => H s ω)) :
    TendstoInMeasure P (fun n => weightedQuadraticSum H
      (fun s ω => driftVersion A T s ω+vectorProcess D U s ω) t (n+1)) atTop
      (fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*
        (∑ j : Fin N,(U j : ℝ≥0 × Ω → ℝ) (s,ω)^2) ∂nonnegativeLebesgueMeasure) := by
  have hmod : IsContinuousProcessModification H H P := ⟨fun _ => EventuallyEq.rfl,hHc⟩
  have hremove := generalItoMixedQuadraticApprox_add_sub_tendstoInMeasure_zero cubic cubic_second_continuous
    H (driftVersion A T) (vectorProcess D U) hH
    (fun s => ((driftVersion_stronglyAdapted A T s).mono (F.le s)).aestronglyMeasurable)
    (fun s => (vectorProcess_memLp_two D U s).aestronglyMeasurable) t
    (fun ω => ∑ j,FilteredQuadraticVariation.predictableQuadraticVariation (U j) t ω)
    (driftVersion_quadratic_zero A T t) (vectorProcess_quadraticVariation D U t)
    (hmod.uniformPartition_secondDerivative_bounded cubic cubic_second_continuous t)
  have hbase := vector_weightedQuadratic_tendsto D U H hH hHc t
  have he : (fun n ω => generalItoMixedQuadraticApprox cubic H
      (fun s ω => driftVersion A T s ω+vectorProcess D U s ω) t (n+1) ω-
        generalItoMixedQuadraticApprox cubic H (vectorProcess D U) t (n+1) ω) =
    fun n ω => weightedQuadraticSum H (fun s ω => driftVersion A T s ω+vectorProcess D U s ω) t (n+1) ω-
      weightedQuadraticSum H (vectorProcess D U) t (n+1) ω := by
    funext n ω
    unfold generalItoMixedQuadraticApprox weightedQuadraticSum
    simp only [half_cubic_second]
  rw [he] at hremove
  apply (hremove.add_real_noMeas hbase).congr
  · intro n
    exact .of_forall (fun ω => sub_add_cancel _ _)
  · exact .of_forall (fun _ => zero_add _)

/-- An actual local strong coordinate has the true continuously weighted
bracket of its existentially actual predictable diffusion row. -/
theorem strong_coordinate_weightedQuadratic_tendsto (D : BrownianDriver N P F)
    {b : Ω → Fin N → State N → ℝ} {sigma : Ω → Fin N → Fin N → State N → ℝ}
    {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D b sigma Z0 X T) (t : ℝ≥0) (ht : t ≤ T)
    (i : Fin N) (H : ℝ≥0 → Ω → ℝ)
    (hH : ∀ s,AEStronglyMeasurable (H s) P)
    (hHc : ∀ᵐ ω ∂P,Continuous (fun s => H s ω)) :
    TendstoInMeasure P (fun n => weightedQuadraticSum H (fun s ω => X s ω i) t (n+1)) atTop
      (fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*
        (∑ j : Fin N,sigma ω i j (X s ω)^2) ∂nonnegativeLebesgueMeasure) := by
  obtain ⟨A,U,hA,hU,hEq⟩ := hX.2.2.2
  have hd : ∀ s,s ≤ T → (fun ω => X s ω i) =ᵐ[P]
      fun ω => Z0 ω i+driftVersion (A i) T s ω+vectorProcess D (U i) s ω := by
    intro s hs
    filter_upwards [hEq s hs i,driftVersion_eq_actual (A i)
      (fun r ω => b ω i (X r ω)) T (hA i),vectorProcessLp_ae_eq D (U i) s] with ω he hdr hi
    rw [hdr s hs,← hi]
    exact he
  have hpred : (fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*
      (∑ j : Fin N,(U i j : ℝ≥0 × Ω → ℝ) (s,ω)^2) ∂nonnegativeLebesgueMeasure) =ᵐ[P]
      fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*
        (∑ j : Fin N,sigma ω i j (X s ω)^2) ∂nonnegativeLebesgueMeasure := by
    have hrows := ae_all_iff.mpr (fun j : Fin N => hU i j)
    have hswap := (Measure.measurePreserving_swap (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae hrows
    filter_upwards [Measure.ae_ae_of_ae_prod hswap] with ω hω
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hω,ae_restrict_mem measurableSet_Ioc] with s hs hst
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have hj := hs j
    dsimp only [Function.comp_def,Prod.swap] at hj
    simpa only [FourPapersCommon.continuousAdaptedTimeCut,
      ite_eq_left (show s ∈ Ioc (0 : ℝ≥0) T from ⟨hst.1,hst.2.trans ht⟩)] using congrArg (fun z : ℝ => z^2) hj
  apply (drift_ito_weightedQuadratic_tendsto D (A i) (U i) T t H hH hHc).congr
  · intro n
    have hgrid : ∀ᵐ ω ∂P,∀ k ∈ Finset.range (n+1),
        X (uniformPartitionTime t (n+1) k) ω i = Z0 ω i+driftVersion (A i) T (uniformPartitionTime t (n+1) k) ω+
          vectorProcess D (U i) (uniformPartitionTime t (n+1) k) ω ∧
        X (uniformPartitionTime t (n+1) (k+1)) ω i = Z0 ω i+driftVersion (A i) T (uniformPartitionTime t (n+1) (k+1)) ω+
          vectorProcess D (U i) (uniformPartitionTime t (n+1) (k+1)) ω :=
      (Finset.range (n+1)).eventually_all.mpr (fun k hk =>
        (hd _ ((uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n)
          (Nat.le_of_lt (Finset.mem_range.mp hk))).2.trans ht)).and
        (hd _ ((uniformPartitionTime_mem_Icc_of_le t (Nat.zero_lt_succ n)
          (Nat.succ_le_of_lt (Finset.mem_range.mp hk))).2.trans ht)))
    filter_upwards [hgrid] with ω hω
    unfold weightedQuadraticSum
    apply Finset.sum_congr rfl
    intro k hk
    dsimp only
    rw [(hω k hk).1,(hω k hk).2]
    ring
  · exact hpred

end SphericalAging.LocalWeightedQuadratic
