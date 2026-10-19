module

public import SphericalAging.BoundedItoMultiplier
public import SphericalAging.RadialProcess
public import SphericalAging.AnnealedSDECore

public section

/-! Actual time-zero multiplier identities for the full-filtration SDE
operators. They justify localization on disorder events known at time zero. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.StaticSDEOperators
open HardSphereDynamics PredictableDriftTime BoundedItoMultiplier VectorIto
set_option maxHeartbeats 1000000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma restrict_mul (T t : ℝ≥0) (ht : t ≤ T) {C : Ω → ℝ}
    (hC : StronglyMeasurable[F 0] C) (K : ℝ≥0) (hK : ∀ ω, ‖C ω‖ ≤ K)
    (U : PredictableProcessL2 F P) :
    FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t
      (predictableMulCLM T hC K hK U) = predictableMulCLM t hC K hK U := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F t
    (predictableMulCLM T hC K hK U), predictableMulCLM_coe T hC K hK U,
    predictableMulCLM_coe t hC K hK U] with q hr hT htq
  by_cases hqt : q.1 ∈ Ioc (0 : ℝ≥0) t
  · have hqT : q.1 ∈ Ioc (0 : ℝ≥0) T := ⟨hqt.1,hqt.2.trans ht⟩
    simp only [hr,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      mem_prod,mem_univ,and_true,hqt,indicator_of_mem,hT,htq,
      elementaryRepresentative,ite_eq_left hqt,ite_eq_left hqT,ite_true]
  · simp [hr,FourPapersCommon.FilteredBrownian.predictableTimeFrame,hqt,htq,
      elementaryRepresentative]

lemma vectorProcessLp_sub (D : BrownianDriver N P F)
    (U V : Fin N → PredictableProcessL2 F P) (t : ℝ≥0) :
    vectorProcessLp D (fun j => U j - V j) t = vectorProcessLp D U t - vectorProcessLp D V t := by
  unfold vectorProcessLp vectorIto
  simp only [← FourPapersCommon.FilteredBrownian.predictableTimeRestrictCLM_apply,
    map_sub,Finset.sum_sub_distrib]

/-- True predictable integral multiplication by a bounded time-zero random
variable, at every terminal time within the multiplier horizon. -/
theorem vectorProcessLp_mul_coe (D : BrownianDriver N P F)
    (T t : ℝ≥0) (ht : t ≤ T) {C : Ω → ℝ}
    (hC : StronglyMeasurable[F 0] C) (K : ℝ≥0) (hK : ∀ ω, ‖C ω‖ ≤ K)
    (U : Fin N → PredictableProcessL2 F P) :
    (vectorProcessLp D (fun j => predictableMulCLM T hC K hK (U j)) t : Ω → ℝ) =ᵐ[P]
      fun ω => C ω * (vectorProcessLp D U t : Ω → ℝ) ω := by
  have heq : vectorProcessLp D (fun j => predictableMulCLM T hC K hK (U j)) t =
      boundedMulCLM (hC.mono (F.le 0)).aestronglyMeasurable K (.of_forall hK)
        (vectorProcessLp D U t) := by
    unfold vectorProcessLp
    simp only [restrict_mul T t ht hC K hK]
    rw [vectorIto_mul D (show (0 : ℝ≥0) ≤ t from zero_le) hC K hK U]
    congr 1
    apply congrArg (vectorIto D)
    funext j
    simp [FourPapersCommon.FilteredBrownian.predictableTimeSlice]
  rw [heq]
  exact boundedMulCLM_coe (hC.mono (F.le 0)).aestronglyMeasurable K (.of_forall hK) _

/-- True drift primitive multiplication by a time-zero random variable. -/
theorem driftVersion_mul_coe (T t : ℝ≥0) (ht : t ≤ T) {C : Ω → ℝ}
    (hC : StronglyMeasurable[F 0] C) (K : ℝ≥0) (hK : ∀ ω, ‖C ω‖ ≤ K)
    (A : PredictableProcessL2 F P) :
    driftVersion (predictableMulCLM T hC K hK A) t t =ᵐ[P]
      fun ω => C ω * driftVersion A t t ω := by
  have hleft := RadialProcess.driftVersion_eq_of_coe _ _ (predictableMulCLM_coe T hC K hK A) t
  have hright := RadialProcess.driftVersion_eq_of_coe A (A : TimeProcessL2 P) (Filter.EventuallyEq.rfl) t
  filter_upwards [hleft,hright] with ω hl hr
  rw [hl,hr,← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  have hST : s ∈ Ioc (0 : ℝ≥0) T := ⟨hs.1,hs.2.trans ht⟩
  simp only [elementaryRepresentative,ite_eq_left hST]

/-- The actual primitive of a genuine coefficient class is its real drift
integral, using a larger coefficient horizon and a smaller terminal time. -/
theorem driftVersion_eq_actual_at (A : PredictableProcessL2 F P) (H : ℝ≥0 → Ω → ℝ)
    (T t : ℝ≥0) (ht : t ≤ T)
    (hA : (A : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut H T) :
    driftVersion A t t =ᵐ[P] fun ω => ∫ s in (0 : ℝ)..(t : ℝ), H s.toNNReal ω := by
  have h := RadialProcess.driftVersion_eq_of_coe A _ hA t
  filter_upwards [h] with ω hω
  rw [hω,← PredictableDriftTime.primitive_eq_real_intervalIntegral
    (fun q : ℝ≥0 × Ω => H q.1 q.2) t ω]
  unfold primitive
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  simp only [FourPapersCommon.continuousAdaptedTimeCut,
    ite_eq_left (show s ∈ Ioc (0 : ℝ≥0) T from ⟨hs.1,hs.2.trans ht⟩)]

end SphericalAging.StaticSDEOperators
