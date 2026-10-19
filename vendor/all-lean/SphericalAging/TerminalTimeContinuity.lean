module

public import SphericalAging.TerminalLinearity
public import FourPapersCommon.FilteredItoL2Continuity

public section

/-! Joint terminal time/data continuity of the genuine drift and Itô operators. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.TerminalTimeContinuity
open HardSphereDynamics PredictableTerminalOperators PredictableItoTime PredictableDriftTime
open TerminalLinearity FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma driftTerminal_eq_restrict (T t : ℝ≥0) (U : PredictableProcessL2 F P) :
    driftTerminal T t U=driftTerminal T T (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t U) := by
  have hr : cutRepresentative (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t U) T =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => if q.1∈Ioc (0 : ℝ≥0) T then
        (if q.1∈Ioc (0 : ℝ≥0) t then (U : TimeProcessL2 P) q else 0) else 0 := by
    filter_upwards [representative_ae (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t U),
      FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F t U] with q hq htq
    simp only [cutRepresentative,hq,htq,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      Set.indicator,Set.mem_prod,Set.mem_univ,and_true]
  have hu : cutRepresentative U T =ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => if q.1∈Ioc (0 : ℝ≥0) T then (U : TimeProcessL2 P) q else 0 := by
    filter_upwards [representative_ae U] with q hq
    simp only [cutRepresentative,hq,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
      Set.indicator,Set.mem_prod,Set.mem_univ,and_true]
  have hrs := (Measure.measurePreserving_swap (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae_eq_comp hr
  have hus := (Measure.measurePreserving_swap (μ := P) (ν := nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae_eq_comp hu
  apply Lp.ext
  filter_upwards [(driftVersion_memLp U T t).coeFn_toLp,
    (driftVersion_memLp (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t U) T T).coeFn_toLp,
    Measure.ae_ae_of_ae_prod hrs,Measure.ae_ae_of_ae_prod hus] with ω htω hTω hrω huω
  change ((driftVersion_memLp U T t).toLp _ : Ω → ℝ) ω =
    ((driftVersion_memLp (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t U) T T).toLp _ : Ω → ℝ) ω
  rw [htω,hTω]
  unfold driftVersion primitive
  rw [← integral_indicator measurableSet_Ioc,← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [hrω,huω] with s hrs hus
  dsimp only [Function.comp_def,Prod.swap] at hrs hus
  by_cases ht : s∈Ioc (0 : ℝ≥0) t <;> by_cases hT : s∈Ioc (0 : ℝ≥0) T <;>
    simp [Set.indicator,ht,hT,hrs,hus]

/-- Fixed-data mean-square drift continuity, including terminal time zero. -/
lemma driftTerminal_time_continuous (T : ℝ≥0) (U : PredictableProcessL2 F P) :
    Continuous (fun t => driftTerminal T t U) := by
  have hc := (driftTerminal_lipschitz (F := F) (P := P) T T).continuous.comp
    (continuous_predictableTimeRestrict U)
  exact hc.congr (fun t => (driftTerminal_eq_restrict T t U).symm)

/-- Strong joint time/data continuity without operator-norm time continuity. -/
theorem driftTerminal_joint_continuous (T : ℝ≥0) :
    Continuous (fun q : ℝ≥0 × PredictableProcessL2 F P => driftTerminalOperator T q.1 q.2) := by
  exact continuous_prod_of_continuous_lipschitzWith' _ (NNReal.sqrt T)
    (fun t => driftTerminal_lipschitz T t) (fun U => driftTerminal_time_continuous T U)

/-- Genuine full-filtration Itô terminal classes are jointly continuous
in deterministic time and the actual predictable integrand. -/
theorem itoTerminal_joint_continuous (D : BrownianDriver N P F) (j : Fin N) :
    Continuous (fun q : ℝ≥0 × PredictableProcessL2 F P => itoTerminalOperator D j q.1 q.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro t
    exact itoTerminalAdapted_lipschitz D j t
  · intro U
    exact continuous_naturalItoProcess (D.brownian j).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable j) (D.filtered j) U

end SphericalAging.TerminalTimeContinuity
