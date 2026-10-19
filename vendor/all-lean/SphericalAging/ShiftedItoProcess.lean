module

public import SphericalAging.ShiftedIto

public section

/-! Exact fixed-time Itô increments under deterministic waiting-time
translation, including the actual vector stochastic operator. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ShiftedItoProcess
open HardSphereDynamics VectorIto ShiftedPredictable TimeShiftMeasure ShiftedIto
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

lemma predictableShift_timeRestrict (s t : ℝ≥0) (U : PredictableProcessL2 F P) :
    FourPapersCommon.FilteredBrownian.predictableTimeRestrict (ShiftedBrownian.filtration F s) t (predictableShift s U)=
      predictableShift s (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F (s+t) U) := by
  apply Subtype.ext
  apply Lp.ext
  have hcut := (shift_quasiMeasurePreserving (P := P) s).ae_eq_comp
    (FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F (s+t) U)
  have hpos : ∀ᵐ q : ℝ≥0 × Ω ∂nonnegativeLebesgueMeasure.prod P,0 < q.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := nonnegativeLebesgueMeasure) (ν := P)).ae
      (ae_iff.mpr (by simp))
  filter_upwards [FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn
    (ShiftedBrownian.filtration F s) t (predictableShift s U),predictableShift_coe s U,
    predictableShift_coe s (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F (s+t) U),hcut,hpos]
    with q hL hU hR hcut hpos
  dsimp only [Function.comp_def] at hcut
  rw [hL,hR,hcut]
  by_cases hqt : q.1 ≤ t
  · have hmem : q ∈ FourPapersCommon.FilteredBrownian.predictableTimeFrame (W := Ω) t :=
      ⟨⟨hpos,hqt⟩,mem_univ _⟩
    have hmem' : shift s q ∈ FourPapersCommon.FilteredBrownian.predictableTimeFrame (W := Ω) (s+t) :=
      ⟨⟨(zero_le : 0 ≤ s).trans_lt (lt_add_of_pos_right s hpos),add_le_add le_rfl hqt⟩,mem_univ _⟩
    rw [indicator_of_mem hmem,indicator_of_mem hmem',hU]
  · have hmem : q ∉ FourPapersCommon.FilteredBrownian.predictableTimeFrame (W := Ω) t := fun h => hqt h.1.2
    have hmem' : shift s q ∉ FourPapersCommon.FilteredBrownian.predictableTimeFrame (W := Ω) (s+t) := by
      intro h
      exact hqt ((add_le_add_iff_left s).mp h.1.2)
    rw [indicator_of_notMem hmem,indicator_of_notMem hmem']

/-- The actual future scalar Itô integral is the original process
increment on `[s,s+t]`, in the true full shifted filtration. -/
theorem coordinateIto_timeShift (D : BrownianDriver N P F) (i : Fin N)
    (s t : ℝ≥0) (U : PredictableProcessL2 F P) :
    coordinateIto (ShiftedBrownian.driver D s) i
      (FourPapersCommon.FilteredBrownian.predictableTimeRestrict (ShiftedBrownian.filtration F s) t (predictableShift s U))=
      coordinateIto D i (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F (s+t) U)-
        coordinateIto D i (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F s U) := by
  rw [predictableShift_timeRestrict,coordinateIto_predictableShift,
    FourPapersCommon.FilteredBrownian.predictableTimeRestrict_restrict F (le_add_right le_rfl),map_sub]

/-- Exact future vector Itô increment, retaining every true coordinate
cross-covariance and full filtration. -/
theorem vectorProcessLp_timeShift (D : BrownianDriver N P F) (s t : ℝ≥0)
    (U : Fin N → PredictableProcessL2 F P) :
    vectorProcessLp (ShiftedBrownian.driver D s) (fun i => predictableShift s (U i)) t=
      vectorProcessLp D U (s+t)-vectorProcessLp D U s := by
  unfold vectorProcessLp vectorIto
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i _ => coordinateIto_timeShift D i s t (U i))

end SphericalAging.ShiftedItoProcess
