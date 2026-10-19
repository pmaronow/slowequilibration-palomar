module

public import SphericalAging.WholeVectorTerminalEnergy

public section

/-! Literal coefficient-field form of the whole-vector terminal energy.
Predictable prefix classes are identified with their true time-cut fields,
and every norm-to-integral conversion and Fubini exchange is derived. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.WholeVectorCoefficientEnergy
open HardSphereDynamics RadialUniqueness TerminalStateRepresentation
open WholeVectorTerminalEnergy
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem restricted_eq_timeCut (A : PredictableProcessL2 F P) (b : ℝ≥0 → Ω → ℝ)
    (T t : ℝ≥0) (ht : t≤T)
    (hA : (A : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut b T) :
    (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t A : TimeProcessL2 P)=ᵐ[
      nonnegativeLebesgueMeasure.prod P] FourPapersCommon.continuousAdaptedTimeCut b t := by
  filter_upwards [FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F t A,hA] with q hr ha
  rw [hr]
  by_cases hqt : q.1∈Ioc (0 : ℝ≥0) t
  · have hqT : q.1∈Ioc (0 : ℝ≥0) T := ⟨hqt.1,hqt.2.trans ht⟩
    rw [Set.indicator_of_mem (show q∈FourPapersCommon.FilteredBrownian.predictableTimeFrame t from ⟨hqt,Set.mem_univ _⟩),ha]
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left hqt,ite_eq_left hqT]
  · rw [Set.indicator_of_notMem (show q∉FourPapersCommon.FilteredBrownian.predictableTimeFrame t from fun h => hqt h.1)]
    simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_right hqt]

theorem timeCut_memLp (A : PredictableProcessL2 F P) (b : ℝ≥0 → Ω → ℝ)
    (T t : ℝ≥0) (ht : t≤T)
    (hA : (A : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut b T) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut b t) 2 (nonnegativeLebesgueMeasure.prod P) :=
  (Lp.memLp (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t A : TimeProcessL2 P)).ae_eq
    (restricted_eq_timeCut A b T t ht hA)

theorem restricted_norm_sq_eq_product_integral (A : PredictableProcessL2 F P) (b : ℝ≥0 → Ω → ℝ)
    (T t : ℝ≥0) (ht : t≤T)
    (hA : (A : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut b T) :
    ‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t A‖^2=
      ∫ q,(FourPapersCommon.continuousAdaptedTimeCut b t q)^2 ∂nonnegativeLebesgueMeasure.prod P := by
  rw [predictable_norm_sq]
  exact integral_congr_ae ((restricted_eq_timeCut A b T t ht hA).mono
    (fun _ h => congrArg (fun z : ℝ => z^2) h))

theorem finite_restricted_norm_sq_eq_integral {I : Type*} [Fintype I]
    (A : I → PredictableProcessL2 F P) (b : I → ℝ≥0 → Ω → ℝ)
    (T t : ℝ≥0) (ht : t≤T)
    (hA : ∀ i,(A i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (b i) T) :
    (∑ i,‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (A i)‖^2)=
      ∫ s in Ioc (0 : ℝ≥0) t,∫ ω,∑ i,(b i s ω)^2 ∂P ∂nonnegativeLebesgueMeasure := by
  have hi (i : I) : Integrable (fun q => (FourPapersCommon.continuousAdaptedTimeCut (b i) t q)^2)
      (nonnegativeLebesgueMeasure.prod P) := (timeCut_memLp (A i) (b i) T t ht (hA i)).integrable_sq
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hi i)
  calc
    _=∫ q,∑ i,(FourPapersCommon.continuousAdaptedTimeCut (b i) t q)^2 ∂nonnegativeLebesgueMeasure.prod P := by
      simp_rw [restricted_norm_sq_eq_product_integral _ _ T t ht (hA _)]
      exact (integral_finsetSum Finset.univ (fun i _ => hi i)).symm
    _=∫ s,(Ioc (0 : ℝ≥0) t).indicator (fun s => ∫ ω,∑ i,(b i s ω)^2 ∂P) s ∂nonnegativeLebesgueMeasure := by
      rw [integral_prod _ hsum]
      apply integral_congr_ae
      exact .of_forall (fun s => by
        by_cases hs : s∈Ioc (0 : ℝ≥0) t
        · simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left hs,Set.indicator_of_mem hs]
        · simp only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_right hs,zero_pow (by norm_num : (2 : ℕ)≠0),
            Finset.sum_const_zero,integral_zero,Set.indicator_of_notMem hs])
    _=_ := integral_indicator measurableSet_Ioc

theorem terminalClass_zero_energy_le (D : BrownianDriver N P F)
    (A : Fin N → PredictableProcessL2 F P) (S : Fin N → Fin N → PredictableProcessL2 F P)
    (μ : ℝ≥0 → Ω → State N) (σ : Fin N → Fin N → ℝ≥0 → Ω → ℝ)
    (T t : ℝ≥0) (ht : t≤T)
    (hA : ∀ i,(A i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s ω => μ s ω i) T)
    (hS : ∀ i j,(S i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (σ i j) T) :
    ‖terminalClass D 0 A S T t‖^2≤
      2*(t : ℝ)*(∫ s in Ioc (0 : ℝ≥0) t,∫ ω,‖μ s ω‖^2 ∂P ∂nonnegativeLebesgueMeasure)+
        2*(∫ s in Ioc (0 : ℝ≥0) t,∫ ω,∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2
          ∂P ∂nonnegativeLebesgueMeasure) := by
  have hd := finite_restricted_norm_sq_eq_integral A (fun i s ω => μ s ω i) T t ht hA
  simp_rw [coordinate_square_sum,real_inner_self_eq_norm_sq] at hd
  have hs := finite_restricted_norm_sq_eq_integral
    (fun ij : Fin N × Fin N => S ij.1 ij.2) (fun ij : Fin N × Fin N => σ ij.1 ij.2)
    T t ht (fun ij => hS ij.1 ij.2)
  simp only [Fintype.sum_prod_type] at hs
  rw [← hd,← hs]
  exact terminalClass_zero_norm_sq_le D A S T t ht

end SphericalAging.WholeVectorCoefficientEnergy
