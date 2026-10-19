module

public import SphericalAging.TerminalStateRepresentation
public import SphericalAging.VectorZeroUniqueness
public import SphericalAging.PredictableFamilyLift
public import SphericalAging.AnnealedSDECore

public section

/-! Whole-vector zero-initial terminal energy from the genuine drift
and full-filtration Itô maps. Summing exact coordinate energies retains
the true Frobenius noise trace, with no additional dimension factor. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.WholeVectorTerminalEnergy
open HardSphereDynamics LocalSDE PredictableDriftTime RadialUniqueness
open TerminalStateRepresentation FourPapersCommon.FilteredBrownian
open PredictableItoTime
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma driftVersion_prefix (A : PredictableProcessL2 F P) (T t : ℝ≥0) (ht : t≤T) (ω : Ω) :
    driftVersion A T t ω=driftVersion A t t ω := by
  unfold driftVersion primitive
  apply setIntegral_congr_fun measurableSet_Ioc
  intro s hs
  simp only [cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame]
  rw [Set.indicator_of_mem (show (s,ω)∈Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω) from ⟨⟨hs.1,hs.2.trans ht⟩,Set.mem_univ _⟩),
    Set.indicator_of_mem (show (s,ω)∈Ioc (0 : ℝ≥0) t×ˢ(Set.univ : Set Ω) from ⟨hs,Set.mem_univ _⟩)]

lemma cutRepresentative_eq_restrict (A : PredictableProcessL2 F P) (t : ℝ≥0) :
    cutRepresentative A t=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t A : TimeProcessL2 P) := by
  filter_upwards [representative_ae A,FourPapersCommon.FilteredBrownian.predictableTimeRestrict_coeFn F t A] with q hq hr
  rw [hr]
  unfold cutRepresentative
  by_cases hqt : q∈FourPapersCommon.FilteredBrownian.predictableTimeFrame t
  · simp only [Set.indicator_of_mem hqt,hq]
  · simp only [Set.indicator_of_notMem hqt]

lemma drift_terminal_integral_sq_le (A : PredictableProcessL2 F P) (T t : ℝ≥0) (ht : t≤T) :
    (∫ ω,(driftVersion A T t ω)^2 ∂P)≤(t : ℝ)*‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t A‖^2 := by
  have hcut := (cutRepresentative_memLp A t).integrable_sq
  have hEq : (∫ q,(cutRepresentative A t q)^2 ∂nonnegativeLebesgueMeasure.prod P)=
      ‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t A‖^2 := by
    rw [predictable_norm_sq]
    exact integral_congr_ae ((cutRepresentative_eq_restrict A t).mono (fun _ h => congrArg (fun z : ℝ => z^2) h))
  simp_rw [driftVersion_prefix A T t ht]
  calc
    _≤∫ ω,(t : ℝ)*(∫ s,(cutRepresentative A t (s,ω))^2 ∂nonnegativeLebesgueMeasure) ∂P :=
      integral_mono_ae (driftVersion_memLp A t t).integrable_sq
        (hcut.integral_prod_right.const_mul _) (driftVersion_sq_le_ae A t t)
    _=(t : ℝ)*‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t A‖^2 := by
      rw [integral_const_mul,← integral_prod_symm _ hcut,hEq]

theorem terminalClass_zero_norm_sq_le (D : BrownianDriver N P F)
    (A : Fin N → PredictableProcessL2 F P) (S : Fin N → Fin N → PredictableProcessL2 F P)
    (T t : ℝ≥0) (ht : t≤T) :
    ‖terminalClass D 0 A S T t‖^2≤
      2*(t : ℝ)*(∑ i : Fin N,‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (A i)‖^2)+
        2*(∑ i : Fin N,∑ j : Fin N,‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (S i j)‖^2) := by
  let M := fun i => VectorIto.vectorProcessLp D (S i) t
  let W : Ω → State N := fun ω => WithLp.toLp 2 (fun i : Fin N => driftVersion (A i) T t ω+M i ω)
  have he : terminalClass D 0 A S T t=ᵐ[P] W := by
    filter_upwards [terminalClass_ae D 0 A S T t,
      ae_all_iff.mpr (fun i : Fin N => AnnealedSDECore.vectorProcessLp_ae_itoVersions D (S i) t)] with ω hω hM
    rw [hω]
    change (∑ i : Fin N,(0+driftVersion (A i) T t ω+∑ j : Fin N,
      itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) (S i j) t ω) • basisVector i)=W ω
    simp only [zero_add,← hM]
    exact state_sum_basis (W ω)
  have hsq : (fun ω => ‖terminalClass D 0 A S T t ω‖^2)=ᵐ[P]
      fun ω => ∑ i : Fin N,(driftVersion (A i) T t ω+M i ω)^2 := by
    filter_upwards [he] with ω hω
    rw [hω]
    simpa only [real_inner_self_eq_norm_sq] using (coordinate_square_sum (W ω)).symm
  have hrow (i : Fin N) : MemLp (fun ω => driftVersion (A i) T t ω+M i ω) 2 P :=
    (driftVersion_memLp (A i) T t).add (Lp.memLp (M i))
  rw [← PredictableFamilyLift.integral_norm_sq_Lp,integral_congr_ae hsq,
    integral_finsetSum Finset.univ (fun i _ => (hrow i).integrable_sq)]
  have hb (i : Fin N) : (∫ ω,(driftVersion (A i) T t ω+M i ω)^2 ∂P)≤
      2*(t : ℝ)*‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (A i)‖^2+
        2*(∑ j : Fin N,‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (S i j)‖^2) := by
    have hd := (driftVersion_memLp (A i) T t).integrable_sq
    have hm := (Lp.memLp (M i)).integrable_sq
    have hnoise : (∫ ω,(M i ω)^2 ∂P)=∑ j : Fin N,‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (S i j)‖^2 := by
      rw [PredictableItoTime.integral_sq_toLp _ (Lp.memLp (M i)),Lp.toLp_coeFn]
      exact VectorIto.vectorProcessLp_norm_sq D (S i) t
    calc
      _≤∫ ω,2*(driftVersion (A i) T t ω)^2+2*(M i ω)^2 ∂P :=
        integral_mono (hrow i).integrable_sq ((hd.const_mul 2).add (hm.const_mul 2))
          (fun ω => by nlinarith [sq_nonneg (driftVersion (A i) T t ω-M i ω)])
      _=2*(∫ ω,(driftVersion (A i) T t ω)^2 ∂P)+2*(∑ j : Fin N,‖FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (S i j)‖^2) := by
        rw [integral_add (hd.const_mul 2) (hm.const_mul 2),integral_const_mul,integral_const_mul,hnoise]
      _≤_ := by have hh := drift_terminal_integral_sq_le (A i) T t ht;nlinarith [hh]
  refine (Finset.sum_le_sum (fun i _ => hb i)).trans_eq ?_
  rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]

end SphericalAging.WholeVectorTerminalEnergy
