module

public import SphericalAging.WholeVectorCoefficientEnergy
public import SphericalAging.RandomInitialUniqueness
public import SphericalAging.RandomSDEConversions

public section

/-! Every genuine random-initial coefficient SDE with square-integrable
initial state has a genuine predictable state class. It is constructed
from the actual drift and Itô Volterra classes, without a bounded-path or
state-class premise. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.RandomSDEStateClass
open HardSphereDynamics LocalSDE AnnealedSDECore PredictableItoTime PredictableDriftTime
open TerminalStateRepresentation WholeVectorCoefficientEnergy
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem strongSolution_stateTimeCut_memLp (D : BrownianDriver N P F)
    (b : Ω → Fin N → State N → ℝ) (σ : Ω → Fin N → Fin N → State N → ℝ)
    (Z0 : Ω → State N) (hZ : MemLp Z0 2 P) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hsol : IsRandomStrongSolutionOn D b σ Z0 X T) :
    MemLp ((Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω)).indicator (fun q => X q.1 q.2))
      2 (nonnegativeLebesgueMeasure.prod P) := by
  rcases hsol with ⟨hZ0,hXa,hXc,A,S,hA,hS,he⟩
  let W : ℝ≥0 → Ω → State N := fun t ω => Z0 ω+∑ i : Fin N,
    (driftVersion (A i) T t ω+∑ j : Fin N,itoVersion (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) (S i j) t ω) • basisVector i
  have hWc : ∀ᵐ ω ∂P,Continuous (fun t => W t ω) := by
    have hd := ae_all_iff.mpr (fun i : Fin N => driftVersion_ae_continuous (A i) T)
    have hn := ae_all_iff.mpr (fun i : Fin N => ae_all_iff.mpr (fun j : Fin N =>
      (itoVersion_continuousModification (D.brownian j) (D.coordinateStronglyMeasurable j)
        (D.filtered j) (S i j)).continuous_paths))
    filter_upwards [hd,hn] with ω hd hn
    apply Continuous.add continuous_const
    apply continuous_finset_sum
    intro i _
    exact ((hd i).add (continuous_finset_sum _ (fun j _ => hn i j))).smul continuous_const
  have hfixed (t : ℝ≥0) (ht : t≤T) : X t=ᵐ[P] W t := by
    have hdr := ae_all_iff.mpr (fun i : Fin N => driftVersion_eq_actual (A i) _ T (hA i))
    have hno := ae_all_iff.mpr (fun i : Fin N => vectorProcessLp_ae_itoVersions D (S i) t)
    filter_upwards [ae_all_iff.mpr (he t ht),hdr,hno] with ω he hd hn
    apply PiLp.ext
    intro i
    have hWi : W t ω i=Z0 ω i+driftVersion (A i) T t ω+
        ∑ j : Fin N,itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
          (D.filtered j) (S i j) t ω := by
      simp [W,basisVector,PiLp.add_apply,Pi.single_apply,add_assoc]
    rw [hWi,hd i t ht,← hn i]
    exact he i
  have hpath := StrongUniqueness.continuous_state_processes_ae_eq_of_fixedTime_on hXc hWc hfixed
  have hprod := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae hpath
  have hcut : ((Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω)).indicator (fun q => X q.1 q.2))=ᵐ[
      nonnegativeLebesgueMeasure.prod P]
      ((Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω)).indicator (fun q => W q.1 q.2)) := by
    filter_upwards [hprod] with q hq
    by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
    · simp only [Set.indicator_of_mem (show q∈Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω) from ⟨ht,Set.mem_univ _⟩)]
      exact hq q.1 ht.2
    · simp [ht]
  have hz : MemLp ((Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω)).indicator (fun q => Z0 q.2))
      2 (nonnegativeLebesgueMeasure.prod P) :=
    (Lp.memLp (RandomInitialSDE.initialClass Z0 hZ0 hZ T :
      Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))).ae_eq
      (RandomInitialSDE.initialClass_coeFn Z0 hZ0 hZ T)
  have hr (i : Fin N) := (driftVersion_timeCut_memLp (A i) T).add
    (memLp_finsetSum Finset.univ (fun j _ => itoVersion_timeCut_memLp (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) (S i j) T))
  have hs := memLp_finsetSum Finset.univ (fun i _ => (hr i).continuousLinearMap_comp
    (ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)))
  have hW : MemLp ((Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω)).indicator (fun q => W q.1 q.2))
      2 (nonnegativeLebesgueMeasure.prod P) := by
    convert hz.add hs using 1
    funext q
    by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
    · simp only [Set.indicator_of_mem (show q∈Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω) from ⟨ht,Set.mem_univ _⟩),
        Pi.add_apply,Finset.sum_apply,ContinuousLinearMap.toSpanSingleton_apply,
        FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left ht,W]
    · have ht' : ¬(0<q.1 ∧ q.1≤T) := ht
      simp [Set.mem_prod,ht,ht',FourPapersCommon.continuousAdaptedTimeCut]
  exact hW.ae_eq hcut.symm

theorem strongSolution_terminal_memLp (D : BrownianDriver N P F)
    (b : Ω → Fin N → State N → ℝ) (σ : Ω → Fin N → Fin N → State N → ℝ)
    (Z0 : Ω → State N) (hZ : MemLp Z0 2 P) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hsol : IsRandomStrongSolutionOn D b σ Z0 X T) (t : ℝ≥0) (ht : t≤T) :
    MemLp (X t) 2 P := by
  rcases hsol with ⟨_,_,_,A,S,hA,_,he⟩
  have hi (i : Fin N) : MemLp (fun ω => X t ω i) 2 P := by
    have hz := hZ.continuousLinearMap_comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i)
    have hm := (hz.add (driftVersion_memLp (A i) T t)).add (Lp.memLp (VectorIto.vectorProcessLp D (S i) t))
    apply hm.ae_eq
    filter_upwards [he t ht i,driftVersion_eq_actual (A i) _ T (hA i)] with ω he hd
    simp only [Pi.add_apply]
    rw [hd t ht]
    exact he.symm
  have hs := memLp_finsetSum Finset.univ (fun i _ => (hi i).continuousLinearMap_comp
    (ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)))
  convert hs using 1
  funext ω
  simp only [ContinuousLinearMap.toSpanSingleton_apply]
  exact (state_sum_basis (X t ω)).symm

theorem randomStrongSolution_to_strongSolution (D : BrownianDriver N P F)
    (b : Fin N → State N → ℝ) (σ : Fin N → Fin N → State N → ℝ)
    (hb : ∀ i,Continuous (b i)) (hσ : ∀ i j,Continuous (σ i j))
    (Z0 : Ω → State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hsol : IsRandomStrongSolutionOn D (fun _ => b) (fun _ => σ) Z0 X T) :
    RandomInitialSDE.IsStrongSolutionOn b σ hσ D Z0 X T := by
  rcases hsol with ⟨_,hXa,hXc,A,S,hA,hS,he⟩
  have hm (i : Fin N) := (Lp.memLp (A i : TimeProcessL2 P)).ae_eq (hA i)
  have hn (i j : Fin N) (t : ℝ≥0) (ht : t≤T) :=
    timeCut_memLp (S i j) (fun s ω => σ i j (X s ω)) T t ht (hS i j)
  refine ⟨hXa,hXc,hm,hn,?_⟩
  intro t ht i
  have hr : (fun j => coefficientPredictableActual hXa hXc (hσ i j) t (hn i j t ht))=
      (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (S i j)) := by
    funext j
    apply Subtype.ext
    apply Lp.ext
    exact (hn i j t ht).coeFn_toLp.trans (restricted_eq_timeCut (S i j)
      (fun s ω => σ i j (X s ω)) T t ht (hS i j)).symm
  rw [hr]
  simpa only [VectorIto.vectorProcessLp,driverItoMap_apply,
    VectorIto.vectorIto,VectorIto.coordinateIto] using he t ht i

theorem coordinate_timeCut_memLp {X : ℝ≥0 → Ω → State N} (T : ℝ≥0)
    (hm : MemLp ((Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω)).indicator (fun q => X q.1 q.2))
      2 (nonnegativeLebesgueMeasure.prod P)) (i : Fin N) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun s ω => X s ω i) T)
      2 (nonnegativeLebesgueMeasure.prod P) := by
  convert hm.continuousLinearMap_comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i) using 1
  funext q
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
  · simp [FourPapersCommon.continuousAdaptedTimeCut,ht]
  · simp [FourPapersCommon.continuousAdaptedTimeCut,Set.mem_prod,ht]

@[expose] def stateClassOfMemLp (X : ℝ≥0 → Ω → State N)
    (ha : StronglyAdapted F X) (hc : ∀ᵐ ω ∂P,Continuous (fun s => X s ω)) (T : ℝ≥0)
    (hm : MemLp ((Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω)).indicator (fun q => X q.1 q.2))
      2 (nonnegativeLebesgueMeasure.prod P)) : PredictableStateL2 N F P :=
  ∑ i : Fin N,scalarToStatePredictable i (coefficientPredictableActual ha hc
    (CutoffSDE.coordinate_lipschitz i).continuous T (coordinate_timeCut_memLp T hm i))

theorem stateClassOfMemLp_coe (X : ℝ≥0 → Ω → State N)
    (ha : StronglyAdapted F X) (hc : ∀ᵐ ω ∂P,Continuous (fun s => X s ω)) (T : ℝ≥0)
    (hm : MemLp ((Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω)).indicator (fun q => X q.1 q.2))
      2 (nonnegativeLebesgueMeasure.prod P)) :
    ((Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω)).indicator (fun q => X q.1 q.2))=ᵐ[
      nonnegativeLebesgueMeasure.prod P]
      (stateClassOfMemLp X ha hc T hm : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  let V (i : Fin N) := coefficientPredictableActual ha hc
    (CutoffSDE.coordinate_lipschitz i).continuous T (coordinate_timeCut_memLp T hm i)
  have hsum := sumState_coeFn (fun i => scalarToStatePredictable i (V i))
  have hi := ae_all_iff.mpr (fun i => scalarToStatePredictable_coeFn i (V i))
  have hv : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ i,
      (V i : TimeProcessL2 P) q=FourPapersCommon.continuousAdaptedTimeCut (fun s ω => X s ω i) T q :=
    ae_all_iff.mpr (fun i => (coordinate_timeCut_memLp T hm i).coeFn_toLp)
  filter_upwards [hsum,hi,hv] with q hsum hi hv
  change _=((∑ i,scalarToStatePredictable i (V i) : PredictableStateL2 N F P) :
    Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q
  rw [hsum]
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
  · rw [Set.indicator_of_mem (show q∈Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω) from ⟨ht,Set.mem_univ _⟩)]
    simp only [hi,hv,FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left ht]
    exact (state_sum_basis (X q.1 q.2)).symm
  · simp only [Set.indicator_of_notMem (show q∉Ioc (0 : ℝ≥0) T×ˢ(Set.univ : Set Ω) from fun h => ht h.1),
      hi,hv,FourPapersCommon.continuousAdaptedTimeCut,ite_eq_right ht,zero_smul,Finset.sum_const_zero]

/-- True cutoff/random-initial pathwise uniqueness, with the predictable
state classes and their L² membership derived from the coefficient SDE. -/
theorem randomStrongSolutions_unique (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {σ : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (σ i j))
    (Z0 : Ω → State N) (hm : MemLp Z0 2 P) (X Y : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D (fun _ => b) (fun _ => σ) Z0 X T)
    (hY : IsRandomStrongSolutionOn D (fun _ => b) (fun _ => σ) Z0 Y T) :
    ∀ᵐ ω ∂P,∀ t,t≤T → X t ω=Y t ω := by
  have hXm := strongSolution_stateTimeCut_memLp D (fun _ => b) (fun _ => σ) Z0 hm X T hX
  have hYm := strongSolution_stateTimeCut_memLp D (fun _ => b) (fun _ => σ) Z0 hm Y T hY
  exact RandomInitialUniqueness.strongSolution_unique_of_stateClasses D hb hs Z0 hX.1 hm T
    (stateClassOfMemLp_coe X hX.2.1 hX.2.2.1 T hXm)
    (stateClassOfMemLp_coe Y hY.2.1 hY.2.2.1 T hYm)
    (randomStrongSolution_to_strongSolution D b σ (fun i => (hb i).continuous)
      (fun i j => (hs i j).continuous) Z0 X T hX)
    (randomStrongSolution_to_strongSolution D b σ (fun i => (hb i).continuous)
      (fun i j => (hs i j).continuous) Z0 Y T hY)

end SphericalAging.RandomSDEStateClass
