module

public import SphericalAging.TerminalLinearity

public section

/-! Actual finite-dimensional terminal L² representatives assembled from
the genuine drift and full-filtration Itô maps. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.TerminalStateRepresentation
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime TerminalLinearity
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def terminalClass (D : BrownianDriver N P F) (v : State N)
    (A : Fin N → PredictableProcessL2 F P) (S : Fin N → Fin N → PredictableProcessL2 F P)
    (T t : ℝ≥0) : Lp (State N) 2 P :=
  initialTerminalOperator v+∑ i,stateTerminalInclusion i
    (driftTerminalOperator T t (A i)+∑ j,itoTerminalOperator D j t (S i j))

 theorem terminalClass_ae (D : BrownianDriver N P F) (v : State N)
    (A : Fin N → PredictableProcessL2 F P) (S : Fin N → Fin N → PredictableProcessL2 F P)
    (T t : ℝ≥0) : terminalClass D v A S T t =ᵐ[P]
      (fun omega => ∑ i : Fin N, (v i+driftVersion (A i) T t omega+
        ∑ j : Fin N,itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
          (D.filtered j) (S i j) t omega) • basisVector i) := by
  classical
  let row := fun i => driftTerminalOperator T t (A i)+∑ j,itoTerminalOperator D j t (S i j)
  have hr : ∀ i : Fin N,(row i : Ω → ℝ) =ᵐ[P] (fun omega => driftVersion (A i) T t omega+
      ∑ j : Fin N,itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
        (D.filtered j) (S i j) t omega) := by
    intro i
    have hsum := Lp.coeFn_fun_finsetSum Finset.univ (fun j => itoTerminalOperator D j t (S i j))
    have hi := ae_all_iff.mpr (fun j : Fin N => itoVersion_ae_eq (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) (S i j) t)
    filter_upwards [Lp.coeFn_add (driftTerminalOperator T t (A i)) (∑ j,itoTerminalOperator D j t (S i j)),
      (driftVersion_memLp (A i) T t).coeFn_toLp,hsum,hi] with omega hadd hd hsum hi
    change ((driftTerminalOperator T t (A i)+∑ j,itoTerminalOperator D j t (S i j) : RandomL2 P) : Ω → ℝ) omega = _
    rw [hadd,Pi.add_apply,hsum]
    simpa only [driftTerminalOperator_apply,PredictableTerminalOperators.driftTerminal,hd,
      itoTerminalOperator_apply,hi] using (rfl : driftVersion (A i) T t omega+
        (∑ j : Fin N,itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
          (D.filtered j) (S i j) t omega)=_)
  have hb : ∀ i : Fin N,(stateTerminalInclusion i (row i) : Ω → State N) =ᵐ[P]
      (fun omega => (row i : Ω → ℝ) omega • basisVector i) := by
    intro i
    exact (ContinuousLinearMap.toSpanSingleton ℝ (basisVector i)).coeFn_compLp (row i)
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun i => stateTerminalInclusion i (row i))
  filter_upwards [Lp.coeFn_add (initialTerminalOperator (P := P) v)
      (∑ i,stateTerminalInclusion i (row i)),Lp.coeFn_const 2 P v,hs,
      ae_all_iff.mpr hr,ae_all_iff.mpr hb] with omega hadd hv hs hr hb
  change ((initialTerminalOperator v+∑ i,stateTerminalInclusion i (row i) : Lp (State N) 2 P) : Ω → State N) omega = _
  rw [hadd,Pi.add_apply,initialTerminalOperator_apply,hv,hs]
  simp only [hb,hr,add_smul,Finset.sum_add_distrib,state_sum_basis,Function.const_apply]
  abel

 theorem nonlinear_terminalClass_ae (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    {b : Fin N → State N → ℝ} {s : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith Kb (b i)) (hs : ∀ i j,LipschitzWith Ks (s i j))
    (v : State N) (T t : ℝ≥0) (U : PredictableStateL2 N F P) :
    terminalClass D v (fun i => predictableCoefficient (hb i) U T)
      (fun i j => predictableCoefficient (hs i j) U T) T t =ᵐ[P]
      LocalSDE.version D hb hs v T U t :=
  terminalClass_ae D v _ _ T t

 theorem linear_terminalClass_ae (D : BrownianDriver N P F) {Kb Ks : ℝ≥0}
    (a : Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Kb)
    (s : Fin N → Fin N → PredictableLinearCoefficient.Coefficient (N := N) (F := F) (P := P) Ks)
    (v : State N) (T t : ℝ≥0) (U : PredictableStateL2 N F P) :
    terminalClass D v (fun i => PredictableLinearCoefficient.apply (a i) U)
      (fun i j => PredictableLinearCoefficient.apply (s i j) U) T t =ᵐ[P]
      LinearVariationalSDE.version D a s v T U t :=
  terminalClass_ae D v _ _ T t

 theorem terminalClass_sub (D : BrownianDriver N P F) (v w : State N)
    (A B : Fin N → PredictableProcessL2 F P) (S Z : Fin N → Fin N → PredictableProcessL2 F P)
    (T t : ℝ≥0) : terminalClass D v A S T t-terminalClass D w B Z T t =
      terminalClass D (v-w) (fun i => A i-B i) (fun i j => S i j-Z i j) T t := by
  classical
  simp only [terminalClass,map_sub,map_add,Finset.sum_sub_distrib,Finset.sum_add_distrib]
  abel

 theorem driverIto_ae_eq_versions (D : BrownianDriver N P F)
    (S : Fin N → PredictableProcessL2 F P) (t : ℝ≥0) :
    (driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (S j)) : Ω → ℝ)
      =ᵐ[P] (fun omega => ∑ j : Fin N,itoVersion (D.brownian j)
        (D.coordinateStronglyMeasurable j) (D.filtered j) (S j) t omega) := by
  have hi := ae_all_iff.mpr (fun j : Fin N => itoVersion_ae_eq (D.brownian j)
    (D.coordinateStronglyMeasurable j) (D.filtered j) (S j) t)
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun j : Fin N =>
    FourPapersCommon.FilteredBrownian.naturalItoProcess (D.brownian j).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable j) (D.filtered j) (S j) t)
  rw [driverItoMap_apply]
  filter_upwards [hi,hs] with omega hi hs
  change ((∑ j : Fin N,FourPapersCommon.FilteredBrownian.naturalItoProcess
    (D.brownian j).toIsPreBrownianReal (D.coordinateStronglyMeasurable j) (D.filtered j) (S j) t :
    RandomL2 P) : Ω → ℝ) omega = _
  rw [hs]
  simp only [hi]
end SphericalAging.TerminalStateRepresentation
