module

public import SphericalAging.StochasticLinearizationError
public import SphericalAging.TerminalStateRepresentation
public import SphericalAging.InhomogeneousLinearSDE

public section

/-! Genuine affine linear variational solutions with arbitrary predictable
L² drift and noise sources. Quadratic second-variation forcing need not be
almost surely bounded. The real continuous solution is constructed from
the actual full-driver drift and Itô operators. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.L2AffineVariationalSolution
open HardSphereDynamics LocalSDE PredictableLinearCoefficient PredictableDriftTime PredictableItoTime
open StochasticLinearizationError VolterraLinearity TerminalStateRepresentation LinearSDETimeFourthMoment
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks : ℝ≥0}

@[expose] def version (D : BrownianDriver N P F) (A : Fin N → PredictableProcessL2 F P)
    (S : Fin N → Fin N → PredictableProcessL2 F P) (T t : ℝ≥0) (omega : Ω) : State N :=
  ∑ i,(driftVersion (A i) T t omega+∑ j,itoVersion (D.brownian j)
    (D.coordinateStronglyMeasurable j) (D.filtered j) (S i j) t omega) • basisVector i

lemma version_apply (D : BrownianDriver N P F) (A : Fin N → PredictableProcessL2 F P)
    (S : Fin N → Fin N → PredictableProcessL2 F P) (T t : ℝ≥0) (omega : Ω) (i : Fin N) :
    version D A S T t omega i=driftVersion (A i) T t omega+
      ∑ j,itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) (S i j) t omega := by
  simp [version,basisVector,Pi.single_apply]

lemma version_adapted (D : BrownianDriver N P F) (A : Fin N → PredictableProcessL2 F P)
    (S : Fin N → Fin N → PredictableProcessL2 F P) (T : ℝ≥0) :
    StronglyAdapted F (version D A S T) := by
  intro t
  exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun i _ =>
    ((driftVersion_stronglyAdapted (A i) T t).add
      (Finset.stronglyMeasurable_fun_sum Finset.univ (fun j _ =>
        itoVersion_stronglyAdapted (D.brownian j) (D.coordinateStronglyMeasurable j)
          (D.filtered j) (S i j) t))).smul_const (basisVector i))

lemma version_continuous (D : BrownianDriver N P F) (A : Fin N → PredictableProcessL2 F P)
    (S : Fin N → Fin N → PredictableProcessL2 F P) (T : ℝ≥0) :
    ∀ᵐ omega ∂P,Continuous (fun t => version D A S T t omega) := by
  have hd := ae_all_iff.mpr (fun i : Fin N => driftVersion_ae_continuous (A i) T)
  have hs := ae_all_iff.mpr (fun i : Fin N => ae_all_iff.mpr (fun j : Fin N =>
    (itoVersion_continuousModification (D.brownian j) (D.coordinateStronglyMeasurable j)
      (D.filtered j) (S i j)).continuous_paths))
  filter_upwards [hd,hs] with omega hd hs
  exact continuous_finsetSum Finset.univ (fun i _ =>
    ((hd i).add (continuous_finsetSum Finset.univ (fun j _ => hs i j))).smul continuous_const)

lemma version_timeCut (D : BrownianDriver N P F) (A : Fin N → PredictableProcessL2 F P)
    (S : Fin N → Fin N → PredictableProcessL2 F P) (T : ℝ≥0) :
    stateTimeCut (version D A S T) T=ᵐ[nonnegativeLebesgueMeasure.prod P]
      ((driftSource T A+noiseSource D T S : PredictableStateL2 N F P) :
        Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  let R := fun i => driftOperator T (A i)+∑ j,itoOperator (D.brownian j)
    (D.coordinateStronglyMeasurable j) (D.filtered j) T (S i j)
  have he : driftSource T A+noiseSource D T S=∑ i,stateInclusion i (R i) := by
    simp only [driftSource,noiseSource,R,map_add,Finset.sum_add_distrib]
  rw [he]
  have hr (i : Fin N) : (R i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun q => if q.1∈Ioc (0 : ℝ≥0) T then driftVersion (A i) T q.1 q.2+
        ∑ j,itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) (S i j) q.1 q.2 else 0) := by
    have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun j =>
      (itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T (S i j) : TimeProcessL2 P))
    have hi := ae_all_iff.mpr (fun j : Fin N =>
      (itoVersion_timeCut_memLp (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) (S i j) T).coeFn_toLp)
    filter_upwards [Lp.coeFn_add (driftOperator T (A i) : TimeProcessL2 P)
      (∑ j,(itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T (S i j) : TimeProcessL2 P)),
      (driftVersion_timeCut_memLp (A i) T).coeFn_toLp,hs,hi] with q hadd hd hs hi
    simp only [R,Submodule.coe_add,Submodule.coe_sum]
    change ((driftOperator T (A i) : TimeProcessL2 P)+
      ∑ j,(itoOperator (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T (S i j) : TimeProcessL2 P)) q=_
    rw [hadd,Pi.add_apply,hs]
    change ((driftVersion_timeCut_memLp (A i) T).toLp _) q+_=_
    rw [hd]
    simp only [itoOperator_apply,itoVolterra,hi,FourPapersCommon.continuousAdaptedTimeCut]
    by_cases ht : q.1∈Ioc (0 : ℝ≥0) T <;> simp only [ht,ite_true,ite_false,Finset.sum_const_zero,add_zero]
  have hs := sumState_coeFn (fun i => stateInclusion i (R i))
  have hi := ae_all_iff.mpr (fun i : Fin N => scalarToStatePredictable_coeFn i (R i))
  filter_upwards [hs,hi,ae_all_iff.mpr hr] with q hs hi hr
  rw [hs]
  simp only [stateInclusion_apply,hi,hr,stateTimeCut,version]
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T <;> simp only [ht,ite_true,ite_false,zero_smul,Finset.sum_const_zero]

section Response
variable (D : BrownianDriver N P F)
  (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
  (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
  (R : Fin N → PredictableProcessL2 F P)
  (S : Fin N → Fin N → PredictableProcessL2 F P) (T : ℝ≥0)

@[expose] def responseClass : PredictableStateL2 N F P :=
  LinearVariationalSDE.sourceClass D a sigma T (driftSource T R+noiseSource D T S)

@[expose] def driftRows (i : Fin N) : PredictableProcessL2 F P :=
  PredictableLinearCoefficient.apply (a i) (responseClass D a sigma R S T)+R i

@[expose] def noiseRows (i j : Fin N) : PredictableProcessL2 F P :=
  PredictableLinearCoefficient.apply (sigma i j) (responseClass D a sigma R S T)+S i j

@[expose] def process : ℝ≥0 → Ω → State N := version D (driftRows D a sigma R S T) (noiseRows D a sigma R S T) T

@[expose] def terminal (t : ℝ≥0) : Lp (State N) 2 P :=
  TerminalStateRepresentation.terminalClass D 0 (driftRows D a sigma R S T) (noiseRows D a sigma R S T) T t

theorem responseClass_full_fixedPoint : responseClass D a sigma R S T=
    driftSource T (driftRows D a sigma R S T)+noiseSource D T (noiseRows D a sigma R S T) := by
  have he := LinearVariationalSDE.sourceClass_fixedPoint D a sigma T (driftSource T R+noiseSource D T S)
  change responseClass D a sigma R S T=_ at he
  rw [he]
  simp only [driftRows,noiseRows,driftSource,noiseSource,map_add,Finset.sum_add_distrib,
    LinearVariationalSDE.finiteDriftPicardMap,LinearVariationalSDE.driftCoefficientMap,
    LinearVariationalSDE.finiteNoisePicardMap,LinearVariationalSDE.stochasticCoefficientMap,
    stateInclusion_apply,driftOperator_apply,itoOperator_apply]
  abel

theorem process_timeCut : stateTimeCut (process D a sigma R S T) T=ᵐ[nonnegativeLebesgueMeasure.prod P]
    (responseClass D a sigma R S T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  rw [responseClass_full_fixedPoint]
  exact version_timeCut D _ _ T

theorem terminal_ae (t : ℝ≥0) : terminal D a sigma R S T t=ᵐ[P] process D a sigma R S T t := by
  have he := TerminalStateRepresentation.terminalClass_ae D 0 (driftRows D a sigma R S T)
    (noiseRows D a sigma R S T) T t
  change TerminalStateRepresentation.terminalClass D 0 _ _ T t=ᵐ[P]
    (fun omega => ∑ i,(driftVersion (driftRows D a sigma R S T i) T t omega+
      ∑ j,itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
        (D.filtered j) (noiseRows D a sigma R S T i j) t omega) • basisVector i)
  simpa only [PiLp.zero_apply,zero_add] using he

/-- Actual affine variational Itô semantics with general L² sources. -/
@[expose] def IsStrongSolutionOn (f : Fin N → ℝ≥0 → Ω → ℝ)
    (g : Fin N → Fin N → ℝ≥0 → Ω → ℝ) (Y : ℝ≥0 → Ω → State N) : Prop :=
  StronglyAdapted F Y ∧ (∀ᵐ omega ∂P,Continuous (fun t => Y t omega)) ∧
  ∃ A : Fin N → PredictableProcessL2 F P,∃ U : Fin N → Fin N → PredictableProcessL2 F P,
    (∀ i,(A i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => (a i).value (t,omega) (Y t omega)+f i t omega) T) ∧
    (∀ i j,(U i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => (sigma i j).value (t,omega) (Y t omega)+g i j t omega) T) ∧
    ∀ t,t≤T → ∀ i,∀ᵐ omega ∂P,Y t omega i=
      (∫ r in (0 : ℝ)..(t : ℝ),(a i).value (r.toNNReal,omega) (Y r.toNNReal omega)+f i r.toNNReal omega)+
      (driverItoMap D (fun j => FourPapersCommon.FilteredBrownian.predictableTimeRestrict F t (U i j)) : Ω → ℝ) omega

/-- The constructed continuous response solves the genuine same-driver
affine SDE with the literal arbitrary square-integrable forcing fields. -/
theorem process_strongSolution
    (f : Fin N → ℝ≥0 → Ω → ℝ) (g : Fin N → Fin N → ℝ≥0 → Ω → ℝ)
    (hR : ∀ i,(R i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (f i) T)
    (hS : ∀ i j,(S i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (g i j) T) :
    IsStrongSolutionOn D a sigma T f g (process D a sigma R S T) := by
  have hc := process_timeCut D a sigma R S T
  have hcut : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
      (fun q => process D a sigma R S T q.1 q.2))=ᵐ[nonnegativeLebesgueMeasure.prod P]
        (responseClass D a sigma R S T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
    have he : stateTimeCut (process D a sigma R S T) T=
        ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator
          (fun q => process D a sigma R S T q.1 q.2)) := by
      funext q
      by_cases ht : q.1∈Ioc (0 : ℝ≥0) T <;> simp [stateTimeCut,ht]
    rw [he] at hc
    exact hc
  have hA (i : Fin N) : (driftRows D a sigma R S T i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => (a i).value (t,omega) (process D a sigma R S T t omega)+f i t omega) T := by
    filter_upwards [Lp.coeFn_add (PredictableLinearCoefficient.apply (a i) (responseClass D a sigma R S T) : TimeProcessL2 P) (R i),
      LinearVariationalSDE.apply_eq_actual hcut (a i),hR i] with q hadd ha hr
    change ((PredictableLinearCoefficient.apply (a i) (responseClass D a sigma R S T) : TimeProcessL2 P)+(R i : TimeProcessL2 P)) q=_
    rw [hadd,Pi.add_apply,ha,hr]
    by_cases ht : q.1∈Ioc (0 : ℝ≥0) T <;> simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,ite_false,zero_add]
  have hU (i j : Fin N) : (noiseRows D a sigma R S T i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t omega => (sigma i j).value (t,omega) (process D a sigma R S T t omega)+g i j t omega) T := by
    filter_upwards [Lp.coeFn_add (PredictableLinearCoefficient.apply (sigma i j) (responseClass D a sigma R S T) : TimeProcessL2 P) (S i j),
      LinearVariationalSDE.apply_eq_actual hcut (sigma i j),hS i j] with q hadd ha hr
    change ((PredictableLinearCoefficient.apply (sigma i j) (responseClass D a sigma R S T) : TimeProcessL2 P)+(S i j : TimeProcessL2 P)) q=_
    rw [hadd,Pi.add_apply,ha,hr]
    by_cases ht : q.1∈Ioc (0 : ℝ≥0) T <;> simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,ite_false,zero_add]
  refine ⟨version_adapted D _ _ T,version_continuous D _ _ T,driftRows D a sigma R S T,
    noiseRows D a sigma R S T,hA,hU,?_⟩
  intro t ht i
  have hd := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun r omega => (a i).value (r,omega) (process D a sigma R S T r omega)+f i r omega)
    T (driftRows D a sigma R S T i) (hA i)
  have hn := TerminalStateRepresentation.driverIto_ae_eq_versions D (noiseRows D a sigma R S T i) t
  filter_upwards [hd,hn] with omega hd hn
  rw [hn,show process D a sigma R S T t omega i=driftVersion (driftRows D a sigma R S T i) T t omega+
    ∑ j,itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) (noiseRows D a sigma R S T i j) t omega from version_apply D _ _ T t omega i]
  rw [hd t ht]

end Response
end SphericalAging.L2AffineVariationalSolution
