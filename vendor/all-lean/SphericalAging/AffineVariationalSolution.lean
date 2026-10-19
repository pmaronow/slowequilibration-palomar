module

public import SphericalAging.InhomogeneousLinearSDE
public import SphericalAging.StochasticLinearizationError
public import SphericalAging.TerminalStateRepresentation

public section

/-! Genuine bounded predictable affine variational response. The response
is the constructed source resolvent and the forcing classes come from the
specified forcing values. Its continuous version solves the actual
inhomogeneous matrix SDE and has its actual terminal L² representative. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.AffineVariationalSolution
open HardSphereDynamics LocalSDE PredictableDriftTime PredictableItoTime
open PredictableLinearCoefficient LinearVariationalSDE StochasticLinearizationError
open VolterraLinearity TerminalStateRepresentation
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks B : ℝ≥0}

lemma forcingCut_predictable (f : InhomogeneousLinearSDE.Forcing (F := F) (P := P) B) (T : ℝ≥0) :
    AEStronglyMeasurable[F.predictable] (FourPapersCommon.continuousAdaptedTimeCut
      (fun t ω => f.value (t,ω)) T) (nonnegativeLebesgueMeasure.prod P) := by
  refine ⟨(FourPapersCommon.FilteredBrownian.predictableTimeFrame T).indicator
    (f.predictable.mk f.value), f.predictable.stronglyMeasurable_mk.indicator
      (FourPapersCommon.FilteredBrownian.measurableSet_predictableTimeFrame F T),?_⟩
  filter_upwards [f.predictable.ae_eq_mk] with q hq
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T <;>
    simp [FourPapersCommon.continuousAdaptedTimeCut,
      FourPapersCommon.FilteredBrownian.predictableTimeFrame,ht,hq]

lemma forcingCut_memLp (f : InhomogeneousLinearSDE.Forcing (F := F) (P := P) B) (T : ℝ≥0) :
    MemLp (FourPapersCommon.continuousAdaptedTimeCut (fun t ω => f.value (t,ω)) T)
      2 (nonnegativeLebesgueMeasure.prod P) := by
  have hm := memLp_indicator_const (μ := nonnegativeLebesgueMeasure.prod P) 2
    (measurableSet_Ioc.prod MeasurableSet.univ) (B : ℝ)
    (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle T))
  apply hm.mono' ((forcingCut_predictable f T).mono (predictable_le_prod F))
  filter_upwards [f.bound] with q hq
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · simpa only [FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left ht,
      indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩),
      Real.norm_eq_abs,abs_of_nonneg B.coe_nonneg] using hq
  · simp [FourPapersCommon.continuousAdaptedTimeCut,ht]

/-- Genuine predictable L² class of the specified forcing restricted to
its deterministic horizon. -/
@[expose] def forcingClass (f : InhomogeneousLinearSDE.Forcing (F := F) (P := P) B) (T : ℝ≥0) :
    PredictableProcessL2 F P :=
  ⟨(forcingCut_memLp f T).toLp _,
    (forcingCut_predictable f T).congr (forcingCut_memLp f T).coeFn_toLp.symm⟩

lemma forcingClass_coe (f : InhomogeneousLinearSDE.Forcing (F := F) (P := P) B) (T : ℝ≥0) :
    (forcingClass f T : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun t ω => f.value (t,ω)) T :=
  (forcingCut_memLp f T).coeFn_toLp

/-- The true zero-initial response class, obtained by solving the bounded
linear Picard equation with the actual forcing drift source. -/
@[expose] def responseClass (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B) (T : ℝ≥0) :
    PredictableStateL2 N F P :=
  sourceClass D a sigma T (driftSource T (fun i => forcingClass (forcing i) T))

/-- Actual affine drift classes for any trial state class. -/
@[expose] def driftRows (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P) (i : Fin N) : PredictableProcessL2 F P :=
  PredictableLinearCoefficient.apply (a i) Q + forcingClass (forcing i) T

@[expose] def affineDriftMap (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P) : PredictableStateL2 N F P :=
  ∑ i : Fin N, scalarToStatePredictable i (driftVolterra T (driftRows a forcing T Q i))

lemma affineDriftMap_eq (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P) :
    affineDriftMap a forcing T Q = LinearVariationalSDE.finiteDriftPicardMap a T Q +
      driftSource T (fun i => forcingClass (forcing i) T) := by
  unfold affineDriftMap driftRows LinearVariationalSDE.finiteDriftPicardMap
    LinearVariationalSDE.driftCoefficientMap driftSource
  simp only [driftVolterra_add,stateInclusion_apply,driftOperator_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (stateInclusion i).map_add _ _

lemma responseClass_fixedPoint (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B) (T : ℝ≥0) :
    responseClass D a sigma forcing T = affineDriftMap a forcing T (responseClass D a sigma forcing T) +
      LinearVariationalSDE.finiteNoisePicardMap D sigma T (responseClass D a sigma forcing T) := by
  rw [affineDriftMap_eq]
  have hf := sourceClass_fixedPoint D a sigma T (driftSource T (fun i => forcingClass (forcing i) T))
  exact hf.trans (by abel)

@[expose] def coordinateVersion (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P) (i : Fin N) (t : ℝ≥0) (ω : Ω) : ℝ :=
  driftVersion (driftRows a forcing T Q i) T t ω +
    ∑ j : Fin N, itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
      (PredictableLinearCoefficient.apply (sigma i j) Q) t ω

@[expose] def version (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P) (t : ℝ≥0) (ω : Ω) : State N :=
  ∑ i : Fin N, coordinateVersion D a sigma forcing T Q i t ω • basisVector i

lemma version_apply (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P) (t : ℝ≥0) (ω : Ω) (i : Fin N) :
    version D a sigma forcing T Q t ω i = coordinateVersion D a sigma forcing T Q i t ω := by
  simp [version,basisVector,Pi.single_apply]

lemma version_stronglyAdapted (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P) : StronglyAdapted F (version D a sigma forcing T Q) := by
  intro t
  apply Finset.stronglyMeasurable_fun_sum Finset.univ
  intro i _
  apply StronglyMeasurable.smul_const
  exact (driftVersion_stronglyAdapted _ T t).add
    (Finset.stronglyMeasurable_fun_sum Finset.univ (fun j _ =>
      itoVersion_stronglyAdapted (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) _ t))

lemma version_ae_continuous (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P) :
    ∀ᵐ ω ∂P, Continuous (fun t => version D a sigma forcing T Q t ω) := by
  have hd := ae_all_iff.mpr (fun i : Fin N => driftVersion_ae_continuous (driftRows a forcing T Q i) T)
  have hs := ae_all_iff.mpr (fun i : Fin N => ae_all_iff.mpr (fun j : Fin N =>
    (itoVersion_continuousModification (D.brownian j) (D.coordinateStronglyMeasurable j)
      (D.filtered j) (PredictableLinearCoefficient.apply (sigma i j) Q)).continuous_paths))
  filter_upwards [hd,hs] with ω hd hs
  exact continuous_finsetSum Finset.univ (fun i _ =>
    ((hd i).add (continuous_finsetSum Finset.univ (fun j _ => hs i j))).smul continuous_const)

lemma affineDriftMap_coe (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P) :
    (affineDriftMap a forcing T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (fun q => if q.1 ∈ Ioc (0 : ℝ≥0) T then
        ∑ i : Fin N, driftVersion (driftRows a forcing T Q i) T q.1 q.2 • basisVector i else 0) := by
  have hsum := sumState_coeFn (fun i => scalarToStatePredictable i (driftVolterra T (driftRows a forcing T Q i)))
  have hi := ae_all_iff.mpr (fun i => scalarToStatePredictable_coeFn i (driftVolterra T (driftRows a forcing T Q i)))
  have hc : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P, ∀ i : Fin N,
      (driftVolterra T (driftRows a forcing T Q i) : TimeProcessL2 P) q =
        FourPapersCommon.continuousAdaptedTimeCut (driftVersion (driftRows a forcing T Q i) T) T q :=
    ae_all_iff.mpr (fun i => (driftVersion_timeCut_memLp (driftRows a forcing T Q i) T).coeFn_toLp)
  filter_upwards [hsum,hi,hc] with q hsum hi hc
  change ((∑ i : Fin N, scalarToStatePredictable i (driftVolterra T (driftRows a forcing T Q i)) :
    PredictableStateL2 N F P) : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q = _
  rw [hsum]
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T <;>
    simp [hi,hc,FourPapersCommon.continuousAdaptedTimeCut,ht]

lemma version_timeCut_eq (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P)
    (hQ : Q = affineDriftMap a forcing T Q + LinearVariationalSDE.finiteNoisePicardMap D sigma T Q) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => version D a sigma forcing T Q q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  have he : (Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) =
      (affineDriftMap a forcing T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) +
        (LinearVariationalSDE.finiteNoisePicardMap D sigma T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) :=
    congrArg Subtype.val hQ
  rw [he]
  filter_upwards [affineDriftMap_coe a forcing T Q,finiteNoisePicardMap_coeFn D sigma T Q,
    Lp.coeFn_add (affineDriftMap a forcing T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))
      (LinearVariationalSDE.finiteNoisePicardMap D sigma T Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))]
    with q hd hs hadd
  rw [hadd,Pi.add_apply,hd,hs]
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [indicator_of_mem (show q ∈ Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩),
      ite_eq_left ht,version,coordinateVersion,add_smul,Finset.sum_add_distrib]
  · simp [ht]

/-- The constructed forcing class agrees with any actual predictable class
whose value is the specified forcing timecut. -/
lemma forcingClass_eq_of_coe (f : InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T : ℝ≥0) (r : PredictableProcessL2 F P)
    (hr : (r : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun t ω => f.value (t,ω)) T) :
    forcingClass f T = r := by
  apply Subtype.ext
  apply Lp.ext
  exact (forcingClass_coe f T).trans hr.symm

lemma driftRows_eq_actual (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P) (X : ℝ≥0 → Ω → State N)
    (hQ : ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => X q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P] (Q : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P))) (i : Fin N) :
    (driftRows a forcing T Q i : TimeProcessL2 P) =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut
        (fun t ω => (a i).value (t,ω) (X t ω) + (forcing i).value (t,ω)) T := by
  filter_upwards [Lp.coeFn_add (PredictableLinearCoefficient.apply (a i) Q : TimeProcessL2 P)
    (forcingClass (forcing i) T : TimeProcessL2 P),
    LinearVariationalSDE.apply_eq_actual hQ (a i),forcingClass_coe (forcing i) T]
    with q hadd ha hf
  change ((PredictableLinearCoefficient.apply (a i) Q + forcingClass (forcing i) T : PredictableProcessL2 F P) :
    TimeProcessL2 P) q = _
  simp only [Submodule.coe_add]
  rw [hadd,Pi.add_apply,ha,hf]
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T <;>
    simp [FourPapersCommon.continuousAdaptedTimeCut,ht]

/-- The genuine continuous affine version solves the actual inhomogeneous
matrix SDE when its class solves the actual affine Picard equation. -/
theorem strongSolution_of_fixedPoint (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T : ℝ≥0) (Q : PredictableStateL2 N F P)
    (hQ : Q = affineDriftMap a forcing T Q + LinearVariationalSDE.finiteNoisePicardMap D sigma T Q) :
    InhomogeneousLinearSDE.IsStrongSolutionOn a sigma forcing D 0 (version D a sigma forcing T Q) T := by
  have hrep := version_timeCut_eq D a sigma forcing T Q hQ
  have hA := fun i => driftRows_eq_actual a forcing T Q _ hrep i
  have hS := fun i j => LinearVariationalSDE.apply_eq_actual hrep (sigma i j)
  refine ⟨version_stronglyAdapted D a sigma forcing T Q,version_ae_continuous D a sigma forcing T Q,
    driftRows a forcing T Q,(fun i j => PredictableLinearCoefficient.apply (sigma i j) Q),hA,hS,?_⟩
  intro t ht i
  have hd := InhomogeneousLinearSDE.driftVersion_eq_actual_of_coe
    (fun t ω => (a i).value (t,ω) (version D a sigma forcing T Q t ω) + (forcing i).value (t,ω))
    T (driftRows a forcing T Q i) (hA i)
  have hn := TerminalStateRepresentation.driverIto_ae_eq_versions D
    (fun j => PredictableLinearCoefficient.apply (sigma i j) Q) t
  filter_upwards [hd,hn] with ω hd hn
  rw [version_apply]
  change driftVersion (driftRows a forcing T Q i) T t ω +
    (∑ j : Fin N, itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
      (PredictableLinearCoefficient.apply (sigma i j) Q) t ω) = _
  rw [hd t ht,hn]
  simp only [PiLp.zero_apply,zero_add]

/-- The actual terminal L² class of the continuous affine version. -/
theorem terminalClass_ae_version (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B)
    (T t : ℝ≥0) (Q : PredictableStateL2 N F P) :
    terminalClass D 0 (driftRows a forcing T Q)
      (fun i j => PredictableLinearCoefficient.apply (sigma i j) Q) T t =ᵐ[P]
      version D a sigma forcing T Q t := by
  have h := terminalClass_ae D 0 (driftRows a forcing T Q)
    (fun i j => PredictableLinearCoefficient.apply (sigma i j) Q) T t
  change (terminalClass D 0 (driftRows a forcing T Q)
    (fun i j => PredictableLinearCoefficient.apply (sigma i j) Q) T t : Ω → State N) =ᵐ[P]
    (fun ω => ∑ i : Fin N, (driftVersion (driftRows a forcing T Q i) T t ω +
      ∑ j : Fin N, itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
        (D.filtered j) (PredictableLinearCoefficient.apply (sigma i j) Q) t ω) • basisVector i)
  simpa only [PiLp.zero_apply,zero_add] using h

/-- Canonical actual zero-initial affine response process. -/
@[expose] def response (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B) (T : ℝ≥0) :
    ℝ≥0 → Ω → State N := version D a sigma forcing T (responseClass D a sigma forcing T)

theorem response_timeCut (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B) (T : ℝ≥0) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => response D a sigma forcing T q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (responseClass D a sigma forcing T : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) :=
  version_timeCut_eq D a sigma forcing T _ (responseClass_fixedPoint D a sigma forcing T)

theorem response_strongSolution (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B) (T : ℝ≥0) :
    InhomogeneousLinearSDE.IsStrongSolutionOn a sigma forcing D 0 (response D a sigma forcing T) T :=
  strongSolution_of_fixedPoint D a sigma forcing T _ (responseClass_fixedPoint D a sigma forcing T)

theorem terminalClass_ae_response (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B) (T t : ℝ≥0) :
    terminalClass D 0 (driftRows a forcing T (responseClass D a sigma forcing T))
      (fun i j => PredictableLinearCoefficient.apply (sigma i j) (responseClass D a sigma forcing T)) T t =ᵐ[P]
      response D a sigma forcing T t := terminalClass_ae_version D a sigma forcing T t _

theorem response_memLp (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (forcing : Fin N → InhomogeneousLinearSDE.Forcing (F := F) (P := P) B) (T t : ℝ≥0) :
    MemLp (response D a sigma forcing T t) 2 P :=
  (Lp.memLp _).ae_eq (terminalClass_ae_response D a sigma forcing T t)

end SphericalAging.AffineVariationalSolution
