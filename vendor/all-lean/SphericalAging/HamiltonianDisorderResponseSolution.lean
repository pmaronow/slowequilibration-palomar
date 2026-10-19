module

public import SphericalAging.HamiltonianDisorderTerminalDerivative
public import SphericalAging.AffineVariationalSolution

public section

/-! The proved tensor-disorder derivative is realized by an actual
continuous adapted inhomogeneous Jacobian SDE, with the true tensor
forcing. Both predictable and fixed-terminal derivative classes are
identified with the same genuine response process. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HamiltonianDisorderResponseSolution
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open PredictableItoTime PredictableDriftTime HamiltonianPicardDependence GlobalHamiltonianParameter
open HamiltonianDisorderDerivative HamiltonianDisorderLinearization HamiltonianDisorderForcingOperator
open HamiltonianPredictableForcing TerminalLinearity TerminalStateRepresentation
set_option maxHeartbeats 1600000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def baseProcess (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) :=
  GlobalSDE.horizonProcess D (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩)
    (noise_family_lipschitz N R hR) x T

@[expose]  def forcing (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J δ : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) (i : Fin N) :
    InhomogeneousLinearSDE.Forcing (F := F) (P := P) (disorderConstant (N := N) (p := p) β R hR*‖δ‖₊) where
  value := FourPapersCommon.continuousAdaptedTimeCut (fun t omega =>
    CutoffSDE.cutoffDrift β δ R hR i (baseProcess D β R hR J x T t omega)-
    CutoffSDE.cutoffDrift β (0 : FiniteModel.Disorder N p) R hR i (baseProcess D β R hR J x T t omega)) T
  predictable := (disorderForcing (baseProcess D β R hR J x T)
    (GlobalSDE.horizonProcess_stronglyAdapted D (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩)
      (noise_family_lipschitz N R hR) x T)
    (GlobalSDE.horizonProcess_continuous D (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩)
      (noise_family_lipschitz N R hR) x T) β 0 δ R hR T i).predictable
  bound := .of_forall (fun q => by
    by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_true,NNReal.coe_mul,coe_nnnorm]
      simpa only [sub_zero] using scalar_disorder_bound β (0 : FiniteModel.Disorder N p) δ R hR i
        (baseProcess D β R hR J x T q.1 q.2)
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,ht,ite_false,norm_zero]
      exact (disorderConstant (N := N) (p := p) β R hR*‖δ‖₊).coe_nonneg)

 theorem forcing_value (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J δ : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) (i : Fin N) (q : ℝ≥0 × Ω) :
    (forcing D β R hR J δ x T i).value q = if q.1 ∈ Ioc 0 T then
      CutoffSDE.cutoffDrift β δ R hR i (baseProcess D β R hR J x T q.1 q.2)-
      CutoffSDE.cutoffDrift β (0 : FiniteModel.Disorder N p) R hR i (baseProcess D β R hR J x T q.1 q.2) else 0 := by
  rfl

 theorem forcingClass_eq (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J δ : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) (i : Fin N) :
    AffineVariationalSolution.forcingClass (forcing D β R hR J δ x T i) T =
      forcingOperator β R hR T (globalClass D β R hR T (J,x)) i δ := by
  let U := globalClass D β R hR T (J,x)
  let hb0 := (CutoffSDE.cutoffDrift_lipschitz β (0 : FiniteModel.Disorder N p) R hR).choose_spec
  let hbδ := (CutoffSDE.cutoffDrift_lipschitz β δ R hR).choose_spec
  have he := coefficient_drift_affine_difference β (0 : FiniteModel.Disorder N p) δ R hR hb0 hbδ T U i
  simp only [sub_zero] at he
  apply AffineVariationalSolution.forcingClass_eq_of_coe
  rw [← he]
  filter_upwards [Lp.coeFn_sub (predictableCoefficient (hbδ i) U T : TimeProcessL2 P)
      (predictableCoefficient (hb0 i) U T),predictableCoefficient_coeFn (hbδ i) U T,
    predictableCoefficient_coeFn (hb0 i) U T,
    GlobalSDE.horizonProcess_timeCut D (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩)
      (noise_family_lipschitz N R hR) x T] with q hsub hδ h0 hX
  simp only [Submodule.coe_sub]
  rw [hsub,Pi.sub_apply,hδ,h0]
  rw [FourPapersCommon.continuousAdaptedTimeCut,forcing_value]
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · have hx : baseProcess D β R hR J x T q.1 q.2 =
        (U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q := by
      simpa only [baseProcess,U,globalClass,hamiltonianClass,indicator_of_mem (show q ∈ Ioc 0 T ×ˢ (univ : Set Ω) from ⟨ht,mem_univ _⟩)] using hX
    simp only [ht,ite_true,hx]
  · simp only [ht,ite_false,sub_self]

 theorem responseClass_eq (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J δ : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) :
    AffineVariationalSolution.responseClass D
      (HamiltonianDisorderLinearization.driftRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T)
      (HamiltonianDisorderLinearization.noiseRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T)
      (forcing D β R hR J δ x T) T = disorderResponse D β R hR J x T δ := by
  simp only [AffineVariationalSolution.responseClass,forcingClass_eq,disorderResponse,
    HamiltonianDisorderLinearization.response,ContinuousLinearMap.comp_apply,driftSourceOperator_apply,forcingVectorOperator]
  rfl

@[expose]  def process (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J δ : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) : ℝ≥0 → Ω → State N :=
  AffineVariationalSolution.response D
    (HamiltonianDisorderLinearization.driftRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T)
    (HamiltonianDisorderLinearization.noiseRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T)
    (forcing D β R hR J δ x T) T

 theorem process_strongSolution (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J δ : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) :
    InhomogeneousLinearSDE.IsStrongSolutionOn
      (HamiltonianDisorderLinearization.driftRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T)
      (HamiltonianDisorderLinearization.noiseRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T)
      (forcing D β R hR J δ x T) D 0 (process D β R hR J δ x T) T :=
  AffineVariationalSolution.response_strongSolution D _ _ _ T

 theorem process_timeCut (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J δ : FiniteModel.Disorder N p) (x : State N) (T : ℝ≥0) :
    ((Ioc (0 : ℝ≥0) T ×ˢ (univ : Set Ω)).indicator (fun q => process D β R hR J δ x T q.1 q.2))
      =ᵐ[nonnegativeLebesgueMeasure.prod P]
        (disorderResponse D β R hR J x T δ : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) := by
  have h := AffineVariationalSolution.response_timeCut D
    (HamiltonianDisorderLinearization.driftRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T)
    (HamiltonianDisorderLinearization.noiseRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T)
    (forcing D β R hR J δ x T) T
  rwa [responseClass_eq] at h

 theorem terminalResponse_ae (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J δ : FiniteModel.Disorder N p) (x : State N) (T t : ℝ≥0) :
    HamiltonianDisorderTerminalDerivative.stateResponse D β R hR J x T t δ =ᵐ[P]
      process D β R hR J δ x T t := by
  rw [HamiltonianDisorderTerminalDerivative.stateResponse_eq_terminalClass]
  have h := AffineVariationalSolution.terminalClass_ae_response D
    (HamiltonianDisorderLinearization.driftRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T)
    (HamiltonianDisorderLinearization.noiseRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T)
    (forcing D β R hR J δ x T) T t
  change terminalClass D 0
    (fun i => apply (HamiltonianDisorderLinearization.driftRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T i)
      (AffineVariationalSolution.responseClass D _ _ (forcing D β R hR J δ x T) T)+
      AffineVariationalSolution.forcingClass (forcing D β R hR J δ x T i) T)
    (fun i j => apply (HamiltonianDisorderLinearization.noiseRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T i j)
      (AffineVariationalSolution.responseClass D _ _ (forcing D β R hR J δ x T) T)) T t =ᵐ[P]
      process D β R hR J δ x T t at h
  simpa only [responseClass_eq,forcingClass_eq] using h
end SphericalAging.HamiltonianDisorderResponseSolution
