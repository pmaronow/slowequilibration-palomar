module

public import SphericalAging.HamiltonianDisorderCoefficientDerivative
public import SphericalAging.TerminalStateRepresentation
public import SphericalAging.CanonicalSphereProcess

public section

/-! True fixed-terminal L² tensor-disorder differentiation of the actual
cutoff Hamiltonian SDE. The terminal state retains the genuine sphere
support and its derivative is assembled from the proved coefficient
Jacobians and actual drift/Itô terminal operators. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HamiltonianDisorderTerminalDerivative
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open PredictableItoTime PredictableDriftTime HamiltonianPicardDependence GlobalHamiltonianParameter
open HamiltonianDisorderDerivative HamiltonianDisorderLinearization HamiltonianDisorderForcingOperator
open HamiltonianCoefficientDependence HamiltonianDisorderCoefficientDerivative
open TerminalLinearity TerminalStateRepresentation
set_option maxHeartbeats 1600000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def stateClass (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T t : ℝ≥0) : Lp (State N) 2 P :=
  terminalClass D x (fun i => driftClass D β R hR T i (J,x))
    (fun i j => noiseClass D β R hR T i j (J,x)) T t

@[expose]  def stateResponse (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T t : ℝ≥0) :
    FiniteModel.Disorder N p →L[ℝ] Lp (State N) 2 P :=
  ∑ i,(stateTerminalInclusion i).comp
    ((driftTerminalOperator T t).comp (driftResponse D β R hR J x T i)+
      ∑ j,(itoTerminalOperator D j t).comp (noiseResponse D β R hR J x T i j))

/-- Actual fixed-terminal L² Fréchet derivative of the constructed
Hamiltonian process in every finite ordered tensor disorder. -/
 theorem stateClass_hasFDerivAt_disorder (D₀ : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T t : ℝ≥0) :
    HasFDerivAt (fun K : FiniteModel.Disorder N p => stateClass (NullAugmentation.driver D₀) β R hR K x T t)
      (stateResponse (NullAugmentation.driver D₀) β R hR J x T t) J := by
  classical
  let D := NullAugmentation.driver D₀
  have hbi (i : Fin N) := driftClass_hasFDerivAt_disorder D₀ β R hR J x T i
  have hsi (i j : Fin N) := noiseClass_hasFDerivAt_disorder D₀ β R hR J x T i j
  have hdi (i : Fin N) := (driftTerminalOperator T t).hasFDerivAt.comp J (hbi i)
  have hni (i j : Fin N) := (itoTerminalOperator D j t).hasFDerivAt.comp J (hsi i j)
  have hrow (i : Fin N) := (stateTerminalInclusion (P := P) i).hasFDerivAt.comp J
    ((hdi i).add (HasFDerivAt.fun_sum (fun j (_ : j ∈ Finset.univ) => hni i j)))
  have hresult := (hasFDerivAt_const (initialTerminalOperator (P := P) x) J).add
    (HasFDerivAt.fun_sum (fun i (_ : i ∈ Finset.univ) => hrow i))
  convert hresult using 1
  · funext K
    rfl
  · simp only [zero_add,stateResponse,ContinuousLinearMap.comp_assoc]
    rfl

 theorem stateClass_ae (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J : FiniteModel.Disorder N p) (x : State N) (T t : ℝ≥0) :
    stateClass D β R hR J x T t =ᵐ[P] HamiltonianJointProcess.process D β R hR T (J,x) t := by
  exact nonlinear_terminalClass_ae D
    (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩)
    (noise_family_lipschitz N R hR) x T t _

 theorem stateClass_onSphere (hN : N ≠ 0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : FiniteModel.Disorder N p) (x : State N) (hx : OnSphere x)
    (T t : ℝ≥0) (ht : t ≤ T) :
    ∀ᵐ omega ∂P, OnSphere ((stateClass (NullAugmentation.driver D₀) β R hR J x T t) omega) := by
  let D := NullAugmentation.driver D₀
  let hb := drift_family_lipschitz β R hR (‖J‖₊+1) (⟨J,by simp⟩)
  let hs := noise_family_lipschitz N R hR
  filter_upwards [stateClass_ae D β R hR J x T t,
    GlobalSDE.process_eq_horizon D hb hs x T,
    CanonicalSphereProcess.globalProcess_onSphere hN D₀ β R hR hNR (J,x) hx] with omega hstate hglob hsphere
  rw [hstate]
  change OnSphere (GlobalSDE.horizonProcess D hb hs x T t omega)
  rw [← hglob t ht]
  exact hsphere t

/-- The identified terminal derivative is the actual terminal class of
its forced Jacobian response, with the genuine tensor forcing included. -/
 theorem stateResponse_eq_terminalClass (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R)
    (J δ : FiniteModel.Disorder N p) (x : State N) (T t : ℝ≥0) :
    stateResponse D β R hR J x T t δ = terminalClass D 0
      (fun i => apply (HamiltonianDisorderLinearization.driftRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T i)
        (disorderResponse D β R hR J x T δ)+forcingOperator β R hR T (globalClass D β R hR T (J,x)) i δ)
      (fun i j => apply (HamiltonianDisorderLinearization.noiseRows D β R hR (‖J‖₊+1) ⟨J,by simp⟩ x T i j)
        (disorderResponse D β R hR J x T δ)) T t := by
  simp only [stateResponse,terminalClass,driftResponse,noiseResponse,add_apply,sum_apply,
    ContinuousLinearMap.comp_apply,coefficientOperator_apply,map_zero,zero_add]
end SphericalAging.HamiltonianDisorderTerminalDerivative
