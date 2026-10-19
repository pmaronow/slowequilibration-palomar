module

public import SphericalAging.HamiltonianDisorderForcingOperator
public import SphericalAging.HamiltonianDisorderIncrement

public section

/-! Exact actual tensor-parameter linearization of the Hamiltonian SDE
fixed point, using its true Jacobian and true affine disorder forcing. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.HamiltonianDisorderLinearization
open HardSphereDynamics LocalSDE VariationalCoefficients HamiltonianPicardDependence
open PredictableItoTime PredictableDriftTime StochasticFlowDerivative LinearResolvent VolterraLinearity
open StochasticTaylorRemainder StochasticLinearizationError HamiltonianDisorderForcingOperator
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def driftRows (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (A : ℝ≥0)
    (J : BoundedDisorder N p A) (x : State N) (T : ℝ≥0) :=
  StochasticFlowDerivative.driftRows D (cutoffDrift_contDiff β J.1 R hR)
    (drift_family_lipschitz β R hR A J) (noise_family_lipschitz N R hR) x T

@[expose]  def noiseRows (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (A : ℝ≥0)
    (J : BoundedDisorder N p A) (x : State N) (T : ℝ≥0) :=
  StochasticFlowDerivative.noiseRows D (cutoffNoise_contDiff R hR)
    (drift_family_lipschitz β R hR A J) (noise_family_lipschitz N R hR) x T

@[expose]  def forcingVectorOperator (β R : ℝ) (hR : 0 < R) (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    FiniteModel.Disorder N p →L[ℝ] (Fin N → PredictableProcessL2 F P) :=
  ContinuousLinearMap.pi (fun i => forcingOperator β R hR T U i)

@[expose]  def response (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (A : ℝ≥0)
    (J : BoundedDisorder N p A) (x : State N) (T : ℝ≥0) :
    FiniteModel.Disorder N p →L[ℝ] PredictableStateL2 N F P :=
  (sourceLinearMap D (driftRows D β R hR A J x T) (noiseRows D β R hR A J x T) T).comp
    ((driftSourceOperator T).comp (forcingVectorOperator β R hR T (hamiltonianClass D β R hR A T (J,x))))

 theorem finiteDrift_parameter_change {Jb Kb : ℝ≥0} (β : ℝ)
    (J K : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R)
    (hj : ∀ i,LipschitzWith Jb (CutoffSDE.cutoffDrift β J R hR i))
    (hk : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β K R hR i))
    (T : ℝ≥0) (U : PredictableStateL2 N F P) :
    PredictableDriftTime.finiteDriftPicardMap hk T U-PredictableDriftTime.finiteDriftPicardMap hj T U =
      driftSource T (fun i => forcingOperator β R hR T U i (K-J)) := by
  classical
  unfold PredictableDriftTime.finiteDriftPicardMap PredictableDriftTime.driftCoefficientMap driftSource
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  change stateInclusion i (driftOperator T (predictableCoefficient (hk i) U T))-
      stateInclusion i (driftOperator T (predictableCoefficient (hj i) U T)) = _
  rw [← map_sub,← map_sub,coefficient_drift_affine_difference β J K R hR hj hk T U i]

 theorem driftSource_add (T : ℝ≥0) (r s : Fin N → PredictableProcessL2 F P) :
    driftSource T (fun i => r i+s i)=driftSource T r+driftSource T s := by
  have h := (driftSourceOperator (N := N) (F := F) (P := P) T).map_add r s
  change driftSource T (r+s)=driftSource T r+driftSource T s
  simpa only [driftSourceOperator_apply] using h

/-- Exact actual nonlinear disorder increment equals the true Jacobian
resolvent of the linear forcing plus actual state Taylor and parameter
cross errors. -/
 theorem increment_resolvent (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (A : ℝ≥0)
    (J K : BoundedDisorder N p A) (x : State N) (T : ℝ≥0) :
    let U := hamiltonianClass D β R hR A T (J,x)
    let V := hamiltonianClass D β R hR A T (K,x)
    let X := GlobalSDE.horizonProcess D (drift_family_lipschitz β R hR A J) (noise_family_lipschitz N R hR) x T
    let ha := GlobalSDE.horizonProcess_stronglyAdapted D (drift_family_lipschitz β R hR A J) (noise_family_lipschitz N R hR) x T
    let hc := GlobalSDE.horizonProcess_continuous D (drift_family_lipschitz β R hR A J) (noise_family_lipschitz N R hR) x T
    let rb := fun i => remainder ha hc (cutoffDrift_contDiff β J.1 R hR i) (drift_family_lipschitz β R hR A J i) T U V
    let rs := fun i j => remainder ha hc (cutoffNoise_contDiff R hR i j) (noise_family_lipschitz N R hR i j) T U V
    let cross := fun i => forcingOperator β R hR T V i (K.1-J.1)-forcingOperator β R hR T U i (K.1-J.1)
    V-U = sourceLinearMap D (driftRows D β R hR A J x T) (noiseRows D β R hR A J x T) T
      (driftSource T (fun i => forcingOperator β R hR T U i (K.1-J.1))+
        driftSource T rb+driftSource T cross+noiseSource D T rs) := by
  classical
  dsimp only
  let hj := drift_family_lipschitz β R hR A J
  let hk := drift_family_lipschitz β R hR A K
  let hs := noise_family_lipschitz N R hR
  let U := hamiltonianClass D β R hR A T (J,x)
  let V := hamiltonianClass D β R hR A T (K,x)
  let ha := GlobalSDE.horizonProcess_stronglyAdapted D hj hs x T
  let hc := GlobalSDE.horizonProcess_continuous D hj hs x T
  have hU := GlobalSDE.horizonClass_fixedPoint D hj hs x T
  have hV := GlobalSDE.horizonClass_fixedPoint D hk hs x T
  have hparam := finiteDrift_parameter_change β J.1 K.1 R hR hj hk T V
  have hb := finiteDrift_linearization ha hc (cutoffDrift_contDiff β J.1 R hR) hj T U V
  have hn := finiteNoise_linearization ha hc D (cutoffNoise_contDiff R hR) hs T U V
  apply (LinearVariationalSDE.exists_unique_picard_fixedPoint D _ _ T _).choose_spec.2
  have hforcing : (fun i => forcingOperator β R hR T V i (K.1-J.1)) =
      (fun i => forcingOperator β R hR T U i (K.1-J.1)+
        (forcingOperator β R hR T V i (K.1-J.1)-forcingOperator β R hR T U i (K.1-J.1))) := by
    funext i
    abel
  rw [hforcing,driftSource_add] at hparam
  have h := congrArg₂ (fun v u : PredictableStateL2 N F P => v-u) hV hU
  calc
    V-U = (PredictableDriftTime.finiteDriftPicardMap hk T V-PredictableDriftTime.finiteDriftPicardMap hj T V)+
      (PredictableDriftTime.finiteDriftPicardMap hj T V-PredictableDriftTime.finiteDriftPicardMap hj T U)+
      (PredictableItoTime.finiteNoisePicardMap D hs T V-PredictableItoTime.finiteNoisePicardMap D hs T U) := h.trans (by dsimp [U,V,HamiltonianPicardDependence.hamiltonianClass];abel)
    _ = _ := by
      rw [hparam,hb,hn]
      unfold HamiltonianDisorderLinearization.driftRows HamiltonianDisorderLinearization.noiseRows
      unfold StochasticFlowDerivative.driftRows StochasticFlowDerivative.noiseRows
      dsimp only [U,V,hj,hs,ha,hc]
      abel
end SphericalAging.HamiltonianDisorderLinearization
