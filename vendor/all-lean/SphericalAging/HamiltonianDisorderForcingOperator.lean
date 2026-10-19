module

public import SphericalAging.HamiltonianPredictableForcing
public import SphericalAging.StochasticLinearizationError
public import SphericalAging.GlobalHamiltonianParameter

public section

/-! The actual tensor-disorder forcing is a continuous linear operator
into predictable L² coefficient classes, and is Lipschitz in the state
class. Both identities use the genuine Hamiltonian tensor decomposition. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.HamiltonianDisorderForcingOperator
open HardSphereDynamics LocalSDE HamiltonianParameter HamiltonianPredictableForcing
open PredictableItoTime PredictableDriftTime VolterraLinearity StochasticLinearizationError
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose]  def couplingConstant (β R : ℝ) (hR : 0 < R) (I : FiniteModel.TensorIndex N p) : ℝ≥0 :=
  (couplingDrift_lipschitz β R hR I).choose

 theorem coupling_coordinate_lipschitz (β R : ℝ) (hR : 0 < R)
    (I : FiniteModel.TensorIndex N p) (i : Fin N) :
    LipschitzWith (couplingConstant β R hR I) (fun x : State N => couplingDrift β R hR I x i) := by
  simpa only [couplingConstant,one_mul,Function.comp_def] using
    (CutoffSDE.coordinate_lipschitz i).comp (couplingDrift_lipschitz β R hR I).choose_spec

@[expose]  def couplingClass (β R : ℝ) (hR : 0 < R) (T : ℝ≥0) (U : PredictableStateL2 N F P)
    (i : Fin N) (I : FiniteModel.TensorIndex N p) : PredictableProcessL2 F P :=
  predictableCoefficient (coupling_coordinate_lipschitz β R hR I i) U T

@[expose]  def forcingOperator (β R : ℝ) (hR : 0 < R) (T : ℝ≥0) (U : PredictableStateL2 N F P)
    (i : Fin N) : FiniteModel.Disorder N p →L[ℝ] PredictableProcessL2 F P :=
  ∑ I,(ContinuousLinearMap.proj I).smulRight (couplingClass β R hR T U i I)

 @[simp] theorem forcingOperator_apply (β R : ℝ) (hR : 0 < R) (T : ℝ≥0)
    (U : PredictableStateL2 N F P) (i : Fin N) (J : FiniteModel.Disorder N p) :
    forcingOperator β R hR T U i J=∑ I,J I • couplingClass β R hR T U i I := by
  simp only [forcingOperator,sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.proj_apply]

 theorem scalar_drift_affine_difference (β : ℝ) (J K : FiniteModel.Disorder N p)
    (R : ℝ) (hR : 0 < R) (i : Fin N) (x : State N) :
    CutoffSDE.cutoffDrift β K R hR i x-CutoffSDE.cutoffDrift β J R hR i x =
      ∑ I,(K I-J I)*(couplingDrift β R hR I x) i := by
  have h := congrArg (VariationalCoefficients.coordinate i) (cutoffDrift_vector_sub β K J R hR x)
  simpa only [CutoffSDE.cutoffDrift,map_sub,map_sum,map_smul,
    VariationalCoefficients.coordinate_apply,smul_eq_mul] using h

 theorem coefficient_drift_affine_difference {Jb Kb : ℝ≥0}
    (β : ℝ) (J K : FiniteModel.Disorder N p) (R : ℝ) (hR : 0 < R)
    (hj : ∀ i,LipschitzWith Jb (CutoffSDE.cutoffDrift β J R hR i))
    (hk : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β K R hR i))
    (T : ℝ≥0) (U : PredictableStateL2 N F P) (i : Fin N) :
    predictableCoefficient (hk i) U T-predictableCoefficient (hj i) U T=
      forcingOperator β R hR T U i (K-J) := by
  classical
  rw [forcingOperator_apply]
  apply Subtype.ext
  apply Lp.ext
  have hs := Lp.coeFn_fun_finsetSum Finset.univ (fun I => (K-J) I •
    (couplingClass β R hR T U i I : TimeProcessL2 P))
  have hm := ae_all_iff.mpr (fun I => Lp.coeFn_smul ((K-J) I)
    (couplingClass β R hR T U i I : TimeProcessL2 P))
  have hc := ae_all_iff.mpr (fun I : FiniteModel.TensorIndex N p => predictableCoefficient_coeFn
    (coupling_coordinate_lipschitz β R hR I i) U T)
  filter_upwards [Lp.coeFn_sub (predictableCoefficient (hk i) U T : TimeProcessL2 P)
    (predictableCoefficient (hj i) U T),predictableCoefficient_coeFn (hk i) U T,
    predictableCoefficient_coeFn (hj i) U T,hs,hm,hc] with q hd hk hj hs hm hc
  simp only [Submodule.coe_sub,Submodule.coe_sum,Submodule.coe_smul] at hd ⊢
  rw [hd,Pi.sub_apply,hk,hj,hs]
  have he : (∑ I : FiniteModel.TensorIndex N p,
      ((((K-J) I • (couplingClass β R hR T U i I : TimeProcessL2 P)) : TimeProcessL2 P) : ℝ≥0 × Ω → ℝ) q) =
      ∑ I : FiniteModel.TensorIndex N p,(K-J) I *
        (if q.1 ∈ Ioc 0 T then couplingDrift β R hR I ((U : Lp (State N) 2 (nonnegativeLebesgueMeasure.prod P)) q) i else 0) := by
    apply Finset.sum_congr rfl
    intro I _
    rw [hm I,Pi.smul_apply]
    change (K-J) I * (predictableCoefficient (coupling_coordinate_lipschitz β R hR I i) U T : TimeProcessL2 P) q = _
    rw [hc I]
  rw [he]
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · simp only [ht,ite_true,Pi.sub_apply]
    exact scalar_drift_affine_difference β J K R hR i _
  · simp only [ht,ite_false,mul_zero,Finset.sum_const_zero,sub_self]

 theorem forcingOperator_state_sub_bound (β R : ℝ) (hR : 0 < R) (T : ℝ≥0)
    (U V : PredictableStateL2 N F P) (i : Fin N) (J : FiniteModel.Disorder N p) :
    ‖forcingOperator β R hR T V i J-forcingOperator β R hR T U i J‖ ≤
      (∑ I : FiniteModel.TensorIndex N p,couplingConstant β R hR I : ℝ≥0)*‖J‖*‖V-U‖ := by
  classical
  rw [forcingOperator_apply,forcingOperator_apply,← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ I : FiniteModel.TensorIndex N p,‖J I • couplingClass β R hR T V i I-J I • couplingClass β R hR T U i I‖ := norm_sum_le _ _
    _ ≤ ∑ I : FiniteModel.TensorIndex N p,‖J‖*((couplingConstant β R hR I : ℝ)*‖V-U‖) := by
      apply Finset.sum_le_sum
      intro I _
      have hsub : J I • couplingClass β R hR T V i I-J I • couplingClass β R hR T U i I =
          J I • (couplingClass β R hR T V i I-couplingClass β R hR T U i I) := by module
      rw [hsub,norm_smul]
      exact mul_le_mul (norm_le_pi_norm J I)
        (norm_predictableCoefficient_sub_le (coupling_coordinate_lipschitz β R hR I i) V U T)
        (norm_nonneg _) (norm_nonneg _)
    _ = _ := by rw [NNReal.coe_sum,← Finset.mul_sum,← Finset.sum_mul];ring

@[expose]  def driftSourceOperator (T : ℝ≥0) : (Fin N → PredictableProcessL2 F P) →L[ℝ] PredictableStateL2 N F P :=
  ∑ i,(stateInclusion i).comp ((driftOperator T).comp (ContinuousLinearMap.proj i))

 @[simp] theorem driftSourceOperator_apply (T : ℝ≥0) (r : Fin N → PredictableProcessL2 F P) :
    driftSourceOperator T r=driftSource T r := by
  simp only [driftSourceOperator,driftSource,sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
end SphericalAging.HamiltonianDisorderForcingOperator
