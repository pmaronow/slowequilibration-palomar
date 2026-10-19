-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairedTensorProjectionFeatures
public import SlowEquilibration.SphericalPosteriorMaps

/-! Same-axis higher projected traces of the actual finite mixed coefficient
model are unchanged by its literal value/score plus zero-gradient posterior
maps. Original value and gradient rows are computed from true tensor jets;
no row-orthogonality or posterior-mean premise is supplied. -/

@[expose] public section
namespace SlowEquilibration.PairedTensorProjectionFeatures
noncomputable section
open MeasureTheory ProbabilityTheory Function
open SphericalModel SphericalGaussianJet WholeFieldRegression IntrinsicGradientRegression
open SphericalPosteriorMaps SphericalSequentialRegression SphericalForm
open scoped RealInnerProductSpace BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def projectionDegree (P q j : ℕ) (hp : 2 ≤ q+j+j) (hP : q+j+j ≤ P) : Degree P :=
  ⟨⟨q+j+j,by omega⟩,hp⟩

def projectedDegreeDisorder (P q j : ℕ) (hp : 2 ≤ q+j+j) (hP : q+j+j ≤ P)
    {N : ℕ} (x : Vector N) : Disorder N P :=
  Pi.single (projectionDegree P q j hp hP) (fun I => pairedTensorFeature N q j x I)

def pairedDegreeSeed (P q j : ℕ) (hp : 2 ≤ q+j+j) (hP : q+j+j ≤ P)
    {N : ℕ} (x : Vector N) : EuclideanDisorder N P :=
  euclideanDisorder (projectedDegreeDisorder P q j hp hP x)

/-- Exact original degree-block realization; the model degree is fixed
before the physical dimension and before either conditioning mark. -/
theorem field_projectedDegreeDisorder {N : ℕ} (P q j : ℕ) (hp : 2 ≤ q+j+j) (hP : q+j+j ≤ P)
    (c : Degree P → ℝ) (x v : Vector N) :
    field c (projectedDegreeDisorder P q j hp hP x) v=
      Real.sqrt (c (projectionDegree P q j hp hP))*
        SphericalAging.FiniteModel.Hamiltonian N (q+j+j) (fun I => pairedTensorFeature N q j x I) v := by
  classical
  unfold field blockField projectedDegreeDisorder
  rw [Finset.sum_eq_single (projectionDegree P q j hp hP)]
  · simp only [Pi.single_eq_same]
    rfl
  · intro p hmem hne
    rw [Pi.single_eq_of_ne hne]
    simp only [SphericalAging.FiniteModel.Hamiltonian,Pi.zero_apply,zero_mul,Finset.sum_const_zero,mul_zero]
  · simp

theorem field_projectedDegreeDisorder_axis_zero {N : ℕ} (hN : 0 < N)
    (P q j : ℕ) (hj : 0 < j) (hp : 2 ≤ q+j+j) (hP : q+j+j ≤ P)
    (c : Degree P → ℝ) (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    field c (projectedDegreeDisorder P q j hp hP x) x=0 := by
  rw [field_projectedDegreeDisorder,pairedTensorFeature_Hamiltonian_axis_zero hN q j hj x hx,mul_zero]

/-- All actual mixed-field one-jets of this original coefficient vector vanish. -/
theorem jet_one_projectedDegreeDisorder_zero {N : ℕ} (hN : 0 < N)
    (P q j : ℕ) (hj : 0 < j) (hp : 2 ≤ q+j+j) (hP : q+j+j ≤ P)
    (c : Degree P → ℝ) (x h : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    jet c 1 x (fun _ => h) (projectedDegreeDisorder P q j hp hP x)=0 := by
  classical
  rw [jet_sum,Finset.sum_eq_single (projectionDegree P q j hp hP)]
  · simp only [projectedDegreeDisorder,Pi.single_eq_same,iteratedFDeriv_one_apply]
    change Real.sqrt (c (projectionDegree P q j hp hP))*
      (fderiv ℝ (SphericalAging.FiniteModel.Hamiltonian N (q+j+j)
        (fun I => pairedTensorFeature N q j x I)) x) h=0
    rw [pairedTensorFeature_Hamiltonian_directional_zero hN q j hj x h hx,mul_zero]
  · intro p hmem hne
    simp only [projectedDegreeDisorder,Pi.single_eq_of_ne hne]
    have hz : SphericalAging.FiniteModel.Hamiltonian N p.val.val (0 : SphericalAging.FiniteModel.Disorder N p.val.val)=
        (fun _ => (0 : ℝ)) := by
      funext v
      simp [SphericalAging.FiniteModel.Hamiltonian]
    rw [hz]
    simp
  · simp

/-- The original field gradient of the actual degree-block coefficient vector is zero. -/
theorem gradient_projectedDegreeDisorder_zero {N : ℕ} (hN : 0 < N)
    (P q j : ℕ) (hj : 0 < j) (hp : 2 ≤ q+j+j) (hP : q+j+j ≤ P)
    (c : Degree P → ℝ) (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    gradient (field c (projectedDegreeDisorder P q j hp hP x)) x=0 := by
  apply ext_inner_left ℝ
  intro h
  rw [real_inner_comm,inner_gradient_left,inner_zero_right]
  simpa only [jet,iteratedFDeriv_one_apply] using
    jet_one_projectedDegreeDisorder_zero hN P q j hj hp hP c x h hx

/-- Literal score observations of the actual mixed model annihilate this seed. -/
theorem pairedDegreeSeed_score_zero {N : ℕ} (hN : 0 < N)
    (P q j : ℕ) (hj : 0 < j) (hp : 2 ≤ q+j+j) (hP : q+j+j ≤ P)
    (c : Degree P → ℝ) (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    scoreCLM c x (pairedDegreeSeed P q j hp hP x)=0 := by
  ext i
  fin_cases i
  · change scoreCLM c x (pairedDegreeSeed P q j hp hP x) 0=0
    rw [scoreCLM_apply_zero]
    simp only [pairedDegreeSeed,unpack_euclideanDisorder,jet,iteratedFDeriv_zero_apply]
    exact field_projectedDegreeDisorder_axis_zero hN P q j hj hp hP c x hx
  · change scoreCLM c x (pairedDegreeSeed P q j hp hP x) 1=0
    rw [scoreCLM_apply_one]
    simp only [pairedDegreeSeed,unpack_euclideanDisorder]
    exact jet_one_projectedDegreeDisorder_zero hN P q j hj hp hP c x x hx

/-- Actual value observation row also vanishes, including proper-pure conditioning. -/
theorem pairedDegreeSeed_value_zero {N : ℕ} (hN : 0 < N)
    (P q j : ℕ) (hj : 0 < j) (hp : 2 ≤ q+j+j) (hP : q+j+j ≤ P)
    (c : Degree P → ℝ) (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    valueCLM c x (pairedDegreeSeed P q j hp hP x)=0 := by
  rw [valueCLM,flatJetCLM_apply]
  simp only [pairedDegreeSeed,unpack_euclideanDisorder,jet,iteratedFDeriv_zero_apply]
  exact field_projectedDegreeDisorder_axis_zero hN P q j hj hp hP c x hx

/-- Actual ambient/surface gradient observation, computed from the true field. -/
theorem pairedDegreeSeed_surfaceGamma_zero {N : ℕ} (hN : 0 < N)
    (P q j : ℕ) (hj : 0 < j) (hp : 2 ≤ q+j+j) (hP : q+j+j ≤ P)
    (c : Degree P → ℝ) (x : Vector N) (hx : ‖x‖^2=(N : ℝ)) :
    surfaceGamma c x (pairedDegreeSeed P q j hp hP x)=0 := by
  rw [surfaceGamma,ContinuousLinearMap.comp_apply,ambientGradientCLM_apply]
  simp only [pairedDegreeSeed,unpack_euclideanDisorder]
  rw [gradient_projectedDegreeDisorder_zero hN P q j hj hp hP c x hx,map_zero]

variable (n : ℕ) (μ : FiniteMixture) (Q : ℝ) (q j : ℕ) (hj : 0 < j)
  (hp : 2 ≤ q+j+j) (hP : q+j+j ≤ μ.maxDegree)
  (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))

include hj hu

private theorem seed_scoreLift_inner_zero (b : EuclideanSpace ℝ (Fin 2)) :
    inner ℝ (pairedDegreeSeed μ.maxDegree q j hp hP u) (scoreLift n μ Q u b)=0 := by
  rw [scoreLift,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    pairedDegreeSeed_score_zero (by omega) μ.maxDegree q j hj hp hP _ u hu,inner_zero_left]

private theorem seed_valueLift_inner_zero (b : ℝ) :
    inner ℝ (pairedDegreeSeed μ.maxDegree q j hp hP u) (valueLift n μ Q u b)=0 := by
  rw [valueLift,ContinuousLinearMap.comp_apply,ContinuousLinearMap.adjoint_inner_right,
    pairedDegreeSeed_value_zero (by omega) μ.maxDegree q j hj hp hP _ u hu,inner_zero_left]

private theorem seed_gradientResidual_inner (g : EuclideanDisorder (n+1) μ.maxDegree) :
    inner ℝ (pairedDegreeSeed μ.maxDegree q j hp hP u) (gradientResidual n μ Q u g)=
      inner ℝ (pairedDegreeSeed μ.maxDegree q j hp hP u) g := by
  simp only [gradientResidual,_root_.sub_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,inner_sub_right,
    real_inner_smul_right,ContinuousLinearMap.adjoint_inner_right]
  rw [pairedDegreeSeed_surfaceGamma_zero (by omega) μ.maxDegree q j hj hp hP _ u hu,
    inner_zero_left,mul_zero,sub_zero]

/-- Same-axis higher projected trace is pointwise preserved by the literal
actual mixed score/zero-gradient posterior, for every original seed and both marks. -/
theorem actual_mixedPosterior_pairedDegree_inner (b : EuclideanSpace ℝ (Fin 2))
    (g : EuclideanDisorder (n+1) μ.maxDegree) :
    inner ℝ (pairedDegreeSeed μ.maxDegree q j hp hP u) (mixedPosterior n μ Q u b g)=
      inner ℝ (pairedDegreeSeed μ.maxDegree q j hp hP u) g := by
  rw [mixedPosterior,inner_add_right,seed_gradientResidual_inner n μ Q q j hj hp hP u hu,
    seed_scoreLift_inner_zero n μ Q q j hj hp hP u hu,add_zero]
  simp only [scoreResidual,_root_.sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,inner_sub_right]
  rw [seed_scoreLift_inner_zero n μ Q q j hj hp hP u hu,sub_zero]

/-- The proper value/zero-gradient posterior has the identical preservation,
without using or inverting a redundant pure score covariance. -/
theorem actual_valuePosterior_pairedDegree_inner (e : ℝ)
    (g : EuclideanDisorder (n+1) μ.maxDegree) :
    inner ℝ (pairedDegreeSeed μ.maxDegree q j hp hP u) (valuePosterior n μ Q u e g)=
      inner ℝ (pairedDegreeSeed μ.maxDegree q j hp hP u) g := by
  rw [valuePosterior,inner_add_right,seed_gradientResidual_inner n μ Q q j hj hp hP u hu,
    seed_valueLift_inner_zero n μ Q q j hj hp hP u hu,add_zero]
  simp only [valueResidual,_root_.sub_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply,inner_sub_right]
  rw [seed_valueLift_inner_zero n μ Q q j hj hp hP u hu,sub_zero]

end
end SlowEquilibration.PairedTensorProjectionFeatures
