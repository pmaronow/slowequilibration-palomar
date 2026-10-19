-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFeatureHeldPressure
public import SlowEquilibration.SphericalLatitudePositivityFeature
public import SlowEquilibration.GaussianThreeBlockParameterComparison
public import Mathlib.Probability.Kernel.MeasurableIntegral

/-! Literal positive tensor cube for arbitrary continuous original
features, with true joint Gibbs and quenched-pressure measurability. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianFeatureDirac

open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation SphericalPositivePerturbation
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open scoped Topology BigOperators RealInnerProductSpace

set_option maxHeartbeats 1700000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n K : ℕ}

abbrev cubeFeature (n K : ℕ) (v : ℝ) (cube : Fin K → ℝ) := SphericalModel.latitudePositivityFeature n K v cube

def cubeLinear (A : Vector n → EuclideanSpace ℝ ι) (β k v : ℝ) (cube : Fin K → ℝ) :=
  threeLinear A β k (cubeFeature n K v cube)

def cubeCoefficient (cube : Fin K → ℝ) : ThreeCoordinate n ι (TensorCoordinate n K) → ℝ
  | .inl _ => 1
  | .inr j => cube j.1

def cubeOperator (cube : Fin K → ℝ) :
    EuclideanSpace ℝ (ThreeCoordinate n ι (TensorCoordinate n K)) →L[ℝ]
      EuclideanSpace ℝ (ThreeCoordinate n ι (TensorCoordinate n K)) :=
  GaussianSpinComparison.diagonal (cubeCoefficient cube)

theorem cubeOperator_joint_continuous (n K : ℕ) :
    Continuous (fun p : (Fin K → ℝ) × EuclideanSpace ℝ (ThreeCoordinate n ι (TensorCoordinate n K)) =>
      cubeOperator p.1 p.2) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : ThreeCoordinate n ι (TensorCoordinate n K) => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i
  cases i with
  | inl j =>
      simpa [cubeOperator,GaussianSpinComparison.diagonal_apply,cubeCoefficient,Function.comp_def,Pi.mul_apply] using
        (PiLp.continuous_apply 2 (fun _ : ThreeCoordinate n ι (TensorCoordinate n K) => ℝ) (.inl j)).comp continuous_snd
  | inr j =>
      change Continuous ((fun p : (Fin K → ℝ) × EuclideanSpace ℝ (ThreeCoordinate n ι (TensorCoordinate n K)) => p.1 j.1)*
        (fun p => p.2 (.inr j)))
      exact ((continuous_apply j.1).comp continuous_fst).mul
        ((PiLp.continuous_apply 2 (fun _ : ThreeCoordinate n ι (TensorCoordinate n K) => ℝ) (.inr j)).comp continuous_snd)

theorem cubeOperator_rotation (cube : Fin K → ℝ) (θ : ℝ)
    (D : EuclideanSpace ℝ (ThreeCoordinate n ι (TensorCoordinate n K))) :
    GaussianThreeBlockComparison.rotation threeLabel θ (cubeOperator cube D)=
      cubeOperator cube (GaussianThreeBlockComparison.rotation threeLabel θ D) := by
  ext i
  simp only [GaussianThreeBlockComparison.rotation_apply,cubeOperator,GaussianSpinComparison.diagonal_apply]
  ring

theorem cubeLinear_realization (A : Vector n → EuclideanSpace ℝ ι) (β k v : ℝ)
    (cube : Fin K → ℝ) (x : Vector n)
    (D : EuclideanSpace ℝ (ThreeCoordinate n ι (TensorCoordinate n K))) :
    cubeLinear A β k v cube x D=cubeLinear A β k v (fun _ => 1) x (cubeOperator cube D) := by
  simp only [cubeLinear,threeLinear,innerSL_apply_apply,PiLp.inner_apply,RCLike.inner_apply,
    conj_trivial,Fintype.sum_sum_type,threeFeature,cubeOperator,GaussianSpinComparison.diagonal_apply,
    cubeCoefficient,one_mul,cubeFeature,SphericalModel.latitudePositivityFeature,feature,coefficients,mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

def cubeRealization (n K : ℕ) (θ : ℝ)
    (p : (Fin K → ℝ) × EuclideanSpace ℝ (ThreeCoordinate n ι (TensorCoordinate n K))) :=
  GaussianThreeBlockComparison.rotation threeLabel θ (cubeOperator p.1 p.2)

theorem cubeRealization_continuous (n K : ℕ) (θ : ℝ) : Continuous (cubeRealization (ι := ι) n K θ) :=
  (GaussianThreeBlockComparison.rotation threeLabel θ).continuous.comp (cubeOperator_joint_continuous n K)

theorem cubeLinear_continuous (A : Vector n → EuclideanSpace ℝ ι) (hA : Continuous A)
    (β k v : ℝ) (cube : Fin K → ℝ) : Continuous (cubeLinear A β k v cube) :=
  threeLinear_continuous A hA β k _ (SphericalModel.latitudePositivityFeature_continuous n K v cube)

theorem cube_gibbs_realization (A : Vector n → EuclideanSpace ℝ ι) (β k v θ : ℝ)
    (cube : Fin K → ℝ) (D : EuclideanSpace ℝ (ThreeCoordinate n ι (TensorCoordinate n K))) :
    gibbsMeasure (sphereLaw n) (GaussianThreeBlockComparison.rotatedLinear (cubeLinear A β k v cube) threeLabel θ) D=
      gibbsMeasure (sphereLaw n) (cubeLinear A β k v (fun _ => 1)) (cubeRealization n K θ (cube,D)) := by
  apply gibbsMeasure_congr_field
  exact .of_forall fun x => by
    rw [GaussianThreeBlockComparison.rotatedLinear,ContinuousLinearMap.comp_apply,
      cubeLinear_realization,← cubeOperator_rotation]
    rfl

theorem cube_logPartition_realization (A : Vector n → EuclideanSpace ℝ ι) (β k v θ : ℝ)
    (cube : Fin K → ℝ) (D : EuclideanSpace ℝ (ThreeCoordinate n ι (TensorCoordinate n K))) :
    logPartition (sphereLaw n) (cubeLinear A β k v cube) (GaussianThreeBlockComparison.rotation threeLabel θ D)=
      logPartition (sphereLaw n) (cubeLinear A β k v (fun _ => 1)) (cubeRealization n K θ (cube,D)) := by
  unfold logPartition
  congr 1
  unfold GaussianSpinInterpolation.moment weight
  apply integral_congr_ae
  exact .of_forall fun x => by
    dsimp only
    rw [cubeLinear_realization,← cubeOperator_rotation]
    rfl

theorem exists_cube_bound (hn : 1≤n) (A : Vector n → EuclideanSpace ℝ ι) (hA : Continuous A)
    (β k v : ℝ) (cube : Fin K → ℝ) :
    ∃ B : ℝ, 0≤B ∧ ∀ᵐ x ∂sphereLaw n,‖cubeLinear A β k v cube x‖≤B := by
  obtain ⟨B,hB,hbound⟩ := exists_threeLinear_sphere_bound A hA β k _
    (SphericalModel.latitudePositivityFeature_continuous n K v cube)
  exact ⟨B,hB,(sphereLaw_support hn).mono fun x hx => hbound x hx⟩

/-- Actual uniform feature envelope over the normalized positive cube. -/
theorem exists_uniform_cube_bound (hn : 1≤n) (A : Vector n → EuclideanSpace ℝ ι)
    (hA : Continuous A) (β k : ℝ) {v : ℝ} (hv : 0≤v) :
    ∃ B : ℝ, 0≤B ∧ ∀cube : Fin K → ℝ,(∀p,|cube p|≤2) →
      ∀ᵐ x ∂sphereLaw n,‖cubeLinear A β k v cube x‖≤B := by
  obtain ⟨C,hC,hbound⟩ := exists_twoLinear_sphere_bound A hA β k
  refine ⟨Real.sqrt (C^2+(2*v)^2),Real.sqrt_nonneg _,?_⟩
  intro cube hcube
  filter_upwards [sphereLaw_support hn] with x hx
  rw [cubeLinear,threeLinear,innerSL_apply_norm]
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity),threeFeature_norm_sq]
  have hc := hbound x hx
  rw [twoLinear,innerSL_apply_norm] at hc
  exact add_le_add ((sq_le_sq₀ (norm_nonneg _) hC).mpr hc)
    (SphericalModel.latitudePositivityFeature_norm_sq_le hn hv cube hcube x hx)

/-- Joint coefficient measurability of the genuine quenched pressure. -/
theorem cube_pressure_measurable (hn : 1≤n) (A : Vector n → EuclideanSpace ℝ ι)
    (hA : Continuous A) (β k v θ : ℝ) :
    Measurable (fun cube : Fin K → ℝ => GaussianThreeBlockComparison.averagedRotatedLogPartition
      (sphereLaw n) (cubeLinear A β k v cube) threeLabel θ) := by
  let T := cubeLinear (K := K) A β k v (fun _ => 1)
  obtain ⟨B,hB,hTb⟩ := exists_cube_bound (K := K) hn A hA β k v (fun _ => 1)
  have hT : Measurable T := (cubeLinear_continuous A hA β k v _).measurable
  have hm := (((logPartition_contDiff (sphereLaw n) T hT hB hTb).continuous.comp
    (cubeRealization_continuous (ι := ι) n K θ)).measurable.stronglyMeasurable.integral_prod_right'
    (ν := SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate n ι (TensorCoordinate n K)))).measurable
  convert hm using 1
  funext cube
  unfold GaussianThreeBlockComparison.averagedRotatedLogPartition
  apply integral_congr_ae
  exact .of_forall fun D => cube_logPartition_realization A β k v θ cube D

end SlowEquilibration.GaussianFeatureDirac
