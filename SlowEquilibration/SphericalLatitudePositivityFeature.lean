-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeThreeBlock
public import SlowEquilibration.SphericalPositivePerturbation

@[expose] public section

/-! # Literal finite positivity feature on the tangent sphere

The actual radius-sqrt(n) transverse spin is rescaled to a unit spin.
The held finite Gaussian tensor feature has diagonal budget at most 4v²,
uniformly in dimension, degree count and positive-cube parameters.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalPositivePerturbation
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n P K : ℕ}

def latitudeUnitScale (n : ℕ) (x : Vector n) : Vector n := (Real.sqrt (n : ℝ))⁻¹ • x

theorem latitudeUnitScale_continuous (n : ℕ) : Continuous (latitudeUnitScale n) := by
  change Continuous (fun x : Vector n => (Real.sqrt (n : ℝ))⁻¹ • x)
  exact (continuous_id : Continuous (fun x : Vector n => x)).const_smul ((Real.sqrt (n : ℝ))⁻¹)

theorem latitudeUnitScale_norm (hn : 1 ≤ n) (x : Vector n) (hx : ‖x‖^2=(n : ℝ)) :
    ‖latitudeUnitScale n x‖=1 := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn0
  have hnrm : ‖x‖=Real.sqrt (n : ℝ) := by rw [← hx,Real.sqrt_sq (norm_nonneg x)]
  rw [latitudeUnitScale,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hsq),hnrm,
    inv_mul_cancel₀ hsq.ne']

def latitudePositivityFeature (n K : ℕ) (v : ℝ) (cube : Fin K → ℝ)
    (x : Vector n) : PerturbationDisorder n K :=
  feature (coefficients v cube) (latitudeUnitScale n x)

theorem latitudePositivityFeature_continuous (n K : ℕ) (v : ℝ) (cube : Fin K → ℝ) :
    Continuous (latitudePositivityFeature n K v cube) :=
  (feature_continuous _).comp (latitudeUnitScale_continuous n)

theorem latitudePositivityFeature_norm_sq_le (hn : 1 ≤ n) {v : ℝ} (hv : 0 ≤ v)
    (cube : Fin K → ℝ) (hcube : ∀ p,|cube p| ≤ 2)
    (x : Vector n) (hx : ‖x‖^2=(n : ℝ)) :
    ‖latitudePositivityFeature n K v cube x‖^2 ≤ (2*v)^2 := by
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 2*v)).mpr
  exact feature_norm_le _ (by positivity) (coefficients_budget v cube hcube) _
    (latitudeUnitScale_norm hn x hx)

/-- Actual finite held tensor coefficients, with the original/trial
coordinates preserved literally. -/
def latitudeCubeCoefficient (cube : Fin K → ℝ) :
    LatitudeThreeCoordinate n P (TensorCoordinate n K) → ℝ
  | Sum.inl _ => 1
  | Sum.inr i => cube i.1

def latitudeCubeOperator (cube : Fin K → ℝ) :
    LatitudeThreeDisorder n P (TensorCoordinate n K) →L[ℝ]
      LatitudeThreeDisorder n P (TensorCoordinate n K) :=
  GaussianSpinComparison.diagonal (latitudeCubeCoefficient cube)

theorem latitudeCubeOperator_joint_continuous (n P K : ℕ) :
    Continuous (fun z : (Fin K → ℝ) × LatitudeThreeDisorder n P (TensorCoordinate n K) =>
      latitudeCubeOperator z.1 z.2) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : LatitudeThreeCoordinate n P (TensorCoordinate n K) => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro i
  cases i with
  | inl j =>
      simpa [latitudeCubeOperator,GaussianSpinComparison.diagonal_apply,latitudeCubeCoefficient,Function.comp_def,Pi.mul_apply] using
        (PiLp.continuous_apply 2 (fun _ : LatitudeThreeCoordinate n P (TensorCoordinate n K) => ℝ)
          (Sum.inl j)).comp continuous_snd
  | inr j =>
      change Continuous ((fun z : (Fin K → ℝ) × LatitudeThreeDisorder n P (TensorCoordinate n K) => z.1 j.1)*
        (fun z => z.2 (Sum.inr j)))
      exact (((continuous_apply j.1).comp continuous_fst).mul
        ((PiLp.continuous_apply 2 (fun _ : LatitudeThreeCoordinate n P (TensorCoordinate n K) => ℝ)
          (Sum.inr j)).comp continuous_snd))

theorem latitudeCubeOperator_rotation (cube : Fin K → ℝ) (θ : ℝ)
    (D : LatitudeThreeDisorder n P (TensorCoordinate n K)) :
    GaussianThreeBlockComparison.rotation latitudeThreeLabel θ (latitudeCubeOperator cube D)=
      latitudeCubeOperator cube (GaussianThreeBlockComparison.rotation latitudeThreeLabel θ D) := by
  ext i
  simp only [GaussianThreeBlockComparison.rotation_apply,latitudeCubeOperator,
    GaussianSpinComparison.diagonal_apply]
  ring

/-- The cube parameters act on the literal held Gaussian coordinates;
all fields share the same original and linear Gaussian blocks. -/
theorem latitudeThreeLinear_positivity_cube (c : Degree P → ℝ) (β κ : ℝ)
    (u : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (q v : ℝ)
    (cube : Fin K → ℝ) (x : Vector n)
    (D : LatitudeThreeDisorder n P (TensorCoordinate n K)) :
    latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube) x D=
      latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v (fun _ => 1)) x
        (latitudeCubeOperator cube D) := by
  simp only [latitudeThreeLinear,innerSL_apply_apply,PiLp.inner_apply,RCLike.inner_apply,
    conj_trivial,Fintype.sum_sum_type,latitudeThreeFeature,latitudeCubeOperator,
    GaussianSpinComparison.diagonal_apply,latitudeCubeCoefficient,one_mul,
    latitudePositivityFeature,feature,coefficients,mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- A true uniformly bounded physical three-block feature for every
positive-cube realization; no replica estimate is assumed. -/
theorem latitudeThreeLinear_positivity_bound (hn : 1 ≤ n) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (β : ℝ) {κ : ℝ} (hκ : 0 ≤ κ)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1 : ℕ) : ℝ))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (he : ∀ x,inner ℝ (e x) u=0)
    {q : ℝ} (hq : |q| ≤ 1) {v : ℝ} (hv : 0 ≤ v)
    (cube : Fin K → ℝ) (hcube : ∀ p,|cube p| ≤ 2) :
    ∀ᵐ x ∂sphereLaw n,
      ‖latitudeThreeLinear c β κ u e q (latitudePositivityFeature n K v cube) x‖ ≤
        Real.sqrt (β^2*((n+1 : ℕ) : ℝ)*covariancePolynomial c 1+κ*(n : ℝ)+(2*v)^2) := by
  filter_upwards [sphereLaw_support hn] with x hx
  rw [latitudeThreeLinear,innerSL_apply_norm]
  have hB : 0 ≤ β^2*((n+1 : ℕ) : ℝ)*covariancePolynomial c 1+κ*(n : ℝ)+(2*v)^2 := by
    have hcov : 0 ≤ covariancePolynomial c 1 := by
      unfold covariancePolynomial
      exact Finset.sum_nonneg fun p _ => by simpa only [one_pow,mul_one] using hc p
    positivity
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt hB,latitudeThreeFeature_norm_sq,latitudeGuerraFeature_norm_sq hn c hc β hκ u hu e he hq x hx]
  exact add_le_add le_rfl (latitudePositivityFeature_norm_sq_le hn hv cube hcube x hx)

end
end SlowEquilibration.SphericalModel
