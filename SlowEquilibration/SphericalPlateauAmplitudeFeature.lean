-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlateauAmplitudeFieldLaw
public import SlowEquilibration.SphericalPlateauAmplitudeDirections
public import SlowEquilibration.GaussianSelectedReplicaIBP

@[expose] public section

/-! # Literal Euclidean features and selected coordinates of the amplitude bank

The Gaussian parameter operator is exactly the physical source amplitude
rescaling, on every bank coordinate and the whole ambient spin space.
-/
namespace SlowEquilibration.SphericalPlateauAmplitudeModel
noncomputable section
open Set MeasureTheory ProbabilityTheory Metric
open SphericalModel GaussianPerturbationParameter GaussianSpinComparison
open scoped Topology BigOperators InnerProductSpace
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {n : ℕ}

/-- Genuine raw tensor coordinate feature of the entire ambient bank polynomial. -/
def amplitudeBankFeature (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (u : Vector (n+1)) : EuclideanBank n μ :=
  WithLp.toLp 2 (fun j => bankAmplitude p₀ s j.1*bankComponentScale μ x j.1 u*
    SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint u) j.2)

/-- The actual exponent feature includes precisely the original inverse temperature. -/
def amplitudeBankLinear (μ : FiniteMixture) (β : ℝ) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (u : Vector (n+1)) : EuclideanBank n μ →L[ℝ] ℝ :=
  β • innerSL ℝ (amplitudeBankFeature μ x e p₀ s u)

/-- The physical source degree-one or degree-two Gaussian bank block. -/
def amplitudeBankLabel (μ : FiniteMixture) (p₀ : Degree μ.maxDegree) (k : Fin 2)
    (j : BankCoordinate n μ) : Bool := decide (j.1.1=p₀ ∧ j.1.2.val=k.val+1)

theorem amplitudeBankFeature_continuous (μ : FiniteMixture) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    Continuous (amplitudeBankFeature μ x e p₀ s) := by
  apply (PiLp.continuousLinearEquiv 2 ℝ (fun _ : BankCoordinate n μ => ℝ)).symm.continuous.comp
  apply continuous_pi
  intro j
  have hS : Continuous (fun u : Vector (n+1) => bankComponentScale μ x j.1 u) := by
    unfold bankComponentScale overlap
    fun_prop
  exact (continuous_const.mul hS).mul
    ((SphericalAging.FiniteModel.tensorMonomial_contDiff j.2).continuous.comp e.toContinuousLinearMap.adjoint.continuous)

theorem amplitudeBankLinear_continuous (μ : FiniteMixture) (β : ℝ) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ) :
    Continuous (amplitudeBankLinear μ β x e p₀ s) :=
  ((innerSL ℝ).continuous.comp (amplitudeBankFeature_continuous μ x e p₀ s)).const_smul β

/-- Exact action on every flattened Gaussian coordinate, including degree zero. -/
theorem amplitudeBankLinear_apply (μ : FiniteMixture) (β : ℝ) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (s : Fin 2 → ℝ)
    (u : Vector (n+1)) (w : EuclideanBank n μ) :
    amplitudeBankLinear μ β x e p₀ s u w=β*amplitudeField μ x e p₀ s (unpackBankCLM n μ w) u := by
  simp only [amplitudeBankLinear,smul_apply,smul_eq_mul,innerSL_apply_apply,PiLp.inner_apply,
    RCLike.inner_apply,conj_trivial,amplitudeBankFeature,
    amplitudeField,bankComponent_eq_scaled,SphericalAging.FiniteModel.tensorLinear]
  congr 1
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I _
  change w ⟨i,I⟩*(bankAmplitude p₀ s i*bankComponentScale μ x i u*
      SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint u) I)=
    bankAmplitude p₀ s i*(bankComponentScale μ x i u*
      (SphericalAging.FiniteModel.tensorMonomial (e.toContinuousLinearMap.adjoint u) I*w ⟨i,I⟩))
  ring

/-- The generic selected-coordinate Gaussian parameter is exactly the
literal physical rescaling of the original independent tensor bank. -/
theorem unpackBank_parameterOperator (μ : FiniteMixture) (p₀ : Degree μ.maxDegree)
    (k : Fin 2) (τ : ℝ) (w : EuclideanBank n μ) :
    unpackBankCLM n μ (parameterOperator (amplitudeBankLabel μ p₀ k) (1+τ) w)=
      amplitudeDisorder p₀ (amplitudeAt k τ) (unpackBankCLM n μ w) := by
  funext i I
  change (parameterOperator (amplitudeBankLabel μ p₀ k) (1+τ) w) ⟨i,I⟩=
    bankAmplitude p₀ (amplitudeAt k τ) i*w ⟨i,I⟩
  simp only [parameterOperator,add_apply,smul_apply,coordinateMask,WithLp.ofLp_add,WithLp.ofLp_smul,Pi.add_apply,Pi.smul_apply,
    diagonal_apply,bankAmplitude_at,smul_eq_mul,amplitudeBankLabel]
  by_cases hi : i.1=p₀ ∧ i.2.val=k.val+1 <;> simp [hi]

/-- The exponent under the generic Gaussian parameter operator is exactly
the physical source exponent at the perturbed amplitude. -/
theorem amplitudeBankLinear_parameter (μ : FiniteMixture) (β : ℝ) (x : Vector (n+1))
    (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree) (k : Fin 2)
    (τ : ℝ) (u : Vector (n+1)) (w : EuclideanBank n μ) :
    amplitudeBankLinear μ β x e p₀ (fun _ => 1) u
      (parameterOperator (amplitudeBankLabel μ p₀ k) (1+τ) w)=
        β*amplitudeField μ x e p₀ (amplitudeAt k τ) (unpackBankCLM n μ w) u := by
  rw [amplitudeBankLinear_apply,unpackBank_parameterOperator,
    ← amplitudeField_eq_rescaled_disorder]

/-- A true finite operator bound on the actual physical sphere is available
for every bank feature, before every Gaussian realization. -/
theorem exists_amplitudeBankLinear_sphere_bound (μ : FiniteMixture) (β : ℝ)
    (x : Vector (n+1)) (e : Vector n →ₗᵢ[ℝ] Vector (n+1)) (p₀ : Degree μ.maxDegree)
    (s : Fin 2 → ℝ) : ∃ K : ℝ, 0≤K ∧ ∀ u : Vector (n+1),‖u‖^2=(n+1:ℝ) →
      ‖amplitudeBankLinear μ β x e p₀ s u‖≤K := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:Vector (n+1)) (Real.sqrt (n+1:ℝ))).exists_bound_of_continuousOn
    (amplitudeBankLinear_continuous μ β x e p₀ s).continuousOn
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro u hu
  apply (hC u ?_).trans (le_max_left _ _)
  simp only [mem_closedBall,dist_zero_right]
  rw [← hu,Real.sqrt_sq (norm_nonneg u)]

end
end SlowEquilibration.SphericalPlateauAmplitudeModel
