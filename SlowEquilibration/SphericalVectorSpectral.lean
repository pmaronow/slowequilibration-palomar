-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPhysicalSpectral

@[expose] public section

/-! The genuine finite-dimensional vector extensions of the physical
spherical spectral identities are obtained by summing actual components. -/

noncomputable section
namespace SlowEquilibration.SphericalPhysicalSpectral

open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalForm SphericalDynamics SphericalReversibility
open SphericalLaplaceIdentification
open scoped Topology InnerProductSpace NNReal ENNReal BigOperators

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ} {hN : 2 ≤ N} {μ : FiniteMixture} {J : Disorder N μ.maxDegree} {β : ℝ}
variable {ι : Type*} [Fintype ι]

/-- The true finite-vector Gibbs Hilbert space. -/
abbrev VectorSpace (ι : Type*) [Fintype ι] (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) :=
  PiLp 2 (fun _ : ι => SphericalL2Semigroup.Space μ J β)

/-- The actual physical transition acts componentwise as a genuine
continuous linear map on the finite-vector Gibbs Hilbert space. -/
def vectorP (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (t : ℝ≥0) : VectorSpace ι μ J β →L[ℝ] VectorSpace ι μ J β :=
  ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι => SphericalL2Semigroup.Space μ J β)).symm.toContinuousLinearMap).comp
    (ContinuousLinearMap.pi (fun a => (SphericalL2Semigroup.P hN μ J β t).comp
      (PiLp.proj 2 (fun _ : ι => SphericalL2Semigroup.Space μ J β) a)))

@[simp] theorem vectorP_apply (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0)
    (f : VectorSpace ι μ J β) (a : ι) :
    (vectorP hN μ J β t f) a = SphericalL2Semigroup.P hN μ J β t (f a) := rfl

theorem vectorP_norm_le (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) (f : VectorSpace ι μ J β) :
    ‖vectorP hN μ J β t f‖ ≤ ‖f‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  exact Finset.sum_le_sum (fun a _ => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    (SphericalL2Semigroup.P_apply_norm_le hN μ J β t (f a)))

theorem vectorP_isSymmetric (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0) :
    (vectorP (ι := ι) hN μ J β t).toLinearMap.IsSymmetric := by
  intro f g
  rw [PiLp.inner_apply, PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun a _ =>
    (SphericalL2Semigroup.P_isSymmetric hN μ J β t).apply_clm (f a) (g a))

def vectorFormValue (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ)
    (u : ι → sphericalSobolevGraph hN β (potential μ J) (potential_continuous μ J)) :
    VectorSpace ι μ J β := WithLp.toLp 2 (fun a => formValue hN μ J β (u a))

/-- The actual finite-vector Hilbert displacement is bounded by the sum
of the genuine completed component energies. -/
theorem vector_semigroup_displacement_energy_le
    (D : SphericalSpectralData hN β (potential μ J) (potential_continuous μ J))
    (t : ℝ≥0)
    (u : ι → sphericalSobolevGraph (show 1 ≤ N by omega) β (potential μ J) (potential_continuous μ J)) :
    ‖vectorFormValue (show 1 ≤ N by omega) μ J β u -
      vectorP (show 1 ≤ N by omega) μ J β t (vectorFormValue (show 1 ≤ N by omega) μ J β u)‖ ^ 2 ≤
      (t : ℝ)*∑ a, sphericalCompletedDirichlet (show 1 ≤ N by omega) β (potential μ J)
        (potential_continuous μ J) (u a) (u a) := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  change ‖formValue (show 1 ≤ N by omega) μ J β (u a) -
    SphericalL2Semigroup.P (show 1 ≤ N by omega) μ J β t
      (formValue (show 1 ≤ N by omega) μ J β (u a))‖ ^ 2 ≤ _
  exact semigroup_displacement_energy_le D t (u a)

/-- The scalar spectral expansion sums to the actual vector correlation
series, with the squared Euclidean norm of each coefficient vector. -/
theorem vector_correlation_hasSum
    (D : SphericalSpectralData hN β (potential μ J) (potential_continuous μ J))
    (t : ℝ≥0) (f : ι → SphericalL2Semigroup.Space μ J β) :
    HasSum (fun j => Real.exp (-(t : ℝ)*D.eigenvalue j)*
      ∑ a, (D.toSemigroupData.coefficient (f a) j)^2)
      (∑ a, inner ℝ (f a) (SphericalL2Semigroup.P (show 1 ≤ N by omega) μ J β t (f a))) := by
  classical
  have h := hasSum_sum (s := Finset.univ) (fun a _ => correlation_hasSum D t (f a))
  simpa only [Finset.mul_sum] using h

/-- Actual finite-vector stationary two-time correlations. Each component
product is genuinely integrable under the same physical two-time law. -/
theorem vector_twoTime_correlation (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (t : ℝ≥0)
    (f g : ι → SphericalL2Semigroup.Space μ J β) :
    (∫ q, ∑ a, f a q.1*g a q.2 ∂twoTimeLaw μ J β t) =
      ∑ a, inner ℝ (f a) (SphericalL2Semigroup.P hN μ J β t (g a)) := by
  classical
  have := mixtureGibbsLaw_probability hN μ β J
  have hi (a : ι) : Integrable (fun q => f a q.1*g a q.2) (twoTimeLaw μ J β t) :=
    StationaryCoupling.correlation_integrable (mixtureGibbsLaw μ β J)
      (mixedTransitionKernel μ J β t) (mixedTransitionKernel_gibbs_invariant hN μ J β t) (f a) (g a)
  rw [integral_finsetSum Finset.univ (fun a _ => hi a)]
  simp only [twoTime_correlation hN]

/-- The actual vector-valued stationary displacement estimate with the
manuscript's factor 2 and sum of true completed component energies. -/
theorem vector_stationary_displacement_energy_le
    (D : SphericalSpectralData hN β (potential μ J) (potential_continuous μ J))
    (t : ℝ≥0)
    (u : ι → sphericalSobolevGraph (show 1 ≤ N by omega) β (potential μ J) (potential_continuous μ J)) :
    (∫ q, ∑ a, ((formValue (show 1 ≤ N by omega) μ J β (u a)) q.2-
      (formValue (show 1 ≤ N by omega) μ J β (u a)) q.1)^2 ∂twoTimeLaw μ J β t) ≤
      2*(t : ℝ)*∑ a, sphericalCompletedDirichlet (show 1 ≤ N by omega) β (potential μ J)
        (potential_continuous μ J) (u a) (u a) := by
  classical
  have := mixtureGibbsLaw_probability (show 1 ≤ N by omega) μ β J
  rw [integral_finsetSum Finset.univ (fun a _ =>
    StationaryCoupling.difference_square_integrable (mixtureGibbsLaw μ β J)
      (mixedTransitionKernel μ J β t)
      (mixedTransitionKernel_gibbs_invariant (show 1 ≤ N by omega) μ J β t)
      (formValue (show 1 ≤ N by omega) μ J β (u a))), Finset.mul_sum]
  exact Finset.sum_le_sum (fun a _ => stationary_displacement_energy_le D t (u a))

end SlowEquilibration.SphericalPhysicalSpectral
