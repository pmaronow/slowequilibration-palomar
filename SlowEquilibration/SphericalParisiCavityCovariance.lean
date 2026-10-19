-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGaussianJet
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-! Actual spherical cavity fields for Chen's ASS decomposition (2.5–2.6).
Both fields are restrictions or directional derivatives of the original
ordered Gaussian tensor Hamiltonian, with the original product disorder law.
No independent surrogate process or thermodynamic conclusion is assumed. -/

namespace SlowEquilibration.SphericalParisiCavityCovariance

noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalGaussianJet
open SphericalAging.HamiltonianDerivativeCovariance
open scoped InnerProductSpace BigOperators ProbabilityTheory

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal concatenation of bulk and cavity coordinates. -/
def append {N M : ℕ} (x : Vector N) (ε : Vector M) : Vector (N+M) :=
  WithLp.toLp 2 (Fin.addCases x ε)

@[simp] theorem append_left {N M : ℕ} (x : Vector N) (ε : Vector M) (i : Fin N) :
    append x ε (Fin.castAdd M i) = x i := by simp [append]

@[simp] theorem append_right {N M : ℕ} (x : Vector N) (ε : Vector M) (i : Fin M) :
    append x ε (Fin.natAdd N i) = ε i := by simp [append]

/-- Exact Euclidean orthogonal decomposition into physical coordinate blocks. -/
theorem append_inner {N M : ℕ} (x y : Vector N) (ε η : Vector M) :
    inner ℝ (append x ε) (append y η) = inner ℝ x y+inner ℝ ε η := by
  rw [PiLp.inner_apply, Fin.sum_univ_add]
  simp only [append_left, append_right, PiLp.inner_apply]

theorem append_norm_sq {N M : ℕ} (x : Vector N) (ε : Vector M) :
    ‖append x ε‖^2 = ‖x‖^2+‖ε‖^2 := by
  rw [← real_inner_self_eq_norm_sq, append_inner,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- The actual no-cavity part H_(M,N), on the original disorder. -/
def bulkField {N M P : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (J : Disorder (N+M) P) : ℝ := field c J (append x (0 : Vector M))

/-- The actual terms with one cavity coordinate, as the true directional
derivative at zero cavity. Ordered tensor symmetry is not assumed. -/
def linearCavity {N M P : ℕ} (c : Degree P → ℝ) (x : Vector N) (ε : Vector M)
    (J : Disorder (N+M) P) : ℝ :=
  jet c 1 (append x (0 : Vector M)) (fun _ => append (0 : Vector N) ε) J

private theorem pure_derivative_value_covariance {D p : ℕ} (hD : 0 < D)
    (x y u : Vector D) :
    cov[fun J : PureDisorder D p => iteratedFDeriv ℝ 1
        (SphericalAging.FiniteModel.Hamiltonian D p J) x (fun _ => u),
      fun J => SphericalAging.FiniteModel.Hamiltonian D p J y; PureLaw D p] =
      (p : ℝ)*(inner ℝ x y/D)^(p-1)*inner ℝ u y := by
  rw [covariance_eq_sub (Hamiltonian_derivative_memLp 1 x (fun _ => u))
    (SphericalAging.FiniteModel.Hamiltonian_memLp y)]
  simp only [Hamiltonian_derivative_mean, SphericalAging.FiniteModel.Hamiltonian_mean,
    zero_mul, sub_zero, Pi.mul_apply]
  have hh := Hamiltonian_derivative_covariance_gram (p := p) 1 0 x y
    (fun _ => u) (Fin.elim0)
  simp only [coefficientDerivative, iteratedFDeriv_one_apply, iteratedFDeriv_zero_apply] at hh
  simp only [iteratedFDeriv_one_apply]
  rw [hh, coefficient_gradient_gram_left]
  calc
    _ = (p : ℝ)*(SphericalAging.FiniteModel.normalization D p^2*
        (inner ℝ x y)^(p-1))*inner ℝ u y := by ring
    _ = _ := by rw [normalization_first_power hD]

/-- Genuine directional-field covariance under the original mixed tensor law. -/
theorem derivative_value_covariance {D P : ℕ} (hD : 0 < D)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x y u : Vector D) :
    cov[jet c 1 x (fun _ => u), fun J => field c J y; disorderLaw D P] =
      firstCovariance c (overlap x y)*inner ℝ u y := by
  have hv : (fun J : Disorder D P => field c J y) = jet c 0 y Fin.elim0 := by
    funext J
    simp only [jet, iteratedFDeriv_zero_apply]
  rw [hv, jet_covariance c hc]
  simp only [iteratedFDeriv_zero_apply]
  simp_rw [pure_derivative_value_covariance hD]
  unfold firstCovariance overlap
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- The actual derivative covariance on orthogonal cavity directions;
the bulk-point rank-one term vanishes by real coordinate orthogonality. -/
theorem orthogonal_derivative_covariance {D P : ℕ} (hD : 0 < D)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x y u v : Vector D)
    (hu : inner ℝ u y = 0) :
    cov[jet c 1 x (fun _ => u), jet c 1 y (fun _ => v); disorderLaw D P] =
      firstCovariance c (overlap x y)*inner ℝ u v := by
  rw [jet_covariance c hc]
  have hpure (p : Degree P) :
      cov[fun J : PureDisorder D p.val.val => iteratedFDeriv ℝ 1
          (SphericalAging.FiniteModel.Hamiltonian D p.val.val J) x (fun _ => u),
        fun J => iteratedFDeriv ℝ 1
          (SphericalAging.FiniteModel.Hamiltonian D p.val.val J) y (fun _ => v);
        PureLaw D p.val.val] =
        (p.val.val : ℝ)*(inner ℝ x y/D)^(p.val.val-1)*inner ℝ u v := by
    rw [covariance_eq_sub (Hamiltonian_derivative_memLp 1 x (fun _ => u))
      (Hamiltonian_derivative_memLp 1 y (fun _ => v))]
    simp only [Hamiltonian_derivative_mean, zero_mul, sub_zero, Pi.mul_apply]
    rw [Hamiltonian_derivative_covariance_gram]
    simp only [coefficientDerivative, iteratedFDeriv_one_apply]
    rw [coefficient_gradient_cross_gram_overlap hD p.property, hu]
    ring
  simp_rw [hpure]
  unfold firstCovariance overlap
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Chen (2.5), for the actual spherical bulk field and its original law. -/
theorem bulk_covariance {N M P : ℕ} (hD : 0 < N+M)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x y : Vector N) :
    cov[bulkField c x (M := M), bulkField c y (M := M); disorderLaw (N+M) P] =
      ((N+M : ℕ) : ℝ)*covariancePolynomial c (inner ℝ x y/(N+M : ℕ)) := by
  unfold bulkField
  rw [field_covariance hD c hc]
  simp only [overlap, append_inner, inner_zero_right, add_zero]

/-- Chen (2.6), including all cavity-coordinate cross-covariances. -/
theorem linear_cavity_covariance {N M P : ℕ} (hD : 0 < N+M)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x y : Vector N) (ε η : Vector M) :
    cov[linearCavity c x ε, linearCavity c y η; disorderLaw (N+M) P] =
      firstCovariance c (inner ℝ x y/(N+M : ℕ))*inner ℝ ε η := by
  unfold linearCavity
  rw [orthogonal_derivative_covariance hD c hc]
  · simp only [overlap, append_inner, inner_zero_right,
      add_zero, zero_add]
  · simp only [append_inner, inner_zero_left, inner_zero_right, add_zero]

/-- The actual bulk and first-order cavity blocks have zero covariance,
at arbitrary distinct bulk points. -/
theorem bulk_linear_covariance_zero {N M P : ℕ} (hD : 0 < N+M)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x y : Vector N) (ε : Vector M) :
    cov[bulkField c x (M := M), linearCavity c y ε; disorderLaw (N+M) P] = 0 := by
  rw [covariance_comm]
  unfold linearCavity bulkField
  rw [derivative_value_covariance hD c hc]
  simp only [append_inner, inner_zero_left, inner_zero_right, add_zero, mul_zero]

/-- The true bulk and one-cavity-coordinate fields are independent at
every pair of finite families of points, under the original disorder law. -/
theorem bulk_linear_independent {N M P : ℕ} (hD : 0 < N+M)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (x : ι → Vector N) (y : κ → Vector N) (ε : κ → Vector M) :
    IndepFun (fun J : Disorder (N+M) P => fun i => bulkField c (x i) J)
      (fun J => fun j => linearCavity c (y j) (ε j) J) (disorderLaw (N+M) P) := by
  have hraw := (disorder_hasGaussianLaw (N+M) P).map_fun
    ((ContinuousLinearMap.pi (fun i => fieldCLM c (append (x i) (0 : Vector M)))).prod
      (ContinuousLinearMap.pi (fun j => jetCLM c 1 (append (y j) (0 : Vector M))
        (fun _ => append (0 : Vector N) (ε j)))))
  have hjoint := hraw.congr (Y := fun J : Disorder (N+M) P =>
    ((fun i => bulkField c (x i) J), fun j => linearCavity c (y j) (ε j) J))
    (.of_forall (fun J => by simp [bulkField, linearCavity]))
  apply hjoint.indepFun_of_covariance_eval
  intro i j
  exact bulk_linear_covariance_zero hD c hc (x i) (y j) (ε j)

end
end SlowEquilibration.SphericalParisiCavityCovariance
