module

public import SphericalAging.SphereGamma2Algebra
public import SphericalAging.SphereGenerator

public section

/-! The actual complete coordinate-rotation generator equals the generator of
the constructed Hamiltonian SDE coefficients on the physical sphere. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.SphereCanonicalGenerator

open FiniteModel HardSphereDynamics LocalSDE SphereGenerator SphereRotationGeometry
open SphericalIntegrationByParts SphereGeneratorIntegrationByParts SphereGamma2Algebra
open scoped BigOperators InnerProductSpace

theorem coordinate_rotation_bilinear_sum {N : ℕ} (x z w : Vector N) :
    (∑ i : Fin N, ∑ j : Fin N, (x j*z i-x i*z j)*(x j*w i-x i*w j)) =
      2*(⟪x,x⟫_ℝ*⟪z,w⟫_ℝ-⟪x,z⟫_ℝ*⟪x,w⟫_ℝ) := by
  have he : (∑ i : Fin N, ∑ j : Fin N, (x j*z i-x i*z j)*(x j*w i-x i*w j)) =
      (∑ i : Fin N, ∑ j : Fin N, ((z i*w i)*(x j)^2 -
        (x i*w i)*(x j*z j) - (x i*z i)*(x j*w j) + (x i)^2*(z j*w j))) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [coordinate_square_sum]
  simp_rw [← Finset.sum_mul]
  rw [coordinate_square_sum, real_inner_coordinates z w, real_inner_coordinates x z,
    real_inner_coordinates x w]
  ring

theorem coordinate_rotation_bilinear_metric {N : ℕ} (hN : 0<N)
    (x z w : Vector N) (hx : OnSphere x) :
    (1/(2*(N : ℝ)))*(∑ i : Fin N, ∑ j : Fin N,
      (x j*z i-x i*z j)*(x j*w i-x i*w j)) =
        ⟪projection x z, projection x w⟫_ℝ := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [coordinate_rotation_bilinear_sum, hx]
  unfold projection
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_comm z x, hx]
  field_simp
  ring

theorem coordinateRotation_apply_coordinate {N : ℕ} (i j a : Fin N) (x : Vector N) :
    coordinateRotation i j x a = x j*(basisVector a) i-x i*(basisVector a) j := by
  rw [coordinateRotation_apply]
  simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, basisVector, PiLp.single_apply]
  have hδ (u v : Fin N) : (if u=v then (1 : ℝ) else 0) =
      (if v=u then (1 : ℝ) else 0) := by
    by_cases h : u=v
    · simp [h]
    · simp [h, Ne.symm h]
  rw [hδ a i, hδ a j]

theorem coordinate_rotation_covariance {N : ℕ} (x : Vector N) (hx : OnSphere x)
    (a b : Fin N) :
    (∑ i : Fin N, ∑ j : Fin N, coordinateRotation i j x a*coordinateRotation i j x b) =
      2*((N : ℝ)*(if a=b then (1 : ℝ) else 0)-x a*x b) := by
  simp_rw [coordinateRotation_apply_coordinate]
  rw [coordinate_rotation_bilinear_sum, hx, basis_inner, basis_inner]
  by_cases hab : a=b
  · simp [basisVector, EuclideanSpace.inner_single_right, hab]
  · simp [basisVector, EuclideanSpace.inner_single_right, hab, Ne.symm hab]

theorem coordinate_rotation_hessian_contraction {N : ℕ} (hN : 0<N)
    (x : Vector N) (hx : OnSphere x) (H : Vector N →L[ℝ] Vector N →L[ℝ] ℝ) :
    (1/(2*(N : ℝ)))*(∑ i : Fin N, ∑ j : Fin N,
      H (coordinateRotation i j x) (coordinateRotation i j x)) =
      (1/2 : ℝ)*(∑ j : Fin N, H (noiseColumn x j) (noiseColumn x j)) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  rw [hessian_noise_contraction (Nat.ne_of_gt hN) x hx]
  rw [show (∑ i : Fin N, ∑ j : Fin N, H (coordinateRotation i j x) (coordinateRotation i j x)) =
    (∑ i : Fin N, ∑ j : Fin N, ∑ a : Fin N, ∑ b : Fin N,
      coordinateRotation i j x a*coordinateRotation i j x b*H (basisVector a) (basisVector b)) from
      Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => bilinear_coordinates H _ _))]
  have he : (∑ i : Fin N, ∑ j : Fin N, ∑ a : Fin N, ∑ b : Fin N,
      coordinateRotation i j x a*coordinateRotation i j x b*H (basisVector a) (basisVector b)) =
      (∑ a : Fin N, ∑ b : Fin N, (∑ i : Fin N, ∑ j : Fin N,
        coordinateRotation i j x a*coordinateRotation i j x b)*H (basisVector a) (basisVector b)) := by
    calc
      _ = ∑ i : Fin N, ∑ a : Fin N, ∑ b : Fin N, ∑ j : Fin N,
          coordinateRotation i j x a*coordinateRotation i j x b*H (basisVector a) (basisVector b) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_comm]
        simp_rw [← Finset.sum_mul]
  rw [he]
  simp_rw [coordinate_rotation_covariance x hx, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  field_simp

theorem coordinate_rotation_square_vector_sum {N : ℕ} (x : Vector N) :
    (∑ i : Fin N, ∑ j : Fin N, coordinateRotation i j (coordinateRotation i j x)) =
      (-2*((N : ℝ)-1)) • x := by
  classical
  have ht (i j : Fin N) : coordinateRotation i j (coordinateRotation i j x) =
      -(x i • basisVector i) - x j • basisVector j +
        (if i=j then (2 : ℝ) • (x i • basisVector i) else 0) := by
    rw [coordinateRotation_apply, coordinateRotation_apply]
    simp only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul, basisVector, PiLp.single_apply]
    by_cases hij : i=j
    · simp [hij]
      module
    · simp only [hij, Ne.symm hij, ite_false, ite_true, mul_zero, mul_one, zero_sub, sub_zero]
      module
  simp_rw [ht, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, ← Finset.smul_sum, Finset.sum_neg_distrib]
  rw [state_sum_basis x]
  module

theorem canonical_rotationGamma_eq_tangent_inner {N : ℕ} (hN : 0<N)
    (f g : Vector N → ℝ) (x : Vector N) (hx : OnSphere x) :
    rotationGamma (1/(2*(N : ℝ)))
      (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2) f g x =
      ⟪projection x (gradient f x), projection x (gradient g x)⟫_ℝ := by
  unfold rotationGamma
  simp only [Fintype.sum_prod_type]
  simp_rw [lieDerivative_coordinate]
  exact coordinate_rotation_bilinear_metric hN x _ _ hx

/-- Exact identification with the coefficient generator of the true projected
noise and Hamiltonian drift, on the actual radius-√N sphere. -/
theorem canonical_rotationGenerator_eq_coefficientGenerator {N p : ℕ} (hN : 0<N)
    (β : ℝ) (J : Disorder N p) {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f)
    (x : Vector N) (hx : OnSphere x) :
    rotationGenerator (1/(2*(N : ℝ))) β J
      (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2) f x =
      coefficientGenerator β J f x := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hsum : (∑ i : Fin N, ∑ j : Fin N,
      fderiv ℝ f x (coordinateRotation i j (coordinateRotation i j x))) =
        fderiv ℝ f x (∑ i : Fin N, ∑ j : Fin N,
          coordinateRotation i j (coordinateRotation i j x)) := by
    rw [map_sum]
    simp_rw [map_sum]
  have hfirst : (1/(2*(N : ℝ)))*(∑ i : Fin N, ∑ j : Fin N,
      fderiv ℝ f x (coordinateRotation i j (coordinateRotation i j x))) =
        -kappa N*⟪x, gradient f x⟫_ℝ := by
    rw [hsum, coordinate_rotation_square_vector_sum, map_smul, smul_eq_mul,
      ← inner_gradient_left, real_inner_comm (gradient f x) x]
    unfold kappa
    field_simp
  have hzero : rotationGenerator (1/(2*(N : ℝ))) 0 J
      (fun ij : Fin N × Fin N => coordinateRotation ij.1 ij.2) f x =
        (1/2 : ℝ)*(∑ j : Fin N, fderiv ℝ (fderiv ℝ f) x (noiseColumn x j) (noiseColumn x j)) -
          kappa N*⟪x, gradient f x⟫_ℝ := by
    unfold rotationGenerator
    simp only [zero_mul, add_zero, Fintype.sum_prod_type]
    simp_rw [lieDerivative_twice_fderiv _ _ hf, Finset.sum_add_distrib]
    rw [mul_add, coordinate_rotation_hessian_contraction hN x hx, hfirst]
    ring
  rw [rotationGenerator_drift_split, hzero,
    canonical_rotationGamma_eq_tangent_inner hN _ _ x hx]
  rw [coefficientGenerator, hamiltonianDrift,
    gradient_drift_pairing (Nat.ne_of_gt hN) x hx β (hamiltonianGradient J) f]
  unfold hamiltonianGradient
  ring

end SphericalAging.SphereCanonicalGenerator
