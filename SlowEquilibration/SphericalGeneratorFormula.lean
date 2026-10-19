module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalRotationGenerator
public import SphericalAging.SphereCanonicalGenerator

@[expose] public section

namespace SlowEquilibration.SphericalForm

noncomputable section
set_option backward.isDefEq.respectTransparency false

open SphericalModel
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped BigOperators InnerProductSpace

/-- The actual Itô coefficient generator for the manuscript's projected
noise and the gradient-ascent Gibbs drift, for any smooth realized field. -/
def sphericalCoefficientGenerator (N : ℕ) (β : ℝ) (H f : Vector N → ℝ)
    (x : Vector N) : ℝ :=
  fderiv ℝ f x (drift β (gradient H) x) +
    (1 / 2 : ℝ) * ∑ j : Fin N,
      fderiv ℝ (fderiv ℝ f) x (noiseColumn x j) (noiseColumn x j)

@[simp] theorem coordinateRotation_eq {N : ℕ} (i j : Fin N) :
    coordinateRotation i j = SphericalAging.SphereRotationGeometry.coordinateRotation i j := rfl

/-- The actual rotation-frame Laplacian is the extrinsic spherical
Laplacian in the manuscript's projected-noise normalization. -/
theorem rotationLaplacian_eq_projected_hessian {N : ℕ} (hN : N ≠ 0)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) (x : Vector N) (hx : OnSphere x) :
    rotationLaplacian N f x =
      (1 / 2 : ℝ) * (∑ j : Fin N,
        fderiv ℝ (fderiv ℝ f) x (noiseColumn x j) (noiseColumn x j)) -
      kappa N * inner ℝ x (gradient f x) := by
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hsum : (∑ i : Fin N, ∑ j : Fin N,
      fderiv ℝ f x (SphericalAging.SphereRotationGeometry.coordinateRotation i j
        (SphericalAging.SphereRotationGeometry.coordinateRotation i j x))) =
        fderiv ℝ f x (∑ i : Fin N, ∑ j : Fin N,
          SphericalAging.SphereRotationGeometry.coordinateRotation i j
            (SphericalAging.SphereRotationGeometry.coordinateRotation i j x)) := by
    rw [map_sum]
    simp_rw [map_sum]
  have hfirst : (1 / (2 * (N : ℝ))) * (∑ i : Fin N, ∑ j : Fin N,
      fderiv ℝ f x (SphericalAging.SphereRotationGeometry.coordinateRotation i j
        (SphericalAging.SphereRotationGeometry.coordinateRotation i j x))) =
      -kappa N * inner ℝ x (gradient f x) := by
    rw [hsum, SphericalAging.SphereCanonicalGenerator.coordinate_rotation_square_vector_sum,
      map_smul, smul_eq_mul, ← inner_gradient_left, real_inner_comm (gradient f x) x]
    unfold kappa
    field_simp
  unfold rotationLaplacian
  simp_rw [coordinateRotation_eq, SphericalAging.SphereGamma2Algebra.lieDerivative_twice_fderiv
    _ _ hf, Finset.sum_add_distrib]
  rw [mul_add,
    SphericalAging.SphereCanonicalGenerator.coordinate_rotation_hessian_contraction
      (by omega) x hx, hfirst]
  ring

/-- Exact identification of the actual rotation generator and the Itô
coefficient generator of the spherical Langevin SDE. -/
theorem rotationGenerator_eq_coefficientGenerator {N : ℕ} (hN : N ≠ 0) (β : ℝ)
    (H : Vector N → ℝ) {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f)
    (x : Vector N) (hx : OnSphere x) :
    rotationGenerator N β H f x = sphericalCoefficientGenerator N β H f x := by
  rw [rotationGenerator, rotationLaplacian_eq_projected_hessian hN hf x hx,
    sphericalCoefficientGenerator, SphericalAging.SphereGenerator.gradient_drift_pairing hN x hx]
  simp only [surfaceGradient, tangentProjection_apply]
  ring

end
end SlowEquilibration.SphericalForm
