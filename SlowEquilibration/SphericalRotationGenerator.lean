module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalEnergy
public import Mathlib.Analysis.Calculus.ContDiff.Comp

@[expose] public section

namespace SlowEquilibration.SphericalForm

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Set
open SphericalModel
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped BigOperators InnerProductSpace Topology

/-- The literal infinitesimal rotation in the `(i,j)` coordinate plane. -/
def coordinateRotation {N : ℕ} (i j : Fin N) : Operator N :=
  InnerProductSpace.rankOne ℝ (basisVector i) (basisVector j) -
    InnerProductSpace.rankOne ℝ (basisVector j) (basisVector i)

theorem coordinateRotation_skew {N : ℕ} (i j : Fin N) :
    star (coordinateRotation i j) = -coordinateRotation i j := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  simp only [coordinateRotation, map_sub, InnerProductSpace.adjoint_rankOne]
  module

theorem lieDerivative_coordinateRotation {N : ℕ} (f : Vector N → ℝ)
    (x : Vector N) (i j : Fin N) :
    lieDerivative (coordinateRotation i j) f x =
      x j * gradient f x i - x i * gradient f x j := by
  unfold lieDerivative coordinateRotation
  simp only [sub_apply, InnerProductSpace.rankOne_apply, map_sub, map_smul,
    ← inner_gradient_left, basisVector, EuclideanSpace.inner_single_left,
    EuclideanSpace.inner_single_right, conj_trivial, one_mul, smul_eq_mul]

/-- The coordinate rotation fields recover the actual tangential metric. -/
theorem rotation_contraction {N : ℕ} (x u v : Vector N) :
    (∑ i : Fin N, ∑ j : Fin N,
      (x j * u i - x i * u j) * (x j * v i - x i * v j)) =
    2 * (inner ℝ x x * inner ℝ u v - inner ℝ x u * inner ℝ x v) := by
  have hrow (i : Fin N) :
      (∑ j : Fin N, (x j * u i - x i * u j) * (x j * v i - x i * v j)) =
      u i * v i * inner ℝ x x - u i * x i * inner ℝ x v -
        x i * v i * inner ℝ x u + x i * x i * inner ℝ u v := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [hrow]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have hi (a b : Vector N) : (∑ i : Fin N, a i * b i) = inner ℝ a b := by
    simp [PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  simp_rw [hi]
  have hux : inner ℝ u x = inner ℝ x u := real_inner_comm _ _
  rw [hux]
  ring

/-- Exact recovery of the spherical gradient pairing from rotation
fields on the manuscript sphere of squared radius `N`. -/
theorem surfaceGradient_rotation_pairing {N : ℕ} (hN : N ≠ 0)
    (f g : Vector N → ℝ) (x : Vector N) (hx : OnSphere x) :
    inner ℝ (surfaceGradient f x) (surfaceGradient g x) =
      (1 / (2 * (N : ℝ))) * ∑ i : Fin N, ∑ j : Fin N,
        lieDerivative (coordinateRotation i j) f x *
          lieDerivative (coordinateRotation i j) g x := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp_rw [lieDerivative_coordinateRotation]
  rw [rotation_contraction]
  unfold surfaceGradient
  rw [tangentProjection_apply, tangentProjection_apply]
  rw [projection_self_adjoint, projection_idempotent hN x _ hx]
  simp only [projection, inner_sub_right, real_inner_smul_right]
  rw [show inner ℝ x x = (N : ℝ) from hx]
  rw [real_inner_comm (gradient f x) x]
  field_simp

/-- Rotation derivatives of a C² function are C¹. -/
theorem lieDerivative_contDiff_one {N : ℕ} (A : Operator N)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (lieDerivative A f) := by
  have hh := hf.contDiff_fderiv_apply (m := 1) (by norm_num)
  exact hh.comp (contDiff_id.prodMk A.contDiff)

/-- The actual spherical Laplacian expressed as a sum of squares of
infinitesimal coordinate rotations, with radius squared `N`. -/
def rotationLaplacian (N : ℕ) (f : Vector N → ℝ) (x : Vector N) : ℝ :=
  (1 / (2 * (N : ℝ))) * ∑ i : Fin N, ∑ j : Fin N,
    lieDerivative (coordinateRotation i j)
      (lieDerivative (coordinateRotation i j) f) x

/-- The actual Langevin generator in the rotation frame. -/
def rotationGenerator (N : ℕ) (β : ℝ) (H f : Vector N → ℝ) (x : Vector N) : ℝ :=
  rotationLaplacian N f x +
    β * inner ℝ (surfaceGradient H x) (surfaceGradient f x)

/-- The actual generator is the Gibbs-weighted sum of the actual rotation
second derivatives, pointwise on the sphere. -/
theorem rotationGenerator_sum_onSphere {N : ℕ} (hN : N ≠ 0) (β : ℝ)
    (H f : Vector N → ℝ) (x : Vector N) (hx : OnSphere x) :
    rotationGenerator N β H f x =
      (1 / (2 * (N : ℝ))) * ∑ i : Fin N, ∑ j : Fin N,
        (lieDerivative (coordinateRotation i j)
          (lieDerivative (coordinateRotation i j) f) x +
        β * lieDerivative (coordinateRotation i j) H x *
          lieDerivative (coordinateRotation i j) f x) := by
  unfold rotationGenerator rotationLaplacian
  rw [surfaceGradient_rotation_pairing hN H f x hx]
  simp only [Finset.sum_add_distrib, mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem rotationLaplacian_continuous {N : ℕ} {f : Vector N → ℝ}
    (hf : ContDiff ℝ 2 f) : Continuous (rotationLaplacian N f) := by
  unfold rotationLaplacian
  apply continuous_const.mul
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  exact lieDerivative_continuous _ (lieDerivative_contDiff_one _ hf)

theorem rotationGenerator_continuous {N : ℕ} (β : ℝ)
    {H f : Vector N → ℝ} (hH : ContDiff ℝ 1 H) (hf : ContDiff ℝ 2 f) :
    Continuous (rotationGenerator N β H f) :=
  (rotationLaplacian_continuous hf).add (continuous_const.mul
    ((surfaceGradient_continuous hH).inner
      (surfaceGradient_continuous (hf.of_le (by norm_num)))))

/-- Integration by parts for an actual weighted rotation square. -/
theorem gibbs_rotation_square_integration_by_parts {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H f g : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g)
    (A : Operator N) (hA : star A = -A) :
    (∫ x, f x * (lieDerivative A (lieDerivative A g) x +
        β * lieDerivative A H x * lieDerivative A g x) ∂gibbsLaw N β H) =
      -(∫ x, lieDerivative A f x * lieDerivative A g x ∂gibbsLaw N β H) := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hDg := lieDerivative_contDiff_one A hg
  have hfD : Integrable (fun x => f x * lieDerivative A (lieDerivative A g) x)
      (gibbsLaw N β H) := integrable_gibbs_of_continuous hN β hH.continuous
    (hf.continuous.mul (lieDerivative_continuous A hDg))
  have hcorr : Integrable (fun x => f x *
      (β * lieDerivative A H x * lieDerivative A g x)) (gibbsLaw N β H) :=
    integrable_gibbs_of_continuous hN β hH.continuous
    (hf.continuous.mul ((continuous_const.mul (lieDerivative_continuous A hH)).mul
      (lieDerivative_continuous A hg1)))
  have hpair : Integrable (fun x => lieDerivative A g x * lieDerivative A f x)
      (gibbsLaw N β H) := integrable_gibbs_of_continuous hN β hH.continuous
    ((lieDerivative_continuous A hg1).mul (lieDerivative_continuous A hf))
  have hcorr' : Integrable (fun x => lieDerivative A g x *
      (β * f x * lieDerivative A H x)) (gibbsLaw N β H) :=
    integrable_gibbs_of_continuous hN β hH.continuous
    ((lieDerivative_continuous A hg1).mul
      ((continuous_const.mul hf.continuous).mul (lieDerivative_continuous A hH)))
  have hbp := gibbs_lie_integration_by_parts hN β hH hf hDg A hA
  have hbp' : (∫ x, f x * lieDerivative A (lieDerivative A g) x ∂gibbsLaw N β H) =
      -(∫ x, lieDerivative A g x * lieDerivative A f x ∂gibbsLaw N β H) -
        (∫ x, lieDerivative A g x * (β * f x * lieDerivative A H x)
          ∂gibbsLaw N β H) := by
    simp_rw [mul_add] at hbp
    rw [integral_add hpair hcorr'] at hbp
    linarith only [hbp]
  simp_rw [mul_add]
  rw [integral_add hfD hcorr, hbp']
  have hc : (∫ x, lieDerivative A g x * (β * f x * lieDerivative A H x)
      ∂gibbsLaw N β H) =
      ∫ x, f x * (β * lieDerivative A H x * lieDerivative A g x) ∂gibbsLaw N β H := by
    congr 1
    funext x
    ring
  rw [hc]
  have hp : (∫ x, lieDerivative A g x * lieDerivative A f x ∂gibbsLaw N β H) =
      ∫ x, lieDerivative A f x * lieDerivative A g x ∂gibbsLaw N β H := by
    congr 1
    funext x
    exact mul_comm _ _
  rw [hp]
  ring

/-- Finite rotation sums may be integrated term by term against the actual
Gibbs measure; all integrability is proved from compact spherical support. -/
theorem integral_rotation_sum {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H)
    (q : Fin N → Fin N → Vector N → ℝ) (hq : ∀ i j, Continuous (q i j)) :
    (∫ x, ∑ i : Fin N, ∑ j : Fin N, q i j x ∂gibbsLaw N β H) =
      ∑ i : Fin N, ∑ j : Fin N, ∫ x, q i j x ∂gibbsLaw N β H := by
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_gibbs_of_continuous hN β hH
      (continuous_finsetSum Finset.univ (fun j _ => hq i j)))]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_finsetSum Finset.univ
    (fun j _ => integrable_gibbs_of_continuous hN β hH (hq i j))

/-- The actual gradient Dirichlet form equals the rotation-frame pairing,
with the coefficient dictated by the manuscript's radius. -/
theorem dirichletForm_eq_rotation_integrals {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H f g : Vector N → ℝ} (hH : Continuous H)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    dirichletForm N β H f g =
      (1 / (2 * (N : ℝ))) * ∑ i : Fin N, ∑ j : Fin N,
        ∫ x, lieDerivative (coordinateRotation i j) f x *
          lieDerivative (coordinateRotation i j) g x ∂gibbsLaw N β H := by
  unfold dirichletForm
  calc
    _ = (1 / (2 * (N : ℝ))) *
        ∫ x, ∑ i : Fin N, ∑ j : Fin N,
          lieDerivative (coordinateRotation i j) f x *
            lieDerivative (coordinateRotation i j) g x ∂gibbsLaw N β H := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [gibbsLaw_support hN β H] with x hx
      exact surfaceGradient_rotation_pairing (by omega) f g x
        ((onSphere_iff_norm_sq x).mpr hx)
    _ = _ := by
      rw [integral_rotation_sum hN β hH
        (fun i j x => lieDerivative (coordinateRotation i j) f x *
          lieDerivative (coordinateRotation i j) g x) (fun i j =>
        (lieDerivative_continuous _ hf).mul (lieDerivative_continuous _ hg))]

/-- The full manuscript integration-by-parts identity for the actual
spherical Gibbs generator and actual gradient Dirichlet form. -/
theorem rotationGenerator_integration_by_parts {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H f g : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 2 g) :
    (∫ x, f x * rotationGenerator N β H g x ∂gibbsLaw N β H) =
      -dirichletForm N β H f g := by
  let q : Fin N → Fin N → Vector N → ℝ := fun i j x =>
    f x * (lieDerivative (coordinateRotation i j)
      (lieDerivative (coordinateRotation i j) g) x +
      β * lieDerivative (coordinateRotation i j) H x *
        lieDerivative (coordinateRotation i j) g x)
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by norm_num)
  have hq (i j : Fin N) : Continuous (q i j) := by
    exact hf.continuous.mul
      ((lieDerivative_continuous _ (lieDerivative_contDiff_one _ hg)).add
        ((continuous_const.mul (lieDerivative_continuous _ hH)).mul
          (lieDerivative_continuous _ hg1)))
  calc
    _ = (1 / (2 * (N : ℝ))) *
        ∫ x, ∑ i : Fin N, ∑ j : Fin N, q i j x ∂gibbsLaw N β H := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [gibbsLaw_support hN β H] with x hx
      rw [rotationGenerator_sum_onSphere (by omega) β H g x
        ((onSphere_iff_norm_sq x).mpr hx)]
      dsimp [q]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (1 / (2 * (N : ℝ))) *
        ∑ i : Fin N, ∑ j : Fin N, ∫ x, q i j x ∂gibbsLaw N β H := by
      rw [integral_rotation_sum hN β hH.continuous q hq]
    _ = _ := by
      dsimp [q]
      simp_rw [gibbs_rotation_square_integration_by_parts hN β hH hf hg
        _ (coordinateRotation_skew _ _)]
      rw [dirichletForm_eq_rotation_integrals hN β hH.continuous hf hg1]
      simp only [Finset.sum_neg_distrib]
      ring

/-- Symmetry of the actual Gibbs generator on smooth spherical test
functions follows from its proved gradient Dirichlet identity. -/
theorem rotationGenerator_symmetric {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H f g : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    (∫ x, f x * rotationGenerator N β H g x ∂gibbsLaw N β H) =
      ∫ x, g x * rotationGenerator N β H f x ∂gibbsLaw N β H := by
  rw [rotationGenerator_integration_by_parts hN β hH (hf.of_le (by norm_num)) hg,
    rotationGenerator_integration_by_parts hN β hH (hg.of_le (by norm_num)) hf,
    dirichletForm_symmetric]

end
end SlowEquilibration.SphericalForm
