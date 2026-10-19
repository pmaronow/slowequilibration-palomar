-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalC2Operator
public import SphericalAging.SphereGeneratorAlgebra

/-! The genuine C² ground-state differential conjugation on the sphere. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalForm
open MeasureTheory Filter Set SphericalModel
open SphericalAging.HardSphereDynamics SphericalAging.SphericalIntegrationByParts
open scoped BigOperators InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem lieDerivative_exp_mul {N : ℕ} (A : Operator N) (q : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 1 H) (x : Vector N) :
    lieDerivative A (fun y => Real.exp (q * H y)) x =
      q * Real.exp (q * H x) * lieDerivative A H x := by
  have hh := ((hH.differentiable (by norm_num) x).hasFDerivAt.const_mul q).exp
  unfold lieDerivative
  rw [hh.fderiv]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

theorem lieDerivative_const_mul {N : ℕ} (A : Operator N) (q : ℝ)
    {f : Vector N → ℝ} (hf : ContDiff ℝ 1 f) (x : Vector N) :
    lieDerivative A (fun y => q * f y) x = q * lieDerivative A f x := by
  exact congrFun (lieDerivative_smul A f (hf.differentiable (by norm_num)) q) x

theorem lieDerivative_twice_exp_mul {N : ℕ} (A : Operator N) (q : ℝ)
    {H : Vector N → ℝ} (hH : ContDiff ℝ 2 H) (x : Vector N) :
    lieDerivative A (lieDerivative A (fun y => Real.exp (q * H y))) x =
      Real.exp (q * H x) * (q * lieDerivative A (lieDerivative A H) x +
        q ^ 2 * (lieDerivative A H x) ^ 2) := by
  have hH1 : ContDiff ℝ 1 H := hH.of_le (by norm_num)
  have he : ContDiff ℝ 1 (fun y => Real.exp (q * H y)) :=
    (contDiff_const.mul hH1).exp
  have hD := lieDerivative_contDiff_one A hH
  rw [show lieDerivative A (fun y => Real.exp (q * H y)) =
      (fun y => q * (Real.exp (q * H y) * lieDerivative A H y)) by
    funext y; rw [lieDerivative_exp_mul A q hH1]; ring]
  rw [lieDerivative_const_mul A q (he.mul hD), lieDerivative_mul A he hD,
    lieDerivative_exp_mul A q hH1]
  ring

/-- The continuous Schrödinger potential arising from the actual Gibbs drift. -/
def groundStatePotential (N : ℕ) (β : ℝ) (H : Vector N → ℝ) (x : Vector N) : ℝ :=
  β ^ 2 / 4 * ‖surfaceGradient H x‖ ^ 2 + β / 2 * rotationLaplacian N H x

theorem groundStatePotential_continuous {N : ℕ} (β : ℝ) {H : Vector N → ℝ}
    (hH : ContDiff ℝ 2 H) : Continuous (groundStatePotential N β H) := by
  exact (continuous_const.mul ((surfaceGradient_continuous
    (hH.of_le (by norm_num))).norm.pow 2)).add
      (continuous_const.mul (rotationLaplacian_continuous hH))

theorem groundStatePotential_bounded {N : ℕ} (β : ℝ) {H : Vector N → ℝ}
    (hH : ContDiff ℝ 2 H) : ∃ C : ℝ, ∀ x, OnSphere x →
      |groundStatePotential N β H x| ≤ C := by
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))).exists_bound_of_continuousOn
    (groundStatePotential_continuous β hH).continuousOn
  refine ⟨C, fun x hx => ?_⟩
  apply hC x
  rw [Metric.mem_closedBall, dist_zero_right]
  have hs : ‖x‖ ^ 2 = (N : ℝ) := (onSphere_iff_norm_sq x).mp hx
  exact (Real.le_sqrt (norm_nonneg x) (Nat.cast_nonneg N)).mpr hs.le

theorem rotationGenerator_groundState {N : ℕ} (hN : N ≠ 0) (β : ℝ)
    {H f : Vector N → ℝ} (hH : ContDiff ℝ 2 H) (hf : ContDiff ℝ 2 f)
    (x : Vector N) (hx : OnSphere x) :
    rotationGenerator N β H (fun y => Real.exp (-(β / 2) * H y) * f y) x =
      Real.exp (-(β / 2) * H x) *
        (rotationLaplacian N f x - groundStatePotential N β H x * f x) := by
  have hH1 : ContDiff ℝ 1 H := hH.of_le (by norm_num)
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have he : ContDiff ℝ 2 (fun y => Real.exp (-(β / 2) * H y)) :=
    (contDiff_const.mul hH).exp
  have term (A : Operator N) :
      lieDerivative A (lieDerivative A (fun y => Real.exp (-(β / 2) * H y) * f y)) x +
          β * lieDerivative A H x *
            lieDerivative A (fun y => Real.exp (-(β / 2) * H y) * f y) x =
        Real.exp (-(β / 2) * H x) *
          (lieDerivative A (lieDerivative A f) x -
            (β ^ 2 / 4 * (lieDerivative A H x) ^ 2 +
              β / 2 * lieDerivative A (lieDerivative A H) x) * f x) := by
    rw [SphericalAging.SphereGeneratorAlgebra.lieDerivative_twice_mul A he hf,
      lieDerivative_mul A (he.of_le (by norm_num)) hf1,
      lieDerivative_twice_exp_mul A (-(β / 2)) hH,
      lieDerivative_exp_mul A (-(β / 2)) hH1]
    ring
  rw [rotationGenerator_sum_onSphere hN β H _ x hx]
  simp_rw [term]
  unfold groundStatePotential rotationLaplacian
  rw [← real_inner_self_eq_norm_sq,
    surfaceGradient_rotation_pairing hN H H x hx]
  simp only [mul_sub, add_mul, mul_add, Finset.sum_mul, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, pow_two]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Literal differential conjugation, with the source normalization and sign. -/
theorem groundState_conjugation {N : ℕ} (hN : N ≠ 0) (β : ℝ)
    {H f : Vector N → ℝ} (hH : ContDiff ℝ 2 H) (hf : ContDiff ℝ 2 f)
    (x : Vector N) (hx : OnSphere x) :
    Real.exp (β / 2 * H x) *
      (-rotationGenerator N β H (fun y => Real.exp (-(β / 2) * H y) * f y) x) =
        -rotationLaplacian N f x + groundStatePotential N β H x * f x := by
  rw [rotationGenerator_groundState hN β hH hf x hx]
  have he : Real.exp (β / 2 * H x) * Real.exp (-(β / 2) * H x) = 1 := by
    rw [← Real.exp_add, show β / 2 * H x + -(β / 2) * H x = 0 by ring, Real.exp_zero]
  calc
    _ = -(Real.exp (β / 2 * H x) * Real.exp (-(β / 2) * H x)) *
        (rotationLaplacian N f x - groundStatePotential N β H x * f x) := by ring
    _ = _ := by rw [he]; ring

end SlowEquilibration.SphericalForm
