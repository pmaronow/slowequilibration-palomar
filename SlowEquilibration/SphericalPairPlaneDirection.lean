-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPairCommonFrame

/-! Literal normalized plane directions for the one-border decomposition
of both actual tangent Hessians. The dimension and directions are geometric. -/
@[expose] public section
namespace SlowEquilibration.SphericalPairCommonFrame
noncomputable section
open SphericalModel SphericalGaussianJet SphericalTwoPointCovariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

def planeScale {N : ℕ} (x y : Vector N) : ℝ := Real.sqrt ((N:ℝ)*(1-overlap x y^2))

def planeDirection {N : ℕ} (x y : Vector N) : Vector N :=
  (planeScale x y)⁻¹ • (y-overlap x y • x)

lemma planeScale_pos {N : ℕ} (hN : 0 < N) (x y : Vector N) (hr : |overlap x y| < 1) :
    0 < planeScale x y := by
  apply Real.sqrt_pos.mpr
  have hsq : overlap x y^2 < 1 := by nlinarith [sq_abs (overlap x y),sq_lt_sq₀ (abs_nonneg (overlap x y)) (by norm_num : 0 ≤ (1:ℝ)) |>.mpr hr]
  exact mul_pos (Nat.cast_pos.mpr hN) (sub_pos.mpr hsq)

lemma planeScale_square {N : ℕ} (hN : 0 < N) (x y : Vector N) (hr : |overlap x y| < 1) :
    planeScale x y^2=(N:ℝ)*(1-overlap x y^2) :=
  Real.sq_sqrt ((Real.sqrt_pos.mp (planeScale_pos hN x y hr)).le)

lemma planeDirection_tangent {N : ℕ} (hN : 0 < N) (x y : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) : inner ℝ (planeDirection x y) x=0 := by
  rw [planeDirection,real_inner_smul_left,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq,hx,
    real_inner_comm x y,inner_eq_dimension_overlap hN x y]
  ring

lemma planeNumerator_norm_sq {N : ℕ} (hN : 0 < N) (x y : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) :
    ‖y-overlap x y • x‖^2=(N:ℝ)*(1-overlap x y^2) := by
  rw [norm_sub_sq_real,real_inner_smul_right,real_inner_comm x y,inner_eq_dimension_overlap hN x y,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hx,hy]
  ring

lemma planeDirection_norm {N : ℕ} (hN : 0 < N) (x y : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) (hr : |overlap x y| < 1) :
    ‖planeDirection x y‖=1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) (by norm_num : 0 ≤ (1:ℝ))).mp
  rw [planeDirection,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inv_pow,
    planeNumerator_norm_sq hN x y hx hy,← planeScale_square hN x y hr,
    inv_mul_cancel₀ (pow_ne_zero 2 (planeScale_pos hN x y hr).ne')]
  norm_num

lemma planeDirection_common_inner {N : ℕ} (x y u : Vector N)
    (hu : inner ℝ u x=0) (hv : inner ℝ u y=0) :
    inner ℝ u (planeDirection x y)=0 := by
  rw [planeDirection,real_inner_smul_right,inner_sub_right,real_inner_smul_right,hu,hv]
  simp

lemma planeDirection_other_inner {N : ℕ} (hN : 0 < N) (x y : Vector N)
    (hy : ‖y‖^2=(N:ℝ)) (hr : |overlap x y| < 1) :
    inner ℝ (planeDirection x y) y=planeScale x y := by
  rw [planeDirection,real_inner_smul_left,inner_sub_left,real_inner_smul_left,
    real_inner_self_eq_norm_sq,hy,inner_eq_dimension_overlap hN x y]
  have hs:=planeScale_square hN x y hr
  have hp:=(planeScale_pos hN x y hr).ne'
  calc
    _=(planeScale x y)⁻¹*((N:ℝ)*(1-overlap x y^2)) := by ring
    _=(planeScale x y)⁻¹*planeScale x y^2 := by rw [hs]
    _=planeScale x y := by field_simp

lemma planeScale_comm {N : ℕ} (x y : Vector N) : planeScale y x=planeScale x y := by
  rw [planeScale,planeScale,overlap_comm]

lemma planeDirection_pair_inner {N : ℕ} (hN : 0 < N) (x y : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ)) (hr : |overlap x y| < 1) :
    inner ℝ (planeDirection x y) (planeDirection y x)= -overlap x y := by
  simp only [planeDirection,real_inner_smul_left,real_inner_smul_right,
    planeScale_comm x y,overlap_comm x y,inner_sub_left,inner_sub_right,
    real_inner_self_eq_norm_sq,hx,hy,real_inner_comm x y,inner_eq_dimension_overlap hN x y]
  have hs:=planeScale_square hN x y hr
  have hp:=(planeScale_pos hN x y hr).ne'
  field_simp
  rw [hs]
  ring

end
end SlowEquilibration.SphericalPairCommonFrame
