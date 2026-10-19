-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PhysicalZeroGradientCornerOrders

/-! Sharp Hessian/score covariance on the original tensor coefficient space.
The extra overlap multiplying the third derivative is retained, giving d−2. -/
@[expose] public section
namespace SlowEquilibration.PhysicalZeroGradientCorner
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance PairObservationNormBounds ScalarCoefficientCovariance
open HessianObservationCovariance PairObservationCrossCovariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma hessian_score_coupling {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (hdeg : ∀ p, c p ≠ 0 → 3 ≤ p.val.val)
    (x y u v : Vector N) (w : EuclideanSpace ℝ (Fin 2)) :
    flatJetCLM c 2 x ![u,v] ((normalizedScore c y).adjoint w) =
      (w 0 / Real.sqrt (N:ℝ)) *
        (secondCovariance c (overlap x y)/(N:ℝ)*inner ℝ u y*inner ℝ v y) +
      (w 1 / Real.sqrt (N:ℝ)) *
        ((2*secondCovariance c (overlap x y)+overlap x y*thirdCovariance c (overlap x y)) /
          (N:ℝ)*inner ℝ u y*inner ℝ v y) := by
  rw [← scalarCross_right_dual, normalizedScore_dual]
  simp only [scalarCross_add_right, scalarCross_smul_right, scalarCross_flatJet]
  rw [hessian_value_covariance hN c hc x y, hessian_radial_covariance hN c hc hdeg x y]

lemma hessian_score_unit_degree_order {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {d : ℕ} (hd : 3 ≤ d)
    (hdeg : ∀ p, c p ≠ 0 → d ≤ p.val.val)
    (x y u v : Vector N) (hy : ‖y‖^2=(N:ℝ)) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (w : EuclideanSpace ℝ (Fin 2)) (hw : ‖w‖=1) (hr : |overlap x y| ≤ 1) :
    |flatJetCLM c 2 x ![u,v] ((normalizedScore c y).adjoint w)| ≤
      4*profileBound c*|overlap x y|^(d-2)/Real.sqrt (N:ℝ) := by
  let s := Real.sqrt (N:ℝ)
  let r := overlap x y
  have hs : 0 < s := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have ha : |inner ℝ u y/s| ≤ 1 := by
    rw [real_inner_comm]
    exact normalized_inner_le_one hN y hy u hu.le
  have hb : |inner ℝ v y/s| ≤ 1 := by
    rw [real_inner_comm]
    exact normalized_inner_le_one hN y hy v hv.le
  have hwc := unit_score_coordinates w hw
  have hp := profile_order_common c d hdeg hr
  have hrT : |r*thirdCovariance c r| ≤ profileBound c*|r|^(d-2) := by
    rw [abs_mul]
    calc
      _ ≤ |r| *(profileBound c*|r|^(d-3)) :=
        mul_le_mul_of_nonneg_left hp.2.2.2 (abs_nonneg r)
      _ = _ := by rw [mul_left_comm, ← pow_succ', show d-3+1=d-2 by omega]
  have hmix : |2*secondCovariance c r+r*thirdCovariance c r| ≤
      3*profileBound c*|r|^(d-2) := by
    have hsum := abs_add_le (2*secondCovariance c r) (r*thirdCovariance c r)
    rw [abs_mul] at hsum
    norm_num only [show |(2:ℝ)|=2 by norm_num] at hsum
    linarith [hp.2.2.1]
  have h1 : |w 0*secondCovariance c r*(inner ℝ u y/s)*(inner ℝ v y/s)| ≤
      profileBound c*|r|^(d-2) := by
    have hab : |(inner ℝ u y/s)*(inner ℝ v y/s)| ≤ 1 := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul ha hb (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    simpa [mul_comm, mul_left_comm, mul_assoc] using abs_triple_le hwc.1 hab hp.2.2.1
  have h2 : |w 1*(2*secondCovariance c r+r*thirdCovariance c r)*
      (inner ℝ u y/s)*(inner ℝ v y/s)| ≤ 3*profileBound c*|r|^(d-2) := by
    have hab : |(inner ℝ u y/s)*(inner ℝ v y/s)| ≤ 1 := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul ha hb (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
    simpa [mul_comm, mul_left_comm, mul_assoc] using abs_triple_le hwc.2 hab hmix
  let core := w 0*secondCovariance c r*(inner ℝ u y/s)*(inner ℝ v y/s)+
    w 1*(2*secondCovariance c r+r*thirdCovariance c r)*(inner ℝ u y/s)*(inner ℝ v y/s)
  have heq : flatJetCLM c 2 x ![u,v] ((normalizedScore c y).adjoint w)=core/s := by
    rw [hessian_score_coupling hN c hc (fun p hp => by have hh:=hdeg p hp; omega)]
    dsimp only [core,r,s]
    field_simp
    rw [← Real.sq_sqrt (Nat.cast_nonneg N)]
    all_goals simp only [Real.sqrt_sq_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [heq,abs_div,abs_of_pos hs]
  apply div_le_div_of_nonneg_right _ hs.le
  exact (abs_add_le _ _).trans (by linarith)

/-- A sharp actual Hessian/score operator row, with a constant independent of N. -/
theorem hessian_score_degree_order {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) {d : ℕ} (hd : 3 ≤ d)
    (hdeg : ∀ p, c p ≠ 0 → d ≤ p.val.val)
    (x y u v : Vector N) (hy : ‖y‖^2=(N:ℝ)) (hu : ‖u‖=1) (hv : ‖v‖=1)
    (hr : |overlap x y| ≤ 1) :
    ‖(flatJetCLM c 2 x ![u,v]).comp (normalizedScore c y).adjoint‖ ≤
      4*profileBound c*|overlap x y|^(d-2)/Real.sqrt (N:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity [profileBound_pos c])
  intro w hw
  exact hessian_score_unit_degree_order hN c hc hd hdeg x y u v hy hu hv w hw hr

end
end SlowEquilibration.PhysicalZeroGradientCorner
