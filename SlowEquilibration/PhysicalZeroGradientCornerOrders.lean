-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.HessianObservationBounds
public import SlowEquilibration.ObservationCrossBlockOrders

/-! Active-degree sharp Hessian covariance rows for the actual coefficient observation. -/
@[expose] public section
namespace SlowEquilibration.PhysicalZeroGradientCorner
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance PairObservationNormBounds PairObservationSmallOverlap
open ScalarCoefficientCovariance HessianObservationCovariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

/-- Unit dual Hessian rows retain order |rho|^(d−3)/sqrt N for the actual normalized
observation. The ambient unit directions need not be tangent for this bound. -/
theorem hessian_mixed_unit_degree_order {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hd : 3 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y u v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hu : ‖u‖=1) (hv : ‖v‖=1) (f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (w : MixedObservationSpace m) (hw : ‖w‖=1) (hr : |overlap x y| ≤ 1) :
    |flatJetCLM c 2 x ![u,v] ((singleMixedObservation c y f).adjoint w)| ≤
      7*profileBound c * |overlap x y|^(d-3)/Real.sqrt (N:ℝ) := by
  let W:=frameSum f w.snd
  let s:=Real.sqrt (N:ℝ)
  let r:=overlap x y
  have hwc:=mixed_unit_coordinate_bounds w hw
  have hW : ‖W‖ ≤ 1 := by rw [frameSum_norm f hf];exact hwc.2.2
  have ha : |inner ℝ u y/s| ≤ 1 := by
    rw [real_inner_comm]
    exact normalized_inner_le_one hN y hy u hu.le
  have hb : |inner ℝ v y/s| ≤ 1 := by
    rw [real_inner_comm]
    exact normalized_inner_le_one hN y hy v hv.le
  have hd : |inner ℝ x W/s| ≤ 1 := normalized_inner_le_one hN x hx W hW
  have he : |inner ℝ u W| ≤ 1 := by
    have h:=(abs_real_inner_le_norm u W).trans (mul_le_mul_of_nonneg_left hW (norm_nonneg u))
    simpa only [hu,mul_one,one_mul] using h
  have hf' : |inner ℝ v W| ≤ 1 := by
    have h:=(abs_real_inner_le_norm v W).trans (mul_le_mul_of_nonneg_left hW (norm_nonneg v))
    simpa only [hv,mul_one,one_mul] using h
  have hp := profile_order_common c d hdeg hr
  have hS : |secondCovariance c r| ≤ profileBound c * |r|^(d-3) :=
    hp.2.2.1.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_of_le_one (abs_nonneg _) hr (by omega : d-3 ≤ d-2))
      (profileBound_pos c).le)
  have hT : |thirdCovariance c r| ≤ profileBound c * |r|^(d-3) := hp.2.2.2
  have hbound:=HessianObservationCovariance.hessian_mixed_form_bound ha hb hd he hf' hwc.1 hwc.2.1 hr
    hS hT
  let core:=w.fst 0*secondCovariance c r*(inner ℝ u y/s)*(inner ℝ v y/s)+
      w.fst 1*(2*secondCovariance c r+r*thirdCovariance c r)*(inner ℝ u y/s)*(inner ℝ v y/s)+
      thirdCovariance c r*(inner ℝ x W/s)*(inner ℝ u y/s)*(inner ℝ v y/s)+
      secondCovariance c r*inner ℝ u W*(inner ℝ v y/s)+
      secondCovariance c r*(inner ℝ u y/s)*inner ℝ v W
  have hs : 0 < s := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have heq : flatJetCLM c 2 x ![u,v] ((singleMixedObservation c y f).adjoint w)=core/s := by
    rw [hessian_mixed_coupling hN c hc (fun p hp => by have hh:=hdeg p hp;omega)]
    dsimp only [core,W,r,s]
    field_simp
    rw [← Real.sq_sqrt (Nat.cast_nonneg N)]
    simp only [Real.sqrt_sq_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
    ring
  rw [heq,abs_div,abs_of_pos hs]
  apply div_le_div_of_nonneg_right _ hs.le
  convert hbound using 1; ring

/-- The same genuine row estimate for arbitrary observation vectors. -/
theorem hessian_mixed_degree_order {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) {d : ℕ} (hd : 3 ≤ d) (hdeg : ∀ p,c p≠0 → d ≤ p.val.val)
    (x y u v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hu : ‖u‖=1) (hv : ‖v‖=1) (f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (w : MixedObservationSpace m) (hr : |overlap x y| ≤ 1) :
    |flatJetCLM c 2 x ![u,v] ((singleMixedObservation c y f).adjoint w)| ≤
      (7*profileBound c * |overlap x y|^(d-3)/Real.sqrt (N:ℝ))*‖w‖ := by
  let F:=(flatJetCLM c 2 x ![u,v]).comp (singleMixedObservation c y f).adjoint
  have hF : ‖F‖ ≤ 7*profileBound c * |overlap x y|^(d-3)/Real.sqrt (N:ℝ) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity [profileBound_pos c])
    intro w hw
    simpa only [F,ContinuousLinearMap.comp_apply,Real.norm_eq_abs] using
      hessian_mixed_unit_degree_order hN c hc hd hdeg x y u v hx hy hu hv f hf w hw hr
  exact (F.le_opNorm w).trans (mul_le_mul_of_nonneg_right hF (norm_nonneg w))

end
end SlowEquilibration.PhysicalZeroGradientCorner
