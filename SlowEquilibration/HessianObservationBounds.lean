-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.HessianObservationCovariance
public import SlowEquilibration.PairObservationSmallOverlap

/-! Dimension-independent actual Hessian observation row estimates. -/
@[expose] public section
namespace SlowEquilibration.HessianObservationCovariance
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open SphericalTwoPointCovariance PairObservationNormBounds PairObservationSmallOverlap
open ScalarCoefficientCovariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma hessian_mixed_form_bound {a b d e f p q r S T L : ℝ}
    (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hd : |d| ≤ 1) (he : |e| ≤ 1) (hf : |f| ≤ 1)
    (hp : |p| ≤ 1) (hq : |q| ≤ 1) (hr : |r| ≤ 1)
    (hS : |S| ≤ L) (hT : |T| ≤ L) :
    |p*S*a*b+q*(2*S+r*T)*a*b+T*d*a*b+S*e*b+S*a*f| ≤ 7*L := by
  have hab : |a*b| ≤ 1 := by
    rw [abs_mul]
    calc
      |a| * |b| ≤ 1*1 := by gcongr
      _=1 := by ring
  have hrT : |r*T| ≤ L := by simpa using abs_triple_le hr (by norm_num : |(1:ℝ)| ≤ 1) hT
  have hmix : |2*S+r*T| ≤ 3*L := by
    have hsum:=abs_add_le (2*S) (r*T)
    rw [abs_mul] at hsum
    norm_num only [show |(2:ℝ)|=2 by norm_num] at hsum
    linarith
  have h1 : |p*S*a*b| ≤ L := by simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le hp hab hS
  have h2 : |q*(2*S+r*T)*a*b| ≤ 3*L := by simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le hq hab hmix
  have h3 : |T*d*a*b| ≤ L := by simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le hd hab hT
  have h4 : |S*e*b| ≤ L := by simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le he hb hS
  have h5 : |S*a*f| ≤ L := by simpa [mul_comm,mul_left_comm,mul_assoc] using abs_triple_le ha hf hS
  grw [abs_add_le,abs_add_le,abs_add_le,abs_add_le]
  linarith

/-- Unit dual Hessian rows decay as |rho|/sqrt N for the actual normalized
observation. The ambient unit directions need not be tangent for this bound. -/
theorem hessian_mixed_unit_bound {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y u v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hu : ‖u‖=1) (hv : ‖v‖=1) (f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (w : MixedObservationSpace m) (hw : ‖w‖=1) (hr : |overlap x y| ≤ 1) :
    |flatJetCLM c 2 x ![u,v] ((singleMixedObservation c y f).adjoint w)| ≤
      7*profileBound c * |overlap x y|/Real.sqrt (N:ℝ) := by
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
  have hprofiles:=profiles_le_common c hdeg hr
  have hbound:=hessian_mixed_form_bound ha hb hd he hf' hwc.1 hwc.2.1 hr
    hprofiles.2.2.1 hprofiles.2.2.2
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
theorem hessian_mixed_bound {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 4 ≤ p.val.val)
    (x y u v : Vector N) (hx : ‖x‖^2=(N:ℝ)) (hy : ‖y‖^2=(N:ℝ))
    (hu : ‖u‖=1) (hv : ‖v‖=1) (f : Fin m → Vector N) (hf : Orthonormal ℝ f)
    (w : MixedObservationSpace m) (hr : |overlap x y| ≤ 1) :
    |flatJetCLM c 2 x ![u,v] ((singleMixedObservation c y f).adjoint w)| ≤
      (7*profileBound c * |overlap x y|/Real.sqrt (N:ℝ))*‖w‖ := by
  let F:=(flatJetCLM c 2 x ![u,v]).comp (singleMixedObservation c y f).adjoint
  have hF : ‖F‖ ≤ 7*profileBound c * |overlap x y|/Real.sqrt (N:ℝ) := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity [profileBound_pos c])
    intro w hw
    simpa only [F,ContinuousLinearMap.comp_apply,Real.norm_eq_abs] using
      hessian_mixed_unit_bound hN c hc hdeg x y u v hx hy hu hv f hf w hw hr
  exact (F.le_opNorm w).trans (mul_le_mul_of_nonneg_right hF (norm_nonneg w))

end
end SlowEquilibration.HessianObservationCovariance
