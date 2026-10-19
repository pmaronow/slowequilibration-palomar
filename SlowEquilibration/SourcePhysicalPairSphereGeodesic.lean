-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPosteriorSphereRegularity
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! Genuine constant-speed great circles and their tangent velocities.
These are the original round-sphere curves used in the critical collar. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open SphericalModel
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 500000

def sourceSphereGeodesic {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v:E) (t:ℝ):E:=Real.cos t • u+Real.sin t • v

def sourceSphereGeodesicVelocity {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v:E) (t:ℝ):E:=(-Real.sin t) • u+Real.cos t • v

lemma sourceSphereGeodesic_hasDerivAt {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v:E) (t:ℝ) :HasDerivAt (sourceSphereGeodesic u v) (sourceSphereGeodesicVelocity u v t) t:=by
  exact ((Real.hasDerivAt_cos t).smul_const u).add ((Real.hasDerivAt_sin t).smul_const v)

lemma sourceSphereGeodesicVelocity_hasDerivAt {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u v:E) (t:ℝ) :HasDerivAt (sourceSphereGeodesicVelocity u v) (-sourceSphereGeodesic u v t) t:=by
  have H:=((Real.hasDerivAt_sin t).neg.smul_const u).add ((Real.hasDerivAt_cos t).smul_const v)
  change HasDerivAt (fun t=>(-Real.sin t) • u+Real.cos t • v)
    (-(Real.cos t • u+Real.sin t • v)) t
  simpa only [neg_add,neg_smul,Pi.add_def,Pi.neg_apply] using H

lemma sourceSphereGeodesic_norm_sq {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v:E) {R:ℝ} (hu:‖u‖^2=R) (hv:‖v‖^2=R) (huv:inner ℝ u v=0) (t:ℝ) :
    ‖sourceSphereGeodesic u v t‖^2=R:=by
  have hvu:inner ℝ v u=0:=by rw [real_inner_comm];exact huv
  have huI:inner ℝ u u=R:=by rw [real_inner_self_eq_norm_sq,hu]
  have hvI:inner ℝ v v=R:=by rw [real_inner_self_eq_norm_sq,hv]
  rw [←real_inner_self_eq_norm_sq]
  simp only [sourceSphereGeodesic,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,huv,hvu,huI,hvI,mul_zero,add_zero,zero_add]
  calc
    _=R*(Real.sin t^2+Real.cos t^2):=by ring
    _=R:=by rw [Real.sin_sq_add_cos_sq,mul_one]

lemma sourceSphereGeodesicVelocity_norm_sq {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v:E) {R:ℝ} (hu:‖u‖^2=R) (hv:‖v‖^2=R) (huv:inner ℝ u v=0) (t:ℝ) :
    ‖sourceSphereGeodesicVelocity u v t‖^2=R:=by
  have hvu:inner ℝ v u=0:=by rw [real_inner_comm];exact huv
  have huI:inner ℝ u u=R:=by rw [real_inner_self_eq_norm_sq,hu]
  have hvI:inner ℝ v v=R:=by rw [real_inner_self_eq_norm_sq,hv]
  rw [←real_inner_self_eq_norm_sq]
  simp only [sourceSphereGeodesicVelocity,inner_add_left,inner_add_right,real_inner_smul_left,
    real_inner_smul_right,huv,hvu,huI,hvI,mul_zero,add_zero,zero_add]
  calc
    _=R*(Real.sin t^2+Real.cos t^2):=by ring
    _=R:=by rw [Real.sin_sq_add_cos_sq,mul_one]

lemma sourceSphereGeodesic_tangent {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u v:E) {R:ℝ} (hu:‖u‖^2=R) (hv:‖v‖^2=R) (huv:inner ℝ u v=0) (t:ℝ) :
    inner ℝ (sourceSphereGeodesic u v t) (sourceSphereGeodesicVelocity u v t)=0:=by
  have hvu:inner ℝ v u=0:=by rw [real_inner_comm];exact huv
  simp only [sourceSphereGeodesic,sourceSphereGeodesicVelocity,inner_add_left,inner_add_right,
    real_inner_smul_left,real_inner_smul_right,huv,hvu,real_inner_self_eq_norm_sq,hu,hv,mul_zero,add_zero,zero_add]
  ring

lemma sourceSphereGeodesic_zero {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u v:E) :
    sourceSphereGeodesic u v 0=u:=by simp only [sourceSphereGeodesic,Real.cos_zero,Real.sin_zero,one_smul,zero_smul,add_zero]

lemma sourceSphereGeodesicVelocity_zero {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (u v:E) :
    sourceSphereGeodesicVelocity u v 0=v:=by simp only [sourceSphereGeodesicVelocity,Real.cos_zero,Real.sin_zero,neg_zero,one_smul,zero_smul,zero_add]

end
end SlowEquilibration.PairConditionalDeterminantMoments
