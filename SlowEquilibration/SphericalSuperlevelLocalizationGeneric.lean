-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCriticalGeodesicDecay
public import Mathlib.Topology.Order.IntermediateValue

/-! The literal deterministic localization lemma `lem:pc-superlevel` for
arbitrary C³ ambient representatives of functions on the physical sphere.
The third derivative is the covariant derivative of the projected intrinsic
Hessian, exactly as in the polynomial-field regularity convention. The
localization radius includes the zero third-derivative case. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalSuperlevelLocalizationGeneric

open Set Filter SphericalModel SphericalForm SphereHessian
open PairConditionalDeterminantMoments SphericalCriticalGeodesicDecay
open SphericalAging.HardSphereDynamics SphericalAging.SphericalIntegrationByParts
open scoped Topology RealInnerProductSpace

set_option autoImplicit false

/-- Ambient extension of the intrinsic Hessian, with both arguments projected
onto thetangent plane. -/
def sphereHessianExtension {N : ℕ} (f : Vector N → ℝ) (x : Vector N) :
    Vector N →L[ℝ] Vector N :=
  (tangentProjection x).comp
    ((fderiv ℝ (surfaceGradient f) x).comp (tangentProjection x))

/-- Covariant third derivative, extended by tangent projection in its two
arguments and its output. Its operator norm is the intrinsic third-derivative
norm on the sphere, in the convention of `sourceSphereThirdExtension`. -/
def sphereThirdExtension {N : ℕ} (f : Vector N → ℝ) (x : Vector N) :
    Vector N →L[ℝ] Vector N →L[ℝ] Vector N :=
  (((ContinuousLinearMap.compL ℝ (Vector N) (Vector N) (Vector N) (tangentProjection x)).comp
    ((ContinuousLinearMap.compL ℝ (Vector N) (Vector N) (Vector N)).flip
      (tangentProjection x))).comp
        (fderiv ℝ (sphereHessianExtension f) x)).comp (tangentProjection x)

/-- The manuscript radius, including its stipulated value when `C₃ = 0`. -/
def localizationRadius (κ C₃ : ℝ) : ℝ :=
  if C₃ = 0 then 1 else min 1 (κ / (2 * C₃))

/-- The quadratic-form inequality `∇²_{S_N} f(x) ≤ -κ I` on the intrinsic
tangent plane. -/
def intrinsicHessianMargin {N : ℕ} (f : Vector N → ℝ) (κ : ℝ) (x : Vector N) : Prop :=
  ∀ v : tangentPlane x, inner ℝ v (intrinsicHessian f x v) ≤ -κ * ‖v‖ ^ 2

private theorem surfaceGradient_contDiff_two {N : ℕ} (f : Vector N → ℝ)
    (hf : ContDiff ℝ 3 f) : ContDiff ℝ 2 (surfaceGradient f) := by
  have hd : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hg : ContDiff ℝ 2 (gradient f) :=
    (InnerProductSpace.toDual ℝ (Vector N)).symm.contDiff.comp hd
  exact ((source_tangentProjection_contDiff N).of_le (by simp)).clm_apply hg

private theorem sphereHessianExtension_contDiff_one {N : ℕ} (f : Vector N → ℝ)
    (hf : ContDiff ℝ 3 f) : ContDiff ℝ 1 (sphereHessianExtension f) := by
  have hπ : ContDiff ℝ 1 (tangentProjection (N := N)) :=
    (source_tangentProjection_contDiff N).of_le (by simp)
  have hd : ContDiff ℝ 1 (fderiv ℝ (surfaceGradient f)) :=
    (surfaceGradient_contDiff_two f hf).fderiv_right (by norm_num)
  exact hπ.clm_comp (hd.clm_comp hπ)

private theorem sphereHessianExtension_intrinsic_apply {N : ℕ} (hN : N ≠ 0)
    (f : Vector N → ℝ) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ))
    (v : tangentPlane x) :
    (intrinsicHessian f x v : Vector N) = sphereHessianExtension f x v := by
  have hx' : OnSphere x := by
    simpa only [OnSphere, real_inner_self_eq_norm_sq] using hx
  have hP : tangentProjection x (v : Vector N) = v := by
    rw [tangentProjection_eq_starProjection hN x hx']
    exact (tangentPlane x).starProjection_eq_self_iff.mpr v.property
  simp only [intrinsicHessian, sphereHessianExtension, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply, Submodule.coe_orthogonalProjectionOnto_apply]
  rw [← tangentProjection_eq_starProjection hN x hx', hP]

private theorem margin_tangent {N : ℕ} (hN : N ≠ 0) (f : Vector N → ℝ)
    {κ : ℝ} (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ))
    (hMargin : intrinsicHessianMargin f κ x) (v : Vector N)
    (hv : inner ℝ x v = 0) :
    inner ℝ v (sphereHessianExtension f x v) ≤ -κ * ‖v‖ ^ 2 := by
  let w : tangentPlane x := ⟨v,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hv⟩
  have H := hMargin w
  change inner ℝ v (intrinsicHessian f x w : Vector N) ≤ -κ * ‖v‖ ^ 2 at H
  rwa [sphereHessianExtension_intrinsic_apply hN f x hx w] at H

private theorem sphereHessianExtension_radial_zero {N : ℕ} (hN : 0 < N)
    (f : Vector N → ℝ) (x : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    sphereHessianExtension f x x = 0 := by
  simp only [sphereHessianExtension, ContinuousLinearMap.comp_apply,
    source_tangentProjection_radial_zero hN x hx, map_zero]

private theorem sphereHessianExtension_range_tangent {N : ℕ} (hN : 0 < N)
    (f : Vector N → ℝ) (x v : Vector N) (hx : ‖x‖ ^ 2 = (N : ℝ)) :
    inner ℝ x (sphereHessianExtension f x v) = 0 := by
  simp only [sphereHessianExtension, ContinuousLinearMap.comp_apply, tangentProjection_apply]
  exact projection_tangent hN.ne' x _
    (by simpa only [OnSphere, real_inner_self_eq_norm_sq] using hx)

private theorem sphereThirdExtension_tangent_apply {N : ℕ} (f : Vector N → ℝ)
    (x v w : Vector N) (hv : inner ℝ x v = 0) (hw : inner ℝ x w = 0) :
    sphereThirdExtension f x v w =
      tangentProjection x ((fderiv ℝ (sphereHessianExtension f) x v) w) := by
  change tangentProjection x ((fderiv ℝ (sphereHessianExtension f) x
    (tangentProjection x v)) (tangentProjection x w)) = _
  rw [source_tangentProjection_fixed x v hv, source_tangentProjection_fixed x w hw]

private def geodesicSlope {N : ℕ} (f : Vector N → ℝ) (u v : Vector N) (t : ℝ) : ℝ :=
  inner ℝ (sourceSphereGeodesicVelocity u v t) (surfaceGradient f (sourceSphereGeodesic u v t))

private def geodesicCurvature {N : ℕ} (f : Vector N → ℝ) (u v : Vector N) (t : ℝ) : ℝ :=
  inner ℝ (sourceSphereGeodesicVelocity u v t)
    (sphereHessianExtension f (sourceSphereGeodesic u v t) (sourceSphereGeodesicVelocity u v t))

private def geodesicCubic {N : ℕ} (f : Vector N → ℝ) (u v : Vector N) (t : ℝ) : ℝ :=
  inner ℝ (sourceSphereGeodesicVelocity u v t)
    (sphereThirdExtension f (sourceSphereGeodesic u v t)
      (sourceSphereGeodesicVelocity u v t) (sourceSphereGeodesicVelocity u v t))

private theorem geodesicSlope_hasDerivAt {N : ℕ} (hN : 0 < N)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 3 f)
    (u v : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ)) (hv : ‖v‖ ^ 2 = (N : ℝ))
    (huv : inner ℝ u v = 0) (t : ℝ) :
    HasDerivAt (geodesicSlope f u v) (geodesicCurvature f u v t) t := by
  let x := sourceSphereGeodesic u v t
  let d := sourceSphereGeodesicVelocity u v t
  have hx : ‖x‖ ^ 2 = (N : ℝ) := sourceSphereGeodesic_norm_sq u v hu hv huv t
  have hxd : inner ℝ x d = 0 := sourceSphereGeodesic_tangent u v hu hv huv t
  have hG := surfaceGradient_contDiff_two f hf
  have hcurve := sourceSphereGeodesic_hasDerivAt u v t
  have hvel := sourceSphereGeodesicVelocity_hasDerivAt u v t
  have hgrad := (hG.differentiable (by simp) x).hasFDerivAt.comp_hasDerivAt t hcurve
  have H := hvel.inner ℝ hgrad
  have hRad : inner ℝ (-x) (surfaceGradient f x) = 0 := by
    rw [inner_neg_left, real_inner_comm, inner_surfaceGradient,
      source_tangentProjection_radial_zero hN x hx, map_zero, neg_zero]
  have hH : inner ℝ d (sphereHessianExtension f x d) =
      inner ℝ d (fderiv ℝ (surfaceGradient f) x d) := by
    simp only [sphereHessianExtension, ContinuousLinearMap.comp_apply,
      source_tangentProjection_fixed x d hxd]
    exact source_inner_tangentProjection x d _ hxd
  convert H using 1
  · rfl
  · change inner ℝ d (sphereHessianExtension f x d) =
      inner ℝ d (fderiv ℝ (surfaceGradient f) x d) + inner ℝ (-x) (surfaceGradient f x)
    rw [hRad, add_zero, hH]

private theorem geodesicCurvature_hasDerivAt {N : ℕ} (hN : 0 < N)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 3 f)
    (u v : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ)) (hv : ‖v‖ ^ 2 = (N : ℝ))
    (huv : inner ℝ u v = 0) (t : ℝ) :
    HasDerivAt (geodesicCurvature f u v) (geodesicCubic f u v t) t := by
  let x := sourceSphereGeodesic u v t
  let d := sourceSphereGeodesicVelocity u v t
  have hx : ‖x‖ ^ 2 = (N : ℝ) := sourceSphereGeodesic_norm_sq u v hu hv huv t
  have hxd : inner ℝ x d = 0 := sourceSphereGeodesic_tangent u v hu hv huv t
  have hcurve := sourceSphereGeodesic_hasDerivAt u v t
  have hvel := sourceSphereGeodesicVelocity_hasDerivAt u v t
  have hess := ((sphereHessianExtension_contDiff_one f hf).differentiable (by simp)
    x).hasFDerivAt.comp_hasDerivAt t hcurve
  have happ := hess.clm_apply hvel
  have H := hvel.inner ℝ happ
  have hRad := sphereHessianExtension_radial_zero hN f x hx
  have hRan := sphereHessianExtension_range_tangent hN f x d hx
  have hT : inner ℝ d (sphereThirdExtension f x d d) =
      inner ℝ d ((fderiv ℝ (sphereHessianExtension f) x d) d) := by
    rw [sphereThirdExtension_tangent_apply f x d d hxd hxd]
    exact source_inner_tangentProjection x d _ hxd
  convert H using 1
  · rfl
  · change inner ℝ d (sphereThirdExtension f x d d) =
      inner ℝ d ((fderiv ℝ (sphereHessianExtension f) x d) d +
        sphereHessianExtension f x (-x)) + inner ℝ (-x) (sphereHessianExtension f x d)
    rw [map_neg, hRad, neg_zero, add_zero, inner_neg_left, hRan, neg_zero, add_zero, hT]

private theorem scalar_derivative_upper_bound
    (f f' : ℝ → ℝ) (b M : ℝ) (hb : 0 ≤ b)
    (hderiv : ∀ r ∈ Icc (0 : ℝ) b, HasDerivAt f (f' r) r)
    (hbound : ∀ r ∈ Icc (0 : ℝ) b, f' r ≤ M) :
    f b - f 0 ≤ M * b := by
  rcases hb.eq_or_lt with rfl | hbpos
  · simp
  have hc : ContinuousOn f (Icc (0 : ℝ) b) :=
    fun x hx => (hderiv x hx).continuousAt.continuousWithinAt
  obtain ⟨r, hr, hslope⟩ := exists_hasDerivAt_eq_slope f f' hbpos hc
    (fun x hx => hderiv x (Ioo_subset_Icc_self hx))
  have hle : (f b - f 0) / b ≤ M := by
    have heq : f' r = (f b - f 0) / b := by simpa using hslope
    rw [← heq]
    exact hbound r (Ioo_subset_Icc_self hr)
  exact (div_le_iff₀ hbpos).mp hle

private theorem geodesic_cubic_abs_le {N : ℕ}
    (hN : 0 < N) (f : Vector N → ℝ) {C : ℝ}
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sphereThirdExtension f x‖ ≤ C / Real.sqrt (N : ℝ))
    (u v : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (hv : ‖v‖ ^ 2 = (N : ℝ)) (huv : inner ℝ u v = 0) (t : ℝ) :
    |geodesicCubic f u v t| ≤ C * (N : ℝ) := by
  let x := sourceSphereGeodesic u v t
  let d := sourceSphereGeodesicVelocity u v t
  let T := sphereThirdExtension f x
  have hx : ‖x‖ ^ 2 = (N : ℝ) := sourceSphereGeodesic_norm_sq u v hu hv huv t
  have hd : ‖d‖ ^ 2 = (N : ℝ) := sourceSphereGeodesicVelocity_norm_sq u v hu hv huv t
  have hdNorm : ‖d‖ = Real.sqrt (N : ℝ) := by
    rw [← hd, Real.sqrt_sq (norm_nonneg _)]
  have hT : ‖T‖ ≤ C / Real.sqrt (N : ℝ) := hThird x hx
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  change |inner ℝ d (T d d)| ≤ _
  calc
    _ ≤ ‖d‖ * ‖T d d‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖d‖ * (‖T d‖ * ‖d‖) :=
      mul_le_mul_of_nonneg_left ((T d).le_opNorm d) (norm_nonneg d)
    _ ≤ ‖d‖ * ((‖T‖ * ‖d‖) * ‖d‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (T.le_opNorm d) (norm_nonneg d)) (norm_nonneg d)
    _ ≤ ‖d‖ * ((C / Real.sqrt (N : ℝ) * ‖d‖) * ‖d‖) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hT (norm_nonneg d)) (norm_nonneg d)) (norm_nonneg d)
    _ = C * (N : ℝ) := by
      rw [hdNorm, div_mul_cancel₀ _ hs.ne']
      calc
        _ = C * (Real.sqrt (N : ℝ)) ^ 2 := by ring
        _ = C * (N : ℝ) := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

private theorem geodesic_curvature_le {N : ℕ}
    (hN : 0 < N) (f : Vector N → ℝ) (hf : ContDiff ℝ 3 f)
    {C κ ρ : ℝ} (hC : 0 ≤ C) (hρκ : 2 * C * ρ ≤ κ)
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sphereThirdExtension f x‖ ≤ C / Real.sqrt (N : ℝ))
    (u v : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (hv : ‖v‖ ^ 2 = (N : ℝ)) (huv : inner ℝ u v = 0)
    (hMargin : intrinsicHessianMargin f κ u) :
    ∀ t ∈ Icc (0 : ℝ) ρ,
      geodesicCurvature f u v t ≤ -(κ / 2) * (N : ℝ) := by
  intro t ht
  have hh0 : geodesicCurvature f u v 0 ≤ -κ * (N : ℝ) := by
    unfold geodesicCurvature
    rw [sourceSphereGeodesicVelocity_zero, sourceSphereGeodesic_zero]
    have H := margin_tangent hN.ne' f u hu hMargin v huv
    simpa only [hv] using H
  have hdiff := scalar_derivative_upper_bound
    (geodesicCurvature f u v) (geodesicCubic f u v)
    t (C * (N : ℝ)) ht.1
    (fun r _ => geodesicCurvature_hasDerivAt hN f hf u v hu hv huv r)
    (fun r _ => (le_abs_self _).trans (geodesic_cubic_abs_le hN f hThird u v hu hv huv r))
  have hct : C * t ≤ κ / 2 := by nlinarith [mul_le_mul_of_nonneg_left ht.2 hC]
  have hctN := mul_le_mul_of_nonneg_right hct (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

private theorem geodesic_slope_le {N : ℕ}
    (hN : 0 < N) (f : Vector N → ℝ) (hf : ContDiff ℝ 3 f)
    {C κ ρ : ℝ} (hC : 0 ≤ C) (hρκ : 2 * C * ρ ≤ κ)
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sphereThirdExtension f x‖ ≤ C / Real.sqrt (N : ℝ))
    (u v : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (hv : ‖v‖ ^ 2 = (N : ℝ)) (huv : inner ℝ u v = 0)
    (hCrit : surfaceGradient f u = 0)
    (hMargin : intrinsicHessianMargin f κ u) :
    ∀ t ∈ Icc (0 : ℝ) ρ,
      geodesicSlope f u v t ≤ -(κ / 2) * (N : ℝ) * t := by
  intro t ht
  have hs0 : geodesicSlope f u v 0 = 0 := by
    simp only [geodesicSlope, sourceSphereGeodesic_zero, hCrit, inner_zero_right]
  have H := scalar_derivative_upper_bound
    (geodesicSlope f u v) (geodesicCurvature f u v)
    t (-(κ / 2) * (N : ℝ)) ht.1
    (fun r _ => geodesicSlope_hasDerivAt hN f hf u v hu hv huv r)
    (fun r hr => geodesic_curvature_le hN f hf hC hρκ hThird u v hu hv huv hMargin
      r (Icc_subset_Icc_right ht.2 hr))
  simpa only [hs0, sub_zero] using H

private theorem function_geodesic_hasDerivAt {N : ℕ}
    (f : Vector N → ℝ) (hf : ContDiff ℝ 3 f)
    (u v : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (hv : ‖v‖ ^ 2 = (N : ℝ)) (huv : inner ℝ u v = 0) (t : ℝ) :
    HasDerivAt (fun r => f (sourceSphereGeodesic u v r))
      (geodesicSlope f u v t) t := by
  have H := (hf.differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    (sourceSphereGeodesic_hasDerivAt u v t)
  convert H using 1
  · rfl
  · unfold geodesicSlope
    rw [real_inner_comm, inner_surfaceGradient, source_tangentProjection_fixed _ _
      (sourceSphereGeodesic_tangent u v hu hv huv t)]

set_option linter.unusedVariables false in
/-- Source `lem:pc-superlevel`: the energy drops by at least `κ N t² / 4`
along every great circle from a critical point with Hessian margin `κ`. -/
private theorem geodesic_quadratic_drop {N : ℕ}
    (hN : 0 < N) (f : Vector N → ℝ) (hf : ContDiff ℝ 3 f)
    {C κ ρ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρκ : 2 * C * ρ ≤ κ)
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sphereThirdExtension f x‖ ≤ C / Real.sqrt (N : ℝ))
    (u v : Vector N)
    (hu : ‖u‖ ^ 2 = (N : ℝ)) (hv : ‖v‖ ^ 2 = (N : ℝ))
    (huv : inner ℝ u v = 0)
    (hCrit : surfaceGradient f u = 0)
    (hMargin : intrinsicHessianMargin f κ u) :
    ∀ t ∈ Icc (0 : ℝ) ρ,
      f (sourceSphereGeodesic u v t) ≤
        f u - κ / 4 * (N : ℝ) * t ^ 2 := by
  intro t ht
  let g : ℝ → ℝ := fun r => f (sourceSphereGeodesic u v r) + κ / 4 * (N : ℝ) * r ^ 2
  let g' : ℝ → ℝ := fun r => geodesicSlope f u v r + κ / 2 * (N : ℝ) * r
  have hg : ∀ r, HasDerivAt g (g' r) r := by
    intro r
    convert (function_geodesic_hasDerivAt f hf u v hu hv huv r).add
      (((hasDerivAt_id r).pow 2).const_mul (κ / 4 * (N : ℝ))) using 1
    · rfl
    · dsimp [g']
      ring
  have H := scalar_derivative_upper_bound g g' t 0 ht.1 (fun r _ => hg r) (by
    intro r hr
    have hs := geodesic_slope_le (by omega) f hf hC hρκ hThird u v hu hv huv hCrit hMargin
      r (Icc_subset_Icc_right ht.2 hr)
    dsimp [g']
    linarith)
  dsimp [g] at H
  rw [sourceSphereGeodesic_zero] at H
  nlinarith

private theorem short_ball_critical_unique {N : ℕ}
    (hN : 0 < N) (f : Vector N → ℝ) (hf : ContDiff ℝ 3 f)
    {C κ ρ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρκ : 2 * C * ρ ≤ κ)
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sphereThirdExtension f x‖ ≤ C / Real.sqrt (N : ℝ))
    (u w : Vector N)
    (hu : ‖u‖ ^ 2 = (N : ℝ)) (hw : ‖w‖ ^ 2 = (N : ℝ))
    (hCrit : surfaceGradient f u = 0)
    (hMargin : intrinsicHessianMargin f κ u)
    (hwCrit : surfaceGradient f w = 0)
    (hDist : sphereGeodesicDist u w ≤ ρ * Real.sqrt (N : ℝ)) :
    w = u := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  by_contra hne
  have hNpos : 0 < n + 1 := by omega
  have hNr : (0 : ℝ) < (n + 1 : ℕ) := Nat.cast_pos.mpr hNpos
  have hsqrt : 0 < Real.sqrt (n + 1 : ℕ) := Real.sqrt_pos.mpr hNr
  have hr := overlap_mem_Icc_of_norm_sq (by omega) u w hu hw
  have hrlt : overlap u w < 1 := lt_of_le_of_ne hr.2 (by
    intro heq
    exact hne (source_sphere_eq_of_overlap_one hNpos u w hu hw heq).symm)
  have hθpos : 0 < Real.arccos (overlap u w) := Real.arccos_pos.mpr hrlt
  have hθle : Real.arccos (overlap u w) ≤ ρ := by
    apply (mul_le_mul_iff_right₀ hsqrt).mp
    simpa only [sphereGeodesicDist, mul_comm] using hDist
  have hρrange : ρ ∈ Ioc (0 : ℝ) 1 := ⟨hρ, hρ1⟩
  have hθone := hθle.trans hρrange.2
  have hrpos : 0 < overlap u w := by
    rw [← Real.cos_arccos hr.1 hr.2]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_gt_three]
  obtain ⟨v, hv, huv, hEnd⟩ := sourceSphereGeodesic_reconstruction u w hu hw ⟨hrpos, hrlt⟩
  have H := geodesic_slope_le hNpos f hf hC hρκ hThird u v hu hv huv hCrit hMargin
    (Real.arccos (overlap u w)) ⟨hθpos.le, hθle⟩
  have hEndSlope : geodesicSlope f u v (Real.arccos (overlap u w)) = 0 := by
    simp only [geodesicSlope, hEnd, hwCrit, inner_zero_right]
  rw [hEndSlope] at H
  have hneg : 0 < κ / 2 * (n + 1 : ℕ) * Real.arccos (overlap u w) := by positivity
  nlinarith

private theorem mem_component_of_mem_closure {E : Type*} [TopologicalSpace E]
    {U : Set E} {w u : E} (hw : w ∈ U) (hu : u ∈ U)
    (hcl : u ∈ closure (connectedComponentIn U w)) :
    u ∈ connectedComponentIn U w := by
  rw [connectedComponentIn_eq_image hw] at hcl ⊢
  have hucomp := (Topology.IsInducing.subtypeVal.isClosed_iff'.mp
    (isClosed_connectedComponent (x := (⟨w, hw⟩ : U)))) (⟨u, hu⟩ : U) hcl
  exact ⟨⟨u, hu⟩, hucomp, rfl⟩

private theorem component_curve_localMax {E : Type*} [TopologicalSpace E]
    (f : E → ℝ) (U : Set E) (u : E)
    (hmax : IsMaxOn f (connectedComponentIn U u) u)
    (γ : ℝ → E) (hγ : Continuous γ) (hγ0 : γ 0 = u)
    (hγU : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ U) :
    IsLocalMax (fun t => f (γ t)) 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hγU
  have hballpre : IsPreconnected (Metric.ball (0 : ℝ) ε) := by
    rw [Real.ball_eq_Ioo]
    exact isPreconnected_Ioo
  have hpre : IsPreconnected (γ '' Metric.ball (0 : ℝ) ε) :=
    hballpre.image γ hγ.continuousOn
  have huim : u ∈ γ '' Metric.ball (0 : ℝ) ε := by
    rw [← hγ0]
    exact mem_image_of_mem γ (Metric.mem_ball_self hε)
  have hsub : γ '' Metric.ball (0 : ℝ) ε ⊆ connectedComponentIn U u :=
    hpre.subset_connectedComponentIn huim (by
      rintro x ⟨t, ht, rfl⟩
      exact hball ht)
  change ∀ᶠ t in 𝓝 (0 : ℝ), f (γ t) ≤ f (γ 0)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hε] with t ht
  rw [hγ0]
  exact hmax (hsub (mem_image_of_mem γ ht))

private theorem component_maximum_critical {N : ℕ} (hN : 0 < N)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 3 f) (a : ℝ)
    (u : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ)) (hhigh : a < f u)
    (hmax : IsMaxOn f
      (connectedComponentIn {x : Vector N | ‖x‖ ^ 2 = (N : ℝ) ∧ a < f x} u) u) :
    surfaceGradient f u = 0 := by
  have hu' : OnSphere u := by
    simpa only [OnSphere, real_inner_self_eq_norm_sq] using hu
  have hdir (v : Vector N) (hv : inner ℝ u v = 0) : fderiv ℝ f u v = 0 := by
    let A := tangentRotation u v
    have hA : star A = -A := tangentRotation_skew u v
    have hAu : A u = v := tangentRotation_apply hN.ne' u v hu' hv
    have hcurve := operatorFlow_apply_hasDerivAt A 0 u
    have hcont : Continuous (fun t : ℝ => operatorFlow A t u) :=
      (operatorFlow_continuous A).clm_apply continuous_const
    have hcomp := (hf.differentiable (by simp) u).hasFDerivAt.comp_hasDerivAt_of_eq
      0 hcurve
        (show u = operatorFlow A 0 u from (operatorFlow_zero A u).symm)
    have hγU : ∀ᶠ t in 𝓝 (0 : ℝ),
        ‖operatorFlow A t u‖ ^ 2 = (N : ℝ) ∧ a < f (operatorFlow A t u) := by
      have hh : ∀ᶠ t in 𝓝 (0 : ℝ), a < f (operatorFlow A t u) :=
        (isOpen_lt continuous_const (hf.continuous.comp hcont)).mem_nhds
          (by simpa only [mem_ofPred_eq, Function.comp_apply, operatorFlow_zero] using hhigh)
      filter_upwards [hh] with t ht
      exact ⟨by rw [operatorFlow_norm A hA t u]; exact hu, ht⟩
    have hlocal := component_curve_localMax f _ u hmax
      (fun t => operatorFlow A t u) hcont (operatorFlow_zero A u) hγU
    simpa only [Function.comp_def, operatorFlow_zero, hAu] using
      hlocal.hasDerivAt_eq_zero hcomp
  apply ext_inner_right ℝ
  intro v
  rw [inner_surfaceGradient, inner_zero_left]
  apply hdir
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp
    (tangentProjection_mem hN.ne' u v hu')

private theorem component_has_critical_maximum {N : ℕ} (hN : 0 < N)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 3 f) (a : ℝ)
    (w : Vector N) (hw : ‖w‖ ^ 2 = (N : ℝ)) (hhigh : a < f w) :
    ∃ u ∈ connectedComponentIn
      {x : Vector N | ‖x‖ ^ 2 = (N : ℝ) ∧ a < f x} w,
      surfaceGradient f u = 0 ∧
      ∀ z ∈ connectedComponentIn
        {x : Vector N | ‖x‖ ^ 2 = (N : ℝ) ∧ a < f x} w,
        f z ≤ f u := by
  let U := {x : Vector N | ‖x‖ ^ 2 = (N : ℝ) ∧ a < f x}
  let V := connectedComponentIn U w
  have hwU : w ∈ U := ⟨hw, hhigh⟩
  have hwV : w ∈ V := mem_connectedComponentIn hwU
  have hclS : closure V ⊆ {x : Vector N | ‖x‖ ^ 2 = (N : ℝ)} :=
    closure_minimal (fun x hx => (connectedComponentIn_subset U w hx).1)
      (sourceSphere_compact N).isClosed
  have hcompact : IsCompact (closure V) :=
    (sourceSphere_compact N).of_isClosed_subset isClosed_closure hclS
  obtain ⟨u, hucl, hmax⟩ := hcompact.exists_isMaxOn
    ⟨w, subset_closure hwV⟩ hf.continuous.continuousOn
  have huU : u ∈ U := ⟨hclS hucl, hhigh.trans_le (hmax (subset_closure hwV))⟩
  have huV : u ∈ V := mem_component_of_mem_closure hwU huU hucl
  have hmaxV : IsMaxOn f V u := fun z hz => hmax (subset_closure hz)
  have hcrit : surfaceGradient f u = 0 := by
    apply component_maximum_critical hN f hf a u huU.1 huU.2
    rwa [← connectedComponentIn_eq huV]
  exact ⟨u, huV, hcrit, hmaxV⟩

private theorem short_ball_quadratic_drop {N : ℕ}
    (hN : 0 < N) (f : Vector N → ℝ) (hf : ContDiff ℝ 3 f)
    {C κ ρ : ℝ} (hC : 0 ≤ C) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρκ : 2 * C * ρ ≤ κ)
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sphereThirdExtension f x‖ ≤ C / Real.sqrt (N : ℝ))
    (u w : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ)) (hw : ‖w‖ ^ 2 = (N : ℝ))
    (hCrit : surfaceGradient f u = 0)
    (hMargin : intrinsicHessianMargin f κ u)
    (hDist : sphereGeodesicDist u w ≤ ρ * Real.sqrt (N : ℝ)) :
    f w ≤ f u - κ / 4 * (sphereGeodesicDist u w) ^ 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  by_cases heq : w = u
  · subst w
    simp [sphereGeodesicDist, overlap_self (by omega) u hu]
  have hNpos : 0 < n + 1 := by omega
  have hsqrt : 0 < Real.sqrt (n + 1 : ℕ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hNpos)
  have hr := overlap_mem_Icc_of_norm_sq hNpos u w hu hw
  have hrlt : overlap u w < 1 := lt_of_le_of_ne hr.2 (by
    intro he
    exact heq (source_sphere_eq_of_overlap_one hNpos u w hu hw he).symm)
  have hθpos : 0 < Real.arccos (overlap u w) := Real.arccos_pos.mpr hrlt
  have hθle : Real.arccos (overlap u w) ≤ ρ := by
    apply (mul_le_mul_iff_right₀ hsqrt).mp
    simpa only [sphereGeodesicDist, mul_comm] using hDist
  have hθone := hθle.trans hρ1
  have hrpos : 0 < overlap u w := by
    rw [← Real.cos_arccos hr.1 hr.2]
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_gt_three]
  obtain ⟨v, hv, huv, hEnd⟩ := sourceSphereGeodesic_reconstruction u w hu hw ⟨hrpos, hrlt⟩
  have H := geodesic_quadratic_drop hN f hf hC hκ hρ hρ1 hρκ hThird
    u v hu hv huv hCrit hMargin (Real.arccos (overlap u w)) ⟨hθpos.le, hθle⟩
  rw [hEnd] at H
  convert H using 1
  unfold sphereGeodesicDist
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

/-- Source `lem:pc-superlevel`: every strict high-energy component has a
unique critical maximizer and lies within both the curvature radius and
the radius determined by its energy deficit. -/
theorem superlevel_component_localization {N : ℕ}
    (f : Vector N → ℝ) (hf : ContDiff ℝ 3 f)
    {C₃ κ δ₀ δ : ℝ}
    (hC₃ : 0 ≤ C₃) (hκ : 0 < κ) (hδ₀ : 0 < δ₀) (hδ : 0 < δ)
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sphereThirdExtension f x‖ ≤ C₃ / Real.sqrt (N : ℝ)) :
    let S := {x : Vector N | ‖x‖ ^ 2 = (N : ℝ)}
    let M := sSup (f '' S)
    let r₀ := localizationRadius κ C₃
    (∀ u ∈ S, surfaceGradient f u = 0 →
      M - δ₀ * (N : ℝ) < f u → intrinsicHessianMargin f κ u) →
    δ < min δ₀ (κ * r₀ ^ 2 / 4) →
    ∀ w ∈ S, M - δ * (N : ℝ) < f w →
      let V := connectedComponentIn
        {x : Vector N | x ∈ S ∧ M - δ * (N : ℝ) < f x} w
      ∃ u ∈ V,
        surfaceGradient f u = 0 ∧
        intrinsicHessianMargin f κ u ∧
        (∀ z ∈ V, f z ≤ f u) ∧
        (∀ z ∈ V, surfaceGradient f z = 0 → z = u) ∧
        (∀ z ∈ V,
          sphereGeodesicDist u z < r₀ * Real.sqrt (N : ℝ) ∧
          sphereGeodesicDist u z <
            2 * Real.sqrt (δ / κ) * Real.sqrt (N : ℝ)) := by
  intro S M r₀ hMargins hsmall w hw hhigh
  let V := connectedComponentIn {x : Vector N | x ∈ S ∧ M - δ * (N : ℝ) < f x} w
  have hN : 0 < N := by
    by_contra hn
    have hzero : N = 0 := by omega
    subst N
    have hS : S = {w} := by
      ext z
      constructor
      · intro _
        exact Subsingleton.elim _ _
      · rintro rfl
        exact hw
    have hM : M = f w := by
      simp only [M, hS, Set.image_singleton, csSup_singleton]
    rw [hM] at hhigh
    simp at hhigh
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hsqrt : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNr
  have hρ : 0 < r₀ := by
    by_cases hzero : C₃ = 0
    · simp [r₀, localizationRadius, hzero]
    · have hpos : 0 < C₃ := lt_of_le_of_ne hC₃ (Ne.symm hzero)
      simpa only [r₀, localizationRadius, ite_eq_right hzero] using
        lt_min (by norm_num : (0 : ℝ) < 1) (div_pos hκ (by positivity : 0 < 2 * C₃))
  have hρ1 : r₀ ≤ 1 := by
    by_cases hzero : C₃ = 0
    · simp [r₀, localizationRadius, hzero]
    · simpa only [r₀, localizationRadius, ite_eq_right hzero] using
        min_le_left (1 : ℝ) (κ / (2 * C₃))
  have hρκ : 2 * C₃ * r₀ ≤ κ := by
    by_cases hzero : C₃ = 0
    · simp only [hzero, mul_zero, zero_mul]
      exact hκ.le
    · have hpos : 0 < C₃ := lt_of_le_of_ne hC₃ (Ne.symm hzero)
      have hh : r₀ ≤ κ / (2 * C₃) := by
        simpa only [r₀, localizationRadius, ite_eq_right hzero] using
          min_le_right (1 : ℝ) (κ / (2 * C₃))
      simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 2 * C₃)).mp hh
  have hδδ₀ : δ < δ₀ := hsmall.trans_le (min_le_left _ _)
  have hδρ : δ < κ * r₀ ^ 2 / 4 := hsmall.trans_le (min_le_right _ _)
  have hVsub : V ⊆ {x : Vector N | x ∈ S ∧ M - δ * (N : ℝ) < f x} :=
    connectedComponentIn_subset _ _
  obtain ⟨u, huV, hcrit, hmax⟩ := component_has_critical_maximum hN f hf
    (M - δ * (N : ℝ)) w hw hhigh
  have huS : u ∈ S := (hVsub huV).1
  have hMargin : intrinsicHessianMargin f κ u := hMargins u huS hcrit (by
    have hh := (hVsub huV).2
    have hd := mul_lt_mul_of_pos_right hδδ₀ hNr
    have hδ₀N := mul_pos hδ₀ hNr
    linarith [hδ₀N])
  have huM : f u ≤ M := le_csSup
    ((sourceSphere_compact N).image hf.continuous).bddAbove ⟨u, huS, rfl⟩
  have hdist : Continuous (sphereGeodesicDist u) := by
    unfold sphereGeodesicDist overlap
    fun_prop
  have hdist0 : sphereGeodesicDist u u = 0 := by
    simp [sphereGeodesicDist, overlap_self (by omega) u huS]
  have hball : ∀ z ∈ V, sphereGeodesicDist u z < r₀ * Real.sqrt (N : ℝ) := by
    intro z hz
    by_contra hh
    have hge : r₀ * Real.sqrt (N : ℝ) ≤ sphereGeodesicDist u z := le_of_not_gt hh
    obtain ⟨y, hy, hdy⟩ := isPreconnected_connectedComponentIn.intermediate_value
      huV hz hdist.continuousOn (show r₀ * Real.sqrt (N : ℝ) ∈
        Icc (sphereGeodesicDist u u) (sphereGeodesicDist u z) from
          ⟨by rw [hdist0]; positivity, hge⟩)
    have hdrop := short_ball_quadratic_drop hN f hf hC₃ hκ hρ hρ1 hρκ hThird
      u y huS (hVsub hy).1 hcrit hMargin hdy.le
    rw [hdy, mul_pow, Real.sq_sqrt hNr.le] at hdrop
    have hhhigh := (hVsub hy).2
    have hd := mul_lt_mul_of_pos_right hδρ hNr
    change f y ≤ f u - κ / 4 * (r₀ ^ 2 * (N : ℝ)) at hdrop
    nlinarith
  refine ⟨u, huV, hcrit, hMargin, hmax, ?_, ?_⟩
  · intro z hz hzcrit
    exact short_ball_critical_unique hN f hf hC₃ hκ hρ hρ1 hρκ hThird
      u z huS (hVsub hz).1 hcrit hMargin hzcrit (hball z hz).le
  · intro z hz
    refine ⟨hball z hz, ?_⟩
    have hdrop := short_ball_quadratic_drop hN f hf hC₃ hκ hρ hρ1 hρκ hThird
      u z huS (hVsub hz).1 hcrit hMargin (hball z hz).le
    have hhhigh := (hVsub hz).2
    have hsq : (sphereGeodesicDist u z) ^ 2 < 4 * (δ / κ) * (N : ℝ) := by
      apply (mul_lt_mul_iff_of_pos_right hκ).mp
      have heq : (4 * (δ / κ) * (N : ℝ)) * κ = 4 * δ * (N : ℝ) := by
        field_simp
      rw [heq]
      change f z ≤ f u - κ / 4 * (sphereGeodesicDist u z) ^ 2 at hdrop
      nlinarith
    have hrad : 0 < 2 * Real.sqrt (δ / κ) * Real.sqrt (N : ℝ) := by positivity
    have hradsq : (2 * Real.sqrt (δ / κ) * Real.sqrt (N : ℝ)) ^ 2 =
        4 * (δ / κ) * (N : ℝ) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hNr.le, Real.sq_sqrt (div_pos hδ hκ).le]
      norm_num
    rw [← hradsq] at hsq
    nlinarith [sq_nonneg (sphereGeodesicDist u z -
      2 * Real.sqrt (δ / κ) * Real.sqrt (N : ℝ))]

end SlowEquilibration.SphericalSuperlevelLocalizationGeneric
