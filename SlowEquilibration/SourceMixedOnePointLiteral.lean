-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalSuperlevelLocalizationGeneric
public import SlowEquilibration.MixedAllHighComplete
public import SlowEquilibration.SphericalMarkedNegativeComplexityCounts
public import SlowEquilibration.SphericalLocalMaxPhysicalIntensity
public import SlowEquilibration.SphericalMaximumAllConclusions
public import SlowEquilibration.SphericalMaximumEnergyDifferential

/-! Literal one-point inputs from manuscript Section 10: intrinsic regularity,
the exact closed critical collar, the full all-high event, and raw marked counts.
All Gaussian and Kac--Rice inputs are the repository's actual disorder laws. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceMixedOnePointLiteral
open MeasureTheory ProbabilityTheory Set Filter Function
open SphericalModel SphericalGaussianJet SphericalForm SphericalMarkedWindows SphericalSequentialRegression
open SphereChartVolume
open GaussianNormConcentration GaussianCompactMaximum SphericalAging.GaussianLandscape
open SphericalAging.FiniteModel (TensorIndex)
open PureTensorJetBounds WholeFieldRegression GaussianRegression IntrinsicHessianLaw
open NormalizedPairObservations PairObservationTargets NormalizedObservationCoercivity GaussianObservationCoercivity
open SphereHessian SphericalCriticalGeodesicDecay SphericalTAPCertificate TwoAtomStationarity
open PairConditionalDeterminantMoments SphericalSuperlevelLocalizationGeneric
open SphericalAging.HardSphereDynamics SphericalAging.SphericalIntegrationByParts
open scoped Topology ENNReal RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000

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


/-- Manuscript `lem:mo-geodesic`, for an arbitrary C³ ambient representative
of a smooth sphere function. The exact π/4 overlap collar includes its boundary. -/
theorem smooth_closed_critical_collar {N : ℕ} (hN : 0 < N)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 3 f) {κ C₃ : ℝ}
    (hκ : 0 < κ) (hC₃ : 0 < C₃)
    (hThird : ∀ w : Vector N, ‖w‖^2 = (N : ℝ) →
      ‖sphereThirdExtension f w‖ ≤ C₃ / Real.sqrt (N : ℝ))
    (u : Vector N) (hu : ‖u‖^2 = (N : ℝ))
    (hCrit : surfaceGradient f u = 0) (hMargin : intrinsicHessianMargin f κ u) :
    ∀ v : Vector N, ‖v‖^2 = (N : ℝ) → surfaceGradient f v = 0 →
      Real.cos (min (Real.pi/4) (κ/(2*C₃))) ≤ overlap u v → v = u := by
  intro v hv hvc hOverlap
  let ρ := min (Real.pi/4) (κ/(2*C₃))
  have hρ : 0 < ρ := lt_min (by positivity [Real.pi_pos]) (by positivity)
  have hρ1 : ρ ≤ 1 := (min_le_left _ _).trans (by linarith [Real.pi_lt_four])
  have hρκ : 2*C₃*ρ ≤ κ := by
    have H := mul_le_mul_of_nonneg_left (min_le_right (Real.pi/4) (κ/(2*C₃)))
      (show 0 ≤ 2*C₃ by positivity)
    rwa [mul_div_cancel₀ κ (by positivity : 2*C₃ ≠ 0)] at H
  have hAngle : Real.arccos (overlap u v) ≤ ρ := by
    have H := Real.arccos_le_arccos hOverlap
    rwa [Real.arccos_cos hρ.le (hρ1.trans (by linarith [Real.pi_gt_three]))] at H
  apply short_ball_critical_unique hN f hf hC₃.le hκ hρ hρ1 hρκ hThird
    u v hu hv hCrit hMargin hvc
  simpa only [sphereGeodesicDist, mul_comm] using
    mul_le_mul_of_nonneg_left hAngle (Real.sqrt_nonneg (N:ℝ))

/-- The complete manuscript `prop:mo-all-high`, with base constants fixed
before the smaller radial interval and every positive δ ≤ δ_U. -/
theorem mixed_all_high_literal
    (μ : FiniteMixture) {β x Q L₀ R₀ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hEdge : 2 * Real.sqrt (Q^2 * μ.xi2 Q) < L₀)
    (hL₀ : L₀ < markK μ β Q) (hR₀ : markK μ β Q < R₀) :
    let κ := (L₀ - 2 * Real.sqrt (Q^2 * μ.xi2 Q))/4
    ∃ C_reg : ℝ, 0 < κ ∧ 0 < C_reg ∧
      let η := 1 - Real.cos (min (Real.pi/4) (κ/(2*C_reg)))
      0 < η ∧ η < 1 ∧
      ∀ L R : ℝ, L₀ < L → R < R₀ → L < markK μ β Q → markK μ β Q < R →
        ∃ δ_U : ℝ, 0 < δ_U ∧ δ_U ≤ 1 ∧
          ∀ δ : ℝ, 0 < δ → δ ≤ δ_U →
            ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
              ∃ Ω : ∀ n : ℕ, Set (Disorder (n+2) μ.maxDegree),
                (∀ n, MeasurableSet (Ω n)) ∧
                (∀ n, ∀ J ∈ Ω n,
                  sourceSphereRegularity (centerCoefficients (mixtureCoefficients μ) Q) J ≤ C_reg ∧
                  (∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
                    ‖sourceSphereThirdExtension (centerCoefficients (mixtureCoefficients μ) Q) J u‖ ≤
                      C_reg / Real.sqrt (n+2 : ℕ)) ∧
                  sSup ((fun u : Vector (n+2) =>
                    ‖sourceSphereThirdExtension (centerCoefficients (mixtureCoefficients μ) Q) J u‖) ''
                      {u | ‖u‖^2 = (n+2 : ℕ)}) ≤ C_reg / Real.sqrt (n+2 : ℕ) ∧
                  ∀ u : Vector (n+2), ‖u‖^2 = (n+2 : ℕ) →
                    surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) u = 0 →
                    (n+2 : ℕ)*(markE μ β x Q-δ) ≤
                      field (centerCoefficients (mixtureCoefficients μ) Q) J u →
                    field (centerCoefficients (mixtureCoefficients μ) Q) J u ≤
                        (n+2 : ℕ)*(markE μ β x Q+δ) ∧
                      actualScore (centerCoefficients (mixtureCoefficients μ) Q) J u 1 ∈ Ioo L R ∧
                      sourceHessianMargin (centerCoefficients (mixtureCoefficients μ) Q) κ J u ∧
                      ∀ v : Vector (n+2), ‖v‖^2 = (n+2 : ℕ) →
                        surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) J) v = 0 →
                        v ≠ u → overlap u v < 1-η) ∧
                (∀ n : ℕ, (disorderLaw (n+2) μ.maxDegree).real (Ω n)ᶜ ≤
                  C * Real.exp (-c*(n+2 : ℕ))) :=
  MixedAllHighComplete.mixed_all_high_complete μ h hnp hEdge hL₀ hR₀

private theorem strong_affine_tensor_tail {ι:Type*} [Fintype ι]
    {N p:ℕ} (hN:0<N)
    (T:EuclideanSpace ℝ ι→L[ℝ]EuclideanSpace ℝ (TensorIndex N p)) (hT:‖T‖ ≤ 1)
    (m:EuclideanSpace ℝ (TensorIndex N p)) {K:ℝ} (hm:‖m‖ ≤ K*Real.sqrt N) :
    (SYK.standardGaussianMeasureOnEuclidean ι).real
      {g|(2*((p:ℝ)+1)+2+K)*Real.sqrt N ≤ ‖tensorForm N p (WithLp.ofLp (T g+m))‖} ≤
      Real.exp (-(N:ℝ)):=by
  have ht := centered_lipschitz_upper_tail _ (show (0:ℝ) ≤ 1 by norm_num)
    (sourceProjectedTensorSupremum_lipschitz hN T hT)
    (show 0 ≤ 2*Real.sqrt (N:ℝ) by positivity)
  have ht' : (SYK.standardGaussianMeasureOnEuclidean ι).real
      {x | (∫ y, absoluteSupremum (sourceUnitTensorFeature N p) (T y)
        ∂SYK.standardGaussianMeasureOnEuclidean ι)+2*Real.sqrt N ≤
        absoluteSupremum (sourceUnitTensorFeature N p) (T x)} ≤ Real.exp (-(N:ℝ)) := by
    apply ht.trans
    apply Real.exp_le_exp.mpr
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
  have hb:=sourceProjectedTensorSupremum_mean_bound hN T hT
  refine (measureReal_mono (fun g hg=>?_)).trans ht'
  have hadd:tensorForm N p (WithLp.ofLp (T g+m))=
      tensorForm N p (WithLp.ofLp (T g))+tensorForm N p (WithLp.ofLp m):=by
    unfold tensorForm
    simp only [PiLp.add_apply,add_smul,Finset.sum_add_distrib]
  have hn:‖tensorForm N p (WithLp.ofLp (T g+m))‖ ≤
      absoluteSupremum (sourceUnitTensorFeature N p) (T g)+K*Real.sqrt N:=by
    rw [hadd]
    exact (norm_add_le _ _).trans (add_le_add (source_tensorForm_norm_le_absoluteSupremum hN _)
      ((source_tensorForm_norm_le_coefficient_norm m).trans hm))
  change (2*((p:ℝ)+1)+2+K)*Real.sqrt N ≤ _ at hg
  change (∫ z,absoluteSupremum (sourceUnitTensorFeature N p) (T z)
    ∂SYK.standardGaussianMeasureOnEuclidean ι)+2*Real.sqrt N ≤ _
  nlinarith

private theorem strong_posterior_tensor_tail {N P:ℕ} {F:Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (hN:0<N) (A:EuclideanDisorder N P→L[ℝ]F) (hA:Surjective A)
    (w:F) {K:ℝ} (hm:‖lift A w‖ ≤ K*Real.sqrt N) (p:Degree P) :
    (coefficientKernel A w).real
      {J|(2*((p.val.val:ℝ)+1)+2+K)*Real.sqrt N ≤ ‖tensorForm N p.val.val (J p)‖} ≤
      Real.exp (-(N:ℝ)):=by
  let T:EuclideanDisorder N P→L[ℝ]EuclideanSpace ℝ (SphericalAging.FiniteModel.TensorIndex N p.val.val):=
    (sourceDegreeProjectionCLM p).comp (residual A)
  have hr:‖residual A‖ ≤ 1:=by rw [residual_eq_starProjection A hA];exact A.ker.starProjection_norm_le
  have hT:‖T‖ ≤ 1:=by
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (by nlinarith [sourceDegreeProjectionCLM_norm_le (N:=N) p,norm_nonneg (sourceDegreeProjectionCLM (N:=N) p)])
  let m:=sourceDegreeProjectionCLM p (lift A w)
  have hshift:‖m‖ ≤ K*Real.sqrt N:=by
    exact ((sourceDegreeProjectionCLM p).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_right (sourceDegreeProjectionCLM_norm_le p) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hm))
  have ht:=strong_affine_tensor_tail hN T hT m hshift
  have hB:MeasurableSet {J:SphericalModel.Disorder N P|
      (2*((p.val.val:ℝ)+1)+2+K)*Real.sqrt N ≤ ‖tensorForm N p.val.val (J p)‖}:=
    measurableSet_le measurable_const
      ((tensorForm_continuous N p.val.val).norm.measurable.comp (measurable_pi_apply p))
  rw [sourceCoefficientKernel_affine A w,map_measureReal_apply (by fun_prop) hB]
  convert ht using 1
  congr 1

private theorem strong_ordered_failure {N P:ℕ} {F:Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F]
    (hN:0<N) (A:EuclideanDisorder N P→L[ℝ]F) (hA:Surjective A)
    (w:F) {K:ℝ} (hm:‖lift A w‖ ≤ K*Real.sqrt N) :
    (coefficientKernel A w).real (sourcePosteriorOrderedRegularity (N:=N) (P:=P) (K+1))ᶜ ≤
      (Fintype.card (Degree P):ℝ)*Real.exp (-(N:ℝ)):=by
  classical
  have hsub:(sourcePosteriorOrderedRegularity (N:=N) (P:=P) (K+1))ᶜ ⊆
      ⋃ p:Degree P,{J:SphericalModel.Disorder N P|
        (2*((p.val.val:ℝ)+1)+2+K)*Real.sqrt N ≤ ‖tensorForm N p.val.val (J p)‖}:=by
    intro J hJ
    change ¬∀ p:Degree P,_ at hJ
    obtain ⟨p,hp⟩:=not_forall.mp hJ
    apply Set.mem_iUnion.mpr
    refine ⟨p,?_⟩
    change ¬landscapeNorm N p.val.val (J p) ≤ _ at hp
    have hh := ((le_div_iff₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN))).mp (le_of_lt (lt_of_not_ge hp)))
    change (2*((p.val.val:ℝ)+1)+2+K)*Real.sqrt N ≤ _
    convert hh using 1
    ring
  refine (measureReal_mono hsub).trans ?_
  calc
    _ ≤ ∑ p:Degree P,(coefficientKernel A w).real
      {J|(2*((p.val.val:ℝ)+1)+2+K)*Real.sqrt N ≤ ‖tensorForm N p.val.val (J p)‖}:=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _p:Degree P,Real.exp (-(N:ℝ)):=
      Finset.sum_le_sum (fun p _=>strong_posterior_tensor_tail hN A hA w hm p)
    _ = _:=by simp


/-- Manuscript `lem:mo-regularity`, with the full covariant D_N norm and
its literal e^{-N} tail, uniformly in the dimension, center, and compact marks. -/
theorem mixed_posterior_regularity_literal (μ : FiniteMixture) {Q M : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ u : Vector (n+1), ∀ hu : ‖u‖^2 = (n+1 : ℕ),
      ∀ e k : ℝ, |e| ≤ M → |k| ≤ M →
        let c := centerCoefficients (mixtureCoefficients μ) Q
        (mixedConditionedLaw c u hu (scorePairEquiv (e,k))).real
          {J | C < sourceSphereRegularity c J} ≤ C*Real.exp (-(n+1 : ℕ)) := by
  obtain ⟨K,hK,hmean⟩ := source_mixed_one_point_coefficient_mean_bound μ hQ hnp hM
  obtain ⟨a,ha,hcoerc⟩ := uniform_mixed_coercivity μ hQ hnp
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let C := 13*sourcePosteriorDerivativeConstant c (K+1)+(Fintype.card (Degree μ.maxDegree):ℝ)
  have hK' : 0 ≤ K+1 := by linarith
  have hC : 0 < C := by
    have H := sourcePosteriorDerivativeConstant_pos c hK'
    dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro n u hu e k he hk
  dsimp only
  rw [scorePairEquiv_apply, source_mixed_physical_one_point_posterior_grouping n μ hQ hnp u hu e k]
  let A := singleMixedObservation c u (tangentFrame u hu)
  have hA : Surjective A := observation_surjective _ ha
    (hcoerc (n+1) n (by omega) u hu _ (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu))
  have H := strong_ordered_failure (by omega) A hA _
    (hmean (n+1) n (by omega) u hu _ (tangentFrame_orthonormal u hu)
      (tangentFrame_tangent u hu) e k he hk)
  have hsub : {J : Disorder (n+1) μ.maxDegree | C < sourceSphereRegularity c J} ⊆
      (sourcePosteriorOrderedRegularity (N:=n+1) (P:=μ.maxDegree) (K+1))ᶜ := by
    intro J hbad hgood
    have H := source_ordered_sphere_regularity_bound (by omega) c hK' J hgood
    have hCard : (0:ℝ) ≤ Fintype.card (Degree μ.maxDegree) := Nat.cast_nonneg _
    dsimp [C] at hbad
    linarith
  apply ((measureReal_mono hsub).trans H).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have H := sourcePosteriorDerivativeConstant_pos c hK'
  dsimp [C]
  linarith

/-- Proper value-only conditioning, including every positive-amplitude pure
mixture, has the same full covariant regularity estimate. -/
theorem value_posterior_regularity_literal (μ : FiniteMixture) {Q M : ℝ}
    (hQ : 0 < Q) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ u : Vector (n+1), ∀ hu : ‖u‖^2 = (n+1 : ℕ),
      ∀ e : ℝ, |e| ≤ M →
        let c := centerCoefficients (mixtureCoefficients μ) Q
        (valueConditionedLaw c u hu e).real
          {J | C < sourceSphereRegularity c J} ≤ C*Real.exp (-(n+1 : ℕ)) := by
  obtain ⟨K,hK,hmean⟩ := source_value_one_point_coefficient_mean_bound μ hQ hM
  obtain ⟨a,ha,hcoerc⟩ := uniform_value_coercivity μ hQ
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let C := 13*sourcePosteriorDerivativeConstant c (K+1)+(Fintype.card (Degree μ.maxDegree):ℝ)
  have hK' : 0 ≤ K+1 := by linarith
  have hC : 0 < C := by
    have H := sourcePosteriorDerivativeConstant_pos c hK'
    dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro n u hu e he
  dsimp only
  rw [source_value_physical_one_point_posterior_grouping n μ hQ u hu e]
  let A := singleValueObservation c u (tangentFrame u hu)
  have hA : Surjective A := observation_surjective _ ha
    (hcoerc (n+1) n (by omega) u hu _ (tangentFrame_orthonormal u hu) (tangentFrame_tangent u hu))
  have H := strong_ordered_failure (by omega) A hA _
    (hmean (n+1) n (by omega) u hu _ (tangentFrame_orthonormal u hu)
      (tangentFrame_tangent u hu) e he)
  have hsub : {J : Disorder (n+1) μ.maxDegree | C < sourceSphereRegularity c J} ⊆
      (sourcePosteriorOrderedRegularity (N:=n+1) (P:=μ.maxDegree) (K+1))ᶜ := by
    intro J hbad hgood
    have H := source_ordered_sphere_regularity_bound (by omega) c hK' J hgood
    have hCard : (0:ℝ) ≤ Fintype.card (Degree μ.maxDegree) := Nat.cast_nonneg _
    dsimp [C] at hbad
    linarith
  apply ((measureReal_mono hsub).trans H).trans
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  have H := sourcePosteriorDerivativeConstant_pos c hK'
  dsimp [C]
  linarith

private theorem original_full_regularity (μ : FiniteMixture) (Q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ J : Disorder (n+2) μ.maxDegree,
      J ∈ regularDisorder →
        sourceSphereRegularity (centerCoefficients (mixtureCoefficients μ) Q) J ≤ C := by
  let K := ∑ q : Degree μ.maxDegree, blockThreshold q
  have hK : 0 ≤ K := Finset.sum_nonneg (fun q _ => (blockThreshold_pos q).le)
  refine ⟨13 * sourcePosteriorDerivativeConstant
    (centerCoefficients (mixtureCoefficients μ) Q) K,
    mul_pos (by norm_num) (sourcePosteriorDerivativeConstant_pos _ hK), ?_⟩
  intro n J hJ
  have hOrdered : J ∈ sourcePosteriorOrderedRegularity K := by
    intro q
    have hq : blockThreshold q ≤ K :=
      Finset.single_le_sum (fun r _ => (blockThreshold_pos r).le) (Finset.mem_univ q)
    have hq0 : 0 ≤ (q.val.val : ℝ) := Nat.cast_nonneg _
    exact (hJ q).trans (by linarith)
  exact source_ordered_sphere_regularity_bound (by omega) _ hK J hOrdered

/-- Original disorder clause of `lem:mo-regularity`, in every N ≥ 2. -/
theorem original_regularity_literal (μ : FiniteMixture) (Q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (disorderLaw (n+2) μ.maxDegree).real
        {J | C < sourceSphereRegularity (centerCoefficients (mixtureCoefficients μ) Q) J} ≤
          C*Real.exp (-(n+2 : ℕ)) := by
  obtain ⟨C,hC,hgood⟩ := original_full_regularity μ Q
  refine ⟨max C 1,lt_of_lt_of_le hC (le_max_left _ _),?_⟩
  intro n
  have hsub : {J | max C 1 < sourceSphereRegularity (centerCoefficients (mixtureCoefficients μ) Q) J} ⊆
      (regularDisorder (N:=n+2) (P:=μ.maxDegree))ᶜ := by
    intro J hbad hJ
    exact not_lt_of_ge ((hgood n J hJ).trans (le_max_left _ _)) hbad
  exact ((measureReal_mono hsub).trans (regularDisorder_failure_probability (by omega))).trans
    (le_mul_of_one_le_left (Real.exp_pos _).le (le_max_right _ _))



/-- The deliberately loose bound `lem:mo-intensity-bounds(d)` is uniform
in every δ' ≥ 0, with the printed N exp(c₀ δ' N) scale. -/
theorem coarse_count_literal (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ δ' : ℝ, 0 ≤ δ' →
      sourceMarkedOriginalCountMass n μ Q
        (rectangularScoreWindow (Ici (markE μ β x Q-δ')) (Ioo L R)) ≤
          ENNReal.ofReal (C*(n+2 : ℕ)*Real.exp ((β*x)*δ'*(n+2 : ℕ))) := by
  let κ := sourceMarkedLeastCurvature μ Q
  have hκ : 0 < κ := sourceMarkedLeastCurvature_pos μ h.overlap_range.1
    (by have hd := h.min_degree; omega) hnp
  have hg : 0 < L-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [sourceRadialEdge] using sub_pos.mpr hL
  obtain ⟨a,B,_ha,hB,hbound⟩ := actual_mixed_intensity_prefactors μ h.overlap_range.1 hnp
    (g:=L-2*Real.sqrt (Q^2*μ.xi2 Q)) (Z:=R) hg
  refine ⟨B*(Real.pi/(κ/2)),by positivity,?_⟩
  intro n δ' _hδ'
  let S := scorePairEquiv ⁻¹' rectangularScoreWindow (Ici (markE μ β x Q-δ')) (Ioo L R)
  let F := fun z : ℝ×ℝ => ENNReal.ofReal (StrongFieldComplexity.gaussianPlane (κ/2)
    (z+(-markE μ β x Q,-markK μ β Q)))
  have hF : Measurable F := by unfold F StrongFieldComplexity.gaussianPlane; fun_prop
  have hIntegral : (∫⁻ z, F z ∂StrongFieldComplexity.planeVolume) =
      ENNReal.ofReal (Real.pi/(κ/2)) := by
    have H := (measurePreserving_add_right (volume : Measure (ℝ×ℝ))
      (-markE μ β x Q,-markK μ β Q)).lintegral_comp_emb
        (Homeomorph.addRight (-markE μ β x Q,-markK μ β Q)).measurableEmbedding
        (fun z => ENNReal.ofReal (StrongFieldComplexity.gaussianPlane (κ/2) z))
    change (∫⁻ z, F z ∂StrongFieldComplexity.planeVolume) = _ at H
    rw [H]
    change (∫⁻ z, ENNReal.ofReal (StrongFieldComplexity.gaussianPlane (κ/2) z)
      ∂StrongFieldComplexity.planeVolume) = _
    rw [←ofReal_integral_eq_lintegral_ofReal
      (StrongFieldComplexity.gaussianPlane_integrable (by positivity : 0 < κ/2))
      (ae_of_all _ (fun _ => (Real.exp_pos _).le)),
      StrongFieldComplexity.integral_gaussianPlane (by positivity : 0 < κ/2)]
  rw [sourceMarkedOriginalCountMass_eq_plane_integral n μ h.overlap_range.1 hnp _
    (rectangularScoreWindow_measurable _ _ measurableSet_Ici measurableSet_Ioo)]
  have hp : ∀ z ∈ S, mixedCriticalIntensity n μ Q (scorePairEquiv z) ≤
      ENNReal.ofReal (B*(n+2 : ℕ)*Real.exp ((β*x)*δ'*(n+2 : ℕ)))*F z := by
    intro z hz
    have hk : (scorePairEquiv z) 1 ∈ Icc
        (2*Real.sqrt (Q^2*μ.xi2 Q)+(L-2*Real.sqrt (Q^2*μ.xi2 Q))) R := by
      constructor <;> linarith [hz.2.1,hz.2.2]
    apply (hbound n (scorePairEquiv z) hk).2.trans
    rw [←ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hβx := mul_pos h.beta_pos h.weight_range.1
    have hloss := sourceMarkedComplexity_global_loss μ h hnp z.1 z.2
    have he : markE μ β x Q-δ' ≤ z.1 := hz.1
    have hpen : 0 ≤ κ/2*((z.1-markE μ β x Q)^2+(z.2-markK μ β Q)^2) := by positivity
    have hN : (1:ℝ) ≤ (n+2 : ℕ) := by norm_cast; omega
    have hlin : -(β*x)*(z.1-markE μ β x Q) ≤ (β*x)*δ' := by
      nlinarith [mul_le_mul_of_nonneg_left he hβx.le]
    have hrate : (n+2 : ℕ)*sourceRadialProfile μ Q z.1 z.2 ≤
        (β*x)*δ'*(n+2 : ℕ)-κ/2*((z.1-markE μ β x Q)^2+(z.2-markK μ β Q)^2) := by
      have H := mul_le_mul_of_nonneg_left hloss (show (0:ℝ) ≤ (n+2 : ℕ) by positivity)
      have H' := mul_le_mul_of_nonneg_left hlin (show (0:ℝ) ≤ (n+2 : ℕ) by positivity)
      have H'' := mul_le_mul_of_nonneg_right hN hpen
      dsimp [κ] at hpen H'' ⊢
      nlinarith
    dsimp [F,StrongFieldComplexity.gaussianPlane,ENNReal.toReal_ofReal]
    rw [mul_assoc (B*(n+2:ℕ)), ←Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    simpa only [sourceRadialProfile, Prod.mk.eta, sub_eq_add_neg, neg_mul] using hrate
  calc
    _ ≤ ∫⁻ z in S, ENNReal.ofReal (B*(n+2 : ℕ)*Real.exp ((β*x)*δ'*(n+2 : ℕ)))*F z
        ∂StrongFieldComplexity.planeVolume := setLIntegral_mono (measurable_const.mul hF) hp
    _ ≤ ∫⁻ z, ENNReal.ofReal (B*(n+2 : ℕ)*Real.exp ((β*x)*δ'*(n+2 : ℕ)))*F z
        ∂StrongFieldComplexity.planeVolume := by
      simpa only [Measure.restrict_univ] using
        (lintegral_mono_set (μ:=StrongFieldComplexity.planeVolume)
          (f:=fun z => ENNReal.ofReal (B*(n+2:ℕ)*Real.exp ((β*x)*δ'*(n+2:ℕ)))*F z)
          (subset_univ S))
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,hIntegral,
        ←ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring


/-- The manuscript constant: surface area times the zero-gradient density,
divided by 2π sqrt(det Σ_Q). Its argument n corresponds to N = n+2. -/
def mathfrakC (n : ℕ) (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  (sphereKRPrefactor (n+1) μ Q).toReal / sourceScoreDenominator μ Q

/-- Identifies mathfrak c_N with exactly the printed physical prefactor. -/
theorem mathfrakC_eq (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) :
    mathfrakC n μ Q =
      (manuscriptRoundVolume (n+1) univ).toReal *
        (2*Real.pi*(Q*μ.xi1 Q))^(-((n+1:ℕ):ℝ)/2) /
          (2*Real.pi*Real.sqrt (μ.scoreCovariance Q).det) := by
  rw [mathfrakC,sphereKRPrefactor_physical (n+1) μ hQ,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (mul_pos hQ (μ.xi1_pos hQ)).le) _)]
  rfl

private def rawEnergyEquiv (a : ℝ) (ha : 0 < a) : (ℝ×ℝ) ≃ᵐ (ℝ×ℝ) :=
  (Homeomorph.prodCongr (Homeomorph.mulLeft₀ a ha.ne') (Homeomorph.refl ℝ)).toMeasurableEquiv

private theorem raw_energy_change (a : ℝ) (ha : 0 < a) (A : Set (ℝ×ℝ))
    (f : ℝ×ℝ → ℝ≥0∞) :
    (∫⁻ z in rawEnergyEquiv a ha ⁻¹' A, f z ∂StrongFieldComplexity.planeVolume) =
      ∫⁻ z in A, ENNReal.ofReal a⁻¹*f (z.1/a,z.2) ∂StrongFieldComplexity.planeVolume := by
  have hp : MeasurePreserving (fun t : ℝ => a*t) volume (ENNReal.ofReal a⁻¹ • volume) :=
    ⟨measurable_const_mul a,by simpa only [abs_of_pos (inv_pos.mpr ha)] using Real.map_volume_mul_left ha.ne'⟩
  have hprod := hp.prod (MeasurePreserving.id (volume : Measure ℝ))
  rw [Measure.prod_smul_left] at hprod
  have H := hprod.setLIntegral_comp_preimage_emb (rawEnergyEquiv a ha).measurableEmbedding
    (fun z => f (z.1/a,z.2)) A
  change (∫⁻ z in rawEnergyEquiv a ha ⁻¹' A, f (a*z.1/a,z.2)
    ∂StrongFieldComplexity.planeVolume) = _ at H
  simp only [mul_div_cancel_left₀ _ ha.ne'] at H
  rw [Measure.restrict_smul,lintegral_smul_measure] at H
  exact H.trans (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

/-- Arbitrary Borel raw-energy/radial marks and arbitrary nonnegative Borel
whole-disorder weights in `lem:mo-intensity`. The sphere integral is written
first, preserving the original Kac--Rice convention. -/
theorem marked_raw_kacRice (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (A : Set (ℝ×ℝ)) (hA : MeasurableSet A)
    (ψ : Disorder (n+2) μ.maxDegree → Vector (n+2) → ℝ≥0∞)
    (hψ : Measurable (fun p : Disorder (n+2) μ.maxDegree × Vector (n+2) => ψ p.1 p.2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    let K := {b : EuclideanSpace ℝ (Fin 2) | ((n+2:ℕ)*b 0,b 1) ∈ A}
    AEMeasurable (actualScoreWindowCount (n+1) c K ψ) (disorderLaw (n+2) μ.maxDegree) ∧
      (∫⁻ J, actualScoreWindowCount (n+1) c K ψ J ∂disorderLaw (n+2) μ.maxDegree) =
        ∫⁻ u, if hu : ‖u‖^2 = (n+2:ℕ) then
          ∫⁻ z in A, ENNReal.ofReal (mathfrakC n μ Q *
            Real.exp (-(n+2:ℕ)/2*scoreQuadratic μ Q (scorePairEquiv (z.1/(n+2:ℕ),z.2)))) *
              (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det| * ψ J u
                ∂mixedConditionedLaw c u hu (scorePairEquiv (z.1/(n+2:ℕ),z.2)))
                ∂StrongFieldComplexity.planeVolume
        else 0 ∂sphereLaw (n+2) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  let K := {b : EuclideanSpace ℝ (Fin 2) | ((n+2:ℕ)*b 0,b 1) ∈ A}
  have hK : MeasurableSet K := hA.preimage (by fun_prop)
  obtain ⟨hm,he⟩ := actual_mixed_score_window_kacRice (n+1) (by omega) μ hQ hnp K hK ψ hψ
  refine ⟨hm,he.trans ?_⟩
  rw [←lintegral_const_mul' _ _ (sphereKRPrefactor_ne_top (n+1) μ Q)]
  apply lintegral_congr
  intro u
  by_cases hu : ‖u‖^2 = (n+2:ℕ)
  · simp only [mixedWindowIntensity,dite_eq_left hu]
    rw [←scorePairEquiv_measurePreserving.setLIntegral_comp_preimage_emb
      scorePairEquiv.measurableEmbedding]
    change sphereKRPrefactor (n+1) μ Q *
      (∫⁻ z in rawEnergyEquiv (n+2:ℕ) (by positivity) ⁻¹' A,
        physicalScorePdf (n+2) μ Q (scorePairEquiv z) *
        (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) u).det| * ψ J u
          ∂mixedConditionedLaw c u hu (scorePairEquiv z))
          ∂StrongFieldComplexity.planeVolume) = _
    rw [raw_energy_change (n+2:ℕ) (by positivity) A]
    rw [←lintegral_const_mul' _ _ (sphereKRPrefactor_ne_top (n+1) μ Q)]
    apply lintegral_congr
    intro z
    have hD := sourceScoreDenominator_pos μ hQ hnp
    rw [physicalScorePdf,←ENNReal.ofReal_toReal (sphereKRPrefactor_ne_top (n+1) μ Q)]
    change ENNReal.ofReal ((sphereKRPrefactor (n+1) μ Q).toReal) *
      (ENNReal.ofReal ((n+2:ℕ):ℝ)⁻¹ *
        (ENNReal.ofReal (((n+2:ℕ):ℝ)/sourceScoreDenominator μ Q *
          Real.exp (-(n+2:ℕ)/2*scoreQuadratic μ Q (scorePairEquiv (z.1/(n+2:ℕ),z.2)))) * _)) = _
    rw [←mul_assoc,←ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ←mul_assoc,←ENNReal.ofReal_mul (by positivity)]
    congr 1
    unfold mathfrakC
    field_simp
  · simp only [mixedWindowIntensity,dite_eq_right hu,mul_zero]


/-- The full determinant-weighted energy-Palm functional in
`eq:mo-full-palm`, acting on arbitrary nonnegative whole-field/radial marks. -/
def maximumPalmExpectation (n : ℕ) (μ : FiniteMixture) (Q : ℝ)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) (e : ℝ) (U : Set ℝ)
    (f : Disorder (n+2) μ.maxDegree → ℝ → ℝ≥0∞) : ℝ≥0∞ :=
  (ENNReal.ofReal (sourceRawRadialNormalization n μ Q U e))⁻¹ *
    ∫⁻ k in U, ENNReal.ofReal (Real.exp (-(n+2:ℕ)/2*
      scoreQuadratic μ Q (scorePairEquiv (e,k)))) *
        ∫⁻ J, ENNReal.ofReal |(intrinsicHessian
          (field (centerCoefficients (mixtureCoefficients μ) Q) J) u).det| *
            SphericalPosteriorMaps.negativeHessianMark (n+1)
              (centerCoefficients (mixtureCoefficients μ) Q) J u * f J k
          ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu
            (scorePairEquiv (e,k))

/-- The full energy-Palm functional is normalized to mass one in every
dimension. The denominator is the raw radial integral, with no KR factor. -/
theorem maximumPalmExpectation_one (n : ℕ) (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) (e : ℝ) :
    maximumPalmExpectation n μ Q u hu e (Ioo L R) (fun _ _ => 1) = 1 := by
  have hF := sourcePhysicalRadialFactor_pos n μ h.overlap_range.1 hnp
  have hDensity := sourceMaximumEnergyDensity_pos_all_dimensions n μ h hnp hL hm ((n+2:ℕ)*e)
  rw [sourceMaximumEnergyDensity_eq_raw n μ h.overlap_range.1 hnp] at hDensity
  have hZ : 0 < sourceRawRadialNormalization n μ Q (Ioo L R) e :=
    pos_of_mul_pos_right hDensity hF.le
  have hi := sourceMaximumRadialDensity_integrable_all_dimensions n μ h hnp hL hm ((n+2:ℕ)*e)
  have hiRaw : IntegrableOn (sourceRawRadialWeight n μ Q e) (Ioo L R) := by
    have H := hi.const_mul (sourcePhysicalRadialFactor n μ Q)⁻¹
    change Integrable (sourceRawRadialWeight n μ Q e) (volume.restrict (Ioo L R))
    convert H using 1
    funext k
    change sourceRawRadialWeight n μ Q e k =
      (sourcePhysicalRadialFactor n μ Q)⁻¹*sourceEnergyRadialDensity n μ Q e k
    rw [sourceEnergyRadialDensity_eq_raw n μ h.overlap_range.1 hnp e]
    rw [←mul_assoc,inv_mul_cancel₀ hF.ne',one_mul]
  unfold maximumPalmExpectation
  simp only [mul_one]
  have he : (∫⁻ k in Ioo L R, ENNReal.ofReal (Real.exp (-(n+2:ℕ)/2*
        scoreQuadratic μ Q (scorePairEquiv (e,k)))) *
      ∫⁻ J, ENNReal.ofReal |(intrinsicHessian
        (field (centerCoefficients (mixtureCoefficients μ) Q) J) u).det| *
          SphericalPosteriorMaps.negativeHessianMark (n+1)
            (centerCoefficients (mixtureCoefficients μ) Q) J u
        ∂mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu
          (scorePairEquiv (e,k))) = ENNReal.ofReal (sourceRawRadialNormalization n μ Q (Ioo L R) e) := by
    calc
      _ = ∫⁻ k in Ioo L R, ENNReal.ofReal (sourceRawRadialWeight n μ Q e k) := by
        apply lintegral_congr
        intro k
        rw [mixed_posterior_negative_det_mean n μ h.overlap_range.1 hnp u hu (scorePairEquiv (e,k)),
          ←ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        unfold sourceRawRadialWeight
        congr 2
        ring
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hiRaw
        (ae_of_all _ (fun k => sourceRawRadialWeight_nonneg n μ Q e k))).symm
  rw [he]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hZ) ENNReal.ofReal_ne_top

/-- All four clauses of `lem:mo-intensity-bounds`, on the same arbitrary
exterior radial interval. The coarse bound is uniform in every δ' ≥ 0. -/
theorem intensity_bounds_literal (μ : FiniteMixture) {β x Q L R δ : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (hA3 : δ ≤ sourceMarkedLeastCurvature μ Q*(sourceRadialClearance μ β Q (Ioo L R))^2/(8*(β*x))) :
    (∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ e k : ℝ, k ∈ Icc L R →
      ENNReal.ofReal (c*Real.exp ((n+2:ℕ)*markedComplexity μ Q (scorePairEquiv (e,k)))) ≤
        mixedLocalMaxPhysicalIntensity n μ Q ((n+2:ℕ)*e) k ∧
      mixedLocalMaxPhysicalIntensity n μ Q ((n+2:ℕ)*e) k ≤ mixedCriticalPhysicalIntensity n μ Q ((n+2:ℕ)*e) k ∧
      mixedCriticalPhysicalIntensity n μ Q ((n+2:ℕ)*e) k ≤
        ENNReal.ofReal (C*Real.exp ((n+2:ℕ)*markedComplexity μ Q (scorePairEquiv (e,k))))) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      sourceHighExcludedCountMass n μ Q (markE μ β x Q-δ) (Ioo L R) ≤
        ENNReal.ofReal (Real.exp (-c*(n+2:ℕ)))) ∧
    (∀ t : ℝ, 0 < t → ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      sourceMarkedOriginalCountMass n μ Q (rectangularScoreWindow (Ici (markE μ β x Q+t)) univ) ≤
        ENNReal.ofReal (Real.exp (-c*(n+2:ℕ)))) ∧
    (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ δ' : ℝ, 0 ≤ δ' →
      sourceMarkedOriginalCountMass n μ Q (rectangularScoreWindow (Ici (markE μ β x Q-δ')) (Ioo L R)) ≤
        ENNReal.ofReal (C*(n+2:ℕ)*Real.exp ((β*x)*δ'*(n+2:ℕ)))) := by
  have hg : 0 < L-2*Real.sqrt (Q^2*μ.xi2 Q) := by
    simpa only [sourceRadialEdge] using sub_pos.mpr hL
  obtain ⟨c,C,hc,hC,hpref⟩ := mixed_localMax_physical_prefactors μ h.overlap_range.1 hnp (Z:=R) hg
  refine ⟨⟨c,C,hc,hC,?_⟩, sourceHighExcludedCountMass_exponential μ h hnp hm hA3,
    (fun t ht => sourceAboveContactCountMass_exponential μ h hnp ht), coarse_count_literal μ h hnp hL⟩
  filter_upwards [hpref] with n hn
  intro e k hk
  apply hn e k
  constructor <;> linarith [hk.1,hk.2]


/-- One constant controls original disorder, mixed marks, and the proper
value-only posterior. All dimensions and centers are quantified last. -/
theorem one_point_regularity_literal (μ : FiniteMixture) {Q M : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      (∀ n : ℕ, (disorderLaw (n+2) μ.maxDegree).real
        {J | C < sourceSphereRegularity (centerCoefficients (mixtureCoefficients μ) Q) J} ≤
          C*Real.exp (-(n+2:ℕ))) ∧
      (∀ n : ℕ, ∀ u : Vector (n+2), ∀ hu : ‖u‖^2=(n+2:ℕ),
        ∀ e k : ℝ, |e| ≤ M → |k| ≤ M →
          let c := centerCoefficients (mixtureCoefficients μ) Q
          (mixedConditionedLaw c u hu (scorePairEquiv (e,k))).real
            {J | C < sourceSphereRegularity c J} ≤ C*Real.exp (-(n+2:ℕ))) ∧
      (∀ n : ℕ, ∀ u : Vector (n+2), ∀ hu : ‖u‖^2=(n+2:ℕ),
        ∀ e : ℝ, |e| ≤ M →
          let c := centerCoefficients (mixtureCoefficients μ) Q
          (valueConditionedLaw c u hu e).real
            {J | C < sourceSphereRegularity c J} ≤ C*Real.exp (-(n+2:ℕ))) := by
  obtain ⟨C₀,hC₀,h₀⟩ := original_regularity_literal μ Q
  obtain ⟨C₁,hC₁,h₁⟩ := mixed_posterior_regularity_literal μ hQ hnp hM
  obtain ⟨C₂,hC₂,h₂⟩ := value_posterior_regularity_literal μ hQ hM
  let C := max C₀ (max C₁ C₂)
  have h0 : C₀ ≤ C := le_max_left _ _
  have h1 : C₁ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have h2 : C₂ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  have enlarge {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) [IsFiniteMeasure ν]
      (D : Ω → ℝ) {A t : ℝ} (hAC : A ≤ C)
      (hbound : ν.real {J | A < D J} ≤ A*Real.exp t) :
      ν.real {J | C < D J} ≤ C*Real.exp t :=
    ((measureReal_mono (fun _ hJ => lt_of_le_of_lt hAC hJ)).trans hbound).trans
      (mul_le_mul_of_nonneg_right hAC (Real.exp_pos _).le)
  refine ⟨C,lt_of_lt_of_le hC₀ h0,?_,?_,?_⟩
  · intro n
    exact enlarge _ _ h0 (h₀ n)
  · intro n u hu e k he hk
    dsimp only
    let : IsProbabilityMeasure (mixedConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu (scorePairEquiv (e,k))) := by
      unfold mixedConditionedLaw; infer_instance
    exact enlarge _ _ h1 (h₁ (n+1) u hu e k he hk)
  · intro n u hu e he
    dsimp only
    let : IsProbabilityMeasure (valueConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu e) := by
      unfold valueConditionedLaw; infer_instance
    exact enlarge _ _ h2 (h₂ (n+1) u hu e he)

/-- Bounded Borel marks have probability-valued expectations under the full
energy-Palm normalization. The determinant remains correlated with the mark. -/
theorem maximumPalmExpectation_le_one (n : ℕ) (μ : FiniteMixture) {β x Q L R : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree)
    (hL : sourceRadialEdge μ Q < L) (hm : markK μ β Q ∈ Ioo L R)
    (u : Vector (n+2)) (hu : ‖u‖^2=(n+2:ℕ)) (e : ℝ)
    (f : Disorder (n+2) μ.maxDegree → ℝ → ℝ≥0∞) (hf : ∀ J k, f J k ≤ 1) :
    maximumPalmExpectation n μ Q u hu e (Ioo L R) f ≤ 1 := by
  rw [←maximumPalmExpectation_one n μ h hnp hL hm u hu e]
  unfold maximumPalmExpectation
  apply mul_le_mul_right
  apply lintegral_mono
  intro k
  apply mul_le_mul_right
  apply lintegral_mono
  intro J
  exact mul_le_mul_right (hf J k) _

end SlowEquilibration.SourceMixedOnePointLiteral
