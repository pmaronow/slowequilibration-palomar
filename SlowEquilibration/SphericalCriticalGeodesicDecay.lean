-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairSphereGeodesicJets
public import SlowEquilibration.SourcePhysicalPairSphereGeodesicReconstruction
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! The deterministic geodesic estimates in manuscript `lem:pc-superlevel`.
A covariant third-derivative bound propagates a critical Hessian margin
along short great circles, giving quadratic energy decay and uniqueness
of the critical point in the corresponding spherical ball. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SphericalCriticalGeodesicDecay

open Set SphericalModel SphericalGaussianJet SphericalForm
open PairConditionalDeterminantMoments
open scoped RealInnerProductSpace

set_option autoImplicit false

/-- Round-sphere arc distance on the physical sphere of radius `√N`. -/
def sphereGeodesicDist {N : ℕ} (u w : Vector N) : ℝ :=
  Real.sqrt (N : ℝ) * Real.arccos (overlap u w)

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

private theorem geodesic_cubic_abs_le {N P : ℕ}
    (hN : 0 < N) (c : Degree P → ℝ) (J : Disorder N P) {C : ℝ}
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sourceSphereThirdExtension c J x‖ ≤ C / Real.sqrt (N : ℝ))
    (u v : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (hv : ‖v‖ ^ 2 = (N : ℝ)) (huv : inner ℝ u v = 0) (t : ℝ) :
    |sourceSphereGeodesicCubic c J u v t| ≤ C * (N : ℝ) := by
  let x := sourceSphereGeodesic u v t
  let d := sourceSphereGeodesicVelocity u v t
  let T := sourceSphereThirdExtension c J x
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

private theorem geodesic_curvature_le {N P : ℕ}
    (hN : 0 < N) (c : Degree P → ℝ) (J : Disorder N P)
    {C κ ρ : ℝ} (hC : 0 < C) (hρκ : 2 * C * ρ ≤ κ)
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sourceSphereThirdExtension c J x‖ ≤ C / Real.sqrt (N : ℝ))
    (u v : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (hv : ‖v‖ ^ 2 = (N : ℝ)) (huv : inner ℝ u v = 0)
    (hMargin : sourceHessianMargin c κ J u) :
    ∀ t ∈ Icc (0 : ℝ) ρ,
      sourceSphereGeodesicCurvature c J u v t ≤ -(κ / 2) * (N : ℝ) := by
  intro t ht
  have hh0 : sourceSphereGeodesicCurvature c J u v 0 ≤ -κ * (N : ℝ) := by
    unfold sourceSphereGeodesicCurvature
    rw [sourceSphereGeodesicVelocity_zero, sourceSphereGeodesic_zero]
    have H := hMargin v
    rwa [source_tangentProjection_fixed u v huv, hv] at H
  have hdiff := scalar_derivative_upper_bound
    (sourceSphereGeodesicCurvature c J u v) (sourceSphereGeodesicCubic c J u v)
    t (C * (N : ℝ)) ht.1
    (fun r _ => sourceSphereGeodesicCurvature_hasDerivAt hN c J u v hu hv huv r)
    (fun r _ => (le_abs_self _).trans (geodesic_cubic_abs_le hN c J hThird u v hu hv huv r))
  have hct : C * t ≤ κ / 2 := by nlinarith [mul_le_mul_of_nonneg_left ht.2 hC.le]
  have hctN := mul_le_mul_of_nonneg_right hct (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

private theorem geodesic_slope_le {N P : ℕ}
    (hN : 0 < N) (c : Degree P → ℝ) (J : Disorder N P)
    {C κ ρ : ℝ} (hC : 0 < C) (hρκ : 2 * C * ρ ≤ κ)
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sourceSphereThirdExtension c J x‖ ≤ C / Real.sqrt (N : ℝ))
    (u v : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (hv : ‖v‖ ^ 2 = (N : ℝ)) (huv : inner ℝ u v = 0)
    (hCrit : surfaceGradient (field c J) u = 0)
    (hMargin : sourceHessianMargin c κ J u) :
    ∀ t ∈ Icc (0 : ℝ) ρ,
      sourceSphereGeodesicSlope c J u v t ≤ -(κ / 2) * (N : ℝ) * t := by
  intro t ht
  have hs0 : sourceSphereGeodesicSlope c J u v 0 = 0 := by
    simp only [sourceSphereGeodesicSlope, sourceSphereGeodesic_zero, hCrit, inner_zero_right]
  have H := scalar_derivative_upper_bound
    (sourceSphereGeodesicSlope c J u v) (sourceSphereGeodesicCurvature c J u v)
    t (-(κ / 2) * (N : ℝ)) ht.1
    (fun r _ => sourceSphereGeodesicSlope_hasDerivAt hN c J u v hu hv huv r)
    (fun r hr => geodesic_curvature_le hN c J hC hρκ hThird u v hu hv huv hMargin
      r (Icc_subset_Icc_right ht.2 hr))
  simpa only [hs0, sub_zero] using H

private theorem field_geodesic_hasDerivAt {N P : ℕ}
    (c : Degree P → ℝ) (J : Disorder N P)
    (u v : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ))
    (hv : ‖v‖ ^ 2 = (N : ℝ)) (huv : inner ℝ u v = 0) (t : ℝ) :
    HasDerivAt (fun r => field c J (sourceSphereGeodesic u v r))
      (sourceSphereGeodesicSlope c J u v t) t := by
  have H := ((field_contDiff c J).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt t
    (sourceSphereGeodesic_hasDerivAt u v t)
  convert H using 1
  · rfl
  · unfold sourceSphereGeodesicSlope
    rw [real_inner_comm, inner_surfaceGradient, source_tangentProjection_fixed _ _
      (sourceSphereGeodesic_tangent u v hu hv huv t)]

-- Keep the plan's positivity and short-angle hypotheses in the public statement;
-- the derivative comparison itself also holds without these three restrictions.
set_option linter.unusedVariables false in
/-- Source `lem:pc-superlevel`: the energy drops by at least `κ N t² / 4`
along every great circle from a critical point with Hessian margin `κ`. -/
theorem field_geodesic_quadratic_drop {N P : ℕ}
    (hN : 2 ≤ N) (c : Degree P → ℝ) (J : Disorder N P)
    {C κ ρ : ℝ} (hC : 0 < C) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρκ : 2 * C * ρ ≤ κ)
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sourceSphereThirdExtension c J x‖ ≤ C / Real.sqrt (N : ℝ))
    (u v : Vector N)
    (hu : ‖u‖ ^ 2 = (N : ℝ)) (hv : ‖v‖ ^ 2 = (N : ℝ))
    (huv : inner ℝ u v = 0)
    (hCrit : surfaceGradient (field c J) u = 0)
    (hMargin : sourceHessianMargin c κ J u) :
    ∀ t ∈ Icc (0 : ℝ) ρ,
      field c J (sourceSphereGeodesic u v t) ≤
        field c J u - κ / 4 * (N : ℝ) * t ^ 2 := by
  intro t ht
  let g : ℝ → ℝ := fun r => field c J (sourceSphereGeodesic u v r) + κ / 4 * (N : ℝ) * r ^ 2
  let g' : ℝ → ℝ := fun r => sourceSphereGeodesicSlope c J u v r + κ / 2 * (N : ℝ) * r
  have hg : ∀ r, HasDerivAt g (g' r) r := by
    intro r
    convert (field_geodesic_hasDerivAt c J u v hu hv huv r).add
      (((hasDerivAt_id r).pow 2).const_mul (κ / 4 * (N : ℝ))) using 1
    · rfl
    · dsimp [g']
      ring
  have H := scalar_derivative_upper_bound g g' t 0 ht.1 (fun r _ => hg r) (by
    intro r hr
    have hs := geodesic_slope_le (by omega) c J hC hρκ hThird u v hu hv huv hCrit hMargin
      r (Icc_subset_Icc_right ht.2 hr)
    dsimp [g']
    linarith)
  dsimp [g] at H
  rw [sourceSphereGeodesic_zero] at H
  nlinarith

/-- The Euclidean chord is no longer than the round-sphere arc between
two points of the physical sphere. -/
theorem norm_sub_le_sphereGeodesicDist {N : ℕ} (hN : 0 < N)
    (u w : Vector N) (hu : ‖u‖ ^ 2 = (N : ℝ)) (hw : ‖w‖ ^ 2 = (N : ℝ)) :
    ‖u - w‖ ≤ sphereGeodesicDist u w := by
  have hr := overlap_mem_Icc_of_norm_sq hN u w hu hw
  have hi : inner ℝ u w = (N : ℝ) * overlap u w := by
    unfold overlap
    field_simp
  have hcos := Real.one_sub_sq_div_two_le_cos (x := Real.arccos (overlap u w))
  rw [Real.cos_arccos hr.1 hr.2] at hcos
  have hmul := mul_le_mul_of_nonneg_left hcos (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  apply (sq_le_sq₀ (norm_nonneg _) (by
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.arccos_nonneg _) : 0 ≤ sphereGeodesicDist u w)).mp
  rw [norm_sub_sq_real, hu, hw, hi]
  unfold sphereGeodesicDist
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  nlinarith

/-- Source `lem:pc-superlevel`: a critical point with margin `κ` is the
only spherical critical point in its closed short geodesic ball. -/
theorem field_short_ball_critical_unique {N P : ℕ}
    (hN : 2 ≤ N) (c : Degree P → ℝ) (J : Disorder N P)
    {C κ ρ : ℝ} (hC : 0 < C) (hκ : 0 < κ)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρκ : 2 * C * ρ ≤ κ)
    (hThird : ∀ x : Vector N, ‖x‖ ^ 2 = (N : ℝ) →
      ‖sourceSphereThirdExtension c J x‖ ≤ C / Real.sqrt (N : ℝ))
    (u w : Vector N)
    (hu : ‖u‖ ^ 2 = (N : ℝ)) (hw : ‖w‖ ^ 2 = (N : ℝ))
    (hCrit : surfaceGradient (field c J) u = 0)
    (hMargin : sourceHessianMargin c κ J u)
    (hwCrit : surfaceGradient (field c J) w = 0)
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
  have H := geodesic_slope_le hNpos c J hC hρκ hThird u v hu hv huv hCrit hMargin
    (Real.arccos (overlap u w)) ⟨hθpos.le, hθle⟩
  have hEndSlope : sourceSphereGeodesicSlope c J u v (Real.arccos (overlap u w)) = 0 := by
    simp only [sourceSphereGeodesicSlope, hEnd, hwCrit, inner_zero_right]
  rw [hEndSlope] at H
  have hneg : 0 < κ / 2 * (n + 1 : ℕ) * Real.arccos (overlap u w) := by positivity
  nlinarith

end SlowEquilibration.SphericalCriticalGeodesicDecay
