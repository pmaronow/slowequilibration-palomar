-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeCountIntensity
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-! Genuine maxima of the actual affine field are intrinsic critical points;
this connects low maxima to the literal score-window critical counts. -/

namespace SlowEquilibration.SphericalLatitudeChartKacRice
noncomputable section
open MeasureTheory ProbabilityTheory Set Function Metric InnerProductSpace
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalKacRiceGluing
open SphericalAging.HardSphereDynamics SphericalAging.SphericalIntegrationByParts
open scoped Topology ENNReal RealInnerProductSpace
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem surfaceGradient_eq_zero_of_sphere_maximum {N : ℕ} (hN : N ≠ 0)
    (H : Vector N → ℝ) (x : Vector N) (hx : OnSphere x) (hH : DifferentiableAt ℝ H x)
    (hmax : ∀ y, OnSphere y → H y ≤ H x) : surfaceGradient H x=0 := by
  have hdir (v : Vector N) (hv : inner ℝ x v=0) : fderiv ℝ H x v=0 := by
    let A := tangentRotation x v
    have hA : star A = -A := tangentRotation_skew x v
    have hAx : A x=v := tangentRotation_apply hN x v hx hv
    have hcurve := operatorFlow_apply_hasDerivAt A 0 x
    have hcomp := hH.hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve
      (show x=operatorFlow A 0 x from (operatorFlow_zero A x).symm)
    have hlocal : IsLocalMax (fun t => H (operatorFlow A t x)) 0 := by
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      rw [operatorFlow_zero]
      apply hmax
      rw [onSphere_iff_norm_sq, operatorFlow_norm A hA t x]
      exact (onSphere_iff_norm_sq x).mp hx
    simpa only [Function.comp_def, operatorFlow_zero, hAx] using hlocal.hasDerivAt_eq_zero hcomp
  apply ext_inner_right ℝ
  intro v
  rw [inner_surfaceGradient, inner_zero_left]
  apply hdir
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp (tangentProjection_mem hN x v hx)

theorem sphere_norm_sq_compact (n : ℕ) :
    IsCompact {y : Vector (n+1) | ‖y‖^2=((n+1 : ℕ) : ℝ)} := by
  have he : {y : Vector (n+1) | ‖y‖^2=((n+1 : ℕ) : ℝ)} =
      sphere 0 (Real.sqrt ((n+1 : ℕ) : ℝ)) := by
    ext y
    simp only [mem_ofPred_eq, mem_sphere, dist_zero_right]
    constructor
    · intro hy
      rw [← hy, Real.sqrt_sq (norm_nonneg y)]
    · intro hy
      rw [hy, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [he]
  exact isCompact_sphere _ _

/-- A true global spherical maximizer exists and has vanishing actual
surface gradient, with no Morse or Kac--Rice hypothesis. -/
theorem exists_sphere_maximum_critical {n : ℕ} (H : Vector (n+1) → ℝ)
    (hH : ContDiff ℝ 1 H) :
    ∃ y, ‖y‖^2=((n+1 : ℕ) : ℝ) ∧ surfaceGradient H y=0 ∧
      ∀ z, ‖z‖^2=((n+1 : ℕ) : ℝ) → H z ≤ H y := by
  obtain ⟨y, hy, hm⟩ := (sphere_norm_sq_compact n).exists_isMaxOn
    ⟨southPole n, southPole_norm_sq n⟩ hH.continuous.continuousOn
  refine ⟨y, hy, ?_, hm⟩
  apply surfaceGradient_eq_zero_of_sphere_maximum (by omega) H y
    ((onSphere_iff_norm_sq y).mpr hy) (hH.differentiable (by norm_num) y)
  intro z hz
  exact hm ((onSphere_iff_norm_sq z).mp hz)

/-- If a genuine field value lies above L and its global maximum lies below
U, then its literal critical count in that value window is at least one. -/
theorem latitude_count_ge_one_of_low_maximum {n P : ℕ} (c : Degree P → ℝ)
    (w : Vector (n+2)) (e : Vector (n+1) →ₗᵢ[ℝ] Vector (n+2)) (q : ℝ)
    (J : Disorder (n+2) P) {L U : ℝ} (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ))
    (hL : L ≤ latitudeField c J w e q x)
    (hU : ∀ y, ‖y‖^2=((n+1 : ℕ) : ℝ) → latitudeField c J w e q y ≤ U) :
    1 ≤ actualLatitudeSphereCount c w e q
      (fun J y => if latitudeField c J w e q y ∈ Icc L U then 1 else 0) J := by
  classical
  obtain ⟨y, hy, hcrit, hm⟩ := exists_sphere_maximum_critical (latitudeField c J w e q)
    ((latitudeField_contDiff c J w e q).of_le (by simp))
  have hwin : latitudeField c J w e q y ∈ Icc L U := ⟨hL.trans (hm x hx), hU y hy⟩
  have hterm := ENNReal.le_tsum (f := fun z : {z : Vector (n+1) | ‖z‖^2=((n+1 : ℕ) : ℝ) ∧
      surfaceGradient (latitudeField c J w e q) z=0} =>
    if latitudeField c J w e q z ∈ Icc L U then (1 : ℝ≥0∞) else 0) ⟨y, hy, hcrit⟩
  simpa only [ite_eq_left hwin, actualLatitudeSphereCount] using hterm

end
end SlowEquilibration.SphericalLatitudeChartKacRice
