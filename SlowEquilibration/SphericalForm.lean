module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalGibbs
public import SphericalAging.HardSphereDynamics
public import SphericalAging.SphericalIntegrationByParts
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Tactic

@[expose] public section

/-!
# The actual spherical tangential gradient and Dirichlet form

The state space is the manuscript's `EuclideanSpace ℝ (Fin N)` and its sphere
of squared radius `N`. The tangent projection is the actual operator
`I - xxᵀ/N`, and the scalar gradient is its application to the ambient Riesz
gradient. Independence of ambient smooth extensions is proved using genuine
orthogonal exponential flows, rather than assumed. The form below is the
integral of the actual tangential gradients against the actual Gibbs law.

Completion, closability, compact embedding, and spectral realization are
separate construction stages, not hypotheses hidden in these definitions.
-/

namespace SlowEquilibration.SphericalForm

noncomputable section

open MeasureTheory Filter Set
open SphericalModel
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped BigOperators InnerProductSpace Topology

/-- The actual tangent projection, as a continuous linear map. -/
def tangentProjection {N : ℕ} (x : Vector N) : Vector N →L[ℝ] Vector N :=
  ContinuousLinearMap.id ℝ (Vector N) -
    (1 / (N : ℝ)) • InnerProductSpace.rankOne ℝ x x

@[simp] theorem tangentProjection_apply {N : ℕ} (x v : Vector N) :
    tangentProjection x v = projection x v := by
  simp only [tangentProjection, sub_apply, ContinuousLinearMap.id_apply,
    _root_.smul_apply, InnerProductSpace.rankOne_apply, projection, smul_smul]
  rw [one_div_mul_eq_div]

/-- The actual tangent plane at a spherical point. -/
def tangentPlane {N : ℕ} (x : Vector N) : Submodule ℝ (Vector N) := (ℝ ∙ x)ᗮ

theorem tangentProjection_mem {N : ℕ} (hN : N ≠ 0) (x v : Vector N)
    (hx : OnSphere x) : tangentProjection x v ∈ tangentPlane x := by
  rw [tangentPlane, Submodule.mem_orthogonal_singleton_iff_inner_right, tangentProjection_apply]
  exact projection_tangent hN x v hx

/-- On the manuscript sphere, `I-xxᵀ/N` is the genuine orthogonal projection
onto the tangent plane. -/
theorem tangentProjection_eq_starProjection {N : ℕ} (hN : N ≠ 0) (x : Vector N)
    (hx : OnSphere x) : tangentProjection x = (tangentPlane x).starProjection := by
  apply ContinuousLinearMap.ext
  intro v
  symm
  apply (tangentPlane x).eq_starProjection_of_mem_of_inner_eq_zero (tangentProjection_mem hN x v hx)
  intro w hw
  have horth : inner ℝ x w = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
  simp [tangentProjection_apply, projection, real_inner_smul_left, horth]

theorem tangentProjection_symmetric {N : ℕ} (x : Vector N) :
    (tangentProjection x : Vector N →ₗ[ℝ] Vector N).IsSymmetric := by
  intro u v
  change inner ℝ (tangentProjection x u) v = inner ℝ u (tangentProjection x v)
  simpa only [tangentProjection_apply] using projection_self_adjoint x u v

theorem tangentProjection_norm_le {N : ℕ} (hN : N ≠ 0) (x : Vector N)
    (hx : OnSphere x) : ‖tangentProjection x‖ ≤ 1 := by
  apply (tangentProjection x).opNorm_le_bound zero_le_one
  intro v
  simpa only [tangentProjection_apply, one_mul] using projection_norm_le_onSphere hN x v hx

theorem tangentProjection_continuous (N : ℕ) :
    Continuous (fun x : Vector N => tangentProjection x) := by
  unfold tangentProjection
  have hr : Continuous (fun x : Vector N => InnerProductSpace.rankOne ℝ x x) := by
    have heq : (fun x : Vector N => InnerProductSpace.rankOne ℝ x x) =
        (fun x => (ContinuousLinearMap.toSpanSingletonLIE ℝ (Vector N) x).comp
          (InnerProductSpace.toDual ℝ (Vector N) x)) := by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      simp [InnerProductSpace.rankOne_apply, InnerProductSpace.toDual_apply_apply]
    rw [heq]
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ (Vector N)).continuous.clm_comp
      (InnerProductSpace.toDual ℝ (Vector N)).continuous
  exact continuous_const.sub (hr.const_smul (1 / (N : ℝ)))

/-- The spherical Riesz gradient of an ambient smooth representative. -/
def surfaceGradient {N : ℕ} (f : Vector N → ℝ) (x : Vector N) : Vector N :=
  tangentProjection x (gradient f x)

/-- The spherical gradient represents the derivative on the actual tangent
directions, with no derivative or gradient identity supplied as a hypothesis. -/
theorem inner_surfaceGradient {N : ℕ} (f : Vector N → ℝ) (x v : Vector N) :
    inner ℝ (surfaceGradient f x) v = (fderiv ℝ f x) (tangentProjection x v) := by
  rw [surfaceGradient, (tangentProjection_symmetric x).apply_clm, inner_gradient_left]

theorem dual_surfaceGradient {N : ℕ} (f : Vector N → ℝ) (x : Vector N) :
    InnerProductSpace.toDual ℝ (Vector N) (surfaceGradient f x) =
      (fderiv ℝ f x).comp (tangentProjection x) := by
  ext v
  simpa only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply] using
    inner_surfaceGradient f x v

theorem surfaceGradient_norm {N : ℕ} (f : Vector N → ℝ) (x : Vector N) :
    ‖surfaceGradient f x‖ = ‖(fderiv ℝ f x).comp (tangentProjection x)‖ := by
  rw [← dual_surfaceGradient]
  exact (InnerProductSpace.toDual ℝ (Vector N)).norm_map _ |>.symm

/-- A skew-adjoint generator whose orbit has any prescribed tangent velocity.
It is constructed explicitly from the actual point and tangent vector. -/
def tangentRotation {N : ℕ} (x v : Vector N) : Vector N →L[ℝ] Vector N :=
  (1 / (N : ℝ)) •
    (InnerProductSpace.rankOne ℝ v x - InnerProductSpace.rankOne ℝ x v)

theorem tangentRotation_skew {N : ℕ} (x v : Vector N) :
    star (tangentRotation x v) = -tangentRotation x v := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  simp only [tangentRotation, map_smul, map_sub, InnerProductSpace.adjoint_rankOne]
  module

theorem tangentRotation_apply {N : ℕ} (hN : N ≠ 0) (x v : Vector N)
    (hx : OnSphere x) (hv : inner ℝ x v = 0) : tangentRotation x v x = v := by
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hxx : inner ℝ x x = (N : ℝ) := hx
  have hvx : inner ℝ v x = 0 := by rw [real_inner_comm]; exact hv
  simp only [tangentRotation, _root_.smul_apply, sub_apply, InnerProductSpace.rankOne_apply,
    smul_sub, smul_smul, hxx, hvx, zero_smul, smul_zero, sub_zero]
  rw [one_div_mul_cancel hNr, one_smul]

/-- Agreement on the actual sphere forces agreement of every tangent
directional derivative. The proof differentiates a genuine orthogonal
exponential orbit with that tangent velocity. -/
theorem tangent_fderiv_eq_of_agree_on_sphere {N : ℕ} (hN : N ≠ 0)
    (f g : Vector N → ℝ) (x v : Vector N) (hx : OnSphere x)
    (hv : inner ℝ x v = 0) (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hagree : ∀ y, OnSphere y → f y = g y) : (fderiv ℝ f x) v = (fderiv ℝ g x) v := by
  let A := tangentRotation x v
  have hA : star A = -A := tangentRotation_skew x v
  have hAx : A x = v := tangentRotation_apply hN x v hx hv
  have hflowSphere : ∀ t, OnSphere (operatorFlow A t x) := by
    intro t
    rw [onSphere_iff_norm_sq, operatorFlow_norm A hA t x]
    exact (onSphere_iff_norm_sq x).mp hx
  have heq : (fun t => (f - g) (operatorFlow A t x)) = (fun _ : ℝ => (0 : ℝ)) := by
    funext t
    exact sub_eq_zero.mpr (hagree _ (hflowSphere t))
  have hcurve := operatorFlow_apply_hasDerivAt A 0 x
  have hcomp := (hf.sub hg).hasFDerivAt.comp_hasDerivAt_of_eq 0 hcurve
    (show x = operatorFlow A 0 x from (operatorFlow_zero A x).symm)
  have hzero : (fderiv ℝ (f - g) x) v = 0 := by
    have hc0 : HasDerivAt ((f - g) ∘ fun s => operatorFlow A s x) 0 0 := by
      simpa only [Function.comp_def, heq] using hasDerivAt_const (0 : ℝ) (0 : ℝ)
    simpa only [operatorFlow_zero, hAx] using hcomp.unique hc0
  rw [fderiv_sub hf hg] at hzero
  simpa only [sub_apply, sub_eq_zero] using hzero

/-- The actual tangential gradient is independent of ambient extensions.
This permits the ensuing form to descend to smooth functions on the sphere. -/
theorem surfaceGradient_eq_of_agree_on_sphere {N : ℕ} (hN : N ≠ 0)
    (f g : Vector N → ℝ) (x : Vector N) (hx : OnSphere x)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (hagree : ∀ y, OnSphere y → f y = g y) : surfaceGradient f x = surfaceGradient g x := by
  apply ext_inner_right ℝ
  intro v
  rw [inner_surfaceGradient, inner_surfaceGradient]
  exact tangent_fderiv_eq_of_agree_on_sphere hN f g x (tangentProjection x v) hx
    (by simpa only [tangentProjection_apply] using projection_tangent hN x v hx) hf hg hagree

end
end SlowEquilibration.SphericalForm
