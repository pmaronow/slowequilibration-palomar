-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalChartGeometry
public import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Actual intrinsic Hessian and its coefficient/chart determinant

The intrinsic Hessian is the tangent projection of the actual derivative of
the spherical gradient. Its extrinsic derivative formula is proved directly.
-/

@[expose] public section

namespace SlowEquilibration.SphereHessian

open MeasureTheory ProbabilityTheory Set Function Metric InnerProductSpace
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphereChartVolume SlowEquilibration.SphericalChartKacRice
open SlowEquilibration.SphericalChartGeometry SlowEquilibration.GaussianLocalCoordinates
open SphericalAging.HardSphereDynamics
open scoped RealInnerProductSpace Topology ENNReal

noncomputable section

variable {N n : ℕ}

/-- The true radial gradient multiplier in the ordinary sphere Hessian. -/
def radialMultiplier (f : Vector N → ℝ) (x : Vector N) : ℝ :=
  inner ℝ x (gradient f x) / (N : ℝ)

/-- The genuine covariant sphere Hessian: project the actual derivative of
the actual spherical gradient onto the ordinary intrinsic tangent plane. -/
def intrinsicHessian (f : Vector N → ℝ) (x : Vector N) : tangentPlane x →L[ℝ] tangentPlane x :=
  (tangentPlane x).orthogonalProjectionOnto.comp
    ((fderiv ℝ (surfaceGradient f) x).comp (tangentPlane x).subtypeL)

/-- The ordinary spherical gradient is its ambient Riesz gradient minus its
true radial component, before any Hessian differentiation. -/
theorem surfaceGradient_eq (f : Vector N → ℝ) :
    surfaceGradient f = fun x => gradient f x - radialMultiplier f x • x := by
  funext x
  simp only [surfaceGradient, tangentProjection_apply, projection, radialMultiplier]

/-- Differentiating the actual sphere gradient and projecting tangentially
yields its true ambient-Hessian minus radial-multiplier formula. -/
theorem intrinsicHessian_apply (hN : N ≠ 0) (f : Vector N → ℝ) (x : Vector N)
    (hx : OnSphere x) (hg : DifferentiableAt ℝ (gradient f) x) (v : tangentPlane x) :
    (intrinsicHessian f x v : Vector N) =
      tangentProjection x ((fderiv ℝ (gradient f) x) v) - radialMultiplier f x • (v : Vector N) := by
  have hLambda : DifferentiableAt ℝ (radialMultiplier f) x := by
    unfold radialMultiplier
    simpa only [div_eq_mul_inv, id_eq] using
      (differentiableAt_id.inner ℝ hg).mul_const (N : ℝ)⁻¹
  have hS := hg.hasFDerivAt.sub (hLambda.hasFDerivAt.smul (hasFDerivAt_id x))
  have he := hS.fderiv
  change fderiv ℝ (fun y => gradient f y - radialMultiplier f y • y) x = _ at he
  rw [← surfaceGradient_eq] at he
  have hπ : tangentProjection x (v : Vector N) = v := by
    rw [tangentProjection_eq_starProjection hN x hx]
    exact (tangentPlane x).starProjection_eq_self_iff.mpr v.2
  have hπx : tangentProjection x x = 0 := by
    rw [tangentProjection_apply]
    exact projection_normal_zero hN x hx
  simp only [intrinsicHessian, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    Submodule.coe_orthogonalProjectionOnto_apply]
  rw [← tangentProjection_eq_starProjection hN x hx, he]
  simp only [sub_apply, add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, id_eq]
  rw [map_sub, map_add, map_smul, map_smul, hπ, hπx, smul_zero, add_zero]

/-- The actual mixed field has a smooth ordinary ambient Riesz gradient. -/
theorem field_gradient_contDiff {P : ℕ} (c : Degree P → ℝ) (J : Disorder N P) :
    ContDiff ℝ ⊤ (gradient (field c J)) := by
  have hd := (field_contDiff c J).fderiv_right (m := ⊤) (by simp)
  exact (InnerProductSpace.toDual ℝ (Vector N)).symm.contDiff.comp hd

/-- The derivative of the actual field Riesz gradient is the actual second
Frechet derivative, rather than an independent Gaussian Hessian surrogate. -/
theorem field_gradient_derivative_inner {P : ℕ} (c : Degree P → ℝ) (J : Disorder N P)
    (x v w : Vector N) :
    inner ℝ ((fderiv ℝ (gradient (field c J)) x) v) w =
      (fderiv ℝ (fderiv ℝ (field c J)) x) v w := by
  have hd := (field_contDiff c J).fderiv_right (m := ⊤) (by simp)
  have h := (InnerProductSpace.toDual ℝ (Vector N)).symm.hasFDerivAt.comp x
    (hd.differentiable (by simp) x).hasFDerivAt
  have he := h.fderiv
  change fderiv ℝ (gradient (field c J)) x = _ at he
  rw [he]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  rw [← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply]

/-- The true multiplier is exactly the actual radial first field jet divided
by the manuscript radius squared. -/
theorem radialMultiplier_eq_jet {P : ℕ} (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N) :
    radialMultiplier (field c J) x =
      SphericalGaussianJet.jet c 1 x (fun _ => x) J / (N : ℝ) := by
  unfold radialMultiplier SphericalGaussianJet.jet
  rw [iteratedFDeriv_one_apply, real_inner_comm, inner_gradient_left]

variable {U V : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- Ordinary pullback of an intrinsic Hessian by a genuine tangent-coordinate equivalence. -/
def pullback (e : U ≃L[ℝ] V) (H : V →L[ℝ] V) : U →L[ℝ] U :=
  (e : U →L[ℝ] V).adjoint.comp (H.comp (e : U →L[ℝ] V))

/-- Every Hessian pullback determinant is the actual coordinate metric
Gram determinant times the actual intrinsic operator determinant. -/
theorem pullback_det (e : U ≃L[ℝ] V) (H : V →L[ℝ] V) :
    (pullback e H).det = ((e : U →L[ℝ] V).adjoint.comp (e : U →L[ℝ] V)).det * H.det := by
  have he : pullback e H = ((e : U →L[ℝ] V).adjoint.comp (e : U →L[ℝ] V)).comp
      ((e.symm : V →L[ℝ] U).comp (H.comp (e : U →L[ℝ] V))) := by
    ext v
    simp only [pullback, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      e.apply_symm_apply]
  rw [he, ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp]
  congr 1
  change LinearMap.det ((e.symm.toLinearEquiv : V →ₗ[ℝ] U).comp
    (H.toLinearMap.comp (e.toLinearEquiv : U →ₗ[ℝ] V))) = _
  exact LinearMap.det_conj H.toLinearMap e.symm.toLinearEquiv

/-- The actual coordinate gradient is the adjoint chart derivative applied
to the actual surface gradient. -/
theorem chartGamma_eq_adjoint_surfaceGradient {P : ℕ} (c : Degree P → ℝ)
    (g : EuclideanDisorder (n + 1) P) {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    chartGamma n c u g = (fderiv ℝ (manuscriptChart n) u).adjoint
      (surfaceGradient (field c (unpackDisorder g)) (manuscriptChart n u)) := by
  apply ext_inner_left ℝ
  intro v
  rw [chartGamma_directional_derivative n c hu, ContinuousLinearMap.adjoint_inner_right,
    (manuscriptChart_hasFDerivAt hu).fderiv, real_inner_comm,
    inner_surfaceGradient, projection_chartDerivative hu]
  have hd := ((field_contDiff c (unpackDisorder g)).differentiable (by simp)
    (manuscriptChart n u)).hasFDerivAt.comp u (manuscriptChart_hasFDerivAt hu)
  exact congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) hd.fderiv

/-- Smoothness of the genuine projected gradient follows from the actual
polynomial field and the explicit tangent projection. -/
theorem field_surfaceGradient_contDiff {P : ℕ} (c : Degree P → ℝ) (J : Disorder N P) :
    ContDiff ℝ ⊤ (surfaceGradient (field c J)) := by
  rw [surfaceGradient_eq]
  have hg := field_gradient_contDiff c J
  exact hg.sub (((contDiff_id.inner ℝ hg).div_const (N : ℝ)).smul contDiff_id)

/-- At an actual spherical critical point, the coordinate Hessian is the
ordinary pullback of the genuine intrinsic Hessian. -/
theorem actualChartHessian_eq_pullback {P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n + 1) P) {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2)
    (hcrit : surfaceGradient (field c J) (manuscriptChart n u) = 0) :
    actualChartHessian n c J u = pullback (chartTangentEquiv u hu)
      (intrinsicHessian (field c J) (manuscriptChart n u)) := by
  have hfd := ((manuscriptChart_contDiffOn n).fderiv_of_isOpen isOpen_ball
    (m := 1) (by simp)).contDiffAt (isOpen_ball.mem_nhds (by simpa using hu))
  have hA := (ContinuousLinearMap.adjoint :
    (EuclideanSpace ℝ (Fin n) →L[ℝ] Vector (n + 1)) ≃ₗᵢ[ℝ]
      (Vector (n + 1) →L[ℝ] EuclideanSpace ℝ (Fin n))).hasFDerivAt.comp u
        hfd.differentiableAt_one.hasFDerivAt
  have hG := ((field_surfaceGradient_contDiff c J).differentiable (by simp)
    (manuscriptChart n u)).hasFDerivAt.comp u (manuscriptChart_hasFDerivAt hu)
  have heq : (fun y => chartGamma n c y (euclideanDisorder J)) =ᶠ[𝓝 u]
      (fun y => (fderiv ℝ (manuscriptChart n) y).adjoint
        (surfaceGradient (field c J) (manuscriptChart n y))) := by
    filter_upwards [isOpen_ball.mem_nhds (by simpa using hu : u ∈ ball 0 2)] with y hy
    simpa only [unpack_euclideanDisorder] using
      chartGamma_eq_adjoint_surfaceGradient c (euclideanDisorder J) (by simpa using hy)
  have hd := hA.clm_apply hG
  simp only [Function.comp_def] at hd
  unfold actualChartHessian spatialJacobian
  rw [heq.fderiv_eq, hd.fderiv]
  simp only [hcrit, map_zero, add_zero, (manuscriptChart_hasFDerivAt hu).fderiv]
  apply ContinuousLinearMap.ext
  intro v
  apply ext_inner_left ℝ
  intro w
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
    pullback, intrinsicHessian]
  rw [Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

/-- The true chart metric Gram is unchanged on viewing chart derivatives
as vectors in the intrinsic tangent plane. -/
theorem chartTangentEquiv_gram_det {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    (((chartTangentEquiv u hu : EuclideanSpace ℝ (Fin n) →L[ℝ]
      tangentPlane (manuscriptChart n u)).adjoint).comp
        (chartTangentEquiv u hu : _ →L[ℝ] _)).det =
      (manuscriptChartGram n u).det := by
  have he : ((chartTangentEquiv u hu : EuclideanSpace ℝ (Fin n) →L[ℝ]
      tangentPlane (manuscriptChart n u)).adjoint).comp
        (chartTangentEquiv u hu : _ →L[ℝ] _) =
      (manuscriptChartDerivative n u).adjoint.comp (manuscriptChartDerivative n u) := by
    apply ContinuousLinearMap.ext
    intro v
    apply ext_inner_left ℝ
    intro w
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right]
    rfl
  rw [he, ContinuousLinearMap.det,
    ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
    chartDerivative_gram_matrix hu]

/-- The ordinary intrinsic Hessian determinant carries exactly one actual
chart metric determinant, with no orthonormal-coordinate assumption. -/
theorem actualChartHessian_det {P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n + 1) P) {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2)
    (hcrit : surfaceGradient (field c J) (manuscriptChart n u) = 0) :
    (actualChartHessian n c J u).det = (manuscriptChartGram n u).det *
      (intrinsicHessian (field c J) (manuscriptChart n u)).det := by
  rw [actualChartHessian_eq_pullback c J hu hcrit, pullback_det, chartTangentEquiv_gram_det hu]

end
end SlowEquilibration.SphereHessian
