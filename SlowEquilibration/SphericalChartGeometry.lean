-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalChartKacRice
public import SlowEquilibration.SphericalForm
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Intrinsic geometry of the genuine round chart

The actual derivative spans the actual tangent plane, so scalar chart critical
points are exactly the intrinsic spherical critical points. Ordinary pullback
Hessian determinants carry precisely the actual derivative Gram determinant.
-/

@[expose] public section

namespace SlowEquilibration.SphericalChartGeometry

open MeasureTheory ProbabilityTheory Set Function Metric
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphereChartVolume SlowEquilibration.SphericalChartKacRice
open scoped RealInnerProductSpace Topology ENNReal

noncomputable section

variable {n : ℕ}

/-- The actual derivative Gram is the intrinsic metric operator Gram. -/
theorem chartDerivative_gram_matrix {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
      ((manuscriptChartDerivative n u).adjoint.comp (manuscriptChartDerivative n u)).toLinearMap =
      manuscriptChartGram n u := by
  classical
  ext i j
  rw [LinearMap.toMatrix_apply]
  change ((manuscriptChartDerivative n u).adjoint (manuscriptChartDerivative n u
    (EuclideanSpace.basisFun (Fin n) ℝ j))) i = _
  rw [← EuclideanSpace.basisFun_inner, ContinuousLinearMap.adjoint_inner_right]
  simp only [manuscriptChartGram, (manuscriptChart_hasFDerivAt hu).fderiv]

/-- The genuine chart derivative is injective, derived from its positive metric determinant. -/
theorem chartDerivative_injective {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    Injective (manuscriptChartDerivative n u) := by
  let T := manuscriptChartDerivative n u
  have hd : (T.adjoint.comp T).det ≠ 0 := by
    rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis,
      chartDerivative_gram_matrix hu]
    exact (manuscriptChartGram_det_pos hu).ne'
  let e := (T.adjoint.comp T).toLinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hd)
  have hi : Injective (T.adjoint.comp T) := by
    intro v w hv
    apply e.injective
    simpa only [e, LinearMap.equivOfIsUnitDet_apply, ContinuousLinearMap.coe_coe] using hv
  intro v w h
  apply hi
  exact congrArg T.adjoint h

/-- Dimension of the actual tangent plane at the actual-radius chart point. -/
theorem chart_tangentPlane_finrank {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    Module.finrank ℝ (tangentPlane (manuscriptChart n u)) = n := by
  have hx : manuscriptChart n u ≠ 0 := by
    intro he
    have h := manuscriptChart_norm_sq hu
    rw [he, norm_zero, zero_pow (by norm_num)] at h
    have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    linarith
  let : Fact (Module.finrank ℝ (Vector (n + 1)) = n + 1) := ⟨by simp⟩
  exact Submodule.finrank_orthogonal_span_singleton hx

/-- The actual chart derivative spans the complete intrinsic tangent plane. -/
theorem chartDerivative_range {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    (manuscriptChartDerivative n u).range = tangentPlane (manuscriptChart n u) := by
  have hle : (manuscriptChartDerivative n u).range ≤ tangentPlane (manuscriptChart n u) := by
    rintro v ⟨w, rfl⟩
    apply Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
    rw [real_inner_comm]
    exact manuscriptChartDerivative_tangent hu w
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [LinearMap.finrank_range_of_inj (chartDerivative_injective hu), chart_tangentPlane_finrank hu]
  simp

/-- Actual chart derivative viewed intrinsically in the true tangent plane. -/
def chartTangentMap (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ < 2) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] tangentPlane (manuscriptChart n u) :=
  (manuscriptChartDerivative n u).codRestrict _ (fun v =>
    Submodule.mem_orthogonal_singleton_iff_inner_right.mpr
      (by rw [real_inner_comm]; exact manuscriptChartDerivative_tangent hu v))

theorem chartTangentMap_bijective (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ < 2) :
    Bijective (chartTangentMap u hu) := by
  constructor
  · intro v w hv
    apply chartDerivative_injective hu
    exact congrArg Subtype.val hv
  · intro w
    have hw : (w : Vector (n + 1)) ∈ (manuscriptChartDerivative n u).range := by
      rw [chartDerivative_range hu]
      exact w.2
    obtain ⟨v, hv⟩ := hw
    exact ⟨v, Subtype.ext hv⟩

/-- A genuine continuous linear chart/tangent equivalence, rather than a chosen frame. -/
def chartTangentEquiv (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ < 2) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] tangentPlane (manuscriptChart n u) :=
  (LinearEquiv.ofBijective (chartTangentMap u hu).toLinearMap (chartTangentMap_bijective u hu)).toContinuousLinearEquiv

@[simp] theorem chartTangentEquiv_coe (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ < 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    (chartTangentEquiv u hu v : Vector (n + 1)) = manuscriptChartDerivative n u v := rfl

/-- The true tangent projection fixes each genuine chart derivative direction. -/
theorem projection_chartDerivative {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2)
    (v : EuclideanSpace ℝ (Fin n)) :
    tangentProjection (manuscriptChart n u) (manuscriptChartDerivative n u v) =
      manuscriptChartDerivative n u v := by
  rw [tangentProjection_eq_starProjection (by omega) _
    (by change inner ℝ _ _ = _; rw [real_inner_self_eq_norm_sq]; exact manuscriptChart_norm_sq hu)]
  exact (tangentPlane (manuscriptChart n u)).starProjection_eq_self_iff.mpr
    ((chartTangentMap u hu v).2)

/-- Literal vanishing of the scalar field chart derivative is equivalent to
vanishing of its actual spherical tangential gradient. -/
theorem chart_critical_iff_intrinsic {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2)
    (f : Vector (n + 1) → ℝ) (hf : DifferentiableAt ℝ f (manuscriptChart n u)) :
    fderiv ℝ (fun y => f (manuscriptChart n y)) u = 0 ↔
      surfaceGradient f (manuscriptChart n u) = 0 := by
  have hd := (hf.hasFDerivAt.comp u (manuscriptChart_hasFDerivAt hu)).fderiv
  simp only [Function.comp_def] at hd
  rw [hd]
  constructor
  · intro hz
    have hm : surfaceGradient f (manuscriptChart n u) ∈ tangentPlane (manuscriptChart n u) :=
      tangentProjection_mem (by omega) _ _
        (by change inner ℝ _ _ = _; rw [real_inner_self_eq_norm_sq]; exact manuscriptChart_norm_sq hu)
    have hr : surfaceGradient f (manuscriptChart n u) ∈ (manuscriptChartDerivative n u).range := by
      rw [chartDerivative_range hu]
      exact hm
    obtain ⟨v, hv⟩ := hr
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    nth_rw 2 [← hv]
    rw [inner_surfaceGradient]
    change (fderiv ℝ f (manuscriptChart n u))
      (tangentProjection (manuscriptChart n u) (manuscriptChartDerivative n u v)) = 0
    rw [projection_chartDerivative hu]
    have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) hz
    exact h
  · intro hz
    ext v
    change (fderiv ℝ f (manuscriptChart n u)) (manuscriptChartDerivative n u v) = 0
    rw [← projection_chartDerivative hu v, ← inner_surfaceGradient, hz, inner_zero_left]

/-- The chart critical predicate of the actual mixed field is its intrinsic
sphere critical predicate, under the original coefficients. -/
theorem actual_field_chart_critical_iff {P : ℕ} (c : Degree P → ℝ)
    (J : Disorder (n + 1) P) {u : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ < 2) :
    fderiv ℝ (fun y => field c J (manuscriptChart n y)) u = 0 ↔
      surfaceGradient (field c J) (manuscriptChart n u) = 0 :=
  chart_critical_iff_intrinsic hu _ ((field_contDiff c J).differentiable (by simp) _)

end
end SlowEquilibration.SphericalChartGeometry
