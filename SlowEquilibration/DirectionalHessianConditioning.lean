-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ConditionedIntrinsicHessian

@[expose] public section

/-! Actual whole-tensor conditioning of a tangent Hessian on the value and
arbitrary first-derivative directions. This includes the affine section's
radial direction, which differs from the ambient radius vector. -/

namespace SlowEquilibration.DirectionalHessianConditioning
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalGaussianJet
open SlowEquilibration.WholeFieldRegression SlowEquilibration.IntrinsicGradientRegression
open SlowEquilibration.ConditionedIntrinsicHessian SlowEquilibration.IntrinsicHessianLaw
open scoped Topology RealInnerProductSpace
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def valueDirectionsCLM {N P d : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (v : Fin d → Vector N) : EuclideanDisorder N P →L[ℝ] EuclideanSpace ℝ (Option (Fin d)) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Option (Fin d) => ℝ)).symm.toContinuousLinearMap.comp
    ((valueGradientCLM c x v).comp (unpackCLM N P))

@[simp] theorem valueDirectionsCLM_apply {N P d : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (v : Fin d → Vector N) (g : EuclideanDisorder N P) (i : Option (Fin d)) :
    valueDirectionsCLM c x v g i = valueGradient c x v (unpackDisorder g) i := by
  simp [valueDirectionsCLM]

theorem ambientHessian_directions_lift_zero {N P k d : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (e : Fin k → Vector N)
    (htan : ∀ i, inner ℝ (e i) x=0) (v : Fin d → Vector N) :
    (ambientHessianCLM c x e).comp (valueDirectionsCLM c x v).adjoint=0 := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Option (Fin d)) ℝ).toBasis.ext
  intro j
  apply PiLp.ext
  intro ij
  rcases ij with ⟨i,l⟩
  let f := (EuclideanSpace.proj (i,l)).comp (ambientHessianCLM c x e)
  have h := actual_scalar_cross_covariance f (valueDirectionsCLM c x v)
    (EuclideanSpace.basisFun (Option (Fin d)) ℝ j)
  simp only [EuclideanSpace.basisFun_inner] at h
  change cov[fun J : Disorder N P => ambientHessianCLM c x e (euclideanDisorder J) (i,l),
    fun J : Disorder N P => valueDirectionsCLM c x v (euclideanDisorder J) j; disorderLaw N P] =
      ambientHessianCLM c x e ((valueDirectionsCLM c x v).adjoint
        (EuclideanSpace.basisFun (Option (Fin d)) ℝ j)) (i,l) at h
  change ambientHessianCLM c x e ((valueDirectionsCLM c x v).adjoint
    (EuclideanSpace.basisFun (Option (Fin d)) ℝ j)) (i,l)=0
  rw [← h]
  simp only [ambientHessianCLM_apply, valueDirectionsCLM_apply, unpack_euclideanDisorder]
  cases j with
  | none => exact hessian_value_covariance_zero c hc x e htan i l
  | some j => exact hessian_gradient_covariance_zero c hc x e htan i l (v j)

/-- The genuine full Hessian matrix law survives every target of the
canonical full-tensor value/directional-derivative posterior. -/
theorem directions_conditioned_ambient_map {N P k d : ℕ} (c : Degree P → ℝ)
    (hc : ∀ p, 0 ≤ c p) (x : Vector N) (e : Fin k → Vector N)
    (htan : ∀ i, inner ℝ (e i) x=0) (v : Fin d → Vector N)
    (a : EuclideanSpace ℝ (Option (Fin d))) :
    (coefficientKernel (valueDirectionsCLM c x v) a).map (hessianMatrix c x e) =
      (disorderLaw N P).map (hessianMatrix c x e) := by
  have hm : Measurable (actualObservation (ambientHessianCLM c x e)) :=
    (ambientHessianCLM c x e).continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp (flatDisorder_measurable N P))
  have h := congrArg (fun m => m.map (hessianDecode k))
    (coefficientKernel_target_map_linear _ _ (ambientHessian_directions_lift_zero c hc x e htan v) a)
  rw [Measure.map_map (hessianDecode_measurable k) hm,
    Measure.map_map (hessianDecode_measurable k) hm] at h
  simpa only [Function.comp_def, hessianDecode_actual] using h

/-- A complete actual GOE matrix law at every prescribed directional
conditioning target, including targets of unconditional probability zero. -/
theorem directions_conditioned_ambient_hasLaw {N P k d : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Vector N) (hx : ‖x‖^2=(N : ℝ))
    (e : Fin k → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i, inner ℝ (e i) x=0)
    (v : Fin d → Vector N) (a : EuclideanSpace ℝ (Option (Fin d))) :
    HasLaw (hessianMatrix c x e) (goeLaw k N (secondCovariance c 1))
      (coefficientKernel (valueDirectionsCLM c x v) a) := by
  have hm : Measurable (actualObservation (ambientHessianCLM c x e)) :=
    (ambientHessianCLM c x e).continuous.measurable.comp ((PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Coordinate N P => ℝ)).symm.continuous.measurable.comp (flatDisorder_measurable N P))
  have hH : Measurable (hessianMatrix c x e) := by
    convert (hessianDecode_measurable k).comp hm using 1
    funext J
    exact (hessianDecode_actual c x e J).symm
  refine ⟨hH.aemeasurable, ?_⟩
  rw [directions_conditioned_ambient_map c hc x e htan v a]
  exact (tangent_hessian_matrix_hasLaw hN c hc x (r := 1) (by simpa using hx) e he htan).map_eq

end
end SlowEquilibration.DirectionalHessianConditioning
