-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianNonorthogonalRegression
public import SlowEquilibration.ObservationTargetEquiv

/-! Canonical lifts on the literal gradient-zero fiber. The original joint
observation is retained; sequential regression is an identity of its actual
minimum-norm lift, including specified fibers of zero observation probability. -/

@[expose] public section
namespace SlowEquilibration.GaussianRegression
noncomputable section
open Function GaussianObservationCoercivity
open scoped RealInnerProductSpace

variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]

/-- The actual minimum-norm lift is unchanged by invertible observation
coordinates, at every target. -/
theorem canonical_lift_target_equiv (A : E →L[ℝ] F) (hA : Surjective A)
    (e : F ≃L[ℝ] G) (w : F) :
    lift ((e : F →L[ℝ] G).comp A) (e w)=lift A w := by
  let B := (e : F →L[ℝ] G).comp A
  have hB : Surjective B := e.surjective.comp hA
  have hker : B.ker=A.ker := by
    ext z
    change e (A z)=0 ↔ A z=0
    exact e.map_eq_zero_iff
  have hobs : B (lift A w)=e w := by
    change e (A (lift A w))=e w
    rw [observation_lift_apply A hA]
  rw [← hobs]
  exact orthogonal_joint_lift A B hB (le_of_eq hker) w

/-- The canonical full joint lift on a zero-gradient fiber is the residual
score lift. This requires no independence of the original score and gradient. -/
theorem zero_gradient_joint_lift (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E →L[ℝ] G) (hB : Surjective (B.comp (residual A)))
    (hC : Surjective (pairHilbert B A)) (b : G) :
    lift (pairHilbert B A) (WithLp.toLp 2 (b,0)) =
      lift (B.comp (residual A)) b := by
  rw [← residual_mark_joint_target A hA B hB b]
  apply orthogonal_joint_lift (B.comp (residual A)) (pairHilbert B A) hC
  rw [mark_gradient_pair_ker A B hA]
  exact inf_le_right

/-- An explicit coefficient identity for the zero-gradient posterior mean. -/
theorem residual_score_lift_apply (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E →L[ℝ] G) (b : G) :
    lift (B.comp (residual A)) b =
      B.adjoint ((gram (B.comp (residual A))).inverse b) -
        A.adjoint ((gram A).inverse
          (A (B.adjoint ((gram (B.comp (residual A))).inverse b)))) := by
  rw [lift, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_comp,
    residual_adjoint A hA, ContinuousLinearMap.comp_apply]
  rfl

/-- The score contribution and the gradient correction have separate operator
norms. Their product, rather than a coarse bound on the full joint observation,
preserves the small-overlap order of the true zero-gradient corner mean. -/
theorem residual_score_hessian_bound (A : E →L[ℝ] F) (hA : Surjective A)
    (B : E →L[ℝ] G) (H : E →L[ℝ] ℝ) (b : G)
    {s g c T U : ℝ} (hs : ‖H.comp B.adjoint‖ ≤ s)
    (hg : ‖H.comp A.adjoint‖ ≤ g) (hc : ‖A.comp B.adjoint‖ ≤ c)
    (hT : ‖(gram A).inverse‖ ≤ T)
    (hU : ‖(gram (B.comp (residual A))).inverse‖ ≤ U) :
    |H (lift (B.comp (residual A)) b)| ≤
      (s + g * T * c) * (U * ‖b‖) := by
  have hs0 : 0 ≤ s := (norm_nonneg _).trans hs
  have hg0 : 0 ≤ g := (norm_nonneg _).trans hg
  have hc0 : 0 ≤ c := (norm_nonneg _).trans hc
  have hT0 : 0 ≤ T := (norm_nonneg _).trans hT
  let z := (gram (B.comp (residual A))).inverse b
  have hz : ‖z‖ ≤ U * ‖b‖ :=
    ((gram (B.comp (residual A))).inverse.le_opNorm b).trans
      (mul_le_mul_of_nonneg_right hU (norm_nonneg b))
  have hscore : |H (B.adjoint z)| ≤ s * ‖z‖ := by
    exact ((H.comp B.adjoint).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hs (norm_nonneg z))
  have hcross : ‖A (B.adjoint z)‖ ≤ c * ‖z‖ :=
    ((A.comp B.adjoint).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right hc (norm_nonneg z))
  have hgrad : |H (A.adjoint ((gram A).inverse (A (B.adjoint z))))| ≤
      g * (T * (c * ‖z‖)) := by
    calc
      _ ≤ g * ‖(gram A).inverse (A (B.adjoint z))‖ :=
        ((H.comp A.adjoint).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hg (norm_nonneg _))
      _ ≤ g * (T * ‖A (B.adjoint z)‖) := by
        gcongr
        exact ((gram A).inverse.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hT (norm_nonneg _))
      _ ≤ _ := by gcongr
  rw [residual_score_lift_apply A hA B b, map_sub]
  calc
    _ ≤ |H (B.adjoint z)| +
        |H (A.adjoint ((gram A).inverse (A (B.adjoint z))))| := abs_sub _ _
    _ ≤ s * ‖z‖ + g * (T * (c * ‖z‖)) := add_le_add hscore hgrad
    _ = (s + g * T * c) * ‖z‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hz (by positivity)

end
end SlowEquilibration.GaussianRegression
