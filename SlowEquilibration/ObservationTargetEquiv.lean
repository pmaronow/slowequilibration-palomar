-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianOrthogonalRegression
public import SlowEquilibration.WholeFieldRegression

/-! The genuine canonical Gaussian posterior is invariant under invertible
observation coordinate changes, at every target including null fibers. -/
@[expose] public section
namespace SlowEquilibration.ObservationTargetEquiv
noncomputable section
open Function MeasureTheory ProbabilityTheory
open GaussianRegression SphericalModel WholeFieldRegression
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [MeasurableSpace G] [BorelSpace G]

theorem regressionKernel_target_equiv (A : E →L[ℝ] F) (hA : Surjective A)
    (e : F ≃L[ℝ] G) (w : F) :
    regressionKernel ((e : F →L[ℝ] G).comp A) (e w)=regressionKernel A w := by
  let B:=(e : F →L[ℝ] G).comp A
  have hB : Surjective B := e.surjective.comp hA
  have hker : B.ker=A.ker := by
    ext z
    change e (A z)=0 ↔ A z=0
    exact e.map_eq_zero_iff
  have hobs : B (lift A w)=e w := by
    change e (A (lift A w))=e w
    rw [observation_lift_apply A hA]
  have hlift : lift B (e w)=lift A w := by
    rw [← hobs]
    exact orthogonal_joint_lift A B hB (le_of_eq hker) w
  have hres : residual B=residual A := by
    rw [residual_eq_starProjection B hB,residual_eq_starProjection A hA]
    simp only [hker]
  rw [regressionKernel_apply,regressionKernel_apply]
  change (stdGaussian E).map (fun z => residual B z+lift B (e w))=
    (stdGaussian E).map (fun z => residual A z+lift A w)
  rw [hres,hlift]

theorem coefficientKernel_target_equiv {N P : ℕ}
    (A : EuclideanDisorder N P →L[ℝ] F) (hA : Surjective A)
    (e : F ≃L[ℝ] G) (w : F) :
    coefficientKernel ((e : F →L[ℝ] G).comp A) (e w)=coefficientKernel A w := by
  rw [coefficientKernel_apply,coefficientKernel_apply,regressionKernel_target_equiv A hA e w]

end
end SlowEquilibration.ObservationTargetEquiv
