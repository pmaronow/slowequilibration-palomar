-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPosteriorGradientIndependence
public import SlowEquilibration.ConditionedEntrancePhysicalHittingSourceCutoff
public import SlowEquilibration.ConditionedEntranceSourceJointKilling

/-! The true original posterior/deleted field has a dimension-independent
spherical gradient bound on the original tensor regularity event. -/
@[expose] public section
namespace SlowEquilibration.SphericalPosteriorGradientIndependence
noncomputable section
open Function MeasureTheory ProbabilityTheory Set
open SphericalModel SphericalForm SphericalGaussianJet SphericalPosteriorMaps SphericalMarkedWindows
open SphericalCriticalLatitude ConditionedEntrance ConditionedEntrance.PhysicalHitting
open SphericalAging HardSphereDynamics
open scoped Topology ENNReal NNReal RealInnerProductSpace
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option maxHeartbeats 300000

def mixedDeletedGradientConstant (μ : FiniteMixture) (Q e k : ℝ) : ℝ :=
  sourceGradientConstant μ Q e k 1 (fun _=>1) contDiff_const

theorem mixedDeletedGradientConstant_nonneg (μ : FiniteMixture) (Q e k : ℝ) :
    0 ≤ mixedDeletedGradientConstant μ Q e k :=
  sourceGradientConstant_nonneg μ Q e k (by norm_num) (fun _=>1) contDiff_const

theorem actual_mixedDeleted_gradient_regular_bound (n : ℕ) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ)) (e k : ℝ)
    (z : EuclideanDisorder (n+1) μ.maxDegree) (hz : unpackDisorder z∈regularDisorder)
    (y : Vector (n+1)) (hy : OnSphere y) :
    ‖SphericalDynamics.mixedGradient μ (unpackDisorder (mixedPosterior n μ Q u (scorePairEquiv (e,k)) z)) y‖≤
      mixedDeletedGradientConstant μ Q e k*Real.sqrt ((n+1:ℕ):ℝ) := by
  let D := SmoothKilled.SourceData.atSourceParameters (by omega : 1≤n+1) μ hnp Q hQ hQ1
    1 (by norm_num) (fun _=>1) contDiff_const (unpackDisorder z,(u,(e,k)))
    ((onSphere_iff_norm_sq u).mpr hu)
  have he : fieldOfMixture μ (unpackDisorder (mixedPosterior n μ Q u (scorePairEquiv (e,k)) z))=D.hamiltonian := by
    funext x
    rw [actual_mixedPosterior_original_field n μ hQ hnp u hu e k z x]
    change _=sourceSmoothCutoffField μ Q hQ hnp (unpackDisorder z) u e k 1 (fun _=>1) x
    rw [sourceSmoothCutoffField_eq]
    simp only [one_mul]
  rw [SphericalDynamics.mixedGradient,he]
  exact regular_source_gradient_bound D hz y hy

theorem actual_original_gradient_regular_bound (n : ℕ) (μ : FiniteMixture)
    (hnp : μ.minDegree<μ.maxDegree) (Q : ℝ) (hQ : 0<Q) (hQ1 : Q≤1)
    (u : Vector (n+1)) (hu : ‖u‖^2=(n+1:ℕ))
    (z : EuclideanDisorder (n+1) μ.maxDegree) (hz : unpackDisorder z∈regularDisorder) :
    ‖surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) (unpackDisorder z)) u‖≤
      centerConstant μ Q*Real.sqrt ((n+1:ℕ):ℝ) := by
  let D := SmoothKilled.SourceData.atSourceParameters (by omega : 1≤n+1) μ hnp Q hQ hQ1
    1 (by norm_num) (fun _=>1) contDiff_const (unpackDisorder z,(u,(0,0)))
    ((onSphere_iff_norm_sq u).mpr hu)
  exact (regular_center_observations D hz).2.2

end
end SlowEquilibration.SphericalPosteriorGradientIndependence
