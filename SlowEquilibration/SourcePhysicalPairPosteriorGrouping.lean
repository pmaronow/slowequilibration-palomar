-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairJetIntensity
public import SlowEquilibration.PairIntrinsicPhysicalDisintegration

/-! The physical Kac--Rice disintegration and the source determinant
estimates use exactly the same posterior, after a genuine observation
coordinate isometry. The physical density Jacobians are retained. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity IntrinsicHessianLaw PairObservationTargets
open ObservationTargetEquiv SphericalPairMarkedWindows PairObservationSmallOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

lemma mixedGrouping_physical_target (N m:ℕ) (h1 k1 h2 k2:ℝ) :
    mixedGroupingEquiv m (mixedPairTarget N m h1 k1 h2 k2)=
      WithLp.toLp 2 (Real.sqrt (N:ℝ) •
        (WithLp.toLp 2 (WithLp.toLp 2 ![h1,k1],WithLp.toLp 2 ![h2,k2]):ScorePairSpace),0):=by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply WithLp.ofLp_injective
    apply Prod.ext <;> apply WithLp.ofLp_injective <;> funext i <;> fin_cases i <;> rfl
  · rfl

lemma valueGrouping_physical_target (N m:ℕ) (h1 h2:ℝ) :
    hilbertRegroup (F:=ℝ) (G:=EuclideanSpace ℝ (Fin m)) (valuePairTarget N m h1 h2)=
      WithLp.toLp 2 (Real.sqrt (N:ℝ) • (WithLp.toLp 2 (h1,h2):ValuePairSpace),0):=by
  apply WithLp.ofLp_injective
  apply Prod.ext
  · apply WithLp.ofLp_injective
    apply Prod.ext <;> rfl
  · rfl

theorem source_mixed_physical_posterior_grouping (μ:FiniteMixture) {Q:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) :
    ∃ η:ℝ,0<η ∧ ∀ n:ℕ,∀ (x y:Vector (n+3))
      (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)), |overlap x y| ≤ η →
      ∀ h1 k1 h2 k2:ℝ,
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      pairMixedConditionedLaw c x y hx hy
        (WithLp.toLp 2 (WithLp.toLp 2 ![h1,k1],WithLp.toLp 2 ![h2,k2]))=
        coefficientKernel (pairHilbert (singleMixedObservation c x (tangentFrame x hx))
          (singleMixedObservation c y (tangentFrame y hy)))
          (mixedPairTarget (n+3) (n+2) h1 k1 h2 k2):=by
  obtain ⟨η,a,hη,ha,hall⟩:=uniform_mixed_pair_nondegenerate μ hQ hnp hd
  refine ⟨η,hη,?_⟩
  intro n x y hx hy hr h1 k1 h2 k2
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let A:=pairHilbert (singleMixedObservation c x (tangentFrame x hx))
    (singleMixedObservation c y (tangentFrame y hy))
  have hA:Surjective A:=observation_surjective _ ha
    (hall (n+3) (n+2) (by omega) x y hx hy _ _
      (tangentFrame_orthonormal x hx) (tangentFrame_orthonormal y hy)
      (tangentFrame_tangent x hx) (tangentFrame_tangent y hy) hr).1
  have hh:=coefficientKernel_target_equiv A hA
    (mixedGroupingEquiv (n+2)).toContinuousLinearEquiv
    (mixedPairTarget (n+3) (n+2) h1 k1 h2 k2)
  have ht:(mixedGroupingEquiv (n+2)).toContinuousLinearEquiv
      (mixedPairTarget (n+3) (n+2) h1 k1 h2 k2)=
      WithLp.toLp 2 (Real.sqrt (n+3:ℕ) •
        (WithLp.toLp 2 (WithLp.toLp 2 ![h1,k1],WithLp.toLp 2 ![h2,k2]):ScorePairSpace),0):=
    mixedGrouping_physical_target (n+3) (n+2) h1 k1 h2 k2
  rw [ht] at hh
  simpa only [pairMixedConditionedLaw,groupedMixedPair_eq,A,c] using hh

theorem source_value_physical_posterior_grouping (μ:FiniteMixture) {Q:ℝ}
    (hQ:0<Q) (hd:4 ≤ μ.minDegree) :
    ∃ η:ℝ,0<η ∧ ∀ n:ℕ,∀ (x y:Vector (n+3))
      (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)), |overlap x y| ≤ η →
      ∀ h1 h2:ℝ,
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      pairValueConditionedLaw c x y hx hy (WithLp.toLp 2 (h1,h2))=
        coefficientKernel (pairHilbert (singleValueObservation c x (tangentFrame x hx))
          (singleValueObservation c y (tangentFrame y hy)))
          (valuePairTarget (n+3) (n+2) h1 h2):=by
  obtain ⟨η,a,hη,ha,hall⟩:=uniform_value_pair_nondegenerate μ hQ hd
  refine ⟨η,hη,?_⟩
  intro n x y hx hy hr h1 h2
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  let A:=pairHilbert (singleValueObservation c x (tangentFrame x hx))
    (singleValueObservation c y (tangentFrame y hy))
  have hA:Surjective A:=observation_surjective _ ha
    (hall (n+3) (n+2) (by omega) x y hx hy _ _
      (tangentFrame_orthonormal x hx) (tangentFrame_orthonormal y hy)
      (tangentFrame_tangent x hx) (tangentFrame_tangent y hy) hr).1
  have hh:=coefficientKernel_target_equiv A hA
    (hilbertRegroup (F:=ℝ) (G:=EuclideanSpace ℝ (Fin (n+2)))).toContinuousLinearEquiv
    (valuePairTarget (n+3) (n+2) h1 h2)
  have ht:(hilbertRegroup (F:=ℝ) (G:=EuclideanSpace ℝ (Fin (n+2)))).toContinuousLinearEquiv
      (valuePairTarget (n+3) (n+2) h1 h2)=
      WithLp.toLp 2 (Real.sqrt (n+3:ℕ) • (WithLp.toLp 2 (h1,h2):ValuePairSpace),0):=
    valueGrouping_physical_target (n+3) (n+2) h1 h2
  rw [ht] at hh
  simpa only [pairValueConditionedLaw,groupedValuePair_eq,A,c] using hh

end
end SlowEquilibration.PairConditionalDeterminantMoments
