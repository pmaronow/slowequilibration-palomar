-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairPosteriorAmbientBounds
public import SlowEquilibration.SourcePhysicalPairValuePointGrouping

/-! Exponential full ordered-tensor regularity under the literal physical
one-point conditioned laws, with constants chosen before the dimension and
every point, frame, and compact physical mark. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet WholeFieldRegression
open IntrinsicHessianLaw SphericalMarkedWindows
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem source_mixed_physical_posterior_orderedRegularity (μ:FiniteMixture) {Q M:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hM:0 ≤ M) :
    ∃ K:ℝ,0<K ∧ ∀ n:ℕ,∀ (x:Vector (n+1)) (hx:‖x‖^2=(n+1:ℕ)),
      ∀ (h k:ℝ),|h| ≤ M → |k| ≤ M →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      (mixedConditionedLaw c x hx (WithLp.toLp 2 ![h,k])).real
        (sourcePosteriorOrderedRegularity (N:=n+1) (P:=μ.maxDegree) K)ᶜ ≤
        (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(n+1:ℕ)/2):=by
  obtain ⟨K,hK,hall⟩:=source_mixed_posterior_orderedRegularity μ hQ hnp hM
  refine ⟨K,hK,?_⟩
  intro n x hx h k hh hk
  dsimp only
  rw [source_mixed_physical_one_point_posterior_grouping n μ hQ hnp x hx h k]
  exact hall (n+1) n (by omega) x hx _
    (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx) h k hh hk

theorem source_value_physical_posterior_orderedRegularity (μ:FiniteMixture) {Q M:ℝ}
    (hQ:0<Q) (hM:0 ≤ M) :
    ∃ K:ℝ,0<K ∧ ∀ n:ℕ,∀ (x:Vector (n+1)) (hx:‖x‖^2=(n+1:ℕ)),
      ∀ h:ℝ,|h| ≤ M →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      (valueConditionedLaw c x hx h).real
        (sourcePosteriorOrderedRegularity (N:=n+1) (P:=μ.maxDegree) K)ᶜ ≤
        (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-(n+1:ℕ)/2):=by
  obtain ⟨K,hK,hall⟩:=source_value_posterior_orderedRegularity μ hQ hM
  refine ⟨K,hK,?_⟩
  intro n x hx h hh
  dsimp only
  rw [source_value_physical_one_point_posterior_grouping n μ hQ x hx h]
  exact hall (n+1) n (by omega) x hx _
    (tangentFrame_orthonormal x hx) (tangentFrame_tangent x hx) h hh

end
end SlowEquilibration.PairConditionalDeterminantMoments
