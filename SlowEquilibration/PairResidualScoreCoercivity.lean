-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairScoreCovariancePerturbation
public import SlowEquilibration.GaussianResidualCoercivity

/-! Actual uniform covariance lower bounds for both tangent gradients and
for the residual pair scores after conditioning at both gradient zeros. -/
@[expose] public section
namespace SlowEquilibration.GaussianObservationCoercivity
noncomputable section
open Function GaussianRegression
open scoped RealInnerProductSpace
variable {E F G : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
lemma pair_snd_coercive (A : E →L[ℝ] F) (B : E →L[ℝ] G) {α : ℝ}
    (h : CoerciveObservation (pairHilbert A B) α) : CoerciveObservation B α := by
  intro v
  have hh:=h (WithLp.toLp 2 (0,v))
  simpa only [pairHilbert_adjoint,WithLp.toLp_fst,WithLp.toLp_snd,map_zero,zero_add,
    WithLp.prod_norm_sq_eq_of_L2,norm_zero,zero_pow (by norm_num : 2≠0),zero_add] using hh
end
end SlowEquilibration.GaussianObservationCoercivity

namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Constants precede dimension and point targets. Both posterior score and
conditioning gradient Grams are the literal maps of the actual tensor field. -/
theorem uniform_residual_pair_score_coercivity (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hdeg : 4 ≤ μ.minDegree) :
    ∃ ρ0 δ : ℝ,0 < ρ0 ∧ 0 < δ ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x y : Vector N),
      ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) → |overlap x y| ≤ ρ0 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairGradient c x y e f
      let B:=residualPairScore c x y e f
      CoerciveObservation A δ ∧ Surjective A ∧ ‖(gram A).inverse‖ ≤ 1/δ ∧
        CoerciveObservation B δ ∧ Surjective B ∧ ‖(gram B).inverse‖ ≤ 1/δ := by
  obtain ⟨ρ0,δ,hρ0,hδ,hall⟩:=uniform_mixed_pair_nondegenerate μ hQ hnp hdeg
  refine ⟨ρ0,δ,hρ0,hδ,?_⟩
  intro N m hN x y hx hy e f he hf htanx htany hρ
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hfull:=groupedMixedPair_coercive c x y e f
    (hall N m hN x y hx hy e f he hf htanx htany hρ).1
  have hGrad:=pair_snd_coercive (scorePair c x y) (pairGradient c x y e f) hfull
  have hA:=observation_surjective _ hδ hGrad
  have hres:=residual_coercivity (pairGradient c x y e f) hA (scorePair c x y) hδ.le hfull
  exact ⟨hGrad,hA,gram_inverse_norm_le _ hδ hGrad,hres,
    observation_surjective _ hδ hres,gram_inverse_norm_le _ hδ hres⟩

end
end SlowEquilibration.PairObservationSmallOverlap
