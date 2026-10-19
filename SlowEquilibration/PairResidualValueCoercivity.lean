-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PairValueResidualCovariance
public import SlowEquilibration.PairResidualScoreCoercivity
public import SlowEquilibration.ValueObservationSmallOverlap
public import SlowEquilibration.GaussianResidualCoercivity

/-! Proper two-height residual covariance lower bounds. This includes pure
models and never introduces the redundant radial score. -/
@[expose] public section
namespace SlowEquilibration.PairObservationSmallOverlap
noncomputable section
open Function SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- Constants precede dimension and point targets. Both posterior value and
conditioning gradient Grams are the literal maps of the actual tensor field. -/
theorem uniform_residual_pair_value_coercivity (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hdeg : 4 ≤ μ.minDegree) :
    ∃ ρ0 δ : ℝ,0 < ρ0 ∧ 0 < δ ∧ ∀ (N m : ℕ) (_hN : 0 < N) (x y : Vector N),
      ‖x‖^2=(N:ℝ) → ‖y‖^2=(N:ℝ) →
      ∀ (e f : Fin m → Vector N),Orthonormal ℝ e → Orthonormal ℝ f →
      (∀ i,inner ℝ (e i) x=0) → (∀ i,inner ℝ (f i) y=0) → |overlap x y| ≤ ρ0 →
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      let A:=pairGradient c x y e f
      let B:=residualPairValue c x y e f
      CoerciveObservation A δ ∧ Surjective A ∧ ‖(gram A).inverse‖ ≤ 1/δ ∧
        CoerciveObservation B δ ∧ Surjective B ∧ ‖(gram B).inverse‖ ≤ 1/δ := by
  obtain ⟨ρ0,δ,hρ0,hδ,hall⟩:=uniform_value_pair_nondegenerate μ hQ hdeg
  refine ⟨ρ0,δ,hρ0,hδ,?_⟩
  intro N m hN x y hx hy e f he hf htanx htany hρ
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hfull:=groupedValuePair_coercive c x y e f
    (hall N m hN x y hx hy e f he hf htanx htany hρ).1
  have hGrad:=pair_snd_coercive (valuePair c x y) (pairGradient c x y e f) hfull
  have hA:=observation_surjective _ hδ hGrad
  have hres:=residual_coercivity (pairGradient c x y e f) hA (valuePair c x y) hδ.le hfull
  exact ⟨hGrad,hA,gram_inverse_norm_le _ hδ hGrad,hres,
    observation_surjective _ hδ hres,gram_inverse_norm_le _ hδ hres⟩

end
end SlowEquilibration.PairObservationSmallOverlap
