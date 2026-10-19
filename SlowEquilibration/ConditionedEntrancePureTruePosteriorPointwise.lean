-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSourceTruePosteriorPointwise
public import SlowEquilibration.ConditionedEntrancePureJointCapHit

/-! Exact cap-hit identity for the proper pure value/tangent posterior and
the uncut pure source Hamiltonian, before averaging either Gaussian law. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SphericalGaussianJet
open SphericalPosteriorMaps WholeFieldRegression SphericalSmoothCapHitDriftCongruence
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 500000

theorem originalTrueCapHitProbability_pureValuePosterior_eq_source_one
    (n p : ℕ) (hp : 2 ≤ p) (c : ℝ) (hc : 0 < c)
    {Q : ℝ} (hQ : 0 < Q)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (e α β : ℝ) (T : ℝ≥0)
    (g : EuclideanDisorder (n+1) (FiniteMixture.pure p hp c hc).maxDegree) :
    originalTrueCapHitProbability (FiniteMixture.pure p hp c hc) β T (α/2) u
      (unpackCLM (n+1) (FiniteMixture.pure p hp c hc).maxDegree
        (valuePosterior n (FiniteMixture.pure p hp c hc) Q u e g)) =
    pureSourceCapHitProbability p hp c hc Q α (fun _ => 1)
      contDiff_const β T (unpackDisorder g,(u,(e,0))) := by
  let μ := FiniteMixture.pure p hp c hc
  let J' := unpackCLM (n+1) μ.maxDegree (valuePosterior n μ Q u e g)
  let J := unpackDisorder g
  have hField (y : Vector (n+1)) :
      fieldOfMixture μ J' y =
        pureSourceSmoothCutoffField p hp c hc Q J u e α (fun _ => 1) y := by
    have hp' := (pureSourceSmoothCutoffField_one_eq_actual_posterior
      n p hp c hc hQ u hu e α g y).symm
    simpa only [μ,J',J,unpackCLM_apply] using hp'
  have hDrift (y : Vector (n+1)) :
      jointSpatialGradient (originalTrueJointHamiltonian μ) (J',y) =
      jointSpatialGradient
        (pureSourceJointHamiltonian p hp c hc Q α (fun _ => 1))
        ((J,(u,(e,0))),y) := by
    change gradient (fun x => fieldOfMixture μ J' x) y =
      gradient (fun x => pureSourceSmoothCutoffField p hp c hc Q J u e α
        (fun _ => 1) x) y
    exact congrArg (fun f : Vector (n+1) → ℝ => gradient f y) (funext hField)
  exact uniformCapHitProbability_eq_of_fixed_drift_eq β
    (jointSpatialGradient (originalTrueJointHamiltonian μ))
    (jointSpatialGradient_contDiff _ (originalTrueJointHamiltonian_contDiff μ))
    (jointSpatialGradient (pureSourceJointHamiltonian p hp c hc Q α (fun _ => 1)))
    (pureSourceJointSpatialGradient_contDiff p hp c hc Q α
      (fun _ : ℝ => (1 : ℝ)) contDiff_const)
    T (α/2) u J' (J,(u,(e,0))) hDrift

end SlowEquilibration.ConditionedEntrance
