-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalSmoothCapHitDriftCongruence
public import SlowEquilibration.SphericalOriginalPosteriorSourceField
public import SlowEquilibration.ConditionedEntranceJointSourceCapHit

/-! Pointwise true-process cap-hit covariance under the actual mixed
Gaussian regression map, before integrating either Gaussian law. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.ConditionedEntrance
open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet SphericalMarkedWindows
open PairConditionalDeterminantMoments
open SphericalSmoothParameter SphericalSmoothCapHitDriftCongruence
open SphericalCriticalLatitude SphericalPosteriorMaps WholeFieldRegression
open scoped NNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

def originalTrueJointHamiltonian {N : ℕ} (μ : FiniteMixture) :
    Disorder N μ.maxDegree × Vector N → ℝ :=
  fun z => fieldOfMixture μ z.1 z.2

theorem originalTrueJointHamiltonian_contDiff {N : ℕ} (μ : FiniteMixture) :
    ContDiff ℝ 2 (originalTrueJointHamiltonian (N := N) μ) := by
  change ContDiff ℝ 2 (fun z : Disorder N μ.maxDegree × Vector N =>
    field (mixtureCoefficients μ) z.1 z.2)
  exact (source_field_joint_contDiff (N := N) (mixtureCoefficients μ)).of_le (by simp)

def originalTrueCapHitProbability {N : ℕ} (μ : FiniteMixture)
    (β : ℝ) (T : ℝ≥0) (a : ℝ) (u : Vector N)
    (J : Disorder N μ.maxDegree) : ℝ :=
  uniformCapHitProbability β
    (jointSpatialGradient (originalTrueJointHamiltonian μ))
    (jointSpatialGradient_contDiff _ (originalTrueJointHamiltonian_contDiff μ))
    T a (u,J)

theorem originalTrueCapHitProbability_measurable {N : ℕ} (μ : FiniteMixture)
    (β : ℝ) (T : ℝ≥0) (a : ℝ) (u : Vector N) :
    Measurable (originalTrueCapHitProbability μ β T a u) := by
  exact (uniformCapHitProbability_measurable β _ _ T a).comp
    (measurable_const.prodMk measurable_id)

theorem originalTrueCapHitProbability_mem_unit {N : ℕ} (μ : FiniteMixture)
    (β : ℝ) (T : ℝ≥0) (a : ℝ) (u : Vector N)
    (J : Disorder N μ.maxDegree) :
    originalTrueCapHitProbability μ β T a u J ∈ Set.Icc 0 1 :=
  uniformCapHitProbability_mem_unit β _ _ T a (u,J)

theorem originalTrueCapHitProbability_mixedPosterior_eq_source_one
    (n : ℕ) (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ))
    (e k α β : ℝ) (T : ℝ≥0)
    (g : EuclideanDisorder (n+1) μ.maxDegree) :
    originalTrueCapHitProbability μ β T (α/2) u
      (unpackCLM (n+1) μ.maxDegree
        (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)) =
    sourceCapHitProbability μ Q hQ hnp α (fun _ => 1)
      (contDiff_const) β T (unpackDisorder g,(u,(e,k))) := by
  let J' := unpackCLM (n+1) μ.maxDegree
    (mixedPosterior n μ Q u (scorePairEquiv (e,k)) g)
  let J := unpackDisorder g
  have hField (y : Vector (n+1)) :
      fieldOfMixture μ J' y =
        sourceSmoothCutoffField μ Q hQ hnp J u e k α (fun _ => 1) y := by
    have hp := actual_mixedPosterior_original_field n μ hQ hnp u hu e k g y
    have hs := sourceSmoothCutoffField_eq μ Q hQ hnp J u e k α
      (fun _ => 1) y
    have hss : fieldOfMixture μ J y +
        sourceRegressionCorrection μ Q hQ hnp J u e k y =
          sourceSmoothCutoffField μ Q hQ hnp J u e k α (fun _ => 1) y := by
      simpa only [one_mul] using hs.symm
    simpa only [J',J,unpackCLM_apply] using hp.trans hss
  have hDrift (y : Vector (n+1)) :
      jointSpatialGradient (originalTrueJointHamiltonian μ) (J',y) =
      jointSpatialGradient
        (sourceJointHamiltonian μ Q hQ hnp α (fun _ => 1))
        ((J,(u,(e,k))),y) := by
    change gradient (fun x => fieldOfMixture μ J' x) y =
      gradient (fun x => sourceSmoothCutoffField μ Q hQ hnp J u e k α
        (fun _ => 1) x) y
    exact congrArg (fun f : Vector (n+1) → ℝ => gradient f y) (funext hField)
  exact uniformCapHitProbability_eq_of_fixed_drift_eq β
    (jointSpatialGradient (originalTrueJointHamiltonian μ))
    (jointSpatialGradient_contDiff _ (originalTrueJointHamiltonian_contDiff μ))
    (jointSpatialGradient (sourceJointHamiltonian μ Q hQ hnp α (fun _ => 1)))
    (sourceJointSpatialGradient_contDiff μ Q hQ hnp α
      (fun _ : ℝ => (1 : ℝ)) contDiff_const)
    T (α/2) u J' (J,(u,(e,k))) hDrift

end SlowEquilibration.ConditionedEntrance
