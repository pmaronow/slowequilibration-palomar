-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePhysicalPairSelectionRegularity
public import SlowEquilibration.SphericalConditionedEntranceCorrection

/-! Actual jointly continuous center jets and scalar regression factors. -/
@[expose] public section
noncomputable section
open scoped InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SphericalGaussianJet PairConditionalDeterminantMoments
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem radialJet_jointContinuous {N P : ℕ} (c : Degree P→ℝ) :
    Continuous (fun z : Disorder N P×Vector N => jet c 1 z.2 (fun _ => z.2) z.1) := by
  have hd := (source_param_fderiv_contDiff (fun (J : Disorder N P) (x : Vector N) => field c J x)
    (source_field_joint_contDiff c)).continuous
  simpa only [jet,iteratedFDeriv_one_apply] using hd.clm_apply continuous_snd

theorem valueTheta_continuous (μ : FiniteMixture) (Q : ℝ) : Continuous (valueTheta μ Q) :=
  (show Differentiable ℝ (valueTheta μ Q) from fun r => (valueTheta_hasDerivAt μ Q r).differentiableAt).continuous

theorem radialTheta_continuous (μ : FiniteMixture) (Q : ℝ) : Continuous (radialTheta μ Q) :=
  (show Differentiable ℝ (radialTheta μ Q) from fun r => (radialTheta_hasDerivAt μ Q r).differentiableAt).continuous

theorem tangentTheta_continuous (μ : FiniteMixture) (Q : ℝ) : Continuous (tangentTheta μ Q) :=
  (show Differentiable ℝ (tangentTheta μ Q) from fun r => (tangentTheta_hasDerivAt μ Q r).differentiableAt).continuous

end SlowEquilibration.ConditionedEntrance
