-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceLatitudeSourceCorrectionBound
public import SlowEquilibration.ConditionedEntranceJointHamiltonian

/-! Axis continuity of the literal source correction follows from the
already constructed joint source Hamiltonian, with the constant cutoff.
The actual original field is subtracted pointwise. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open SphericalModel SphericalForm SphericalGaussianJet ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal source correction is continuous in the actual frozen axis. -/
theorem sourceRegressionCorrection_axis_continuous {N : ℕ} (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree)
    (J : Disorder N μ.maxDegree) (e k : ℝ) (x : Vector N) :
    Continuous (fun u => sourceRegressionCorrection μ Q hQ hnp J u e k x) := by
  have hfull : Continuous (fun u : Vector N => sourceSmoothCutoffField μ Q hQ hnp J u e k 1 (fun _ => 1) x) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp 1 (fun _ => 1) continuous_const).comp
      (show Continuous (fun u : Vector N => ((J,(u,(e,k))),x)) by fun_prop)
  have he : (fun u : Vector N => sourceRegressionCorrection μ Q hQ hnp J u e k x)=
      (fun u => sourceSmoothCutoffField μ Q hQ hnp J u e k 1 (fun _ => 1) x-fieldOfMixture μ J x) := by
    funext u
    rw [sourceSmoothCutoffField_eq]
    simp only [one_mul]
    ring
  rw [he]
  exact hfull.sub continuous_const

end
end SlowEquilibration.EntranceLatitudeTangentObservable
