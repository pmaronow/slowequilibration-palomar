-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPerturbationGibbsKernel
public import SlowEquilibration.GaussianSelectedReplicaIBP

@[expose] public section

/-! Exact active-coordinate factorization of the actual parameterized
tensor Gibbs field. It links the joint kernel to the selected Gaussian IBP. -/
namespace SlowEquilibration.SphericalPositivePerturbation
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology BigOperators RealInnerProductSpace
open SphericalAging.FiniteModel GaussianSpinInterpolation GaussianSpinComparison
  GaussianPerturbationParameter GaussianPerturbationSelfAveraging
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

theorem coefficientOperator_update {N K : ℕ} (x : Fin K → ℝ) (p : Fin K) (t : ℝ) :
    coefficientOperator (N:=N) (Function.update x p t)=
      (coefficientOperator (Function.update x p 1)).comp (parameterOperator (degreeLabel p) t) := by
  classical
  ext w i
  change (Function.update x p t) i.1*w i=
    (Function.update x p 1) i.1*
      ((if degreeLabel p i=false then (1:ℝ) else 0)*w i+
        t*((if degreeLabel p i=true then (1:ℝ) else 0)*w i))
  by_cases hi : i.1=p
  · simp [degreeLabel,hi]
  · simp [degreeLabel,hi]

theorem unitLinear_active_slice {N K : ℕ} (v : ℝ) (x : Fin K → ℝ) (p : Fin K) (t : ℝ)
    (z : UnitSpin N) (w : PerturbationDisorder N K) :
    parameterLinear (unitLinear (coefficients v (Function.update x p 1))) (degreeLabel p) t z w=
      unitLinear (coefficients v (Function.update x p t)) z w := by
  change unitLinear (coefficients v (Function.update x p 1)) z (parameterOperator (degreeLabel p) t w)=_
  calc
    _ = unitLinear (coefficients (K:=K) v (fun _ => 1)) z
        (coefficientOperator (Function.update x p 1) (parameterOperator (degreeLabel p) t w)) :=
      (unitLinear_coefficientOperator v (Function.update x p 1) z _).symm
    _ = unitLinear (coefficients (K:=K) v (fun _ => 1)) z
        (coefficientOperator (Function.update x p t) w) := by
      congr 1
      exact congrArg (fun D : PerturbationDisorder N K →L[ℝ] PerturbationDisorder N K => D w)
        (coefficientOperator_update x p t).symm
    _ = _ := unitLinear_coefficientOperator v (Function.update x p t) z w

theorem parameterizedGibbsKernel_active_slice {N K : ℕ} (ν : Measure (UnitSpin N)) [IsProbabilityMeasure ν]
    {v : ℝ} (hv : 0≤v) (x : Fin K → ℝ) (p : Fin K) (t : ℝ) (w : PerturbationDisorder N K) :
    parameterizedGibbsKernel ν v (Function.update x p t,w)=
      gibbsMeasure ν
        (parameterLinear (unitLinear (coefficients v (Function.update x p 1))) (degreeLabel p) t) w := by
  rw [parameterizedGibbsKernel_apply ν hv]
  have hm : GaussianSpinInterpolation.moment ν (fun _ => 1)
      (parameterLinear (unitLinear (coefficients v (Function.update x p 1))) (degreeLabel p) t) w=
      GaussianSpinInterpolation.moment ν (fun _ => 1) (unitLinear (coefficients v (Function.update x p t))) w := by
    unfold GaussianSpinInterpolation.moment weight
    apply integral_congr_ae
    exact .of_forall fun z => by
      change 1*Real.exp (parameterLinear (unitLinear (coefficients v (Function.update x p 1)))
          (degreeLabel p) t z w)=1*Real.exp (unitLinear (coefficients v (Function.update x p t)) z w)
      rw [unitLinear_active_slice]
  unfold gibbsMeasure
  rw [hm]
  congr 1
  funext z
  rw [unitLinear_active_slice]

end
end SlowEquilibration.SphericalPositivePerturbation
