-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedActualRadialHessian
public import SlowEquilibration.SphericalMarkedContactGradient

@[expose] public section

/-! The literal mixed exponent's energy-latitude derivative vanishes at
physical contact. -/

namespace SlowEquilibration.SphericalTAPMixedActualEnergyCross
noncomputable section
open Set SphericalTAPMixedBandExponent ConditionedEntrance SphericalMarkedWindows
open SphericalTAPMixedContactDerivatives
set_option autoImplicit false

theorem sourceRadialProfile_energy_first (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (e k : ℝ)
    (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    deriv (fun ee => sourceRadialProfile μ Q ee k) e =
      -sourceEnergySlope μ Q e k := by
  have hcurve : HasDerivAt (fun ee : ℝ => (ee,k)) (1,0) e :=
    (hasDerivAt_id e).prodMk (hasDerivAt_const e k)
  have hh := (sourceMarkedComplexity_hasFDerivAt μ hQ e k hk).comp_hasDerivAt
    e hcurve
  change HasDerivAt (fun ee => sourceRadialProfile μ Q ee k)
    (sourceMarkedGradient μ Q e k (1,0)) e at hh
  rw [hh.deriv]
  simp [sourceMarkedGradient]

theorem sourceMixedBandExponent_energy_first (μ : FiniteMixture) (β : ℝ)
    {Q : ℝ} (hQ : 0 < Q) (e k a : ℝ)
    (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    deriv (fun ee => sourceMixedBandExponent μ β Q ee k a) e =
      -sourceEnergySlope μ Q e k+β*valueTheta μ Q a := by
  have hrad : HasDerivAt (fun ee => sourceRadialProfile μ Q ee k)
      (-sourceEnergySlope μ Q e k) e := by
    have hcurve : HasDerivAt (fun ee : ℝ => (ee,k)) (1,0) e :=
      (hasDerivAt_id e).prodMk (hasDerivAt_const e k)
    have hh := (sourceMarkedComplexity_hasFDerivAt μ hQ e k hk).comp_hasDerivAt
      e hcurve
    change HasDerivAt (fun ee => sourceRadialProfile μ Q ee k)
      (sourceMarkedGradient μ Q e k (1,0)) e at hh
    convert hh using 1
    simp [sourceMarkedGradient]
  have hm : HasDerivAt (fun ee => sourceMixedMean μ Q ee k a)
      (valueTheta μ Q a) e := by
    unfold sourceMixedMean
    convert ((hasDerivAt_id e).const_mul (valueTheta μ Q a)).add_const
      (radialTheta μ Q a*k) using 1
    · funext ee
      simp only [id_eq]
    · ring
  have hxi : HasDerivAt (fun ee => sourceMixedXi μ β Q ee k a)
      (β*valueTheta μ Q a) e := by
    unfold sourceMixedXi
    convert (hm.const_mul β).add_const (β^2/2*sourceMixedVariance μ Q a) using 1
  have hh := (hrad.add hxi).add_const (Real.log (1-a^2)/2)
  change HasDerivAt (fun ee => sourceMixedBandExponent μ β Q ee k a) _ e at hh
  exact hh.deriv

/-- The actual mixed energy-latitude Hessian entry of `g` is zero at
physical contact, uniformly in the exterior energy and radial marks. -/
theorem sourceMixedBandExponent_energy_latitude_contact
    (μ : FiniteMixture) (β : ℝ) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (e k : ℝ) (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    deriv (fun a => deriv
      (fun ee => sourceMixedBandExponent μ β Q ee k a) e) (Real.sqrt Q)=0 := by
  have hfun : (fun a => deriv
      (fun ee => sourceMixedBandExponent μ β Q ee k a) e) =
      fun a => -sourceEnergySlope μ Q e k+β*valueTheta μ Q a := by
    funext a
    exact sourceMixedBandExponent_energy_first μ β hQ e k a hk
  rw [hfun]
  have hh := ((valueTheta_hasDerivAt μ Q (Real.sqrt Q)).const_mul β).const_add
    (-sourceEnergySlope μ Q e k)
  rw [hh.deriv,(mixed_regression_row_derivative_contact μ hQ hnp).1]
  ring

end
end SlowEquilibration.SphericalTAPMixedActualEnergyCross
