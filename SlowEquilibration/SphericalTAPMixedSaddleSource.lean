-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedCommonAnalyticChoice

@[expose] public section

/-! The literal derivative and negative-Hessian assertions of the mixed
contact saddle in manuscript Lemma 12.15, bundled at the actual source
parameters. -/

namespace SlowEquilibration.SphericalTAPMixedSaddleSource
noncomputable section
open SphericalTAPCertificate TwoAtomStationarity SphericalMarkedWindows
open ConditionedEntrance
open SphericalTAPMixedBandExponent SphericalTAPMixedJointHessianNeighborhood
open SphericalTAPMixedActualEnergyCross SphericalTAPMixedActualRadialHessian
open SphericalTAPMixedActualLatitudeStationarity
open SphericalTAPMixedActualLatitudeHessian
open SphericalTAPMixedJointHessianContinuity
set_option autoImplicit false

/-- All four first-derivative identities at the actual mixed source saddle,
including the energy slope of the literal radial and joint exponents. -/
theorem mixed_source_contact_first_derivatives
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let E := markE μ β x Q
    let K := markK μ β Q
    let q := Real.sqrt Q
    deriv (fun e => sourceRadialProfile μ Q e K) E = -(β*x) ∧
    deriv (sourceRadialProfile μ Q E) K = 0 ∧
    deriv (fun e => sourceMixedBandExponent μ β Q e K q) E = β-β*x ∧
    deriv (fun k => sourceMixedBandExponent μ β Q E k q) K = 0 ∧
    deriv (sourceMixedBandExponent μ β Q E K) q = 0 := by
  dsimp only
  let E := markE μ β x Q
  let K := markK μ β Q
  let q := Real.sqrt Q
  have hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < K :=
    sourceContact_markK_above_edge μ h
  have hE : sourceEnergySlope μ Q E K = β*x :=
    sourceEnergySlope_at_contact μ h hnp
  have hθ0 : valueTheta μ Q q = 1 := by
    simpa [q,sourceMixedMean] using
      (sourceMixedMean_contact μ h.overlap_range.1 hnp 1 0)
  have hθ1 : radialTheta μ Q q = 0 := by
    simpa [q,sourceMixedMean] using
      (sourceMixedMean_contact μ h.overlap_range.1 hnp 0 1)
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [sourceRadialProfile_energy_first μ h.overlap_range.1 E K hk,hE]
  · rw [(sourceRadialProfile_hasDerivAt μ h.overlap_range.1 E K hk).deriv]
    exact sourceContact_radial_profile_derivative_zero μ h hnp
  · rw [sourceMixedBandExponent_energy_first μ β h.overlap_range.1 E K q hk,
      hE,hθ0]
    ring
  · rw [sourceMixedBandExponent_radial_first μ β h.overlap_range.1 E K q hk,
      sourceContact_radial_profile_derivative_zero μ h hnp,hθ1]
    ring
  · exact sourceMixedBandExponent_latitude_deriv_contact μ h hnp

/-- The printed three second-derivative entries at contact, with the
energy-latitude entry and strict negative definiteness of the literal
`(k,a)` Hessian. -/
theorem mixed_source_contact_second_derivatives
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q) (hnp : μ.minDegree < μ.maxDegree) :
    let E := markE μ β x Q
    let K := markK μ β Q
    let q := Real.sqrt Q
    let ρ := markB μ Q/(markY β Q)^2
    let C := profileConstant x Q
    actualMixedHkk μ β Q ((E,K),q) =
      -sourceRadialCurvature μ Q-1/((markY β Q)^2-markB μ Q) ∧
    actualMixedHka μ β Q ((E,K),q) = β/q ∧
    actualMixedHaa μ β Q ((E,K),q) =
      -(1-ρ)*(1+Q-C*ρ)/(1-Q)^2 ∧
    deriv (fun a => deriv
      (fun e => sourceMixedBandExponent μ β Q e K a) E) q = 0 ∧
    ∀ u v : ℝ, u ≠ 0 ∨ v ≠ 0 →
      actualMixedHkk μ β Q ((E,K),q)*u^2+
        2*actualMixedHka μ β Q ((E,K),q)*u*v+
        actualMixedHaa μ β Q ((E,K),q)*v^2 < 0 := by
  dsimp only
  let E := markE μ β x Q
  let K := markK μ β Q
  let q := Real.sqrt Q
  let ρ := markB μ Q/(markY β Q)^2
  let C := profileConstant x Q
  have hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < K :=
    sourceContact_markK_above_edge μ h
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact sourceMixedBandExponent_radial_second_contact μ h q
  · change deriv (fun t => deriv
        (fun kk => sourceMixedBandExponent μ β Q E kk t) K) q = β/q
    rw [sourceMixedBandExponent_radial_latitude μ β h.overlap_range.1 E K q hk]
    rw [(SphericalTAPMixedContactDerivatives.mixed_regression_row_derivative_contact
      μ h.overlap_range.1 hnp).2]
    ring
  · exact sourceMixedBandExponent_latitude_second_contact μ h hnp
  · exact sourceMixedBandExponent_energy_latitude_contact μ β
      h.overlap_range.1 hnp E K hk
  · intro u v huv
    rw [show actualMixedHkk μ β Q ((E,K),q) =
      -sourceRadialCurvature μ Q-1/((markY β Q)^2-markB μ Q) from
        sourceMixedBandExponent_radial_second_contact μ h q]
    rw [show actualMixedHka μ β Q ((E,K),q) = β/q by
      change deriv (fun t => deriv
        (fun kk => sourceMixedBandExponent μ β Q E kk t) K) q = β/q
      rw [sourceMixedBandExponent_radial_latitude μ β h.overlap_range.1 E K q hk]
      rw [(SphericalTAPMixedContactDerivatives.mixed_regression_row_derivative_contact
        μ h.overlap_range.1 hnp).2]
      ring]
    rw [show actualMixedHaa μ β Q ((E,K),q) =
      -(1-ρ)*(1+Q-C*ρ)/(1-Q)^2 from
        sourceMixedBandExponent_latitude_second_contact μ h hnp]
    exact SphericalTAPMixedContactHessian.printed_mixed_contact_hessian_negative
      μ h hnp huv

/-- The joint exponent has the printed exact value at the physical central
latitude for every pair of score marks. -/
theorem mixed_source_contact_exact_value
    (μ : FiniteMixture) {β Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (e k : ℝ) :
    sourceMixedBandExponent μ β Q e k (Real.sqrt Q) =
      sourceRadialProfile μ Q e k+β*e+
        (Real.log (1-Q)+β^2*residualAtOne μ Q)/2 :=
  sourceMixedBandExponent_contact μ hQ hnp e k

end
end SlowEquilibration.SphericalTAPMixedSaddleSource
