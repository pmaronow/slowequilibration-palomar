-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedActualLatitudeStationarity

@[expose] public section

/-! The literal mixed joint exponent has the true marked-complexity radial
second derivative throughout the exterior region. -/

namespace SlowEquilibration.SphericalTAPMixedActualRadialHessian
noncomputable section
open Set SphericalTAPMixedBandExponent ConditionedEntrance SphericalMarkedWindows
open scoped Topology
set_option autoImplicit false

theorem sourceMixedBandExponent_radial_first (μ : FiniteMixture) (β : ℝ)
    {Q : ℝ} (hQ : 0 < Q) (e k a : ℝ)
    (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    deriv (fun kk => sourceMixedBandExponent μ β Q e kk a) k =
      sourceRadialProfileDerivative μ Q e k+β*radialTheta μ Q a := by
  have hm : HasDerivAt (fun kk => sourceMixedMean μ Q e kk a)
      (radialTheta μ Q a) k := by
    unfold sourceMixedMean
    convert (hasDerivAt_const k (valueTheta μ Q a*e)).add
      ((hasDerivAt_id k).const_mul (radialTheta μ Q a)) using 1
    · funext kk
      rfl
    · ring
  have hxi : HasDerivAt (fun kk => sourceMixedXi μ β Q e kk a)
      (β*radialTheta μ Q a) k := by
    unfold sourceMixedXi
    convert (hm.const_mul β).add_const (β^2/2*sourceMixedVariance μ Q a) using 1
  have hg := (sourceRadialProfile_hasDerivAt μ hQ e k hk).add hxi
  have hmain : HasDerivAt (fun kk => sourceMixedBandExponent μ β Q e kk a)
      (sourceRadialProfileDerivative μ Q e k+β*radialTheta μ Q a) k := by
    convert hg.add_const (Real.log (1-a^2)/2) using 1
    · funext kk
      rfl
    · unfold sourceRadialProfileDerivative
      simp only [div_eq_mul_inv]
  exact hmain.deriv

/-- The actual `∂ₖ²g` equals the radial Hessian of the source marked
complexity; no auxiliary comparison profile enters this identity. -/
theorem sourceMixedBandExponent_radial_second (μ : FiniteMixture) (β : ℝ)
    {Q : ℝ} (hQ : 0 < Q) (e k a : ℝ)
    (hk : 2*Real.sqrt (Q^2*μ.xi2 Q) < k) :
    deriv (deriv (fun kk => sourceMixedBandExponent μ β Q e kk a)) k =
      deriv (sourceRadialProfileDerivative μ Q e) k := by
  have he : deriv (fun kk => sourceMixedBandExponent μ β Q e kk a) =ᶠ[𝓝 k]
      (fun kk => sourceRadialProfileDerivative μ Q e kk+
        β*radialTheta μ Q a) := by
    filter_upwards [isOpen_Ioi.mem_nhds hk] with kk hkk
    exact sourceMixedBandExponent_radial_first μ β hQ e kk a hkk
  rw [he.deriv_eq]
  have hh := (sourceRadialProfileDerivative_hasDerivAt μ hQ e k hk).add_const
    (β*radialTheta μ Q a)
  rw [(sourceRadialProfileDerivative_hasDerivAt μ hQ e k hk).deriv]
  exact hh.deriv

theorem sourceMixedBandExponent_radial_second_contact
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : SphericalTAPCertificate.Certificate μ β x Q)
    (a : ℝ) :
    deriv (deriv (fun kk => sourceMixedBandExponent μ β Q
      (TwoAtomStationarity.markE μ β x Q) kk a))
        (TwoAtomStationarity.markK μ β Q) =
      -sourceRadialCurvature μ Q-
        1/((TwoAtomStationarity.markY β Q)^2-
          TwoAtomStationarity.markB μ Q) := by
  rw [sourceMixedBandExponent_radial_second μ β h.overlap_range.1
      (TwoAtomStationarity.markE μ β x Q)
      (TwoAtomStationarity.markK μ β Q) a
      (sourceContact_markK_above_edge μ h),
    SphericalTAPMixedContactHessian.sourceRadialProfile_second_derivative_contact μ h]

end
end SlowEquilibration.SphericalTAPMixedActualRadialHessian
