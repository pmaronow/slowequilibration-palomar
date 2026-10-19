-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedPalmCoarea
public import SlowEquilibration.SphericalTAPPhysicalAngularSlice

@[expose] public section

/-! The exact Jacobian and all-critical radial density appearing after
determinant-weighted physical coarea combine into the manuscript's mixed
two-variable Laplace integrand. -/

namespace SlowEquilibration.SphericalTAPMixedPalmDensityIdentity
noncomputable section
open Set SphericalModel SphericalTAPMixedPhysicalRadialBridge
open SphericalTAPMixedPhysicalJointLaplace SphericalTAPMixedBandExponent
open SphericalTAPCriticalEnergyPalmAverage SphericalTAPPhysicalAngularSlice
open SphericalMarkedWindows SphericalTAPMixedPhysicalChi
set_option autoImplicit false

/-- The angular entropy has exactly the source's `N-3`, rather than `N-2`,
power because the transverse sphere is one dimension below ambient. -/
theorem mixed_palm_entropy_density_identity
    (d : ℕ) (hd : 1 ≤ d) (a : ℝ) (ha : a ∈ Ioo (-1:ℝ) 1) :
    (1-a^2)^(-(3/2:ℝ)) *
      Real.exp (((d+2:ℕ):ℝ)*Real.log (1-a^2)/2) =
      (Real.sqrt (1-a^2))^(d-1) := by
  have ht : 0 < 1-a^2 := by nlinarith [ha.1,ha.2]
  have hphys : Real.exp ((((d-1:ℕ):ℝ)/2)*Real.log (1-a^2)) =
      (Real.sqrt (1-a^2))^(d-1) := by
    simpa only [show d+1-2=d-1 by omega] using
      physicalEntropy_exp_eq_sqrt_pow (d+1) a ha
  rw [Real.rpow_def_of_pos ht,← Real.exp_add]
  rw [← hphys]
  congr 1
  rw [Nat.cast_sub hd]
  push_cast
  ring

/-- The literal determinant-weighted coarea density equals the joint
source Laplace density after removal of its common radial constant. -/
theorem mixed_palm_density_eq_source_joint
    (d : ℕ) (hd : 1 ≤ d) (μ : FiniteMixture)
    {Q : ℝ} (hQ : 0 < Q) (β e k a : ℝ)
    (ha : a ∈ Ioo (-1:ℝ) 1) :
    sourceAllCriticalRadialWeight d μ Q e k *
        (Real.sqrt (1-a^2))^(d-1) *
        Real.exp (((d+2:ℕ):ℝ)*sourceMixedXi μ β Q e k a) =
      Real.exp (((d+2:ℕ):ℝ)*
        (Real.log (Q*μ.xi1 Q)/2-1/2)) *
        sourceMixedJointIntegrand d μ β Q e (k,a) := by
  let N : ℝ := ((d+2:ℕ):ℝ)
  let T := 1-a^2
  let θ := sourceRadialProfile μ Q e k
  let ξ := sourceMixedXi μ β Q e k a
  have hexp : Real.exp (N*sourceMixedBandExponent μ β Q e k a) =
      Real.exp (N*θ)*Real.exp (N*ξ)*
        Real.exp (N*Real.log T/2) := by
    unfold sourceMixedBandExponent
    change Real.exp (N*(θ+ξ+Real.log T/2)) = _
    rw [show N*(θ+ξ+Real.log T/2) = N*θ+N*ξ+N*Real.log T/2 by ring,
      Real.exp_add,Real.exp_add]
  rw [sourceAllCriticalRadialWeight_eq_chi_profile d μ hQ e k]
  unfold sourceMixedJointIntegrand
  rw [hexp]
  have hentropy := mixed_palm_entropy_density_identity d hd a ha
  change (sourceMixedChi d μ Q k *
      Real.exp (N*(Real.log (Q*μ.xi1 Q)/2-1/2)) *
      Real.exp (N*θ))*
      (Real.sqrt T)^(d-1)*Real.exp (N*ξ) =
    Real.exp (N*(Real.log (Q*μ.xi1 Q)/2-1/2)) *
      (sourceMixedChi d μ Q k*T^(-(3/2:ℝ)) *
        (Real.exp (N*θ)*Real.exp (N*ξ)*Real.exp (N*Real.log T/2)))
  rw [← hentropy]
  ring

end
end SlowEquilibration.SphericalTAPMixedPalmDensityIdentity
