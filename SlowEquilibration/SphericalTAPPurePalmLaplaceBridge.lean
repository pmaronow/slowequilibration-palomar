-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPureQuadraticRealTransfer
public import SlowEquilibration.SphericalTAPMixedPalmDensityIdentity
public import SlowEquilibration.SphericalTAPCriticalPureLatitudeContactValue

@[expose] public section

/-! The genuine spherical latitude Jacobian has precisely the pure
Laplace exponent's entropy term, including the N−3 dimensional power. -/

namespace SlowEquilibration.SphericalTAPPurePalmLaplaceBridge
noncomputable section
open Set MeasureTheory SphericalModel
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeVariance
open SphericalTAPMixedPalmDensityIdentity
set_option autoImplicit false

theorem pure_palm_entropy_density_identity
    (d : ℕ) (hd : 1 ≤ d)
    (p : ℕ) (alpha Q β e a : ℝ) (ha : a ∈ Ioo (-1:ℝ) 1) :
    (Real.sqrt (1-a^2))^(d-1) *
        Real.exp (((d+2:ℕ):ℝ)*
          (β*e*(a/Real.sqrt Q)^p+
            β^2/2*sourcePureLatitudeVariance p alpha a)) =
      (1-a^2)^(-(3/2:ℝ)) *
        Real.exp (((d+2:ℕ):ℝ)*
          sourcePureLatitudeExponent p alpha Q β e a) := by
  have hh := mixed_palm_entropy_density_identity d hd a ha
  unfold sourcePureLatitudeExponent
  calc
    _ = ((1-a^2)^(-(3/2:ℝ)) *
          Real.exp (((d+2:ℕ):ℝ)*Real.log (1-a^2)/2)) *
          Real.exp (((d+2:ℕ):ℝ)*
            (β*e*(a/Real.sqrt Q)^p+
              β^2/2*sourcePureLatitudeVariance p alpha a)) := by rw [hh]
    _ = _ := by
      rw [mul_assoc,←Real.exp_add]
      congr 1
      ring

theorem pure_palm_weighted_density_eq_laplace_integral
    (d : ℕ) (hd : 1 ≤ d)
    (p : ℕ) (alpha Q β e q b C detMean : ℝ)
    (hband : Icc (q-b) (q+b) ⊆ Ioo (-1:ℝ) 1) :
    (∫ a in Icc (q-b) (q+b),
      (Real.sqrt (1-a^2))^(d-1) *
        (C*detMean*Real.exp (((d+2:ℕ):ℝ)*
          (β*e*(a/Real.sqrt Q)^p+
            β^2/2*sourcePureLatitudeVariance p alpha a)))) =
      C*detMean * (∫ a in Icc (q-b) (q+b),
        (1-a^2)^(-(3/2:ℝ)) *
          Real.exp (((d+2:ℕ):ℝ)*
            sourcePureLatitudeExponent p alpha Q β e a)) := by
  have hpoint (a : ℝ) (ha : a ∈ Icc (q-b) (q+b)) :
      (Real.sqrt (1-a^2))^(d-1) *
        (C*detMean*Real.exp (((d+2:ℕ):ℝ)*
          (β*e*(a/Real.sqrt Q)^p+
            β^2/2*sourcePureLatitudeVariance p alpha a))) =
      C*detMean*((1-a^2)^(-(3/2:ℝ)) *
        Real.exp (((d+2:ℕ):ℝ)*
          sourcePureLatitudeExponent p alpha Q β e a)) := by
    rw [← pure_palm_entropy_density_identity d hd p alpha Q β e a (hband ha)]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc hpoint]
  rw [integral_const_mul]

end
end SlowEquilibration.SphericalTAPPurePalmLaplaceBridge
