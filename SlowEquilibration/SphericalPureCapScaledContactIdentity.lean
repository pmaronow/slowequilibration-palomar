-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapTailScale
public import SlowEquilibration.SphericalPureLaplaceUniformLogPhysical
public import SlowEquilibration.SphericalTAPCriticalPureLatitudeContactValue

@[expose] public section

/-! Exact cancellation of the source logarithmic energy centering against
the polynomial annealed scale at the pure contact latitude. -/

namespace SlowEquilibration.SphericalPureCapScaledContactIdentity
noncomputable section
open Set MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile SphericalPureLaplaceRegularity
open SphericalPureCapCenteringIdentity SphericalPureCapTailScale
open SphericalPureCapRawProfileIdentity PureStationarity
open SphericalPureCapSourceScalars
open SphericalTAPCriticalPureLatitudeContactValue
open SphericalModel
set_option autoImplicit false

/-- Pure contact cancellation, pointwise in the physical latitude and energy
shift. This is the exact algebra underlying the source `N^{-1/(2x)}` factor. -/
theorem scaled_profile_density_eq_centered
    (p N : ℕ) (hN : 0 < N) (φ : ℝ → ℝ)
    (J : ℝ → ℝ) (β cp q F r t z : ℝ)
    (hcp : cp ≠ 0) (hφ : φ q = F)
    (hr : r = β*q^p/(2*cp)) :
    capScale N F r *
        (J z * Real.exp ((N:ℝ)*φ z +
          β*(t-Real.log (N:ℝ)/(2*cp))*z^p)) =
      J z * Real.exp ((N:ℝ)*(φ z-φ q) + β*t*q^p +
        β*(t-Real.log (N:ℝ)/(2*cp))*(z^p-q^p)) := by
  have hNr : (0:ℝ) < N := Nat.cast_pos.mpr hN
  dsimp only [capScale]
  rw [Real.rpow_def_of_pos hNr]
  calc
    Real.exp (Real.log (N:ℝ)*r) * Real.exp (-(N:ℝ)*F) *
        (J z * Real.exp ((N:ℝ)*φ z +
          β*(t-Real.log (N:ℝ)/(2*cp))*z^p)) =
      J z * Real.exp (Real.log (N:ℝ)*r-(N:ℝ)*F+
        ((N:ℝ)*φ z+β*(t-Real.log (N:ℝ)/(2*cp))*z^p)) := by
          calc
            _ = J z * (Real.exp (Real.log (N:ℝ)*r) *
                Real.exp (-(N:ℝ)*F) *
                  Real.exp ((N:ℝ)*φ z+
                    β*(t-Real.log (N:ℝ)/(2*cp))*z^p)) := by ring
            _ = _ := by
              rw [←Real.exp_add,←Real.exp_add]
              congr 1
              ring
    _ = _ := by
      congr 1
      rw [hφ,hr]
      field_simp
      ring

/-- The same exact identity after physical latitude integration and the
true coarea factor. -/
theorem scaled_profile_interval_eq_centered
    (p N : ℕ) (hN : 0 < N) (φ : ℝ → ℝ)
    (J : ℝ → ℝ) (β cp q F r t l u : ℝ)
    (hcp : cp ≠ 0) (hφ : φ q = F)
    (hr : r = β*q^p/(2*cp)) :
    capScale N F r *
      ((latitudeNormalization (N-1)).toReal *
        (∫ z in l..u, J z *
          Real.exp ((N:ℝ)*φ z+
            β*(t-Real.log (N:ℝ)/(2*cp))*z^p))) =
      (latitudeNormalization (N-1)).toReal *
        (∫ z in l..u, J z *
          Real.exp ((N:ℝ)*(φ z-φ q)+β*t*q^p+
            β*(t-Real.log (N:ℝ)/(2*cp))*(z^p-q^p))) := by
  calc
    _ = (latitudeNormalization (N-1)).toReal *
        (∫ z in l..u, capScale N F r *
          (J z * Real.exp ((N:ℝ)*φ z+
            β*(t-Real.log (N:ℝ)/(2*cp))*z^p))) := by
              rw [intervalIntegral.integral_const_mul]
              ring
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro z _
      exact scaled_profile_density_eq_centered p N hN φ J β cp q F r t z hcp hφ hr

/-- Source certificate specialization of the exact integrated cancellation.
It uses the literal pure intensity `c_p`, contact free energy, and `1/(2x)`
polynomial power. -/
theorem sourcePure_scaled_profile_interval_eq_centered
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (N : ℕ) (hN : 0 < N) (t l u : ℝ) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let q := Real.sqrt Q
    let φ := sourcePureLatitudeExponent p 1 Q β (markE μ β x Q)
    let cp := pureIntensityConstant p (by omega)
    let F := CSParisiMeasure.variationalValue μ β
    capScale N F (1/(2*x)) *
      ((latitudeNormalization (N-1)).toReal *
        (∫ z in l..u, sourcePureLatitudeJacobian z *
          Real.exp ((N:ℝ)*φ z+
            β*(t-Real.log (N:ℝ)/(2*cp))*z^p))) =
      (latitudeNormalization (N-1)).toReal *
        (∫ z in l..u, sourcePureLatitudeJacobian z *
          Real.exp ((N:ℝ)*(φ z-φ q)+β*t*q^p+
            β*(t-Real.log (N:ℝ)/(2*cp))*(z^p-q^p))) := by
  dsimp only
  have hcp : pureIntensityConstant p (by omega) ≠ 0 :=
    (pureIntensityConstant_pos p (by omega)).ne'
  have hφ := sourcePureLatitudeExponent_contact_eq_variationalValue
    p (by omega) 1 (by positivity) h
  have hr := sourcePure_cap_centering_power p hp h
  exact scaled_profile_interval_eq_centered p N hN
    (sourcePureLatitudeExponent p 1 Q β
      (markE (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q))
    sourcePureLatitudeJacobian β (pureIntensityConstant p (by omega))
    (Real.sqrt Q)
    (CSParisiMeasure.variationalValue
      (FiniteMixture.pure p (by omega) 1 (by positivity)) β)
    (1/(2*x)) t l u hcp hφ hr.symm

end
end SlowEquilibration.SphericalPureCapScaledContactIdentity
