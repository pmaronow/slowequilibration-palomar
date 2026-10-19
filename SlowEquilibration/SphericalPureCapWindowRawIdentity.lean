-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureCapScaledContactIdentity
public import SlowEquilibration.SourceGaussianLaplaceTaylor

/-! The microscopic source window is eventually inside the positive
hemisphere, where the raw conditional-density integral equals the centered
Laplace profile exactly, simultaneously for every energy shift. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureCapWindowRawIdentity
noncomputable section
open Filter Set MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalPureCapSourceScalars SphericalPureCapIntegralDecomposition
open SphericalPureCapScaledContactIdentity SphericalPureCapTailScale
open SphericalTAPCriticalPureLatitudeProfile SphericalPureLaplaceRegularity
open SourceGaussianLaplaceTaylor PureStationarity SphericalModel
open scoped Topology
set_option autoImplicit false

/-- After a geometry-dependent threshold, the scaled *raw* source mean of
`I_{N,w}` is the centered physical Gaussian-window integral. -/
theorem sourcePure_scaled_raw_window_eq_centered_eventually
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (w : ℝ) (hw : 0 ≤ w) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let q := Real.sqrt Q
    let cp := pureIntensityConstant p (by omega)
    let ep := pureEnergyConstant p (by omega)
    let F := CSParisiMeasure.variationalValue μ β
    let φ := sourcePureLatitudeExponent p 1 Q β (markE μ β x Q)
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      capScale (n+2) F (1/(2*x)) *
        ((latitudeNormalization (n+1)).toReal *
          (∫ z in q-w/Real.sqrt (n+2 : ℕ)..q+w/Real.sqrt (n+2 : ℕ),
            rawDensity p (n+2) β
              ((n+2 : ℕ)*ep+t-Real.log (n+2 : ℕ)/(2*cp)) z)) =
      (latitudeNormalization (n+1)).toReal *
        (∫ z in q-w/Real.sqrt (n+2 : ℕ)..q+w/Real.sqrt (n+2 : ℕ),
          sourcePureLatitudeJacobian z *
            Real.exp ((n+2 : ℕ)*(φ z-φ q)+β*t*q^p+
              β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-q^p))) := by
  dsimp only
  let q := Real.sqrt Q
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  let ep := pureEnergyConstant p (by omega : 3 ≤ p)
  let F := CSParisiMeasure.variationalValue
    (FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)) β
  let φ := sourcePureLatitudeExponent p 1 Q β
    (markE (FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)) β x Q)
  have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hq1 : q < 1 := by
    dsimp [q]
    nlinarith [Real.sq_sqrt h.overlap_range.1.le,h.overlap_range.2]
  have hLeft := scaled_tendsto q (-w)
  have hRight := scaled_tendsto q w
  filter_upwards [hLeft.eventually (Ioo_mem_nhds hq0 hq1),
    hRight.eventually (Ioo_mem_nhds hq0 hq1)] with n hln hrn
  intro t
  let u := t-Real.log (n+2 : ℕ)/(2*cp)
  have hle : q-w/Real.sqrt (n+2 : ℕ) ≤
      q+w/Real.sqrt (n+2 : ℕ) := by
    have hs : 0 < Real.sqrt (n+2 : ℕ) := by positivity
    have hw' : 0 ≤ w/Real.sqrt (n+2 : ℕ) := div_nonneg hw hs.le
    linarith
  have hraw := raw_interval_eq_profile_interval p hp h (n+2) u
    (q-w/Real.sqrt (n+2 : ℕ)) (q+w/Real.sqrt (n+2 : ℕ))
    (by simpa only [neg_div,sub_eq_add_neg] using hln.1) hrn.2 hle
  have hcenter := sourcePure_scaled_profile_interval_eq_centered p hp h
    (n+2) (by omega) t
    (q-w/Real.sqrt (n+2 : ℕ)) (q+w/Real.sqrt (n+2 : ℕ))
  calc
    _ = capScale (n+2) F (1/(2*x)) *
        ((latitudeNormalization (n+1)).toReal *
          (∫ z in q-w/Real.sqrt (n+2 : ℕ)..q+w/Real.sqrt (n+2 : ℕ),
            profileDensity p (n+2) (by omega) Q β x u z)) := by
              simpa only [q,cp,ep,F,u,add_sub_assoc] using
                congrArg (fun I : ℝ =>
                  capScale (n+2) F (1/(2*x)) *
                    ((latitudeNormalization (n+1)).toReal * I)) hraw
    _ = _ := by
      simpa only [profileDensity,q,cp,F,φ,u,
        show n+2-1=n+1 by omega,add_sub_assoc] using hcenter

end
end SlowEquilibration.SphericalPureCapWindowRawIdentity
