-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureCapWindowRawIdentity
public import SlowEquilibration.SphericalPureLaplaceUniformLogPhysicalCurvature

/-! Uniform source Gaussian Laplace limit for the literal raw conditional
Palm mean on a shrinking microscopic latitude window. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureCapWindowRawLaplace
noncomputable section
open Filter Set MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalPureCapTailScale SphericalPureCapSourceScalars
open SphericalPureCapIntegralDecomposition SphericalPureCapWindowRawIdentity
open SphericalPureLaplaceUniformLogPhysicalCurvature
open SphericalPureLaplaceUniformLogCurvature PureStationarity SphericalModel
open scoped Topology
set_option autoImplicit false

/-- The actual raw window mean has the exact coarea-normalized Gaussian
limit, uniformly on any bounded source critical-value shift interval. -/
theorem sourcePure_cap_raw_window_laplace_uniform
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let q := Real.sqrt Q
    let cp := pureIntensityConstant p (by omega)
    let ep := pureEnergyConstant p (by omega)
    let F := CSParisiMeasure.variationalValue μ β
    ∃ κ : ℝ, 0 < κ ∧ κ = purePrintedKStar p hp β Q ∧
      ∀ L w : ℝ, 0 ≤ L → 0 ≤ w →
        TendstoUniformlyOn
          (fun n : ℕ => fun t : ℝ =>
            capScale (n+2) F (1/(2*x)) *
              ((latitudeNormalization (n+1)).toReal *
                (∫ z in q-w/Real.sqrt (n+2 : ℕ)..q+w/Real.sqrt (n+2 : ℕ),
                  rawDensity p (n+2) β
                    ((n+2 : ℕ)*ep+t-Real.log (n+2 : ℕ)/(2*cp)) z)))
          (fun t : ℝ =>
            ((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
              Real.exp (β*t*q^p) *
                (∫ u in Icc (-w) w, Real.exp (-κ*u^2/2)))
          atTop (Icc (-L) L) := by
  dsimp only
  obtain ⟨b₀,κ,hb₀,_,_,hκ,hκEq,hlocal⟩ :=
    sourcePureLatitude_uniform_log_physical_exact_curvature p hp h
  refine ⟨κ,hκ,hκEq,?_⟩
  intro L w hL hw
  have hwin := (hlocal b₀ hb₀ le_rfl L).2 w hw
  have hraw := sourcePure_scaled_raw_window_eq_centered_eventually
    p hp h w hw
  apply hwin.congr
  filter_upwards [hraw] with n hn t ht
  simpa only [] using (hn t).symm

end
end SlowEquilibration.SphericalPureCapWindowRawLaplace
