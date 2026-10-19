-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalPureLaplaceUniformLogCenteredSubband
public import SlowEquilibration.SourcePureLogPolynomialPhysicalWindowUniform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! The exact pure-model local latitude integral, in physical coordinates,
has uniform Gaussian total and microscopic-window masses after true spherical
coarea normalization and the source logarithmic centering. -/
@[expose] public section
namespace SlowEquilibration.SphericalPureLaplaceUniformLogPhysical
noncomputable section
open Filter Set MeasureTheory SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile SphericalPureLaplaceRegularity
open SphericalPureCapSourceScalars
open SphericalPureLaplaceUniformLogCenteredSubband
open SourcePureLogPolynomialLaplace SourcePureLogPolynomialPhysical
open SourcePureLogPolynomialPhysicalWindowUniform
open scoped Topology
set_option autoImplicit false

/-- Any positive subband below one certificate-dependent radius has the
exact total and fixed microscopic-window Gaussian masses, uniformly for
`|t|≤L`. The finite-dimensional integrals use the literal source profile,
Jacobian, coarea constant, and log-polynomial shift. -/
theorem sourcePureLatitude_uniform_log_physical
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let E := markE μ β x Q
    let q := Real.sqrt Q
    let φ := sourcePureLatitudeExponent p 1 Q β E
    let cp := pureIntensityConstant p (by omega)
    ∃ b₀ κ : ℝ, 0 < b₀ ∧ b₀ < q ∧ q+b₀ < 1 ∧ 0 < κ ∧
      ∀ b : ℝ, 0 < b → b ≤ b₀ → ∀ L : ℝ,
        TendstoUniformlyOn
          (fun n t => (SphericalModel.latitudeNormalization (n+1)).toReal *
            (∫ z in q-b..q+b, sourcePureLatitudeJacobian z *
              Real.exp ((n+2 : ℕ)*(φ z-φ q) + β*t*q^p +
                β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-q^p))))
          (fun t => ((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
            Real.exp (β*t*q^p) * Real.sqrt (Real.pi/(κ/2)))
          atTop (Icc (-L) L) ∧
        ∀ w : ℝ, 0 ≤ w →
          TendstoUniformlyOn
            (fun n t => (SphericalModel.latitudeNormalization (n+1)).toReal *
              (∫ z in q-w/Real.sqrt (n+2 : ℕ)..q+w/Real.sqrt (n+2 : ℕ),
                sourcePureLatitudeJacobian z *
                  Real.exp ((n+2 : ℕ)*(φ z-φ q) + β*t*q^p +
                    β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-q^p))))
            (fun t => ((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
              Real.exp (β*t*q^p) *
                (∫ u in Icc (-w) w, Real.exp (-κ*u^2/2)))
            atTop (Icc (-L) L) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let E := markE μ β x Q
  let q := Real.sqrt Q
  let φ := sourcePureLatitudeExponent p 1 Q β E
  let cp := pureIntensityConstant p (by omega : 3 ≤ p)
  obtain ⟨b₀,κ,hb₀,hb₀q,hb₀r,hκ,huni⟩ :=
    sourcePureLatitude_uniform_log_centered_subband p hp h
  refine ⟨b₀,κ,hb₀,hb₀q,hb₀r,hκ,?_⟩
  intro b hb hbb₀ L
  have hl : q-b < q := by linarith
  have hr : q < q+b := by linarith
  have hlr : q-b ≤ q+b := by linarith
  have hs0 (n : ℕ) : Real.sqrt (n+2 : ℕ) ≠ 0 := by positivity
  constructor
  · have hlocal := huni b hb hbb₀ Set.univ L
    have hF (n : ℕ) (t : ℝ) :
        ((SphericalModel.latitudeNormalization (n+1)).toReal /
          Real.sqrt (n+2 : ℕ)) *
          centeredIntegral φ sourcePureLatitudeJacobian p β cp q
            (q-b) (q+b) Set.univ n t =
        (SphericalModel.latitudeNormalization (n+1)).toReal *
          (∫ z in q-b..q+b, sourcePureLatitudeJacobian z *
            Real.exp ((n+2 : ℕ)*(φ z-φ q) + β*t*q^p +
              β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-q^p))) := by
      rw [SourcePureLogPolynomialPhysical.centeredIntegral_univ_eq_physical
        φ sourcePureLatitudeJacobian p β cp q (q-b) (q+b) t hlr n]
      rw [← mul_assoc, div_mul_cancel₀ _ (hs0 n)]
    have hphysical : TendstoUniformlyOn
        (fun n t => (SphericalModel.latitudeNormalization (n+1)).toReal *
          (∫ z in q-b..q+b, sourcePureLatitudeJacobian z *
            Real.exp ((n+2 : ℕ)*(φ z-φ q) + β*t*q^p +
              β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-q^p))))
        (fun t => ((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
          Real.exp (β*t*q^p) *
            (∫ u in Set.univ, Real.exp (-κ*u^2/2)))
        atTop (Icc (-L) L) :=
      hlocal.congr (Filter.Eventually.of_forall fun n t _ => by
        simpa only [μ,E,q,φ,cp] using hF n t)
    have hg : (∫ u : ℝ, Real.exp (-κ*u^2/2)) =
        Real.sqrt (Real.pi/(κ/2)) := by
      have heq (u : ℝ) : -κ*u^2/2 = -(κ/2)*u^2 := by ring
      simp_rw [heq]
      exact integral_gaussian (κ/2)
    simpa only [setIntegral_univ,hg,μ,E,q,φ,cp] using hphysical
  · intro w hw
    have hlocal := huni b hb hbb₀ (Icc (-w) w) L
    have heq := centeredIntegral_symmetric_window_eq_physical_eventually_uniform
      φ sourcePureLatitudeJacobian p β cp hl hr hw
    have hphysical : TendstoUniformlyOn
        (fun n t => (SphericalModel.latitudeNormalization (n+1)).toReal *
          (∫ z in q-w/Real.sqrt (n+2 : ℕ)..q+w/Real.sqrt (n+2 : ℕ),
            sourcePureLatitudeJacobian z *
              Real.exp ((n+2 : ℕ)*(φ z-φ q) + β*t*q^p +
                β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-q^p))))
        (fun t => ((1-Q)^(-(3/2:ℝ))/Real.sqrt (2*Real.pi)) *
          Real.exp (β*t*q^p) *
            (∫ u in Icc (-w) w, Real.exp (-κ*u^2/2)))
        atTop (Icc (-L) L) := by
      apply hlocal.congr
      filter_upwards [heq] with n hn
      intro t _
      have hF :
          ((SphericalModel.latitudeNormalization (n+1)).toReal /
            Real.sqrt (n+2 : ℕ)) *
            centeredIntegral φ sourcePureLatitudeJacobian p β cp q
              (q-b) (q+b) (Icc (-w) w) n t =
          (SphericalModel.latitudeNormalization (n+1)).toReal *
            (∫ z in q-w/Real.sqrt (n+2 : ℕ)..q+w/Real.sqrt (n+2 : ℕ),
              sourcePureLatitudeJacobian z *
                Real.exp ((n+2 : ℕ)*(φ z-φ q) + β*t*q^p +
                  β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-q^p))) := by
        rw [hn t]
        rw [← mul_assoc, div_mul_cancel₀ _ (hs0 n)]
      simpa only [μ,E,q,φ,cp] using hF
    simpa only [μ,E,q,φ,cp] using hphysical

end
end SlowEquilibration.SphericalPureLaplaceUniformLogPhysical
