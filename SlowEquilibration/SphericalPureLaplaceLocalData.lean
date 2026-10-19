-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureLaplaceRegularity
public import SlowEquilibration.SphericalTAPCriticalPureLatitudeQuadraticEnvelope

@[expose] public section

/-! The proper-pure contact supplies every local Gaussian Laplace hypothesis
directly from its certificate and the literal latitude profile. -/

namespace SlowEquilibration.SphericalPureLaplaceLocalData
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeContactStationarity
open SphericalTAPCriticalPureLatitudeContactCurvature
open SphericalTAPCriticalPureLatitudeQuadraticEnvelope
open SphericalPureLaplaceRegularity
set_option autoImplicit false

theorem sourcePureLatitudeExponent_local_laplace_data
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let E := markE μ β x Q
    let q := Real.sqrt Q
    let φ := sourcePureLatitudeExponent p alpha Q β E
    ∃ b c M κ : ℝ, 0 < b ∧ b < q ∧ 0 < c ∧ 0 ≤ M ∧ 0 < κ ∧
      Icc (q-b) (q+b) ⊆ Ioo (-1:ℝ) 1 ∧
      ContDiffOn ℝ 2 φ (Ioo (q-b) (q+b)) ∧
      ContinuousOn sourcePureLatitudeJacobian (Icc (q-b) (q+b)) ∧
      (∀ a ∈ Icc (q-b) (q+b), |sourcePureLatitudeJacobian a| ≤ M) ∧
      (∀ a ∈ Icc (q-b) (q+b), φ a ≤ φ q-c*(a-q)^2) ∧
      deriv φ q=0 ∧ iteratedDeriv 2 φ q=-κ := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let E := markE μ β x Q
  let q := Real.sqrt Q
  let φ := sourcePureLatitudeExponent p alpha Q β E
  obtain ⟨ε,b,c₀,C₂,hε,hb,hbq,hc₀,hC₂,hband,henv⟩ :=
    sourcePureLatitudeExponent_contact_quadratic_envelope
      p hp alpha halpha h
  obtain ⟨M,hM,hamp⟩ := sourcePureLatitudeJacobian_bounded_on_band hband
  let c := c₀/4
  let κ := -deriv (deriv φ) q
  have hc : 0 < c := by dsimp [c]; positivity
  have hκ : 0 < κ := by
    dsimp [κ,φ,q,E,μ]
    exact neg_pos.mpr
      (sourcePureLatitudeExponent_contact_second_deriv_neg p hp alpha halpha h)
  refine ⟨b,c,M,κ,hb,hbq,hc,hM,hκ,hband,?_,?_,hamp,?_,?_,?_⟩
  · apply (sourcePureLatitudeExponent_contDiffOn p alpha Q β E h.overlap_range.1).mono
    intro a ha
    apply hband
    exact ⟨ha.1.le,ha.2.le⟩
  · intro a ha
    exact (sourcePureLatitudeJacobian_continuousAt (hband ha)).continuousWithinAt
  · intro a ha
    have hE : E ∈ Icc (E-ε) (E+ε) := ⟨by linarith,by linarith⟩
    have hh := henv E hE a ha
    dsimp [φ,c,q,E,μ] at hh ⊢
    nlinarith
  · exact sourcePureLatitudeExponent_contact_deriv_zero p hp alpha halpha h
  · dsimp [κ]
    simp only [neg_neg]
    change iteratedDeriv 2 φ q = deriv (deriv φ) q
    simp [iteratedDeriv_succ]

end
end SlowEquilibration.SphericalPureLaplaceLocalData
