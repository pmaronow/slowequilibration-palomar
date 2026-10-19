-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPureLatitudeProfile

@[expose] public section

/-! The literal proper-pure latitude exponent has the negative contact
curvature printed in Section 12. The contact energy and the edge ratio here
are the marks derived from the source certificate. -/

namespace SlowEquilibration.SphericalTAPCriticalPureLatitudeContactCurvature
noncomputable section
open Set TwoAtomStationarity SphericalTAPCertificate SphericalMarkedWindows
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeVariance
open SphericalTAPCriticalPureLatitudeContactSign
set_option autoImplicit false
set_option maxHeartbeats 500000

private theorem pure_curvature_at_contact_normal_form
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q β e : ℝ) (hQ : 0 < Q) :
    let μ := FiniteMixture.pure p hp alpha halpha
    sourcePureLatitudeExponentCurvature p alpha Q β e (Real.sqrt Q) =
      β*e*(p:ℝ)*((p:ℝ)-1)/Q-(1+Q)/(1-Q)^2+
        β^2*(markB μ Q/Q^2)*
          ((((2*p:ℕ):ℝ)-1)*Q-(((2*p:ℕ):ℝ)-3)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  have hq : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  have hpow : Q^p=Q^(p-2)*Q^2 := by
    rw [← pow_add, Nat.sub_add_cancel hp]
  have hB : markB μ Q=(p:ℝ)*((p:ℝ)-1)*alpha*Q^p := by
    rw [(sourcePure_contact_covariance_scalars p hp alpha halpha Q).2]
    rw [FiniteMixture.pure_xi p hp alpha halpha Q]
    ring
  have hBdiv : markB μ Q/Q^2=(p:ℝ)*((p:ℝ)-1)*alpha*Q^(p-2) := by
    rw [hB,hpow]
    field_simp [hQ.ne']
  have hroot : (Real.sqrt Q/Real.sqrt Q)^(p-2)=1 := by
    rw [div_self hq]
    simp
  have hv := sourcePureLatitudeVariance_curvature_at_contact p hp alpha hQ
  unfold sourcePureLatitudeExponentCurvature
  rw [hroot,Real.sq_sqrt hQ.le,hv,hBdiv]
  ring

private theorem pure_contact_curvature_algebra
    (t β e Q B ρ : ℝ) (hQ : 0 < Q) (hQ1 : Q < 1)
    (hE : β*t*e=Q/(1-Q)+β^2*B*(1-Q)/Q)
    (hρ : ρ=β^2*B*(1-Q)^2/Q^2) :
    β*e*t*(t-1)/Q-(1+Q)/(1-Q)^2+
      β^2*(B/Q^2)*((2*t-1)*Q-(2*t-3)) =
        -((1-ρ)*(t*Q-(t-2)))/(1-Q)^2 := by
  have hs : 1-Q ≠ 0 := (sub_pos.mpr hQ1).ne'
  calc
    β*e*t*(t-1)/Q-(1+Q)/(1-Q)^2+
        β^2*(B/Q^2)*((2*t-1)*Q-(2*t-3)) =
      (β*t*e)*(t-1)/Q-(1+Q)/(1-Q)^2+
        β^2*(B/Q^2)*((2*t-1)*Q-(2*t-3)) := by ring
    _ = -((1-ρ)*(t*Q-(t-2)))/(1-Q)^2 := by
      rw [hE,hρ]
      field_simp [hQ.ne',hs]
      ring

/-- The printed exact contact curvature for the literal proper-pure Palm
latitude exponent, expressed entirely through the certificate's physical
marks. -/
theorem sourcePureLatitudeExponent_contact_curvature
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let E := markE μ β x Q
    sourcePureLatitudeExponentCurvature p alpha Q β E (Real.sqrt Q) =
      -((1-markB μ Q/(markY β Q)^2)*
        ((p:ℝ)*Q-((p:ℝ)-2)))/(1-Q)^2 := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let E := markE μ β x Q
  let B := markB μ Q
  let y := markY β Q
  let ρ := B/y^2
  have hQ : 0 < Q := h.overlap_range.1
  have hs : 0 < 1-Q := sub_pos.mpr h.overlap_range.2
  have hy : 0 < y := markY_pos h.beta_pos h.overlap_range
  have hE : β*(p:ℝ)*E=Q/(1-Q)+β^2*B*(1-Q)/Q := by
    have hk := sourcePure_contact_radial_graph p hp alpha halpha h
    change markK μ β Q=(p:ℝ)*E at hk
    calc
      β*(p:ℝ)*E = β*markK μ β Q := by rw [hk]; ring
      _ = β*(y+B/y) := by rfl
      _ = Q/(1-Q)+β^2*B*(1-Q)/Q := by
        dsimp [y,markY]
        field_simp [h.beta_pos.ne',hQ.ne',hs.ne']
  have hρ : ρ=β^2*B*(1-Q)^2/Q^2 := by
    dsimp [ρ,y,markY]
    field_simp [h.beta_pos.ne',hQ.ne',hs.ne']
  have hcast : ((2*p:ℕ):ℝ)=2*(p:ℝ) := by push_cast; ring
  have hnormal := pure_curvature_at_contact_normal_form p hp alpha halpha Q β E hQ
  dsimp only at hnormal
  rw [hcast] at hnormal
  change sourcePureLatitudeExponentCurvature p alpha Q β E (Real.sqrt Q) =
    -((1-ρ)*((p:ℝ)*Q-((p:ℝ)-2)))/(1-Q)^2
  rw [hnormal]
  exact pure_contact_curvature_algebra (p:ℝ) β E Q B ρ hQ
    h.overlap_range.2 hE hρ

/-- The proper-pure contact is a strict local maximum in latitude for the
actual exponent, with no assumed Hessian sign. -/
theorem sourcePureLatitudeExponent_contact_second_deriv_neg
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    deriv (deriv (sourcePureLatitudeExponent p alpha Q β
      (markE (FiniteMixture.pure p hp alpha halpha) β x Q))) (Real.sqrt Q) < 0 := by
  have hq0 : 0 < Real.sqrt Q := Real.sqrt_pos.mpr h.overlap_range.1
  have hq1 : Real.sqrt Q < 1 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
  have hqmem : Real.sqrt Q ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,hq1⟩
  rw [sourcePureLatitudeExponent_second_deriv p hp alpha Q β
    (markE (FiniteMixture.pure p hp alpha halpha) β x Q)
    (Real.sqrt Q) h.overlap_range.1 hqmem]
  rw [sourcePureLatitudeExponent_contact_curvature p hp alpha halpha h]
  have hρ : 0 < 1-markB (FiniteMixture.pure p hp alpha halpha) Q/
      (markY β Q)^2 := by linarith [h.edge_margin.1]
  have hf := pure_contact_latitude_factor_pos p hp alpha halpha h
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (mul_pos hρ hf))
    (sq_pos_of_pos (sub_pos.mpr h.overlap_range.2))

end
end SlowEquilibration.SphericalTAPCriticalPureLatitudeContactCurvature
