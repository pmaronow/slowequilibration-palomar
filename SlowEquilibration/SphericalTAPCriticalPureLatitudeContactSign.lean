-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalAnalyticNeighborhood
public import SlowEquilibration.SphericalProperPureContactGeometry

@[expose] public section

/-! A proper-pure source contact has the additional positive latitude
factor in the printed second-derivative formula of Section 12. -/

namespace SlowEquilibration.SphericalTAPCriticalPureLatitudeContactSign
noncomputable section
open Set TwoAtomStationarity SphericalTAPCertificate SphericalMarkedWindows
set_option autoImplicit false

/-- The pure contact and its strict Hessian edge force the polynomial factor
`p Q-(p-2)` in the source latitude curvature to be positive. -/
theorem pure_contact_latitude_factor_pos
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    0 < (p:ℝ)*Q-((p:ℝ)-2) := by
  let μ := FiniteMixture.pure p hp alpha halpha
  let A := markA μ Q
  let B := markB μ Q
  let y := markY β Q
  let z := markZ x Q
  let s := 1-Q
  have hs : 0 < s := sub_pos.mpr h.overlap_range.2
  have hA : 0 < A := by
    dsimp [A,markA]
    exact mul_pos h.overlap_range.1 (μ.xi1_pos h.overlap_range.1)
  have hy : 0 < y := markY_pos h.beta_pos h.overlap_range
  have hB : B=(p:ℝ)*((p:ℝ)-1)*μ.xi Q :=
    (sourcePure_contact_covariance_scalars p hp alpha halpha Q).2
  have hAeq : A=(p:ℝ)*μ.xi Q :=
    (sourcePure_contact_covariance_scalars p hp alpha halpha Q).1
  have hp0 : (0:ℝ) < p := by exact_mod_cast (show 0<p by omega)
  have hBA : B=((p:ℝ)-1)*A := by rw [hB,hAeq]; ring
  have hy2 : y^2=(1+z)*A :=
    markY_sq_from_contact μ h.beta_pos h.weight_range h.overlap_range
      h.contact_value h.contact_derivative
  have hrho : B/y^2 < 1 := h.edge_margin.1
  have hBlt : B < y^2 := by
    simpa only [one_mul] using (div_lt_iff₀ (sq_pos_of_pos hy)).mp hrho
  have hpz : (p:ℝ)-2 < z := by
    rw [hy2,hBA] at hBlt
    by_contra hnot
    have hnonneg : 0 ≤ (p:ℝ)-2-z := by linarith
    nlinarith [mul_nonneg hA.le hnonneg]
  have hzx : z < Q/s := by
    dsimp [z,markZ,s]
    exact div_lt_div_of_pos_right
      (mul_lt_of_lt_one_left h.overlap_range.1 h.weight_range.2) hs
  have hps : ((p:ℝ)-2)*s < Q := by
    have := mul_lt_mul_of_pos_right (lt_trans hpz hzx) hs
    dsimp [s] at *
    convert this using 1
    field_simp
  have hpR : (2:ℝ) ≤ p := by exact_mod_cast hp
  nlinarith [hps,h.overlap_range.2]

end
end SlowEquilibration.SphericalTAPCriticalPureLatitudeContactSign
