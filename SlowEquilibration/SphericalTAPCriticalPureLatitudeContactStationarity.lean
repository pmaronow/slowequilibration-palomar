-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPureLatitudeUniformCurvature

@[expose] public section

/-! The source proper-pure contact latitude is stationary for the literal
conditional Palm exponent. -/

namespace SlowEquilibration.SphericalTAPCriticalPureLatitudeContactStationarity
noncomputable section
open Set TwoAtomStationarity SphericalTAPCertificate SphericalMarkedWindows
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeVariance
set_option autoImplicit false

private theorem variance_slope_at_contact_marks
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    (Q : ℝ) (hQ : 0 < Q) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let q := Real.sqrt Q
    sourcePureLatitudeVarianceSlope p alpha q =
      -2*(markB μ Q/Q^2)*q*(1-Q) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let q := Real.sqrt Q
  have hq2 : q^2=Q := Real.sq_sqrt hQ.le
  have hpow1 : q^(2*p-1)=q^(2*p-3)*Q := by
    rw [show 2*p-1=(2*p-3)+2 by omega,pow_add,hq2]
  have hpow2 : q^(2*p-3)=Q^(p-2)*q := by
    calc
      q^(2*p-3)=q^(2*(p-2)+1) := by congr 1; omega
      _=q^(2*(p-2))*q := by rw [pow_add,pow_one]
      _=(q^2)^(p-2)*q := by rw [pow_mul]
      _=Q^(p-2)*q := by rw [hq2]
  have hpowQ : Q^p=Q^(p-2)*Q^2 := by
    rw [←pow_add,Nat.sub_add_cancel hp]
  have hB : markB μ Q=(p:ℝ)*((p:ℝ)-1)*alpha*Q^p := by
    rw [(sourcePure_contact_covariance_scalars p hp alpha halpha Q).2]
    rw [FiniteMixture.pure_xi p hp alpha halpha Q]
    ring
  have hBdiv : markB μ Q/Q^2=(p:ℝ)*((p:ℝ)-1)*alpha*Q^(p-2) := by
    rw [hB,hpowQ]
    field_simp [hQ.ne']
  have hc2 : ((2*p-2:ℕ):ℝ)=2*(p:ℝ)-2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ 2*p)]
    push_cast
    ring
  unfold sourcePureLatitudeVarianceSlope
  rw [hpow1,hpow2,hBdiv,hc2]
  dsimp [q]
  ring

/-- The first latitude derivative of the actual proper-pure source Palm
exponent vanishes at its certificate contact latitude. -/
theorem sourcePureLatitudeExponent_contact_deriv_zero
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    deriv (sourcePureLatitudeExponent p alpha Q β
      (markE (FiniteMixture.pure p hp alpha halpha) β x Q))
      (Real.sqrt Q) = 0 := by
  let μ := FiniteMixture.pure p hp alpha halpha
  let E := markE μ β x Q
  let B := markB μ Q
  let y := markY β Q
  let q := Real.sqrt Q
  let s := 1-Q
  have hQ : 0 < Q := h.overlap_range.1
  have hs : 0 < s := sub_pos.mpr h.overlap_range.2
  have hq : 0 < q := Real.sqrt_pos.mpr hQ
  have hq2 : q^2=Q := Real.sq_sqrt hQ.le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt hQ.le h.overlap_range.2
  have hqmem : q ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,hq1⟩
  rw [(sourcePureLatitudeExponent_hasDerivAt p hp alpha Q β E q hQ hqmem).deriv]
  have hv := variance_slope_at_contact_marks p hp alpha halpha Q hQ
  dsimp only at hv
  have hroot : (q/Real.sqrt Q)^(p-1)=1 := by
    dsimp [q]
    rw [div_self hq.ne']
    simp
  have hk := sourcePure_contact_radial_graph p hp alpha halpha h
  change markK μ β Q=(p:ℝ)*E at hk
  have hE : β*(p:ℝ)*E=Q/s+β^2*B*s/Q := by
    calc
      β*(p:ℝ)*E = β*markK μ β Q := by rw [hk]; ring
      _ = β*(y+B/y) := by rfl
      _ = Q/s+β^2*B*s/Q := by
        dsimp [y,s,markY]
        field_simp [h.beta_pos.ne',hQ.ne',hs.ne']
  have hBQ : (B/Q^2)*q=B/(q*Q) := by
    rw [← hq2]
    field_simp [hq.ne']
  have hqS : q/s=(Q/s)/q := by
    rw [← hq2]
    field_simp [hq.ne',hs.ne']
  have hterm : β^2*(B/Q^2)*q*s=(β^2*B*s/Q)/q := by
    calc
      β^2*(B/Q^2)*q*s=β^2*((B/Q^2)*q)*s := by ring
      _=β^2*(B/(q*Q))*s := by rw [hBQ]
      _=(β^2*B*s/Q)/q := by
        field_simp [hq.ne',hQ.ne']
  calc
    sourcePureLatitudeExponentSlope p alpha Q β E q =
        β*E*(p:ℝ)/q-q/s-β^2*(B/Q^2)*q*s := by
      unfold sourcePureLatitudeExponentSlope
      rw [hroot,hv,hq2]
      dsimp [q,s,B]
      ring
    _ = (β*(p:ℝ)*E-Q/s-β^2*B*s/Q)/q := by
      rw [hterm,hqS]
      field_simp [hq.ne',hQ.ne',hs.ne']
    _ = 0 := by rw [hE]; ring

end
end SlowEquilibration.SphericalTAPCriticalPureLatitudeContactStationarity
