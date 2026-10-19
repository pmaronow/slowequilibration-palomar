-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPureLatitudeLaplaceUpper

@[expose] public section

/-! The pure contact latitude exponent is exactly the certificate's
variational free energy. This identifies the Laplace exponent with the
source TAP band normalization. -/

namespace SlowEquilibration.SphericalTAPCriticalPureLatitudeContactValue
noncomputable section
open SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeVariance
open SphericalMarkedWindows
set_option autoImplicit false

/-- At the pure contact, the conditional value-and-gradient variance is the
literal Taylor residual variance at overlap one. -/
theorem sourcePureLatitudeVariance_contact_eq_residual
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {Q : ℝ} (hQ : 0 < Q) :
    sourcePureLatitudeVariance p alpha (Real.sqrt Q) =
      residualAtOne (FiniteMixture.pure p hp alpha halpha) Q := by
  let μ := FiniteMixture.pure p hp alpha halpha
  let q := Real.sqrt Q
  have hq2 : q^2=Q := Real.sq_sqrt hQ.le
  have hpow1 : q^(2*p)=Q^p := by
    calc
      q^(2*p)=(q^2)^p := by rw [pow_mul]
      _=_ := by rw [hq2]
  have hpow2 : q^(2*p-2)=Q^(p-1) := by
    calc
      q^(2*p-2)=q^(2*(p-1)) := by congr 1; omega
      _=(q^2)^(p-1) := by rw [pow_mul]
      _=_ := by rw [hq2]
  have hpowQ : Q^(p-1)*Q=Q^p := by
    rw [←pow_succ,Nat.sub_add_cancel (by omega : 1 ≤ p)]
  have hA := (sourcePure_contact_covariance_scalars p hp alpha halpha Q).1
  have hxi1 : μ.xi1 Q=alpha*(p:ℝ)*Q^(p-1) := by
    change Q*μ.xi1 Q=(p:ℝ)*μ.xi Q at hA
    rw [FiniteMixture.pure_xi] at hA
    have heq : Q*(μ.xi1 Q-alpha*(p:ℝ)*Q^(p-1))=0 := by
      rw [←hpowQ] at hA
      nlinarith [hA]
    have hz : μ.xi1 Q-alpha*(p:ℝ)*Q^(p-1)=0 :=
      (mul_eq_zero.mp heq).resolve_left hQ.ne'
    linarith
  unfold sourcePureLatitudeVariance residualAtOne
  rw [FiniteMixture.pure_xi,FiniteMixture.pure_xi,hxi1,hpow1,hpow2,hq2]
  simp only [one_pow]
  ring

/-- Printed contact identity `L_p(E₀,√Q)=F(β)`, with `F(β)` represented
by the actual canonical Crisanti--Sommers variational value. -/
theorem sourcePureLatitudeExponent_contact_eq_variationalValue
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    sourcePureLatitudeExponent p alpha Q β
      (markE (FiniteMixture.pure p hp alpha halpha) β x Q)
      (Real.sqrt Q) =
        CSParisiMeasure.variationalValue
          (FiniteMixture.pure p hp alpha halpha) β := by
  let μ := FiniteMixture.pure p hp alpha halpha
  let E := markE μ β x Q
  let q := Real.sqrt Q
  have hq : q ≠ 0 := (Real.sqrt_pos.mpr h.overlap_range.1).ne'
  have hq2 : q^2=Q := Real.sq_sqrt h.overlap_range.1.le
  have hroot : (q/Real.sqrt Q)^p=1 := by
    dsimp [q]
    rw [div_self hq]
    simp
  have hvar := sourcePureLatitudeVariance_contact_eq_residual
    p hp alpha halpha h.overlap_range.1
  have hTAP := h.variational_TAP
  unfold sourcePureLatitudeExponent
  rw [hroot,hq2,hvar]
  rw [hTAP]
  ring

/-- Source proper-pure Laplace and optimized-exponent bounds under a single
fixed physical band and energy window. The exponent is the canonical
variational free energy, and the integral retains its `N⁻¹ᐟ²` width. -/
theorem sourcePureLatitudeExponent_freeEnergy_laplace_upper
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let E := markE μ β x Q
    let q := Real.sqrt Q
    ∃ ε b C C₂ : ℝ, 0 < ε ∧ 0 < b ∧ b < q ∧ 0 < C ∧ 0 ≤ C₂ ∧
      Set.Icc (q-b) (q+b) ⊆ Set.Ioo (-1:ℝ) 1 ∧
      (∀ e ∈ Set.Icc (E-ε) (E+ε), ∀ a ∈ Set.Icc (q-b) (q+b),
        sourcePureLatitudeExponent p alpha Q β e a ≤
          CSParisiMeasure.variationalValue μ β+
            β*(e-E)+C₂*(e-E)^2) ∧
      ∀ (N : ℝ), 0 < N → ∀ e ∈ Set.Icc (E-ε) (E+ε),
        (∫ a in Set.Icc (q-b) (q+b),
          (1-a^2)^(-(3/2:ℝ))*
            Real.exp (N*sourcePureLatitudeExponent p alpha Q β e a)) ≤
          C*Real.exp (N*(CSParisiMeasure.variationalValue μ β+
            β*(e-E)+C₂*(e-E)^2))/Real.sqrt N := by
  dsimp only
  obtain ⟨ε,b,C,C₂,hε,hb,hbq,hC,hC₂,hband,hpoint,hintegral⟩ :=
    SphericalTAPCriticalPureLatitudeLaplaceUpper.sourcePureLatitudeExponent_weighted_laplace_upper
      p hp alpha halpha h
  have hcontact := sourcePureLatitudeExponent_contact_eq_variationalValue
    p hp alpha halpha h
  refine ⟨ε,b,C,C₂,hε,hb,hbq,hC,hC₂,hband,?_,?_⟩
  · intro e he a ha
    simpa only [hcontact] using hpoint e he a ha
  · intro N hN e he
    simpa only [hcontact] using hintegral N hN e he

end
end SlowEquilibration.SphericalTAPCriticalPureLatitudeContactValue
