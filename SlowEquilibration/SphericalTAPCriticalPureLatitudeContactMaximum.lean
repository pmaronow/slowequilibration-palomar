-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPureLatitudeBandMaximizer

@[expose] public section

/-! At the contact energy, the literal proper-pure latitude exponent is
maximized at the contact latitude in the chosen source band. -/

namespace SlowEquilibration.SphericalTAPCriticalPureLatitudeContactMaximum
noncomputable section
open Set TwoAtomStationarity SphericalTAPCertificate
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeContactStationarity
open SphericalTAPCriticalPureLatitudeBandMaximizer
set_option autoImplicit false

theorem sourcePureLatitudeExponent_contact_is_band_max
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q)
    (b : ℝ) (hb : 0 < b)
    (hband : Icc (Real.sqrt Q-b) (Real.sqrt Q+b) ⊆ Ioo (-1:ℝ) 1)
    (hconc : StrictConcaveOn ℝ (Icc (Real.sqrt Q-b) (Real.sqrt Q+b))
      (sourcePureLatitudeExponent p alpha Q β
        (markE (FiniteMixture.pure p hp alpha halpha) β x Q))) :
    IsMaxOn (sourcePureLatitudeExponent p alpha Q β
      (markE (FiniteMixture.pure p hp alpha halpha) β x Q))
      (Icc (Real.sqrt Q-b) (Real.sqrt Q+b)) (Real.sqrt Q) := by
  let E := markE (FiniteMixture.pure p hp alpha halpha) β x Q
  let q := Real.sqrt Q
  let f := sourcePureLatitudeExponent p alpha Q β E
  let D : Set ℝ := Icc (q-b) (q+b)
  have hqD : q ∈ D := by
    change q ∈ Icc (q-b) (q+b)
    constructor <;> linarith
  have hdiff : ∀ a ∈ D, DifferentiableAt ℝ f a := by
    intro a ha
    exact (sourcePureLatitudeExponent_hasDerivAt p hp alpha Q β E a
      h.overlap_range.1 (hband ha)).differentiableAt
  have hanti : StrictAntiOn (deriv f) D := hconc.strictAntiOn_deriv hdiff
  have hzero : deriv f q=0 :=
    sourcePureLatitudeExponent_contact_deriv_zero p hp alpha halpha h
  have hleft : ∀ a ∈ Ioo (q-b) q, 0 ≤ deriv f a := by
    intro a ha
    have haD : a ∈ D := ⟨ha.1.le,by linarith [ha.2]⟩
    have hh := hanti haD hqD ha.2
    rw [hzero] at hh
    exact hh.le
  have hright : ∀ a ∈ Ioo q (q+b), deriv f a ≤ 0 := by
    intro a ha
    have haD : a ∈ D := ⟨by linarith [ha.1],ha.2.le⟩
    have hh := hanti hqD haD ha.1
    rw [hzero] at hh
    exact hh.le
  exact isMaxOn_Icc_of_deriv
    (hdiff (q-b) ⟨by linarith,by linarith⟩).continuousAt
    (hdiff q hqD).continuousAt
    (hdiff (q+b) ⟨by linarith,by linarith⟩).continuousAt
    (fun a ha => (hdiff a ⟨ha.1.le,by linarith [ha.2]⟩).differentiableWithinAt)
    (fun a ha => (hdiff a ⟨by linarith [ha.1],ha.2.le⟩).differentiableWithinAt)
    hleft hright

/-- The selected source neighborhood has a unique band maximizer at each
nearby energy, and its contact-energy maximizer is exactly `√Q`. -/
theorem sourcePureLatitudeExponent_selected_contact_maximum
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let E := markE (FiniteMixture.pure p hp alpha halpha) β x Q
    let q := Real.sqrt Q
    ∃ ε b c : ℝ, 0 < ε ∧ 0 < b ∧ b < q ∧ 0 < c ∧
      Icc (q-b) (q+b) ⊆ Ioo (-1:ℝ) 1 ∧
      IsMaxOn (sourcePureLatitudeExponent p alpha Q β E)
        (Icc (q-b) (q+b)) q ∧
      ∀ e ∈ Icc (E-ε) (E+ε),
        StrictConcaveOn ℝ (Icc (q-b) (q+b))
          (sourcePureLatitudeExponent p alpha Q β e) ∧
        ∃! a : ℝ, a ∈ Icc (q-b) (q+b) ∧
          IsMaxOn (sourcePureLatitudeExponent p alpha Q β e)
            (Icc (q-b) (q+b)) a := by
  dsimp only
  obtain ⟨ε,b,c,hε,hb,hbq,hc,hband,hmax⟩ :=
    sourcePureLatitudeExponent_unique_band_maximizer p hp alpha halpha h
  let E := markE (FiniteMixture.pure p hp alpha halpha) β x Q
  let q := Real.sqrt Q
  have hEwin : E ∈ Icc (E-ε) (E+ε) := ⟨by linarith,by linarith⟩
  refine ⟨ε,b,c,hε,hb,hbq,hc,hband,?_,hmax⟩
  exact sourcePureLatitudeExponent_contact_is_band_max p hp alpha halpha
    h b hb hband (hmax E hEwin).1

end
end SlowEquilibration.SphericalTAPCriticalPureLatitudeContactMaximum
