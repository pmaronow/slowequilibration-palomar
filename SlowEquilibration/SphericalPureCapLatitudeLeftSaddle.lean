-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapLatitudeRightSaddle
public import SlowEquilibration.SphericalTAPCriticalPureLatitudeContactMaximum

@[expose] public section

/-! The literal pure source latitude exponent rises strictly into the
contact from a fixed cap latitude on its left. -/

namespace SlowEquilibration.SphericalPureCapLatitudeLeftSaddle
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeContactStationarity
open SphericalTAPCriticalPureLatitudeBandMaximizer
set_option autoImplicit false

theorem sourcePureLatitudeExponent_strictMonoOn_left_of_contact
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let E := markE μ β x Q
    let q := Real.sqrt Q
    ∃ b : ℝ, 0 < b ∧ b < q ∧
      Icc (q-b) (q+b) ⊆ Ioo (-1:ℝ) 1 ∧
      StrictMonoOn (sourcePureLatitudeExponent p 1 Q β E) (Icc (q-b) q) := by
  dsimp only
  obtain ⟨ε,b,c,hε,hb,hbq,hc,hband,hmax⟩ :=
    sourcePureLatitudeExponent_unique_band_maximizer p (by omega) 1
      (by positivity) h
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let E := markE μ β x Q
  let q := Real.sqrt Q
  let F := sourcePureLatitudeExponent p 1 Q β E
  let D : Set ℝ := Icc (q-b) (q+b)
  have hEwin : E ∈ Icc (E-ε) (E+ε) := ⟨by linarith,by linarith⟩
  have hconc : StrictConcaveOn ℝ D F := (hmax E hEwin).1
  have hdiff : ∀ a ∈ D, DifferentiableAt ℝ F a := by
    intro a ha
    exact (sourcePureLatitudeExponent_hasDerivAt p (by omega) 1 Q β E a
      h.overlap_range.1 (hband ha)).differentiableAt
  have hanti : StrictAntiOn (deriv F) D := hconc.strictAntiOn_deriv hdiff
  have hqD : q ∈ D := ⟨by linarith,by linarith⟩
  have hzero : deriv F q=0 :=
    sourcePureLatitudeExponent_contact_deriv_zero p (by omega) 1 (by positivity) h
  refine ⟨b,hb,hbq,hband,?_⟩
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
  · intro a ha
    have haD : a ∈ D := ⟨ha.1,by linarith [ha.2]⟩
    exact (hdiff a haD).continuousAt.continuousWithinAt
  · intro a ha
    have ha' : a ∈ Ioo (q-b) q := by simpa only [interior_Icc] using ha
    have haD : a ∈ D := ⟨ha'.1.le,by linarith [ha'.2]⟩
    have hh := hanti haD hqD ha'.2
    rw [hzero] at hh
    exact hh

end
end SlowEquilibration.SphericalPureCapLatitudeLeftSaddle
