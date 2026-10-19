-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPureLatitudeContactStationarity

@[expose] public section

/-! The source proper-pure Palm latitude exponent has a unique maximizer
throughout one common energy neighborhood and physical band. -/

namespace SlowEquilibration.SphericalTAPCriticalPureLatitudeBandMaximizer
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeUniformCurvature
set_option autoImplicit false

theorem sourcePureLatitudeExponent_unique_band_maximizer
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let E := markE (FiniteMixture.pure p hp alpha halpha) β x Q
    let q := Real.sqrt Q
    ∃ ε b c : ℝ, 0 < ε ∧ 0 < b ∧ b < q ∧ 0 < c ∧
      Icc (q-b) (q+b) ⊆ Ioo (-1:ℝ) 1 ∧
      ∀ e ∈ Icc (E-ε) (E+ε),
        StrictConcaveOn ℝ (Icc (q-b) (q+b))
          (sourcePureLatitudeExponent p alpha Q β e) ∧
        ∃! a : ℝ, a ∈ Icc (q-b) (q+b) ∧
          IsMaxOn (sourcePureLatitudeExponent p alpha Q β e)
            (Icc (q-b) (q+b)) a := by
  dsimp only
  obtain ⟨ε,b,c,hε,hb,hbq,hc,hband,hcurv⟩ :=
    sourcePureLatitudeExponent_uniform_negative_curvature p hp alpha halpha h
  let E := markE (FiniteMixture.pure p hp alpha halpha) β x Q
  let q := Real.sqrt Q
  refine ⟨ε,b,c,hε,hb,hbq,hc,hband,?_⟩
  intro e he
  let f := sourcePureLatitudeExponent p alpha Q β e
  let D : Set ℝ := Icc (q-b) (q+b)
  have hcont : ContinuousOn f D := by
    intro a ha
    exact (sourcePureLatitudeExponent_hasDerivAt p hp alpha Q β e a
      h.overlap_range.1 (hband ha)).continuousAt.continuousWithinAt
  have hconc : StrictConcaveOn ℝ D f := by
    apply strictConcaveOn_of_deriv2_neg' (convex_Icc _ _) hcont
    intro a ha
    have hneg := hcurv e he a ha
    change deriv (deriv f) a < 0
    exact lt_of_le_of_lt hneg (neg_lt_zero.mpr hc)
  have hqD : q ∈ D := by
    change q ∈ Icc (q-b) (q+b)
    constructor <;> linarith
  obtain ⟨a,ha,hamax⟩ := (isCompact_Icc : IsCompact D).exists_isMaxOn
    ⟨q,hqD⟩ hcont
  refine ⟨hconc,a,⟨ha,hamax⟩,?_⟩
  intro a' ha'
  exact hconc.eq_of_isMaxOn ha'.2 hamax ha'.1 ha

end
end SlowEquilibration.SphericalTAPCriticalPureLatitudeBandMaximizer
