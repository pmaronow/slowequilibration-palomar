-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapLatitudeChoice
public import SlowEquilibration.CSStability

@[expose] public section

/-! The numerical pure residual margin and the full cap saddle are
consequences of the actual source strict one-step certificate. -/

namespace SlowEquilibration.SphericalPureCapResidualMargin
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile
open SphericalPureCapLatitudeChoice
open PureStationarity PureScalarStatic
set_option autoImplicit false

/-- Canonical pure parameter uniqueness transports the proved source
`159/320` residual bound to the certificate's own contact overlap. -/
theorem sourcePure_certificate_residual_margin
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    pureResidualCoefficient p β (Real.sqrt Q) < 1/2 := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  have hxi : μ.xi = fun r : ℝ => r^p := by
    funext r
    simp only [μ,FiniteMixture.pure_xi,one_mul]
  have hβ := h.superstatic
  rw [hxi] at hβ
  obtain ⟨x',hx',Q',hQ',hlaw',hbound⟩ :=
    canonical_pure_residualCoefficient_bound p hp hβ
  have hQ' : Q' ∈ Ioo (0:ℝ) 1 :=
    ⟨(staticOverlap_mem_Ioo (zParameter_spec p (by omega)).1).1.trans hQ'.1,
      hQ'.2⟩
  have hmine := CSStability.parameters_of_twoAtom μ β h.weight_range
    h.overlap_range h.canonical_law
  have hother := CSStability.parameters_of_twoAtom μ β hx' hQ' hlaw'
  have heq : Q=Q' := hmine.1.symm.trans hother.1
  rw [heq]
  have hq1 : Real.sqrt Q' ≤ 1 := by
    rw [←Real.sqrt_one]
    exact (Real.sqrt_lt_sqrt hQ'.1.le hQ'.2).le
  exact (hbound (Real.sqrt Q') ⟨le_refl _,hq1⟩).trans (by norm_num)

/-- Manuscript Lemma 9.13 in the normalized pure source coordinates,
conditional only on the actual strict certificate. The intensity slope is
represented by the equal canonical scalar mark `β x Q^(p/2)`. -/
theorem sourcePure_cap_latitude_choice
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q) :
    let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
    let E := markE μ β x Q
    let q := Real.sqrt Q
    let Λ := sourcePureLatitudeExponent p 1 Q β E
    ∃ a : ℝ, 1/Real.sqrt 2 < a ∧ a < q ∧
      pureResidualCoefficient p β a < 1/2 ∧
      β*a^p > β*x*q^p ∧
      StrictMonoOn Λ (Icc a q) ∧
      StrictAntiOn Λ (Ico q 1) ∧
      Λ q = CSParisiMeasure.variationalValue μ β ∧
      deriv (deriv Λ) q < 0 ∧
      ∀ t ∈ Ico a 1, t ≠ q → Λ t < Λ q :=
  sourcePure_cap_latitude_choice_of_residual_margin p hp h
    (sourcePure_certificate_residual_margin p hp h)

end
end SlowEquilibration.SphericalPureCapResidualMargin
