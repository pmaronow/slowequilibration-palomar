-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPureCapLatitudeLeftSaddle

@[expose] public section

/-! The one fixed cap latitude of manuscript Lemma 9.13, with the two
strict stochastic margins and the global scalar saddle. -/

namespace SlowEquilibration.SphericalPureCapLatitudeChoice
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeContactValue
open SphericalTAPCriticalPureLatitudeContactCurvature
open SphericalPureCapLatitudeRightSaddle
open SphericalPureCapLatitudeLeftSaddle
open PureStationarity
open scoped Topology
set_option autoImplicit false

/-- Under the printed strict residual margin at the contact, choose one
source cap latitude and retain the strict global saddle conclusions. The
ground-state intensity slope is the actual canonical mark `β x q^p`. -/
theorem sourcePure_cap_latitude_choice_of_residual_margin
    (p : ℕ) (hp : 4 ≤ p) {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p (by omega) 1 (by positivity)) β x Q)
    (hC : pureResidualCoefficient p β (Real.sqrt Q) < 1/2) :
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
      ∀ t ∈ Ico a 1, t ≠ q → Λ t < Λ q := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)
  let E := markE μ β x Q
  let q := Real.sqrt Q
  let Λ := sourcePureLatitudeExponent p 1 Q β E
  obtain ⟨b,hb,hbq,hband,hleft⟩ :=
    sourcePureLatitudeExponent_strictMonoOn_left_of_contact p hp h
  have hright : StrictAntiOn Λ (Ico q 1) :=
    sourcePureLatitudeExponent_strictAntiOn_right_of_contact p hp h
  have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hq1 : q < 1 := by
    rw [←Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
  have hq2 : q^2=Q := Real.sq_sqrt h.overlap_range.1.le
  have hp4 : (4:ℝ) ≤ p := by exact_mod_cast hp
  have hfactor := SphericalTAPCriticalPureLatitudeContactSign.pure_contact_latitude_factor_pos
    p (by omega) 1 (by positivity) h
  have hQhalf : (1/2:ℝ) < Q := by
    have hp0 : (0:ℝ) ≤ p := by positivity
    by_contra hh
    have hQle : Q ≤ 1/2 := le_of_not_gt hh
    have htest : (p:ℝ)*Q ≤ (p:ℝ)/2 := by
      nlinarith [mul_nonneg hp0 (sub_nonneg.mpr hQle)]
    linarith
  have hqhalf : 1/Real.sqrt 2 < q := by
    have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hs2sq : (Real.sqrt 2)^2=2 := Real.sq_sqrt (by norm_num)
    have hhalfSq : (1/Real.sqrt 2)^2=(1/2:ℝ) := by
      field_simp [hs2.ne']
      rw [hs2sq]
    nlinarith [hhalfSq,hq2]
  have hqMargin : β*x*q^p < β*q^p := by
    have hx := mul_lt_mul_of_pos_left h.weight_range.2 h.beta_pos
    have hh := mul_lt_mul_of_pos_right hx (pow_pos hq0 p)
    nlinarith
  have hCcont : ContinuousAt (pureResidualCoefficient p β) q := by
    unfold pureResidualCoefficient pureResidualAtOne
    fun_prop
  have hCapCont : ContinuousAt (fun t : ℝ => β*t^p) q := by fun_prop
  have hEvC : ∀ᶠ t : ℝ in 𝓝 q,
      pureResidualCoefficient p β t < 1/2 :=
    hCcont.eventually (gt_mem_nhds hC)
  have hEvCap : ∀ᶠ t : ℝ in 𝓝 q,
      β*x*q^p < β*t^p :=
    hCapCont.eventually (lt_mem_nhds hqMargin)
  have hEvHalf : ∀ᶠ t : ℝ in 𝓝 q, 1/Real.sqrt 2 < t :=
    eventually_gt_nhds hqhalf
  have hEvBand : ∀ᶠ t : ℝ in 𝓝 q, q-b < t :=
    eventually_gt_nhds (by linarith : q-b < q)
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp
    (hEvC.and (hEvCap.and (hEvHalf.and hEvBand)))
  let d := min δ b/2
  let a := q-d
  have hd0 : 0 < d := by dsimp [d]; positivity
  have hdδ : d < δ := by
    dsimp [d]
    have hh := min_le_left δ b
    linarith
  have hdb : d < b := by
    dsimp [d]
    have hh := min_le_right δ b
    linarith
  have hadist : dist a q < δ := by
    rw [Real.dist_eq]
    dsimp [a]
    rw [show q-d-q=-d by ring,abs_neg,abs_of_pos hd0]
    exact hdδ
  obtain ⟨hCa,hCapa,hHalf,hBand⟩ := hball hadist
  have haLt : a < q := by dsimp [a]; linarith
  have haBand : q-b ≤ a := by dsimp [a]; linarith
  have hleft' : StrictMonoOn Λ (Icc a q) :=
    hleft.mono (by
      intro t ht
      exact ⟨le_trans haBand ht.1,ht.2⟩)
  have hcontact := sourcePureLatitudeExponent_contact_eq_variationalValue
    p (by omega) 1 (by positivity) h
  have hcurv := sourcePureLatitudeExponent_contact_second_deriv_neg
    p (by omega) 1 (by positivity) h
  refine ⟨a,hHalf,haLt,hCa,hCapa,hleft',hright,hcontact,hcurv,?_⟩
  intro t ht htq
  rcases lt_or_gt_of_ne htq with hlt|hgt
  · exact hleft' ⟨le_refl a |>.trans ht.1,hlt.le⟩
      ⟨by linarith,le_refl q⟩ hlt
  · exact hright ⟨le_refl q,hq1⟩ ⟨hgt.le,ht.2⟩ hgt

end
end SlowEquilibration.SphericalPureCapLatitudeChoice
