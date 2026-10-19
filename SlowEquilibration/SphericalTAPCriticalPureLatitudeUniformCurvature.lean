-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCriticalPureLatitudeContactCurvature

@[expose] public section

/-! The strict pure contact curvature persists on one common positive
energy-and-latitude rectangle, as required by the source neighborhood choice. -/

namespace SlowEquilibration.SphericalTAPCriticalPureLatitudeUniformCurvature
noncomputable section
open Set SphericalTAPCertificate TwoAtomStationarity
open SphericalTAPCriticalPureLatitudeProfile
open SphericalTAPCriticalPureLatitudeVariance
open SphericalTAPCriticalPureLatitudeContactCurvature
open scoped Topology
set_option autoImplicit false

private theorem curvature_continuousAt
    (p : ℕ) (alpha Q β E a : ℝ) (hQ : 0 < Q)
    (ha : a ∈ Ioo (-1:ℝ) 1) :
    ContinuousAt (fun z : ℝ × ℝ =>
      sourcePureLatitudeExponentCurvature p alpha Q β z.1 z.2) (E,a) := by
  have hq : Real.sqrt Q ≠ 0 := (Real.sqrt_pos.mpr hQ).ne'
  have hs : 1-a^2 ≠ 0 := by
    apply ne_of_gt
    nlinarith [ha.1,ha.2]
  have hq2 : (Real.sqrt Q)^2 ≠ 0 := pow_ne_zero _ hq
  have hs2 : (1-a^2)^2 ≠ 0 := pow_ne_zero _ hs
  unfold sourcePureLatitudeExponentCurvature
    sourcePureLatitudeVarianceCurvature
  fun_prop (disch := assumption)

/-- One common proper-pure energy window and latitude band have a uniform
strictly negative *actual* second derivative of the printed exponent. -/
theorem sourcePureLatitudeExponent_uniform_negative_curvature
    (p : ℕ) (hp : 2 ≤ p) (alpha : ℝ) (halpha : 0 < alpha)
    {β x Q : ℝ}
    (h : Certificate (FiniteMixture.pure p hp alpha halpha) β x Q) :
    let E := markE (FiniteMixture.pure p hp alpha halpha) β x Q
    let q := Real.sqrt Q
    ∃ ε b c : ℝ, 0 < ε ∧ 0 < b ∧ b < q ∧ 0 < c ∧
      Icc (q-b) (q+b) ⊆ Ioo (-1:ℝ) 1 ∧
      ∀ e ∈ Icc (E-ε) (E+ε), ∀ a ∈ Icc (q-b) (q+b),
        deriv (deriv (sourcePureLatitudeExponent p alpha Q β e)) a ≤ -c := by
  dsimp only
  let E := markE (FiniteMixture.pure p hp alpha halpha) β x Q
  let q := Real.sqrt Q
  let f : ℝ × ℝ → ℝ := fun z =>
    sourcePureLatitudeExponentCurvature p alpha Q β z.1 z.2
  have hq0 : 0 < q := Real.sqrt_pos.mpr h.overlap_range.1
  have hq1 : q < 1 := by
    dsimp [q]
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt h.overlap_range.1.le h.overlap_range.2
  have hqmem : q ∈ Ioo (-1:ℝ) 1 := ⟨by linarith,hq1⟩
  have hval : f (E,q) < 0 := by
    have hh := sourcePureLatitudeExponent_contact_second_deriv_neg
      p hp alpha halpha h
    rw [sourcePureLatitudeExponent_second_deriv p hp alpha Q β E q
      h.overlap_range.1 hqmem] at hh
    exact hh
  let c := -f (E,q)/2
  have hc : 0 < c := by dsimp [c]; linarith
  have hct : ContinuousAt f (E,q) :=
    curvature_continuousAt p alpha Q β E q h.overlap_range.1 hqmem
  have hnear : ∀ᶠ z : ℝ × ℝ in 𝓝 (E,q), f z < -c :=
    hct.tendsto.eventually (gt_mem_nhds (by dsimp [c]; linarith))
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hnear
  let δ := min (min (r/2) (q/2)) ((1-q)/2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ < r := by
    have h1 := min_le_left (min (r/2) (q/2)) ((1-q)/2)
    have h2 := min_le_left (r/2) (q/2)
    dsimp [δ] at *
    linarith
  have hδq : δ < q := by
    have h1 := min_le_left (min (r/2) (q/2)) ((1-q)/2)
    have h2 := min_le_right (r/2) (q/2)
    dsimp [δ] at *
    linarith
  have hδ1 : δ < 1-q := by
    have h1 := min_le_right (min (r/2) (q/2)) ((1-q)/2)
    dsimp [δ] at *
    linarith
  refine ⟨δ,δ,c,hδ,hδ,hδq,hc,?_,?_⟩
  · intro a ha
    constructor <;> linarith [ha.1,ha.2]
  · intro e he a ha
    have hamem : a ∈ Ioo (-1:ℝ) 1 := by
      constructor <;> linarith [ha.1,ha.2]
    rw [sourcePureLatitudeExponent_second_deriv p hp alpha Q β e a
      h.overlap_range.1 hamem]
    have hd : dist (e,a) (E,q) < r := by
      rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
      apply max_lt
      · apply lt_of_le_of_lt (abs_le.mpr ?_) hδr
        constructor <;> linarith [he.1,he.2]
      · apply lt_of_le_of_lt (abs_le.mpr ?_) hδr
        constructor <;> linarith [ha.1,ha.2]
    exact (hball hd).le

end
end SlowEquilibration.SphericalTAPCriticalPureLatitudeUniformCurvature
