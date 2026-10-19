-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
public import Mathlib.Tactic

@[expose] public section

/-!
# Geometric support and row bounds for aligned bumps

The Hilbert-space geometry and actual probability-integral row estimate in
manuscript Lemma `lem:sp-bumps`, equation `eq:sp-bump-row`, are proved here.
A positive trial function supported in a small image ball is contained, on
the good alignment set, in a cap around a normalized image direction.

The bump cutoff, Euclidean volume column bound, mass estimate, and Dirichlet
energy estimate are separate analytic steps and are not claimed in this file.
-/

namespace SlowEquilibration

open MeasureTheory Filter
open scoped InnerProductSpace

section Geometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Positive alignment with a unit vector forces a positive image norm. -/
theorem norm_pos_of_unit_alignment (u b : H) (q : ℝ)
    (hu : ‖u‖ = 1) (halign : q ≤ inner ℝ u b) (hq : 0 < q) :
    0 < ‖b‖ := by
  have hi := real_inner_le_norm u b
  rw [hu, one_mul] at hi
  exact hq.trans_le (halign.trans hi)

/-- The direction obtained by normalizing a nonzero vector is a unit vector. -/
theorem normalized_direction_norm (b : H) (hb : 0 < ‖b‖) :
    ‖(‖b‖)⁻¹ • b‖ = 1 := by
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hb.le), inv_mul_cancel₀ hb.ne']

/-- Two aligned image points at distance at most `2ρ` share a cap of latitude
`q - 2ρ` centered at the normalized first image.  The normalization and cap
inequality are both derived. -/
theorem normalized_direction_cap (ux uy bx b_y : H) (q ρ : ℝ)
    (hux : ‖ux‖ = 1) (huy : ‖uy‖ = 1)
    (halignx : q ≤ inner ℝ ux bx) (haligny : q ≤ inner ℝ uy b_y)
    (hbx : ‖bx‖ ≤ 1) (hclose : ‖b_y - bx‖ ≤ 2 * ρ)
    (hρ : 0 ≤ ρ) (hqρ : 2 * ρ < q) :
    ‖(‖bx‖)⁻¹ • bx‖ = 1 ∧
      q - 2 * ρ ≤ inner ℝ uy ((‖bx‖)⁻¹ • bx) := by
  have hq : 0 < q := lt_of_le_of_lt (mul_nonneg (by norm_num) hρ) hqρ
  have hnorm : 0 < ‖bx‖ := norm_pos_of_unit_alignment ux bx q hux halignx hq
  have hdiff : inner ℝ uy (b_y - bx) ≤ 2 * ρ := by
    have hi := real_inner_le_norm uy (b_y - bx)
    rw [huy, one_mul] at hi
    exact hi.trans hclose
  have hlower : q - 2 * ρ ≤ inner ℝ uy bx := by
    rw [inner_sub_right] at hdiff
    linarith
  refine ⟨normalized_direction_norm bx hnorm, ?_⟩
  rw [real_inner_smul_right, ← div_eq_inv_mul]
  apply (le_div_iff₀ hnorm).2
  have hqρnonneg : 0 ≤ q - 2 * ρ := by linarith
  calc
    (q - 2 * ρ) * ‖bx‖ ≤ q - 2 * ρ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hbx hqρnonneg
    _ ≤ inner ℝ uy bx := hlower

end Geometry

section Measure

variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
    (π : Measure X) [IsProbabilityMeasure π]

/-- The actual inner-product cap of a measurable unit-spin map is measurable. -/
theorem measurableSet_inner_cap (U : X → H) (hU : Measurable U) (v : H) (a : ℝ) :
    MeasurableSet {x | a ≤ inner ℝ (U x) v} := by
  exact measurableSet_le measurable_const ((continuous_id.inner continuous_const).measurable.comp hU)

/-- A measurable `[0,1]` trial function is integrable against a probability
measure. -/
theorem integrable_trial_of_unit_interval (f : X → ℝ) (hf : Measurable f)
    (hzero : ∀ x, 0 ≤ f x) (hone : ∀ x, f x ≤ 1) : Integrable f π := by
  apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
  exact ae_of_all _ (fun x => by simpa [Real.norm_of_nonneg (hzero x)] using hone x)

/-- Actual row bound for an aligned bump at a fixed center.  A good point in
its positive support is chosen only within this proof, so no measurable
selection of centers is required. -/
theorem aligned_bump_row_bound (U B : X → H) (G : Set X) (f : X → ℝ)
    (z : H) (q ρ K : ℝ) (hU : Measurable U) (hG : MeasurableSet G)
    (hf : Measurable f) (hfzero : ∀ x, 0 ≤ f x) (hfone : ∀ x, f x ≤ 1)
    (hunit : ∀ x ∈ G, ‖U x‖ = 1)
    (halign : ∀ x ∈ G, q ≤ inner ℝ (U x) (B x))
    (hB : ∀ x ∈ G, ‖B x‖ ≤ 1)
    (hsupport : ∀ x, 0 < f x → dist (B x) z < ρ)
    (hρ : 0 ≤ ρ) (hqρ : 2 * ρ < q) (hK : 0 ≤ K)
    (hcap : ∀ v : H, ‖v‖ = 1 → π.real {x | q - 2 * ρ ≤ inner ℝ (U x) v} ≤ K) :
    Integrable f π ∧ (∫ x, f x ∂π) ≤ π.real Gᶜ + K := by
  classical
  have hint := integrable_trial_of_unit_interval π f hf hfzero hfone
  refine ⟨hint, ?_⟩
  by_cases hexists : ∃ x, x ∈ G ∧ 0 < f x
  · obtain ⟨x, hxG, hxf⟩ := hexists
    let v : H := (‖B x‖)⁻¹ • B x
    have hq : 0 < q := lt_of_le_of_lt (mul_nonneg (by norm_num) hρ) hqρ
    have hv : ‖v‖ = 1 := normalized_direction_norm (B x)
      (norm_pos_of_unit_alignment (U x) (B x) q (hunit x hxG) (halign x hxG) hq)
    let cap : Set X := {y | q - 2 * ρ ≤ inner ℝ (U y) v}
    have hcapmeas : MeasurableSet cap := measurableSet_inner_cap U hU v (q - 2 * ρ)
    have hcontain : ∀ y ∈ G, 0 < f y → y ∈ cap := by
      intro y hyG hyf
      have hdist : ‖B y - B x‖ ≤ 2 * ρ := by
        have ht := dist_triangle (B y) z (B x)
        have hzx : dist z (B x) < ρ := by simpa [dist_comm] using hsupport x hxf
        have hyz := hsupport y hyf
        rw [dist_eq_norm] at ht
        linarith
      exact (normalized_direction_cap (U x) (U y) (B x) (B y) q ρ
        (hunit x hxG) (hunit y hyG) (halign x hxG) (halign y hyG)
        (hB x hxG) hdist hρ hqρ).2
    have hmajor : ∀ y, f y ≤ Gᶜ.indicator (fun _ => (1 : ℝ)) y +
        cap.indicator (fun _ => (1 : ℝ)) y := by
      intro y
      by_cases hyG : y ∈ G
      · by_cases hyf : 0 < f y
        · have hycap := hcontain y hyG hyf
          simpa [Set.indicator_of_mem, Set.indicator_of_notMem, hyG, hycap] using hfone y
        · have hzero : f y = 0 := le_antisymm (le_of_not_gt hyf) (hfzero y)
          simp only [hzero, Set.indicator, Set.mem_compl_iff, hyG, not_true_eq_false,
            ite_false, zero_add]
          split_ifs <;> norm_num
      · simpa [Set.indicator, hyG] using (hfone y).trans
          (le_add_of_nonneg_right (Set.indicator_nonneg (fun _ _ => (by norm_num : (0 : ℝ) ≤ 1)) y))
    have hbadint : Integrable (Gᶜ.indicator (fun _ : X => (1 : ℝ))) π :=
      (integrable_const 1).indicator hG.compl
    have hcapint : Integrable (cap.indicator (fun _ : X => (1 : ℝ))) π :=
      (integrable_const 1).indicator hcapmeas
    calc
      (∫ y, f y ∂π) ≤ ∫ y, Gᶜ.indicator (fun _ => (1 : ℝ)) y +
          cap.indicator (fun _ => (1 : ℝ)) y ∂π :=
        integral_mono hint (hbadint.add hcapint) hmajor
      _ = π.real Gᶜ + π.real cap := by
        rw [integral_add hbadint hcapint]
        congr 1
        · simpa only [Pi.one_def] using integral_indicator_one (μ := π) hG.compl
        · simpa only [Pi.one_def] using integral_indicator_one (μ := π) hcapmeas
      _ ≤ π.real Gᶜ + K := add_le_add le_rfl (hcap v hv)
  · have hmajor : ∀ y, f y ≤ Gᶜ.indicator (fun _ => (1 : ℝ)) y := by
      intro y
      by_cases hyG : y ∈ G
      · have hyf : ¬ 0 < f y := fun h => hexists ⟨y, hyG, h⟩
        simpa [Set.indicator, hyG] using le_of_not_gt hyf
      · simpa [Set.indicator, hyG] using hfone y
    calc
      (∫ y, f y ∂π) ≤ ∫ y, Gᶜ.indicator (fun _ => (1 : ℝ)) y ∂π :=
        integral_mono hint ((integrable_const 1).indicator hG.compl) hmajor
      _ = π.real Gᶜ := integral_indicator_one hG.compl
      _ ≤ π.real Gᶜ + K := le_add_of_nonneg_right hK

/-- Uniform row bound for a jointly measurable family of actual bumps,
indexed by all image-space centers.  The point used to prove each bound
requires no measurable choice across centers. -/
theorem aligned_bump_family_row_bound (U B : X → H) (G : Set X)
    (f : H → X → ℝ) (q ρ K : ℝ) (hU : Measurable U) (hG : MeasurableSet G)
    (hf : Measurable (Function.uncurry f))
    (hfzero : ∀ z x, 0 ≤ f z x) (hfone : ∀ z x, f z x ≤ 1)
    (hunit : ∀ x ∈ G, ‖U x‖ = 1)
    (halign : ∀ x ∈ G, q ≤ inner ℝ (U x) (B x))
    (hB : ∀ x ∈ G, ‖B x‖ ≤ 1)
    (hsupport : ∀ z x, 0 < f z x → dist (B x) z < ρ)
    (hρ : 0 ≤ ρ) (hqρ : 2 * ρ < q) (hK : 0 ≤ K)
    (hcap : ∀ v : H, ‖v‖ = 1 → π.real {x | q - 2 * ρ ≤ inner ℝ (U x) v} ≤ K) :
    ∀ z, Integrable (f z) π ∧ (∫ x, f z x ∂π) ≤ π.real Gᶜ + K := by
  intro z
  exact aligned_bump_row_bound π U B G (f z) z q ρ K hU hG hf.of_uncurry_left
    (hfzero z) (hfone z) hunit halign hB (hsupport z) hρ hqρ hK hcap

end Measure

end SlowEquilibration
