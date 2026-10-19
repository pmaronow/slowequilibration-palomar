module
public import FourPapersCommon.MixtureBounds
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! Actual convex covariance and the Guerra tangent remainder. -/
noncomputable section
open Set
namespace FourPapersCommon.AdmissibleEvenMixture

theorem abs_value_le_at_one (ξ : AdmissibleEvenMixture) {q : ℝ} (hq : |q| ≤ 1) :
    |ξ.value q| ≤ ξ.value 1 := by
  calc
    |ξ.value q| ≤ ∑' p, |ξ.coefficient p * q ^ p| := by
      simpa only [value, Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (ξ.summable_value hq).norm
    _ ≤ ∑' p, ξ.coefficient p := Summable.tsum_le_tsum
      (fun p => by
        rw [abs_mul, abs_of_nonneg (ξ.nonneg p), abs_pow]
        simpa only [mul_one] using mul_le_mul_of_nonneg_left
          (pow_le_one₀ (abs_nonneg q) hq (n := p)) (ξ.nonneg p))
      (ξ.summable_value hq).abs ξ.summable_coefficient
    _ = ξ.value 1 := by simp [value]

theorem value_one_nonneg (ξ : AdmissibleEvenMixture) : 0 ≤ ξ.value 1 :=
  (abs_nonneg _).trans (ξ.abs_value_le_at_one (q := 0) (by norm_num))

theorem abs_first_le_variance (ξ : AdmissibleEvenMixture) {q : ℝ} (hq : |q| ≤ 1) :
    |ξ.first q| ≤ ξ.variance := by
  have hm := ξ.first_strictMonoOn.monotoneOn
  apply abs_le.mpr
  constructor
  · have hh := hm (show (-1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)
      (abs_le.mp hq) (abs_le.mp hq).1
    simpa only [ξ.first_odd, AdmissibleEvenMixture.variance] using hh
  · exact hm (abs_le.mp hq) (show (1 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num) (abs_le.mp hq).2

theorem strictConvexOn_value (ξ : AdmissibleEvenMixture) :
    StrictConvexOn ℝ (Icc (-1 : ℝ) 1) ξ.value := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc _ _) ξ.continuousOn_value
  rw [interior_Icc]
  intro x hx y hy hxy
  rw [(ξ.hasDerivAt_value (by rw [abs_lt]; constructor <;> linarith [hx.1, hx.2])).deriv,
    (ξ.hasDerivAt_value (by rw [abs_lt]; constructor <;> linarith [hy.1, hy.2])).deriv]
  exact ξ.first_strictMonoOn ⟨hx.1.le, hx.2.le⟩ ⟨hy.1.le, hy.2.le⟩ hxy

theorem convexOn_value (ξ : AdmissibleEvenMixture) : ConvexOn ℝ (Icc (-1 : ℝ) 1) ξ.value :=
  ξ.strictConvexOn_value.convexOn

def tangentRemainder (ξ : AdmissibleEvenMixture) (r q : ℝ) : ℝ :=
  ξ.value r - ξ.value q - ξ.first q * (r - q)

def correction (ξ : AdmissibleEvenMixture) (q : ℝ) : ℝ := q * ξ.first q - ξ.value q

theorem abs_correction_le (ξ : AdmissibleEvenMixture) {q : ℝ} (hq : |q| ≤ 1) :
    |ξ.correction q| ≤ ξ.variance + ξ.value 1 := by
  calc
    _ ≤ |q * ξ.first q| + |ξ.value q| := abs_sub _ _
    _ ≤ ξ.variance + ξ.value 1 := add_le_add (by
      rw [abs_mul]
      have hh := mul_le_mul hq (ξ.abs_first_le_variance hq)
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
      simpa only [one_mul] using hh) (ξ.abs_value_le_at_one hq)

@[simp] theorem correction_one (ξ : AdmissibleEvenMixture) :
    ξ.correction 1 = ξ.variance - ξ.value 1 := by simp [correction, variance]

theorem tangentRemainder_eq (ξ : AdmissibleEvenMixture) (r q : ℝ) :
    ξ.tangentRemainder r q = ξ.value r - r * ξ.first q + ξ.correction q := by
  simp only [tangentRemainder, correction]
  ring

theorem tangentRemainder_nonneg (ξ : AdmissibleEvenMixture) {r q : ℝ}
    (hr : r ∈ Icc (-1 : ℝ) 1) (hq : q ∈ Icc (-1 : ℝ) 1) :
    0 ≤ ξ.tangentRemainder r q := by
  rcases lt_trichotomy r q with hrq | rfl | hqr
  · have hh := ξ.convexOn_value.slope_le_of_hasDerivAt hr hq hrq
      (ξ.hasDerivAt_value_unit hq)
    rw [slope_def_field] at hh
    have hp := (div_le_iff₀ (sub_pos.mpr hrq)).mp hh
    unfold tangentRemainder
    nlinarith
  · simp [tangentRemainder]
  · have hh := ξ.convexOn_value.le_slope_of_hasDerivAt hq hr hqr
      (ξ.hasDerivAt_value_unit hq)
    rw [slope_def_field] at hh
    have hp := (le_div_iff₀ (sub_pos.mpr hqr)).mp hh
    unfold tangentRemainder
    nlinarith

theorem correction_nonneg (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : q ∈ Icc (-1 : ℝ) 1) : 0 ≤ ξ.correction q := by
  simpa [tangentRemainder, correction, ξ.value_zero, mul_comm] using
    ξ.tangentRemainder_nonneg (r := 0) (by norm_num) hq

theorem hasDerivAt_correction (ξ : AdmissibleEvenMixture) {q : ℝ}
    (hq : |q| < 5/4) : HasDerivAt ξ.correction (q * ξ.second q) q := by
  convert ((hasDerivAt_id q).mul (ξ.hasDerivAt_first hq)).sub (ξ.hasDerivAt_value hq) using 1
  · rfl
  · simp only [id_eq]
    ring

theorem convex_covariance_block_bound (ξ : AdmissibleEvenMixture) {r s : ℝ}
    (hr : r ∈ Icc (-1 : ℝ) 1) (hs : s ∈ Icc (-1 : ℝ) 1) (N M : ℝ)
    (hN : 0 < N) (hM : 0 < M) :
    (N + M) * ξ.value ((N * r + M * s) / (N + M)) ≤ N * ξ.value r + M * ξ.value s := by
  have hNM : 0 < N + M := add_pos hN hM
  have ha : 0 ≤ N / (N + M) := div_nonneg hN.le hNM.le
  have hb : 0 ≤ M / (N + M) := div_nonneg hM.le hNM.le
  have he : N / (N + M) + M / (N + M) = 1 := by field_simp
  have hh := ξ.convexOn_value.2 hr hs ha hb he
  simp only [smul_eq_mul] at hh
  have hc : N / (N + M) * r + M / (N + M) * s = (N * r + M * s) / (N + M) := by ring
  rw [hc] at hh
  have hm := mul_le_mul_of_nonneg_left hh hNM.le
  field_simp at hm
  nlinarith

end FourPapersCommon.AdmissibleEvenMixture
