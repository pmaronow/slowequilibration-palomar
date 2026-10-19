-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOENormalizedPotential
public import SlowEquilibration.GOERawMoments

/-! # Actual variance-b/N determinant exponent with a fixed codimension

The dimension m=n+1 and ambient dimension N=m+r have the manuscript's exact
variance b/N. Genuine law scaling and the proved varying-shift GOE prefactors
identify the ordinary expected absolute determinant's exponent.
-/

@[expose] public section

namespace SlowEquilibration.GOEPhysicalPotential

noncomputable section
open MeasureTheory ProbabilityTheory Filter Function
open GOEScaling GOERawMoments GOENormalizedPotential GOEPrefactors
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Literal ordinary expected absolute determinant under the actual matrix law. -/
def physicalMean (n N : ℕ) (b k : ℝ) : ℝ :=
  ∫ W, matrixAbsoluteDet n k W ∂SphericalGaussianJet.goeLaw (n + 1) N b

/-- The exact mean identity includes the deterministic determinant factor. -/
theorem physicalMean_scaling (n : ℕ) {N : ℕ} (hN : 0 < N)
    {b : ℝ} (hb : 0 < b) (k : ℝ) :
    physicalMean n N b k = (scaleFactor n N b) ^ (n + 1) *
      meanAbsolute n (k / scaleFactor n N b) := by
  let a := scaleFactor n N b
  have ha : 0 < a := scaleFactor_pos n hN hb
  have hm : Measurable (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => a • W) := by fun_prop
  unfold physicalMean
  rw [← goeLaw_scale n hN hb.le, integral_map hm.aemeasurable
    (matrixAbsoluteDet_measurable n k).aestronglyMeasurable]
  simp only [matrixAbsoluteDet_scaled n ha k]
  rw [integral_const_mul, ← GOEDeterminantMoments.realization_law n,
    integral_map (GOEDeterminantMoments.realization_measurable n).aemeasurable
      (matrixAbsoluteDet_measurable n (k / a)).aestronglyMeasurable]
  rfl

lemma dimension_ratio_tendsto (r : ℕ) :
    Tendsto (fun n : ℕ => (n + 1 : ℝ) / (n + 1 + r : ℕ)) atTop (𝓝 1) := by
  have h := tendsto_add_mul_div_add_mul_atTop_nhds (𝕜 := ℝ)
    1 (1 + (r : ℝ)) 1 (d := 1) one_ne_zero
  convert h using 1
  · funext n
    simp only [Nat.cast_add, Nat.cast_one, one_mul]
    congr 1 <;> ring
  · simp

lemma scaleFactor_tendsto (r : ℕ) {b : ℝ} (_hb : 0 ≤ b) :
    Tendsto (fun n : ℕ => scaleFactor n (n + 1 + r) b) atTop (𝓝 (Real.sqrt b)) := by
  have h := ((dimension_ratio_tendsto r).const_mul b).sqrt
  simpa only [mul_one, scaleFactor, mul_div_assoc] using h

/-- Actual log-of-expectation leading exponent per matrix dimension, for every
fixed codimension and physical shift strictly above the GOE edge. -/
theorem physical_log_mean_per_matrix_tendsto (r : ℕ) {b k : ℝ}
    (hb : 0 < b) (hk : 2 * Real.sqrt b < k) :
    Tendsto (fun n : ℕ => Real.log (physicalMean n (n + 1 + r) b k) / (n + 1 : ℝ))
      atTop (𝓝 (Real.log (Real.sqrt b) + SemicirclePotential.potential (k / Real.sqrt b))) := by
  have hs := Real.sqrt_pos.mpr hb
  have hz : 2 < k / Real.sqrt b := (lt_div_iff₀ hs).mpr hk
  have ha := scaleFactor_tendsto r hb.le
  have hshift := (tendsto_const_nhds (x := k)).div ha hs.ne'
  have h1 := normalized_log_mean_tendsto
    (fun n => k / scaleFactor n (n + 1 + r) b) hz hshift
  have h2 := ha.log hs.ne'
  convert h2.add h1 using 1
  funext n
  have hN : 0 < n + 1 + r := by omega
  have han := scaleFactor_pos n hN hb
  have hstd : 2 < k / scaleFactor n (n + 1 + r) b := by
    apply (lt_div_iff₀ han).mpr
    exact (mul_le_mul_of_nonneg_left (scaleFactor_le_sqrt hN (by omega) hb.le)
      (by norm_num : (0 : ℝ) ≤ 2)).trans_lt hk
  rw [physicalMean_scaling n hN hb, Real.log_mul (pow_pos han _).ne'
    (meanAbsolute_pos n hstd).ne', Real.log_pow]
  unfold normalizedLogMean
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp

/-- The same genuine exponent per ambient dimension N=m+r, which is the
normalization in the manuscript's one-point critical-point intensity. -/
theorem physical_log_mean_per_ambient_tendsto (r : ℕ) {b k : ℝ}
    (hb : 0 < b) (hk : 2 * Real.sqrt b < k) :
    Tendsto (fun n : ℕ => Real.log (physicalMean n (n + 1 + r) b k) / (n + 1 + r : ℕ))
      atTop (𝓝 (Real.log (Real.sqrt b) + SemicirclePotential.potential (k / Real.sqrt b))) := by
  have h := (physical_log_mean_per_matrix_tendsto r hb hk).mul (dimension_ratio_tendsto r)
  simp only [mul_one] at h
  convert h using 1
  funext n
  have hm : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp

end
end SlowEquilibration.GOEPhysicalPotential
