-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEPhysicalPotential

/-! # Exact physical GOE determinant prefactors at fixed codimension

The ordinary actual variance-b/N moments retain bounded prefactors in every
positive matrix dimension m with N=m+j. Their literal exponent is
m (log sqrt(bm/N) + Ω(k/sqrt(bm/N))).
-/

@[expose] public section

namespace SlowEquilibration.GOEPhysicalPrefactors

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Function
open GOEScaling GOERawMoments GOEPrefactors GOEPhysicalPotential
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The source's exact finite-dimensional exponent Λ_(m,N). -/
def physicalRate (n j : ℕ) (b k : ℝ) : ℝ :=
  (n + 1 : ℝ) * (Real.log (scaleFactor n (n + 1 + j) b) +
    SemicirclePotential.potential (k / scaleFactor n (n + 1 + j) b))

lemma scaleFactor_lower (n j : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    Real.sqrt (b / (j + 1 : ℝ)) ≤ scaleFactor n (n + 1 + j) b := by
  apply Real.sqrt_le_sqrt
  have hj : (0 : ℝ) < j + 1 := by positivity
  have hN : (0 : ℝ) < (n + 1 + j : ℕ) := by positivity
  apply (div_le_div_iff₀ hj hN).mpr
  have hn : (0 : ℝ) ≤ n := by positivity
  have hjn : (0 : ℝ) ≤ j := by positivity
  simp only [Nat.cast_add, Nat.cast_one]
  nlinarith [mul_nonneg hn hjn]

lemma shifted_interval {b g k Z : ℝ} (hb : 0 < b) (hg : 0 < g) (n j : ℕ)
    (hk : 2 * Real.sqrt b + g ≤ k) (hZ : k ≤ Z) :
    2 + g / Real.sqrt b ≤ k / scaleFactor n (n + 1 + j) b ∧
      k / scaleFactor n (n + 1 + j) b ≤ Z / Real.sqrt (b / (j + 1 : ℝ)) := by
  have hN : 0 < n + 1 + j := by omega
  have ha := scaleFactor_pos n hN hb
  have hl : 0 < Real.sqrt (b / (j + 1 : ℝ)) := Real.sqrt_pos.mpr (by positivity)
  have hZpos : 0 ≤ Z := by
    have hs : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    linarith
  refine ⟨scaled_shift_gap hN (by omega) hb hg hk, ?_⟩
  calc
    _ ≤ Z / scaleFactor n (n + 1 + j) b := div_le_div_of_nonneg_right hZ ha.le
    _ ≤ _ := div_le_div_of_nonneg_left hZpos hl (scaleFactor_lower n j hb.le)

lemma exp_rate_factor (n j : ℕ) {b : ℝ} (hb : 0 < b) (k : ℝ) :
    Real.exp (physicalRate n j b k) = (scaleFactor n (n + 1 + j) b) ^ (n + 1) *
      Real.exp ((n + 1 : ℝ) * SemicirclePotential.potential (k / scaleFactor n (n + 1 + j) b)) := by
  have ha := scaleFactor_pos n (by omega : 0 < n + 1 + j) hb
  have hlog : (n + 1 : ℝ) * Real.log (scaleFactor n (n + 1 + j) b) =
      Real.log ((scaleFactor n (n + 1 + j) b) ^ (n + 1)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (Real.log_pow (scaleFactor n (n + 1 + j) b) (n + 1)).symm
  rw [physicalRate, mul_add, Real.exp_add, hlog, Real.exp_log (pow_pos ha _)]

/-- Exact lower constant one and uniform finite upper prefactor, for every
actual physical GOE dimension m=N−j≥1 and compact physical shift interval. -/
theorem physical_first_prefactors (j : ℕ) {b g Z : ℝ} (hb : 0 < b) (hg : 0 < g) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ k : ℝ, 2 * Real.sqrt b + g ≤ k → k ≤ Z →
      Real.exp (physicalRate n j b k) ≤ physicalMean n (n + 1 + j) b k ∧
        physicalMean n (n + 1 + j) b k ≤ C * Real.exp (physicalRate n j b k) := by
  obtain ⟨C, hC, h⟩ := canonical_first_prefactors
    (Z := Z / Real.sqrt (b / (j + 1 : ℝ))) (div_pos hg (Real.sqrt_pos.mpr hb))
  refine ⟨C, hC, ?_⟩
  intro n k hk hZ
  have hshift := shifted_interval hb hg n j hk hZ
  have hh := h n (k / scaleFactor n (n + 1 + j) b) hshift.1 hshift.2
  rw [physicalMean_scaling n (by omega) hb, exp_rate_factor n j hb k]
  have hscale := (pow_pos (scaleFactor_pos n (by omega : 0 < n + 1 + j) hb) (n + 1)).le
  exact ⟨mul_le_mul_of_nonneg_left hh.1 hscale,
    (mul_le_mul_of_nonneg_left hh.2 hscale).trans_eq (by ring)⟩

/-- Every real nonnegative ordinary absolute-determinant moment has a true
uniform physical prefactor; actual moment integrability is also proved. -/
theorem physical_moments_prefactors (j : ℕ) {b g Z r : ℝ}
    (hb : 0 < b) (hg : 0 < g) (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ k : ℝ, 2 * Real.sqrt b + g ≤ k → k ≤ Z →
      Integrable (fun W => matrixAbsoluteDet n k W ^ r)
        (SphericalGaussianJet.goeLaw (n + 1) (n + 1 + j) b) ∧
      (∫ W, matrixAbsoluteDet n k W ^ r ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1 + j) b) ≤
        C * Real.exp (r * physicalRate n j b k) := by
  obtain ⟨C, hC, h⟩ := canonical_moments_prefactors
    (Z := Z / Real.sqrt (b / (j + 1 : ℝ))) (div_pos hg (Real.sqrt_pos.mpr hb)) hr
  refine ⟨C, hC, ?_⟩
  intro n k hk hZ
  let a := scaleFactor n (n + 1 + j) b
  have ha : 0 < a := scaleFactor_pos n (by omega) hb
  have hap : 0 < a ^ (n + 1) := pow_pos ha _
  have hshift := shifted_interval hb hg n j hk hZ
  have hh := h n (k / a) hshift.1 hshift.2
  have hm : Measurable (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => a • W) := by fun_prop
  have hd := (matrixAbsoluteDet_measurable n k).pow_const r
  have hmap : (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).map
      (fun A => a • GOEDeterminantMoments.realization n A) =
        SphericalGaussianJet.goeLaw (n + 1) (n + 1 + j) b :=
    scaled_realization_law n (by omega) hb.le
  have hreal : Measurable (fun A : GOEAsymptotics.GaussianMatrix (n + 1) =>
      a • GOEDeterminantMoments.realization n A) :=
    hm.comp (GOEDeterminantMoments.realization_measurable n)
  have he (A : GOEAsymptotics.GaussianMatrix (n + 1)) :
      matrixAbsoluteDet n k (a • GOEDeterminantMoments.realization n A) ^ r =
        (a ^ (n + 1)) ^ r * GOEClippedDeterminants.absoluteDet n (k / a) A ^ r := by
    rw [matrixAbsoluteDet_scaled n ha k, Real.mul_rpow hap.le (by exact abs_nonneg _)]
    rfl
  have hint : Integrable (fun W => matrixAbsoluteDet n k W ^ r)
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1 + j) b) := by
    rw [← hmap]
    apply (integrable_map_measure hd.aestronglyMeasurable hreal.aemeasurable).mpr
    simpa only [Function.comp_def, he] using hh.1.const_mul ((a ^ (n + 1)) ^ r)
  refine ⟨hint, ?_⟩
  rw [← hmap, integral_map hreal.aemeasurable hd.aestronglyMeasurable]
  simp only [he]
  rw [integral_const_mul]
  have hbnd := mul_le_mul_of_nonneg_left hh.2.2.1 (Real.rpow_nonneg hap.le r)
  calc
    _ ≤ _ := hbnd
    _ = C * Real.exp (r * physicalRate n j b k) := by
      rw [Real.rpow_def_of_pos hap, Real.log_pow, mul_left_comm, ← Real.exp_add]
      congr 1
      congr 1
      dsimp only [a, physicalRate]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

end
end SlowEquilibration.GOEPhysicalPrefactors
