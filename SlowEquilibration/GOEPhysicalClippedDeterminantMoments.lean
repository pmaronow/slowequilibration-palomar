-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOESpectralScale
public import SlowEquilibration.GOESharpMoments
public import SlowEquilibration.GOEPhysicalPotential

/-! Ordinary clipped determinant moments divided by the actual raw bulk
mean under the literal variance-b/N GOE law. The physical cutoff is displayed
as a_N times the standard cutoff throughout the exact law scaling.
-/
@[expose] public section
namespace SlowEquilibration.GOEPhysicalClippedDeterminantMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics GOEScaling GOEPhysicalPotential GOERawMoments GOEClippedDeterminants
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1100000

def matrixClippedDet (n : ℕ) (k ρ : ℝ)
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : ℝ :=
  Real.exp (∑ i, Real.log (max |k - eigenvalues n W i| ρ))

lemma matrixClippedDet_measurable (n : ℕ) (k ρ : ℝ) : Measurable (matrixClippedDet n k ρ) := by
  unfold matrixClippedDet
  apply Measurable.exp
  exact Finset.measurable_sum _ (fun i _ =>
    (((measurable_const.sub ((measurable_pi_apply i).comp (eigenvalues_measurable n))).abs).max
      measurable_const).log)

lemma matrixClippedDet_pos (n : ℕ) (k ρ : ℝ)
    (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : 0 < matrixClippedDet n k ρ W := Real.exp_pos _

lemma matrixClippedDet_mono_cutoff (n : ℕ) (k : ℝ) {ρ τ : ℝ}
    (hρ : 0 < ρ) (hρτ : ρ ≤ τ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    matrixClippedDet n k ρ W ≤ matrixClippedDet n k τ W := by
  apply Real.exp_le_exp.mpr
  apply Finset.sum_le_sum
  intro i hi
  exact Real.log_le_log (lt_of_lt_of_le hρ (le_max_right _ _)) (max_le_max_left _ hρτ)

lemma matrixClippedDet_realization (n : ℕ) (k ρ : ℝ)
    (A : GaussianMatrix (n + 1)) :
    matrixClippedDet n k ρ (GOEDeterminantMoments.realization n A) =
      Real.exp (clippedTrace n k ρ A) := by
  unfold matrixClippedDet eigenvalues GOEDeterminantMoments.realization clippedTrace
  rw [matrixToGaussian_gaussianToMatrix]
  rfl

/-- Exact scaling of the literal clipped determinant, including the
deterministic dimension factor. -/
theorem matrixClippedDet_scale (n : ℕ) {a ρ : ℝ} (ha : 0 < a) (hρ : 0 < ρ)
    (k : ℝ) (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    matrixClippedDet n k (a * ρ) (a • W) =
      a ^ (n + 1) * matrixClippedDet n (k / a) ρ W := by
  unfold matrixClippedDet
  rw [eigenvalues_spectral_sum_scale n a W (fun z => Real.log (max |k - z| (a * ρ)))]
  have he (z : ℝ) : Real.log (max |k - a * z| (a * ρ)) =
      Real.log a + Real.log (max |k / a - z| ρ) := by
    have hs : k - a * z = a * (k / a - z) := by field_simp
    rw [hs, abs_mul, abs_of_pos ha, ← mul_max_of_nonneg |k / a - z| ρ ha.le,
      Real.log_mul ha.ne' (ne_of_gt (lt_of_lt_of_le hρ (le_max_right _ _)))]
  simp only [he, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  rw [Real.exp_add, ← Real.log_pow, Real.exp_log (pow_pos ha _)]

theorem standard_clipped_normalized_moments_eventually {g ρ : ℝ}
    (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ g / 2) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 2 + g ≤ k → ∀ r : ℝ, 0 ≤ r →
      Integrable (fun W => (matrixClippedDet n k ρ W / physicalMean n (n + 1) 1 k) ^ r)
        (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1) ∧
      (∫ W, (matrixClippedDet n k ρ W / physicalMean n (n + 1) 1 k) ^ r
        ∂SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1) ≤
        (2 : ℝ) ^ r * Real.exp (4 * r ^ 2 / g ^ 2) := by
  filter_upwards [GOESharpMoments.clipped_over_raw_normalized_eventually hg,
    GOESharpMoments.raw_absoluteDet_normalized_eventually hg] with n hclip hraw
  intro k hk r hr
  let μ := SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1
  let m := physicalMean n (n + 1) 1 k
  have hmEq : m = ∫ A, absoluteDet n k A ∂stdGaussian (GaussianMatrix (n + 1)) := by
    unfold m physicalMean
    rw [← GOEDeterminantMoments.realization_law n,
      integral_map (GOEDeterminantMoments.realization_measurable n).aemeasurable
        (matrixAbsoluteDet_measurable n k).aestronglyMeasurable]
    rfl
  have hm : 0 < m := by rw [hmEq]; exact (hraw k hk).2.1
  have hmeas := ((matrixClippedDet_measurable n k (g / 2)).div_const m).pow_const r
  have hI : Integrable (fun W => (matrixClippedDet n k (g / 2) W / m) ^ r) μ := by
    unfold μ
    rw [← GOEDeterminantMoments.realization_law n]
    apply (integrable_map_measure hmeas.aestronglyMeasurable
      (GOEDeterminantMoments.realization_measurable n).aemeasurable).mpr
    simpa only [Function.comp_def, matrixClippedDet_realization, hmEq] using (hclip k hk r hr).1
  have hbound : (∫ W, (matrixClippedDet n k (g / 2) W / m) ^ r ∂μ) ≤
      (2 : ℝ) ^ r * Real.exp (4 * r ^ 2 / g ^ 2) := by
    unfold μ
    rw [← GOEDeterminantMoments.realization_law n,
      integral_map (GOEDeterminantMoments.realization_measurable n).aemeasurable hmeas.aestronglyMeasurable]
    simpa only [matrixClippedDet_realization, hmEq] using (hclip k hk r hr).2
  have hpoint (W) : (matrixClippedDet n k ρ W / m) ^ r ≤
      (matrixClippedDet n k (g / 2) W / m) ^ r :=
    Real.rpow_le_rpow (div_nonneg (matrixClippedDet_pos n k ρ W).le hm.le)
      (div_le_div_of_nonneg_right (matrixClippedDet_mono_cutoff n k hρ hρg W) hm.le) hr
  have hi : Integrable (fun W => (matrixClippedDet n k ρ W / m) ^ r) μ :=
    hI.mono' (((matrixClippedDet_measurable n k ρ).div_const m).pow_const r).aestronglyMeasurable
      (ae_of_all μ (fun W => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg
          (div_nonneg (matrixClippedDet_pos n k ρ W).le hm.le) r)]
        exact hpoint W))
  exact ⟨hi, (integral_mono hi hI hpoint).trans hbound⟩

/-- Genuine physical GOE clipped/raw-mean normalized moments. One matrix
dimension threshold works for every ambient dimension and outside-edge shift. -/
theorem physical_clipped_normalized_moments_eventually {b g ρ : ℝ}
    (hb : 0 < b) (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ g / (2 * Real.sqrt b)) :
    ∀ᶠ n : ℕ in atTop, ∀ N : ℕ, n + 1 ≤ N → ∀ k : ℝ, 2 * Real.sqrt b + g ≤ k →
      ∀ r : ℝ, 0 ≤ r →
      Integrable (fun W => (matrixClippedDet n k (scaleFactor n N b * ρ) W /
        physicalMean n N b k) ^ r) (SphericalGaussianJet.goeLaw (n + 1) N b) ∧
      (∫ W, (matrixClippedDet n k (scaleFactor n N b * ρ) W / physicalMean n N b k) ^ r
        ∂SphericalGaussianJet.goeLaw (n + 1) N b) ≤
        (2 : ℝ) ^ r * Real.exp (4 * b * r ^ 2 / g ^ 2) := by
  have hsb := Real.sqrt_pos.mpr hb
  have hρg' : ρ ≤ (g / Real.sqrt b) / 2 := by simpa only [div_div, mul_comm] using hρg
  filter_upwards [standard_clipped_normalized_moments_eventually (div_pos hg hsb) hρ hρg'] with n hn
  intro N hmN k hk r hr
  have hN : 0 < N := by omega
  let a := scaleFactor n N b
  have ha : 0 < a := scaleFactor_pos n hN hb
  have hap : 0 < a ^ (n + 1) := pow_pos ha _
  have hstd := hn (k / a) (scaled_shift_gap hN hmN hb hg hk) r hr
  have hmean : physicalMean n N b k = a ^ (n + 1) * physicalMean n (n + 1) 1 (k / a) := by
    unfold physicalMean
    rw [← goeLaw_scale n hN hb.le,
      integral_map (show Measurable (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => a • W) from by fun_prop).aemeasurable
        (matrixAbsoluteDet_measurable n k).aestronglyMeasurable]
    simp only [matrixAbsoluteDet_scaled n ha k]
    exact integral_const_mul _ _
  have hm : Measurable (fun W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ => a • W) := by fun_prop
  have hfn := ((matrixClippedDet_measurable n k (a * ρ)).div_const (physicalMean n N b k)).pow_const r
  have he (W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
      (matrixClippedDet n k (a * ρ) (a • W) / physicalMean n N b k) ^ r =
        (matrixClippedDet n (k / a) ρ W / physicalMean n (n + 1) 1 (k / a)) ^ r := by
    rw [matrixClippedDet_scale n ha hρ k, hmean, mul_div_mul_left _ _ hap.ne']
  constructor
  · rw [← goeLaw_scale n hN hb.le]
    apply (integrable_map_measure hfn.aestronglyMeasurable hm.aemeasurable).mpr
    simpa only [Function.comp_def, he] using hstd.1
  · rw [← goeLaw_scale n hN hb.le, integral_map hm.aemeasurable hfn.aestronglyMeasurable]
    simp only [he]
    exact hstd.2.trans_eq (by
      congr 1
      congr 1
      rw [div_pow, Real.sq_sqrt hb.le]
      field_simp)

end
end SlowEquilibration.GOEPhysicalClippedDeterminantMoments
