-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOELogPotential
public import SlowEquilibration.SemicircleInsidePotential

@[expose] public section

/-!
# Actual Whole-line GOE clipping and exact Jacobi coupling

The expected normalized clipped logarithm is compared to the actual clipped Jacobi
logarithmic potential using the proved eigenvalue coupling and genuine Gaussian
concentration. No expected log-determinant limit is a premise.
-/

namespace SlowEquilibration.GOEWholeLineClipping

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open OAI.CriticalSK GOEAsymptotics GOEEdgeConcentration GOEClippedDeterminants
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology

def jacobiNormalizedLog (n : ℕ) (s rho : ℝ) : ℝ :=
  (∑ i, SpectralTraceLipschitz.clippedLog (2+s) rho (2-orderedJacobiGaps n i)) / (n+1 : ℝ)

def normalizedClippedLog (n : ℕ) (s rho : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) : ℝ :=
  clippedTrace n (2 + s) rho A / (n + 1 : ℝ)

def logDeviationBad (n : ℕ) (s rho eps : ℝ) : Set (GOEAsymptotics.GaussianMatrix (n + 1)) :=
  {A | eps < |normalizedClippedLog n s rho A - jacobiNormalizedLog n s rho|}

lemma normalizedClippedLog_difference_of_good (n : ℕ) {h s rho eta : ℝ}
    (hh : 0 ≤ h) (hrho : 0 < rho)
    (hcost : traceCost n h 1 ≤ eta) (A : GOEAsymptotics.GaussianMatrix (n + 1))
    (hgood : GOEDeterminantMoments.realization n A ∈ goodEvent n h 1) :
    |normalizedClippedLog n s rho A - jacobiNormalizedLog n s rho| ≤ 5 * eta / rho := by
  have heta : 0 ≤ eta := (traceCost_nonneg n hh (by norm_num : (0 : ℝ) < 1)).trans hcost
  have heig : eigenvalues n (GOEDeterminantMoments.realization n A) = realizedEigenvalues n A := by
    unfold eigenvalues GOEDeterminantMoments.realization realizedEigenvalues
    rw [matrixToGaussian_gaussianToMatrix]
  have hpoint (i : Fin (n + 1)) :
      |SpectralTraceLipschitz.clippedLog (2 + s) rho (realizedEigenvalues n A i) -
        SpectralTraceLipschitz.clippedLog (2+s) rho (2-orderedJacobiGaps n i)| ≤ 5 * eta / rho := by
    have he := spectralGood_relative_error n hh (by norm_num : (0 : ℝ) < 1) le_rfl hcost hgood i
    rw [heig] at he
    have h4 := orderedJacobiGaps_le_four n i
    have he' := he.trans (by nlinarith : eta * (1 + orderedJacobiGaps n i) ≤ 5 * eta)
    have hl := (SpectralTraceLipschitz.clippedLog_lipschitz (2 + s) hrho).dist_le_mul
      (realizedEigenvalues n A i) (2 - orderedJacobiGaps n i)
    simp only [Real.dist_eq] at hl
    change _ ≤ (1 / rho) * _ at hl
    exact hl.trans (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using
      mul_le_mul_of_nonneg_left he' (by positivity : 0 ≤ 1 / rho))
  unfold normalizedClippedLog jacobiNormalizedLog clippedTrace
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos (by positivity : 0 < (n + 1 : ℝ))]
  apply (div_le_iff₀ (by positivity : 0 < (n + 1 : ℝ))).mpr
  calc
    _ ≤ ∑ i : Fin (n + 1), |SpectralTraceLipschitz.clippedLog (2 + s) rho (realizedEigenvalues n A i) -
        SpectralTraceLipschitz.clippedLog (2+s) rho (2-orderedJacobiGaps n i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (n + 1), 5 * eta / rho := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

lemma logDeviationBad_measurable (n : ℕ) (s : ℝ) {rho : ℝ} (hrho : 0 < rho) (eps : ℝ) :
    MeasurableSet (logDeviationBad n s rho eps) := by
  apply measurableSet_lt measurable_const
  exact (((clippedTrace_lipschitz n (2 + s) hrho).continuous.measurable.div_const _).sub_const _).abs

lemma logDeviation_failure_probability_eventually {h s rho eps : ℝ}
    (hh : 0 ≤ h) (hrho : 0 < rho) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).real (logDeviationBad n s rho eps) ≤
        32 * Real.exp (-h ^ 2) := by
  have hcost := (traceCost_fixed_tendsto hh (by norm_num : (0 : ℝ) < 1)).eventually
    (gt_mem_nhds (by positivity : 0 < eps * rho / 10))
  filter_upwards [hcost, goodEvent_failure_probability_eventually hh (by norm_num : (0 : ℝ) < 1)] with n hcost hprob
  have hsub : logDeviationBad n s rho eps ⊆ GOEDeterminantMoments.realization n ⁻¹' (goodEvent n h 1)ᶜ := by
    intro A hA hgood
    have h := normalizedClippedLog_difference_of_good n (s := s) hh hrho hcost.le A hgood
    have hhalf : 5 * (eps * rho / 10) / rho = eps / 2 := by field_simp; ring
    rw [hhalf] at h
    exact (not_lt_of_ge (h.trans (by linarith))) hA
  have hmap : (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).real
        (GOEDeterminantMoments.realization n ⁻¹' (goodEvent n h 1)ᶜ) =
      (SphericalGaussianJet.goeLaw (n + 1) (n + 1) 1).real (goodEvent n h 1)ᶜ := by
    rw [← GOEDeterminantMoments.realization_law n]
    simp only [Measure.real]
    rw [Measure.map_apply (GOEDeterminantMoments.realization_measurable n) (goodEvent_measurable n h 1).compl]
  exact ((measureReal_mono hsub).trans_eq hmap).trans hprob

/-- Actual normalized clipped logdet converges in probability to the actual
moving deterministic Jacobi logarithmic potential. -/
theorem normalized_clipped_log_minus_jacobi_converges_in_probability
    {s rho eps : ℝ} (hrho : 0 < rho) (heps : 0 < eps) :
    Tendsto (fun n : ℕ =>
      (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).real (logDeviationBad n s rho eps))
      atTop (𝓝 0) :=
  tendsto_zero_of_gaussian_tail_envelope (fun _ => measureReal_nonneg)
    (fun _ hh => logDeviation_failure_probability_eventually hh hrho heps)

lemma normalizedClippedLog_integrable (n : ℕ) (s : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    Integrable (normalizedClippedLog n s rho) (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) :=
  (clippedTrace_integrable n (2 + s) hrho).div_const _

lemma normalizedClippedLog_measurable (n : ℕ) (s : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    Measurable (normalizedClippedLog n s rho) :=
  (clippedTrace_lipschitz n (2 + s) hrho).continuous.measurable.div_const _

lemma normalizedClippedLog_subGaussian (n : ℕ) (s : ℝ) {rho : ℝ} (hrho : 0 < rho) :
    HasSubgaussianMGF (fun A => normalizedClippedLog n s rho A -
      ∫ B, normalizedClippedLog n s rho B ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
      (Real.pi ^ 2 / (2 * rho ^ 2 * (n + 1 : ℝ) ^ 2)).toNNReal
      (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) := by
  have h := (clippedTrace_centered_subGaussian n (2 + s) hrho).const_mul (1 / (n + 1 : ℝ))
  have hc : (⟨(1 / (n + 1 : ℝ)) ^ 2, sq_nonneg _⟩ *
      (Real.pi ^ 2 / (2 * rho ^ 2)).toNNReal : ℝ≥0) =
      (Real.pi ^ 2 / (2 * rho ^ 2 * (n + 1 : ℝ) ^ 2)).toNNReal := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul]
    rw [Real.coe_toNNReal _ (by positivity), Real.coe_toNNReal _ (by positivity)]
    change (1 / (n + 1 : ℝ)) ^ 2 * (Real.pi ^ 2 / (2 * rho ^ 2)) = _
    field_simp
  rw [hc] at h
  apply h.congr
  exact ae_of_all _ (fun A => by
    unfold normalizedClippedLog
    rw [integral_div]
    ring)

/-- A genuine centered MGF and a high-probability neighborhood locate the
actual expectation. This elementary step avoids an expected-limit premise. -/
lemma mean_close_of_subGaussian {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (c : ℝ≥0)
    (hG : HasSubgaussianMGF (fun x => f x - ∫ y, f y ∂μ) c μ)
    (a delta : ℝ) (hdelta : 0 < delta)
    (hprob : μ.real {x | delta < |f x - a|} < 1 / 4)
    (htail : Real.exp (-delta ^ 2 / (2 * (c : ℝ))) < 1 / 4) :
    |(∫ y, f y ∂μ) - a| ≤ 2 * delta := by
  have hcompl := measureReal_compl (μ := μ) (s := {x | delta < |f x - a|})
    (measurableSet_lt measurable_const (hf.sub_const a).abs)
  rw [probReal_univ] at hcompl
  have hright := hG.measure_ge_le hdelta.le
  have hleft := hG.neg.measure_ge_le hdelta.le
  simp only [Pi.neg_apply, neg_sub] at hleft
  apply abs_le.mpr
  constructor
  · by_contra hh
    have hsub : {x | delta < |f x - a|}ᶜ ⊆ {x | delta ≤ f x - ∫ y, f y ∂μ} := by
      intro x hx
      have hx' : |f x - a| ≤ delta := le_of_not_gt hx
      have hlow := (abs_le.mp hx').1
      change delta ≤ _
      linarith
    have hp := measureReal_mono (μ := μ) hsub
    rw [hcompl] at hp
    linarith
  · by_contra hh
    have hsub : {x | delta < |f x - a|}ᶜ ⊆ {x | delta ≤ (∫ y, f y ∂μ) - f x} := by
      intro x hx
      have hx' : |f x - a| ≤ delta := le_of_not_gt hx
      have hupp := (abs_le.mp hx').2
      change delta ≤ _
      linarith
    have hp := measureReal_mono (μ := μ) hsub
    rw [hcompl] at hp
    linarith

lemma normalized_log_tail_tendsto {rho delta : ℝ} (hrho : 0 < rho) (hdelta : 0 < delta) :
    Tendsto (fun n : ℕ => Real.exp (-(n + 1 : ℝ) ^ 2 * rho ^ 2 * delta ^ 2 / Real.pi ^ 2))
      atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
    ((tendsto_pow_atTop two_ne_zero |>.comp hn).atTop_mul_const
      (by positivity : 0 < rho ^ 2 * delta ^ 2 / Real.pi ^ 2))
  convert hh using 1
  funext n
  simp only [Function.comp_def]
  congr 1
  ring

/-- The actual expected normalized clipped logdet differs from the actual
Jacobi log potential by a quantity tending to zero. Both ingredients are proved. -/
theorem expected_normalized_clipped_log_minus_jacobi_tendsto {s rho : ℝ}
    (hrho : 0 < rho) :
    Tendsto (fun n : ℕ =>
      (∫ A, normalizedClippedLog n s rho A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) -
        jacobiNormalizedLog n s rho) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have hprob := (normalized_clipped_log_minus_jacobi_converges_in_probability (s := s) hrho
    (by positivity : 0 < eps / 4)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  have htail := (normalized_log_tail_tendsto hrho (by positivity : 0 < eps / 4)).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  filter_upwards [hprob, htail] with n hprob htail
  have htail' : Real.exp (-(eps / 4) ^ 2 /
      (2 * ((Real.pi ^ 2 / (2 * rho ^ 2 * (n + 1 : ℝ) ^ 2)).toNNReal : ℝ))) < 1 / 4 := by
    rw [Real.coe_toNNReal _ (by positivity)]
    convert htail using 1
    congr 1
    field_simp
  have hmean := mean_close_of_subGaussian (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
    (normalizedClippedLog n s rho) (normalizedClippedLog_measurable n s hrho)
    (Real.pi ^ 2 / (2 * rho ^ 2 * (n + 1 : ℝ) ^ 2)).toNNReal
    (normalizedClippedLog_subGaussian n s hrho) (jacobiNormalizedLog n s rho) (eps / 4)
    (by positivity) hprob htail'
  simpa only [Real.dist_eq, sub_zero] using hmean.trans_lt (by linarith : 2 * (eps / 4) < eps)

end
end SlowEquilibration.GOEWholeLineClipping
