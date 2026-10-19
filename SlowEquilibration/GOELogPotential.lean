-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOERawMoments

@[expose] public section

/-!
# Actual outside-edge GOE clipped logarithmic potentials

The expected normalized clipped logarithm is compared to the actual Jacobi
logarithmic potential using the proved eigenvalue coupling and genuine Gaussian
concentration. No expected log-determinant limit is a premise.
-/

namespace SlowEquilibration.GOELogPotential

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open OAI.CriticalSK GOEAsymptotics GOEEdgeConcentration GOEClippedDeterminants
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology

def jacobiNormalizedLog (n : ℕ) (s : ℝ) : ℝ :=
  (∑ i, Real.log (s + orderedJacobiGaps n i)) / (n + 1 : ℝ)

def normalizedClippedLog (n : ℕ) (s rho : ℝ) (A : GOEAsymptotics.GaussianMatrix (n + 1)) : ℝ :=
  clippedTrace n (2 + s) rho A / (n + 1 : ℝ)

def logDeviationBad (n : ℕ) (s rho eps : ℝ) : Set (GOEAsymptotics.GaussianMatrix (n + 1)) :=
  {A | eps < |normalizedClippedLog n s rho A - jacobiNormalizedLog n s|}

lemma jacobi_clippedLog_eq (n : ℕ) {s rho : ℝ} (hs : 0 < s) (hrhos : rho ≤ s) (i : Fin (n + 1)) :
    SpectralTraceLipschitz.clippedLog (2 + s) rho (2 - orderedJacobiGaps n i) =
      Real.log (s + orderedJacobiGaps n i) := by
  have hg := orderedJacobiGaps_nonneg n i
  unfold SpectralTraceLipschitz.clippedLog
  rw [show 2 + s - (2 - orderedJacobiGaps n i) = s + orderedJacobiGaps n i by ring,
    abs_of_pos (by linarith), max_eq_left (by linarith)]

lemma normalizedClippedLog_difference_of_good (n : ℕ) {h s rho eta : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hrho : 0 < rho) (hrhos : rho ≤ s)
    (hcost : traceCost n h 1 ≤ eta) (A : GOEAsymptotics.GaussianMatrix (n + 1))
    (hgood : GOEDeterminantMoments.realization n A ∈ goodEvent n h 1) :
    |normalizedClippedLog n s rho A - jacobiNormalizedLog n s| ≤ 5 * eta / rho := by
  have heta : 0 ≤ eta := (traceCost_nonneg n hh (by norm_num : (0 : ℝ) < 1)).trans hcost
  have heig : eigenvalues n (GOEDeterminantMoments.realization n A) = realizedEigenvalues n A := by
    unfold eigenvalues GOEDeterminantMoments.realization realizedEigenvalues
    rw [matrixToGaussian_gaussianToMatrix]
  have hpoint (i : Fin (n + 1)) :
      |SpectralTraceLipschitz.clippedLog (2 + s) rho (realizedEigenvalues n A i) -
        Real.log (s + orderedJacobiGaps n i)| ≤ 5 * eta / rho := by
    have he := spectralGood_relative_error n hh (by norm_num : (0 : ℝ) < 1) le_rfl hcost hgood i
    rw [heig] at he
    have h4 := orderedJacobiGaps_le_four n i
    have he' := he.trans (by nlinarith : eta * (1 + orderedJacobiGaps n i) ≤ 5 * eta)
    have hl := (SpectralTraceLipschitz.clippedLog_lipschitz (2 + s) hrho).dist_le_mul
      (realizedEigenvalues n A i) (2 - orderedJacobiGaps n i)
    rw [jacobi_clippedLog_eq n hs hrhos i] at hl
    simp only [Real.dist_eq] at hl
    change _ ≤ (1 / rho) * _ at hl
    exact hl.trans (by simpa only [div_eq_mul_inv, one_mul, mul_one, mul_comm] using
      mul_le_mul_of_nonneg_left he' (by positivity : 0 ≤ 1 / rho))
  unfold normalizedClippedLog jacobiNormalizedLog clippedTrace
  rw [← sub_div, ← Finset.sum_sub_distrib, abs_div, abs_of_pos (by positivity : 0 < (n + 1 : ℝ))]
  apply (div_le_iff₀ (by positivity : 0 < (n + 1 : ℝ))).mpr
  calc
    _ ≤ ∑ i : Fin (n + 1), |SpectralTraceLipschitz.clippedLog (2 + s) rho (realizedEigenvalues n A i) -
        Real.log (s + orderedJacobiGaps n i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (n + 1), 5 * eta / rho := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

lemma logDeviationBad_measurable (n : ℕ) (s : ℝ) {rho : ℝ} (hrho : 0 < rho) (eps : ℝ) :
    MeasurableSet (logDeviationBad n s rho eps) := by
  apply measurableSet_lt measurable_const
  exact (((clippedTrace_lipschitz n (2 + s) hrho).continuous.measurable.div_const _).sub_const _).abs

lemma logDeviation_failure_probability_eventually {h s rho eps : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hrho : 0 < rho) (hrhos : rho ≤ s) (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop,
      (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).real (logDeviationBad n s rho eps) ≤
        32 * Real.exp (-h ^ 2) := by
  have hcost := (traceCost_fixed_tendsto hh (by norm_num : (0 : ℝ) < 1)).eventually
    (gt_mem_nhds (by positivity : 0 < eps * rho / 10))
  filter_upwards [hcost, goodEvent_failure_probability_eventually hh (by norm_num : (0 : ℝ) < 1)] with n hcost hprob
  have hsub : logDeviationBad n s rho eps ⊆ GOEDeterminantMoments.realization n ⁻¹' (goodEvent n h 1)ᶜ := by
    intro A hA hgood
    have h := normalizedClippedLog_difference_of_good n hh hs hrho hrhos hcost.le A hgood
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
    {s rho eps : ℝ} (hs : 0 < s) (hrho : 0 < rho) (hrhos : rho ≤ s) (heps : 0 < eps) :
    Tendsto (fun n : ℕ =>
      (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))).real (logDeviationBad n s rho eps))
      atTop (𝓝 0) :=
  tendsto_zero_of_gaussian_tail_envelope (fun _ => measureReal_nonneg)
    (fun _ hh => logDeviation_failure_probability_eventually hh hs hrho hrhos heps)

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
    (hs : 0 < s) (hrho : 0 < rho) (hrhos : rho ≤ s) :
    Tendsto (fun n : ℕ =>
      (∫ A, normalizedClippedLog n s rho A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) -
        jacobiNormalizedLog n s) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have hprob := (normalized_clipped_log_minus_jacobi_converges_in_probability hs hrho hrhos
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
    (normalizedClippedLog_subGaussian n s hrho) (jacobiNormalizedLog n s) (eps / 4)
    (by positivity) hprob htail'
  simpa only [Real.dist_eq, sub_zero] using hmean.trans_lt (by linarith : 2 * (eps / 4) < eps)

def jacobiNormalizedResolvent (n : ℕ) (s : ℝ) : ℝ :=
  (∑ i, (s + orderedJacobiGaps n i)⁻¹) / (n + 1 : ℝ)

lemma jacobiNormalizedLog_hasDerivAt (n : ℕ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (jacobiNormalizedLog n) (jacobiNormalizedResolvent n s) s := by
  unfold jacobiNormalizedLog jacobiNormalizedResolvent
  convert (HasDerivAt.fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (n + 1)))) =>
    ((hasDerivAt_id s).add_const (orderedJacobiGaps n i)).log
      (add_pos_of_pos_of_nonneg hs (orderedJacobiGaps_nonneg n i)).ne')).div_const (n + 1 : ℝ) using 1
  <;> simp

lemma jacobiNormalizedResolvent_continuousOn (n : ℕ) {a b : ℝ} (ha : 0 < a) :
    ContinuousOn (jacobiNormalizedResolvent n) (Icc a b) := by
  unfold jacobiNormalizedResolvent
  apply ContinuousOn.div_const
  apply continuousOn_finsetSum
  intro i _
  apply (continuousOn_id.add_const _).inv₀
  intro u hu
  exact (add_pos_of_pos_of_nonneg (ha.trans_le hu.1) (orderedJacobiGaps_nonneg n i)).ne'

lemma semicircleResolvent_continuous : Continuous OAI.CriticalSK.semicircleResolvent := by
  unfold OAI.CriticalSK.semicircleResolvent
  fun_prop

/-- The deterministic actual Jacobi log potential is a true primitive of its
actual resolvent, by finite-dimensional differentiation and ordinary FTC. -/
theorem jacobi_log_difference_eq_integral (n : ℕ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    jacobiNormalizedLog n b - jacobiNormalizedLog n a =
      ∫ u in a..b, jacobiNormalizedResolvent n u := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    rw [uIcc_of_le hab] at hu
    exact jacobiNormalizedLog_hasDerivAt n (ha.trans_le hu.1)
  · exact (jacobiNormalizedResolvent_continuousOn n ha).intervalIntegrable_of_Icc hab

lemma jacobi_resolvent_error_uniform_eventually {a b : ℝ} (ha : 0 < a) :
    ∀ᶠ n : ℕ in atTop, ∀ u ∈ Icc a b,
      |jacobiNormalizedResolvent n u - OAI.CriticalSK.semicircleResolvent u| ≤ 2 / ((n + 1 : ℝ) * a) := by
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hscale := ((hn.atTop_mul_const ha).atTop_mul_const (Real.sqrt_pos.mpr ha)).eventually
    (eventually_ge_atTop 2)
  filter_upwards [hscale] with n hn
  intro u hu
  have hu0 : 0 < u := ha.trans_le hu.1
  have hsqrt := Real.sqrt_le_sqrt hu.1
  have hmul : (n + 1 : ℝ) * a * Real.sqrt a ≤ (n + 1 : ℝ) * u * Real.sqrt u := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hu.1 (by positivity)) hsqrt
      (Real.sqrt_nonneg _) (by positivity)
  have h := (orderedJacobi_trace n hu0 (hn.trans hmul)).2.1
  exact h.trans (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (by positivity : 0 < (n + 1 : ℝ) * a) (mul_le_mul_of_nonneg_left hu.1 (by positivity)))

/-- The actual Jacobi logarithmic potential differences converge to the
integral of the derived semicircle resolvent, with no log-potential limit input. -/
theorem jacobi_log_difference_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => jacobiNormalizedLog n b - jacobiNormalizedLog n a) atTop
      (𝓝 (∫ u in a..b, OAI.CriticalSK.semicircleResolvent u)) := by
  have hbound := jacobi_resolvent_error_uniform_eventually (b := b) ha
  have herror : ∀ᶠ n : ℕ in atTop,
      |(jacobiNormalizedLog n b - jacobiNormalizedLog n a) -
        (∫ u in a..b, OAI.CriticalSK.semicircleResolvent u)| ≤
      2 / ((n + 1 : ℝ) * a) * (b - a) := by
    filter_upwards [hbound] with n hn
    have hiJ : IntervalIntegrable (jacobiNormalizedResolvent n) volume a b :=
      (jacobiNormalizedResolvent_continuousOn n ha).intervalIntegrable_of_Icc hab
    have hiS : IntervalIntegrable OAI.CriticalSK.semicircleResolvent volume a b :=
      semicircleResolvent_continuous.intervalIntegrable a b
    rw [jacobi_log_difference_eq_integral n ha hab, ← intervalIntegral.integral_sub hiJ hiS]
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun u => jacobiNormalizedResolvent n u - OAI.CriticalSK.semicircleResolvent u)
      (C := 2 / ((n + 1 : ℝ) * a)) (fun u hu => by
        rw [uIoc_of_le hab] at hu
        simpa only [Real.norm_eq_abs] using hn u ⟨hu.1.le, hu.2⟩)
    simpa only [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] using h
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hlim := (hn.atTop_mul_const ha).const_div_atTop 2 |>.mul_const (b - a)
  simp only [zero_mul] at hlim
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  filter_upwards [herror, hlim.eventually (gt_mem_nhds heps)] with n herror hsmall
  simpa only [Real.dist_eq] using herror.trans_lt hsmall

/-- Expected actual GOE logarithmic potential differences have the same
outside-edge primitive limit. Both expectations are genuine Gaussian integrals. -/
theorem expected_clipped_log_difference_tendsto {a b rho : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hrho : 0 < rho) (hrhoa : rho ≤ a) :
    Tendsto (fun n : ℕ =>
      (∫ A, normalizedClippedLog n b rho A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) -
      (∫ A, normalizedClippedLog n a rho A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))))
      atTop (𝓝 (∫ u in a..b, OAI.CriticalSK.semicircleResolvent u)) := by
  have haMean := expected_normalized_clipped_log_minus_jacobi_tendsto ha hrho hrhoa
  have hbMean := expected_normalized_clipped_log_minus_jacobi_tendsto (ha.trans_le hab) hrho (hrhoa.trans hab)
  have hJ := jacobi_log_difference_tendsto ha hab
  convert (hbMean.sub haMean).add hJ using 1
  · funext n
    ring
  · simp

/-- The expected ordinary determinant and the true expected clipped logarithm
have logarithms within a dimension-independent interval. -/
lemma log_expected_dominated_exponential_bounds {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y D : Ω → ℝ)
    (hY : Integrable Y μ) (hD : AEMeasurable D μ) (c : ℝ≥0)
    (hG : HasSubgaussianMGF (fun x => Y x - ∫ y, Y y ∂μ) c μ)
    (B : Set Ω) (hB : MeasurableSet B)
    (hdom : ∀ᵐ x ∂μ, 0 ≤ D x ∧ D x ≤ Real.exp (Y x))
    (heq : ∀ᵐ x ∂μ, x ∉ B → D x = Real.exp (Y x))
    (hsmall : Real.exp (c : ℝ) * Real.sqrt (μ.real B) ≤ 1 / 2) :
    -Real.log 2 ≤ Real.log (∫ y, D y ∂μ) - ∫ y, Y y ∂μ ∧
      Real.log (∫ y, D y ∂μ) - ∫ y, Y y ∂μ ≤ (c : ℝ) / 2 := by
  have hbase := RareEventMomentTransfer.normalized_dominated_exponential_moments
    Y D hY hD c hG B hB hdom heq hsmall
  let m := ∫ y, Y y ∂μ
  have hExp : Integrable (fun x => Real.exp (Y x)) μ := by
    apply ((hG.integrable_exp_mul 1).mul_const (Real.exp m)).congr
    exact ae_of_all μ (fun x => by simp only [one_mul]; rw [← Real.exp_add]; congr 1; dsimp [m]; ring)
  have hInt : (∫ x, D x ∂μ) ≤ ∫ x, Real.exp (Y x) ∂μ :=
    integral_mono_ae hbase.1 hExp (hdom.mono fun _ hx => hx.2)
  have hfun : (fun x => Real.exp (Y x)) = fun x => Real.exp m * Real.exp (Y x - m) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  have hmgf := hG.mgf_le 1
  simp only [mgf, one_mul, one_pow, mul_one] at hmgf
  have hupper : (∫ x, D x ∂μ) ≤ Real.exp (m + (c : ℝ) / 2) := by
    apply hInt.trans
    rw [hfun, integral_const_mul, Real.exp_add]
    exact mul_le_mul_of_nonneg_left hmgf (Real.exp_pos m).le
  have hlogupper := (Real.log_le_iff_le_exp hbase.2.2.1).mpr hupper
  have hloglower : m - Real.log 2 ≤ Real.log (∫ y, D y ∂μ) := by
    apply (Real.le_log_iff_exp_le hbase.2.2.1).mpr
    rw [Real.exp_sub, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact hbase.2.1
  constructor <;> linarith

def logMeanAbsoluteDet (n : ℕ) (s : ℝ) : ℝ :=
  Real.log (∫ A, absoluteDet n (2 + s) A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) /
    (n + 1 : ℝ)

lemma log_mean_minus_expected_clipped_tendsto {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => logMeanAbsoluteDet n s -
      ∫ A, normalizedClippedLog n s (s / 2) A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
      atTop (𝓝 0) := by
  let C := Real.log 2 + (Real.pi ^ 2 / (2 * (s / 2) ^ 2)) / 2
  have hbound : ∀ᶠ n : ℕ in atTop,
      |logMeanAbsoluteDet n s -
        ∫ A, normalizedClippedLog n s (s / 2) A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))| ≤
      C / (n + 1 : ℝ) := by
    filter_upwards [GOERawMoments.clipping_smallness_eventually hs] with n hsmall
    have hrho : 0 < s / 2 := by positivity
    have h := log_expected_dominated_exponential_bounds
      (stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
      (clippedTrace n (2 + s) (s / 2)) (absoluteDet n (2 + s))
      (clippedTrace_integrable n (2 + s) hrho) (absoluteDet_measurable n (2 + s)).aemeasurable
      (Real.pi ^ 2 / (2 * (s / 2) ^ 2)).toNNReal (clippedTrace_centered_subGaussian n (2 + s) hrho)
      (gapBad n s) (gapBad_measurable n s)
      (ae_of_all _ (fun A => ⟨absoluteDet_nonneg n (2 + s) A, absoluteDet_le_exp_clippedTrace n (2 + s) hrho A⟩))
      (ae_of_all _ (fun A hA => absoluteDet_eq_clipped_of_not_bad n hs le_rfl A hA))
      (by rw [Real.coe_toNNReal _ (by positivity)]; exact hsmall)
    rw [Real.coe_toNNReal _ (by positivity)] at h
    have hlog2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hc : (0 : ℝ) ≤ Real.pi ^ 2 / (2 * (s / 2) ^ 2) := by positivity
    have habs : |Real.log (∫ A, absoluteDet n (2 + s) A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))) -
        ∫ A, clippedTrace n (2 + s) (s / 2) A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1))| ≤ C := by
      apply abs_le.mpr
      dsimp [C]
      constructor <;> linarith [h.1, h.2]
    unfold logMeanAbsoluteDet normalizedClippedLog
    rw [integral_div, ← sub_div, abs_div, abs_of_pos (by positivity : 0 < (n + 1 : ℝ))]
    exact div_le_div_of_nonneg_right habs (by positivity)
  have hn : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hlim := hn.const_div_atTop C
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  filter_upwards [hbound, hlim.eventually (gt_mem_nhds heps)] with n hn hsmall
  simpa only [Real.dist_eq, sub_zero] using hn.trans_lt hsmall

/-- The normalized logarithm of the expectation of the ordinary absolute GOE
determinant differs from the actual Jacobi potential by a vanishing amount. -/
theorem log_expected_absolute_det_minus_jacobi_tendsto {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => logMeanAbsoluteDet n s - jacobiNormalizedLog n s) atTop (𝓝 0) := by
  have h1 := log_mean_minus_expected_clipped_tendsto hs
  have h2 := expected_normalized_clipped_log_minus_jacobi_tendsto hs (by positivity : 0 < s / 2)
    (by linarith : s / 2 ≤ s)
  convert h1.add h2 using 1
  · funext n
    ring
  · simp

/-- Actual ordinary expected determinants have the derived outside-edge
log-potential difference limit; no mean-log or determinant limit is an input. -/
theorem log_expected_absolute_det_difference_tendsto {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun n : ℕ => logMeanAbsoluteDet n b - logMeanAbsoluteDet n a) atTop
      (𝓝 (∫ u in a..b, OAI.CriticalSK.semicircleResolvent u)) := by
  have h1 := log_expected_absolute_det_minus_jacobi_tendsto (ha.trans_le hab)
  have h2 := log_expected_absolute_det_minus_jacobi_tendsto ha
  have hJ := jacobi_log_difference_tendsto ha hab
  convert (h1.sub h2).add hJ using 1
  · funext n
    ring
  · simp

end
end SlowEquilibration.GOELogPotential
