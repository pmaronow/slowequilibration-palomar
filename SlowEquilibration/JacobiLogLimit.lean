-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOELogPotential

@[expose] public section

/-!
# Absolute logarithmic potential limit from the proved resolvent

The explicit outside-edge primitive is normalized by its logarithmic behavior
at infinity. Actual Jacobi log sums and actual ordinary expected GOE determinants
converge to it. Equality with a separately defined semicircle-density integral
is not assumed and is a separate scalar identification.
-/

namespace SlowEquilibration.JacobiLogLimit

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Set Filter
open OAI.CriticalSK GOEAsymptotics GOELogPotential
open scoped BigOperators InnerProductSpace NNReal ENNReal Topology

def outsideSpectralPotential (s : ℝ) : ℝ :=
  semicircleResolvent s ^ 2 / 2 - Real.log (semicircleResolvent s)

lemma resolvent_quadratic {s : ℝ} (hs : 0 < s) :
    semicircleResolvent s ^ 2 - (2 + s) * semicircleResolvent s + 1 = 0 := by
  have hr := Real.sq_sqrt (semicircle_discriminant_pos hs).le
  unfold semicircleResolvent
  nlinarith

lemma resolvent_root_product {s : ℝ} (hs : 0 < s) :
    Real.sqrt (s * (4 + s)) * semicircleResolvent s = 1 - semicircleResolvent s ^ 2 := by
  have hq := resolvent_quadratic hs
  have hr : Real.sqrt (s * (4 + s)) = 2 + s - 2 * semicircleResolvent s := by
    unfold semicircleResolvent
    ring
  rw [hr]
  nlinarith

lemma semicircleResolvent_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt semicircleResolvent (-semicircleResolvent s / Real.sqrt (s * (4 + s))) s := by
  have hroot := (((hasDerivAt_id s).mul ((hasDerivAt_id s).const_add 4)).sqrt
    (semicircle_discriminant_pos hs).ne')
  have hd := (((hasDerivAt_id s).const_add 2).sub hroot).div_const 2
  simp only [Pi.mul_apply, Pi.sub_apply, id_eq, one_mul, mul_one] at hd
  unfold semicircleResolvent
  convert hd using 1
  field_simp
  ring

/-- The actual explicit outside-edge potential is a true primitive of the
proved scalar limit resolvent, with no primitive assumption. -/
theorem outsideSpectralPotential_hasDerivAt {s : ℝ} (hs : 0 < s) :
    HasDerivAt outsideSpectralPotential (semicircleResolvent s) s := by
  have hR := semicircleResolvent_pos hs
  have hroot := Real.sqrt_pos.mpr (semicircle_discriminant_pos hs)
  have hder := semicircleResolvent_hasDerivAt hs
  have h := ((hder.pow 2).div_const 2).sub (hder.log hR.ne')
  norm_num only [Nat.reduceSub, pow_one, Nat.cast_ofNat] at h
  change HasDerivAt outsideSpectralPotential _ s at h
  convert h using 1
  field_simp
  have hh := resolvent_root_product hs
  nlinarith

lemma resolvent_tendsto_zero : Tendsto semicircleResolvent atTop (𝓝 0) := by
  have hbound : ∀ᶠ s : ℝ in atTop, 0 ≤ semicircleResolvent s ∧
      semicircleResolvent s ≤ 2 / (2 + s) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs0 : 0 < s := by linarith
    have hpos := semicircleResolvent_pos hs0
    have hle := semicircleResolvent_le_one hs0.le
    have hq := resolvent_quadratic hs0
    refine ⟨hpos.le, ?_⟩
    apply (le_div_iff₀ (by linarith : 0 < 2 + s)).mpr
    nlinarith
  apply squeeze_zero' (hbound.mono fun _ h => h.1) (hbound.mono fun _ h => h.2)
  have ht : Tendsto (fun s : ℝ => 2 + s) atTop atTop := by
    simpa only [add_comm, id_eq] using tendsto_id.atTop_add (tendsto_const_nhds (x := (2 : ℝ)))
  exact ht.const_div_atTop 2

/-- The infinity normalization of the explicit primitive is derived from its
actual quadratic equation, not supplied as an asymptotic premise. -/
theorem outsideSpectralPotential_minus_log_tendsto :
    Tendsto (fun s : ℝ => outsideSpectralPotential s - Real.log (2 + s)) atTop (𝓝 0) := by
  have hprod : Tendsto (fun s => (2 + s) * semicircleResolvent s) atTop (𝓝 1) := by
    have h := resolvent_tendsto_zero.pow 2 |>.const_add 1
    simp only [zero_pow two_ne_zero, add_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hq := resolvent_quadratic (by linarith : 0 < s)
    linarith
  have hlog := hprod.log (by norm_num : (1 : ℝ) ≠ 0)
  simp only [Real.log_one] at hlog
  have hlim := (resolvent_tendsto_zero.pow 2 |>.div_const 2).sub hlog
  simp only [zero_pow two_ne_zero, zero_div, sub_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
  have hR := semicircleResolvent_pos (by linarith : 0 < s)
  have hz : 0 < 2 + s := by linarith
  rw [Real.log_mul hz.ne' hR.ne']
  unfold outsideSpectralPotential
  ring

lemma outsideSpectralPotential_difference_eq_integral {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    outsideSpectralPotential b - outsideSpectralPotential a = ∫ u in a..b, semicircleResolvent u := by
  symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro u hu
    rw [uIcc_of_le hab] at hu
    exact outsideSpectralPotential_hasDerivAt (ha.trans_le hu.1)
  · exact GOELogPotential.semicircleResolvent_continuous.intervalIntegrable a b

/-- The large-shift anchor is uniform in the actual Jacobi dimension. -/
lemma jacobi_log_anchor_bound (n : ℕ) {s : ℝ} (hs : 0 < s) :
    |jacobiNormalizedLog n s - Real.log (2 + s)| ≤ 2 / s := by
  have hpoint (i : Fin (n + 1)) :
      |Real.log (s + orderedJacobiGaps n i) - Real.log (2 + s)| ≤ 2 / s := by
    have h0 := orderedJacobiGaps_nonneg n i
    have h4 := orderedJacobiGaps_le_four n i
    have h := SpectralTraceLipschitz.log_difference_le hs
      (by linarith : s ≤ s + orderedJacobiGaps n i) (by linarith : s ≤ 2 + s)
    apply h.trans
    apply div_le_div_of_nonneg_right _ hs.le
    apply abs_le.mpr
    constructor <;> linarith
  have heq : jacobiNormalizedLog n s - Real.log (2 + s) =
      (∑ i : Fin (n + 1), (Real.log (s + orderedJacobiGaps n i) - Real.log (2 + s))) / (n + 1 : ℝ) := by
    unfold jacobiNormalizedLog
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  rw [heq, abs_div, abs_of_pos (by positivity : 0 < (n + 1 : ℝ))]
  apply (div_le_iff₀ (by positivity : 0 < (n + 1 : ℝ))).mpr
  calc
    _ ≤ ∑ i : Fin (n + 1), |Real.log (s + orderedJacobiGaps n i) - Real.log (2 + s)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin (n + 1), 2 / s := Finset.sum_le_sum (fun i _ => hpoint i)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

/-- The absolute actual Jacobi logarithmic potential limit follows from the
proved resolvent primitive and the uniform large-shift anchor. -/
theorem jacobi_normalized_log_tendsto {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => jacobiNormalizedLog n s) atTop (𝓝 (outsideSpectralPotential s)) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  have hdiv := (tendsto_id.const_div_atTop (2 : ℝ)).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < eps / 4))
  have hF := Metric.tendsto_nhds.mp outsideSpectralPotential_minus_log_tendsto
    (eps / 4) (by positivity)
  obtain ⟨T, hTs, hT1, hdiv, hF⟩ :=
    ((eventually_ge_atTop s).and ((eventually_ge_atTop (1 : ℝ)).and (hdiv.and hF))).exists
  simp only [id_eq] at hdiv
  have hT : 0 < T := by linarith
  have hdiff := jacobi_log_difference_tendsto hs hTs
  rw [← outsideSpectralPotential_difference_eq_integral hs hTs] at hdiff
  have hN := Metric.tendsto_nhds.mp hdiff (eps / 4) (by positivity)
  filter_upwards [hN] with n hn
  have hJa := jacobi_log_anchor_bound n hT
  have hJap := abs_le.mp hJa
  have hFp : |outsideSpectralPotential T - Real.log (2 + T)| < eps / 4 := by
    simpa only [Real.dist_eq, sub_zero] using hF
  have hFa := abs_lt.mp hFp
  have hNp : |(jacobiNormalizedLog n T - jacobiNormalizedLog n s) -
      (outsideSpectralPotential T - outsideSpectralPotential s)| < eps / 4 := by
    simpa only [Real.dist_eq] using hn
  have hNa := abs_lt.mp hNp
  have hresult : |jacobiNormalizedLog n s - outsideSpectralPotential s| < eps := by
    apply abs_lt.mpr
    constructor <;> linarith [hJap.1, hJap.2, hFa.1, hFa.2, hNa.1, hNa.2]
  simpa only [Real.dist_eq] using hresult

/-- Actual expected clipped GOE logdet has the absolute derived spectral
potential limit. The limiting function is explicitly defined and normalized. -/
theorem expected_normalized_clipped_log_tendsto {s rho : ℝ}
    (hs : 0 < s) (hrho : 0 < rho) (hrhos : rho ≤ s) :
    Tendsto (fun n : ℕ =>
      ∫ A, normalizedClippedLog n s rho A ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n + 1)))
      atTop (𝓝 (outsideSpectralPotential s)) := by
  have h1 := expected_normalized_clipped_log_minus_jacobi_tendsto hs hrho hrhos
  have h2 := jacobi_normalized_log_tendsto hs
  convert h1.add h2 using 1
  · funext n
    ring
  · simp

/-- The logarithm of the expectation of the ordinary absolute GOE determinant,
normalized by its actual dimension, converges to the derived absolute potential. -/
theorem log_expected_absolute_det_tendsto {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => logMeanAbsoluteDet n s) atTop (𝓝 (outsideSpectralPotential s)) := by
  have h1 := log_expected_absolute_det_minus_jacobi_tendsto hs
  have h2 := jacobi_normalized_log_tendsto hs
  convert h1.add h2 using 1
  · funext n
    ring
  · simp

end
end SlowEquilibration.JacobiLogLimit
