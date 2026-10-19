-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixtureCurvature
public import SlowEquilibration.Thresholds

@[expose] public section

/-!
# Threshold calculus for canonical finite mixtures

Instantiates the scalar threshold theorems for the actual covariance polynomial
of every canonical finite nonzero mixture. In particular, the threshold ordering
requires no unverified mixture regularity or boundedness premise.
-/

namespace SlowEquilibration.FiniteMixture

variable (μ : FiniteMixture)

/-- The covariance has no constant term. -/
theorem xi_zero : μ.xi 0 = 0 := by
  unfold xi
  apply Finset.sum_eq_zero
  intro p hp
  have hp2 := μ.degree_ge_two hp
  rw [zero_pow (show p ≠ 0 by omega), mul_zero]

/-- The actual covariance is positive at every positive radius. -/
theorem xi_pos {r : ℝ} (hr : 0 < r) : 0 < μ.xi r := by
  unfold xi
  apply Finset.sum_pos
  · intro p hp
    exact mul_pos (μ.coeff_pos hp) (pow_pos hr _)
  · exact μ.support_nonempty

/-- The actual dynamical scalar agrees with an explicit finite polynomial
away from the removable singularity at zero. -/
theorem A_eq_polynomial {r : ℝ} (hr : r ≠ 0) :
    Thresholds.A μ.xi r = ∑ p ∈ μ.coeff.support,
      μ.coeff p * (p : ℝ) * (1 - r) * r ^ (p - 2) := by
  unfold Thresholds.A
  rw [(μ.hasDerivAt_xi r).deriv]
  unfold xi1
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p hp
  have hp2 := μ.degree_ge_two hp
  rw [show p - 1 = p - 2 + 1 by omega, pow_succ]
  field_simp

/-- The actual dynamical scalar is positive on its intended domain. -/
theorem A_pos {r : ℝ} (hr : r ∈ Set.Ioo 0 1) : 0 < Thresholds.A μ.xi r := by
  rw [μ.A_eq_polynomial hr.1.ne']
  apply Finset.sum_pos
  · intro p hp
    have hp2 := μ.degree_ge_two hp
    exact mul_pos (mul_pos (mul_pos (μ.coeff_pos hp)
      (Nat.cast_pos.mpr (by omega))) (sub_pos.mpr hr.2)) (pow_pos hr.1 _)
  · exact μ.support_nonempty

/-- A finite, deterministic upper bound for the actual dynamical scalar. -/
theorem A_le_coefficient_sum {r : ℝ} (hr : r ∈ Set.Ioo 0 1) :
    Thresholds.A μ.xi r ≤ ∑ p ∈ μ.coeff.support, μ.coeff p * (p : ℝ) := by
  rw [μ.A_eq_polynomial hr.1.ne']
  apply Finset.sum_le_sum
  intro p hp
  have hpow : r ^ (p - 2) ≤ 1 := pow_le_one₀ hr.1.le hr.2.le
  have hprod : (1 - r) * r ^ (p - 2) ≤ 1 := by
    calc
      _ ≤ 1 * r ^ (p - 2) :=
        mul_le_mul_of_nonneg_right (by linarith [hr.1]) (pow_nonneg hr.1.le _)
      _ = r ^ (p - 2) := one_mul _
      _ ≤ 1 := hpow
  calc
    _ = (μ.coeff p * (p : ℝ)) * ((1 - r) * r ^ (p - 2)) := by ring
    _ ≤ (μ.coeff p * (p : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left hprod (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p))
    _ = _ := mul_one _

/-- The dynamical scalar image is bounded above for every genuine mixture. -/
theorem A_image_bddAbove : BddAbove (Thresholds.A μ.xi '' Set.Ioo 0 1) := by
  refine ⟨∑ p ∈ μ.coeff.support, μ.coeff p * (p : ℝ), ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  exact μ.A_le_coefficient_sum hr

/-- The dynamical scalar has a strictly positive finite supremum. -/
theorem A_sSup_pos : 0 < sSup (Thresholds.A μ.xi '' Set.Ioo 0 1) := by
  have hhalf : (1 / 2 : ℝ) ∈ Set.Ioo 0 1 := by norm_num
  exact (μ.A_pos hhalf).trans_le (le_csSup μ.A_image_bddAbove ⟨1 / 2, hhalf, rfl⟩)

/-- Continuity of the actual dynamical scalar away from its removable
singularity at zero, including the endpoint one. -/
theorem continuousAt_A {r : ℝ} (hr : r ≠ 0) : ContinuousAt (Thresholds.A μ.xi) r := by
  have h1 : deriv μ.xi = μ.xi1 := funext (fun x => (μ.hasDerivAt_xi x).deriv)
  unfold Thresholds.A
  rw [h1]
  exact ((continuousAt_const.sub continuousAt_id).mul
    (μ.hasDerivAt_xi1 r).continuousAt).div continuousAt_id hr

/-- The actual dynamical scalar is continuous throughout `(0,1)`. -/
theorem continuousOn_A : ContinuousOn (Thresholds.A μ.xi) (Set.Ioo 0 1) := by
  intro r hr
  exact (μ.continuousAt_A hr.1.ne').continuousWithinAt

/-- The continuous right-endpoint value of the dynamical scalar is zero. -/
theorem A_one : Thresholds.A μ.xi 1 = 0 := by simp [Thresholds.A]

/-- Every fixed temperature has a neighborhood of one containing no strict
superlevel points, derived from actual polynomial continuity and `A(1)=0`. -/
theorem A_near_one_bound (β : ℝ) :
    ∃ u < 1, ∀ r ∈ Set.Ioo 0 1, u ≤ r → β ^ 2 * Thresholds.A μ.xi r ≤ 1 := by
  have hg : ContinuousAt (fun r => β ^ 2 * Thresholds.A μ.xi r) 1 :=
    (μ.continuousAt_A (by norm_num)).const_mul (β ^ 2)
  have hvalue : β ^ 2 * Thresholds.A μ.xi 1 < 1 := by rw [μ.A_one]; norm_num
  have hevent : ∀ᶠ r in nhds 1, β ^ 2 * Thresholds.A μ.xi r < 1 :=
    hg.eventually (gt_mem_nhds hvalue)
  obtain ⟨l, v, h1, hsub⟩ := hevent.exists_Ioo_subset
  refine ⟨(l + 1) / 2, by linarith [h1.1], ?_⟩
  intro r hr hcut
  exact (hsub ⟨by linarith [h1.1], hr.2.trans h1.2⟩).le

/-- Above the actual dynamical threshold, the strict superlevel set is
nonempty; no such nonemptiness hypothesis is assumed. -/
theorem plateauSuperlevel_nonempty {β : ℝ}
    (hlt : Thresholds.dynamicalThreshold μ.xi < β) :
    (Thresholds.plateauSuperlevel μ.xi β).Nonempty := by
  have hβpos : 0 < β := (Real.sqrt_nonneg _).trans_lt hlt
  have hβsq : 0 < β ^ 2 := sq_pos_of_pos hβpos
  have hsq : Thresholds.dynamicalThreshold μ.xi ^ 2 < β ^ 2 :=
    (sq_lt_sq₀ (Real.sqrt_nonneg _) hβpos.le).mpr hlt
  have hdsq : Thresholds.dynamicalThreshold μ.xi ^ 2 =
      (sSup (Thresholds.A μ.xi '' Set.Ioo 0 1))⁻¹ :=
    Real.sq_sqrt (inv_nonneg.mpr μ.A_sSup_pos.le)
  rw [hdsq, inv_eq_one_div] at hsq
  have hproduct : 1 < β ^ 2 * sSup (Thresholds.A μ.xi '' Set.Ioo 0 1) :=
    (div_lt_iff₀ μ.A_sSup_pos).mp hsq
  have hratio : 1 / β ^ 2 < sSup (Thresholds.A μ.xi '' Set.Ioo 0 1) := by
    apply (div_lt_iff₀ hβsq).mpr
    nlinarith
  have himage : (Thresholds.A μ.xi '' Set.Ioo 0 1).Nonempty :=
    ⟨Thresholds.A μ.xi (1 / 2), ⟨1 / 2, by norm_num, rfl⟩⟩
  obtain ⟨a, ⟨r, hr, rfl⟩, hlevel⟩ := exists_lt_of_lt_csSup himage hratio
  refine ⟨r, hr, ?_⟩
  have h := (div_lt_iff₀ hβsq).mp hlevel
  nlinarith

/-- The actual reference endpoint is in `(0,1)` and solves the plateau equation
for every canonical finite mixture and every `β > β_d`. It makes no largest-root
claim, preserving the manuscript's possible tangencies farther to the right. -/
theorem qStar_solves_plateau {β : ℝ}
    (hlt : Thresholds.dynamicalThreshold μ.xi < β) :
    Thresholds.qStar μ.xi β ∈ Set.Ioo 0 1 ∧
      β ^ 2 * deriv μ.xi (Thresholds.qStar μ.xi β) =
        Thresholds.qStar μ.xi β / (1 - Thresholds.qStar μ.xi β) :=
  Thresholds.qStar_solves_plateau μ.continuousOn_A
    (μ.plateauSuperlevel_nonempty hlt) (μ.A_near_one_bound β)

/-- Elementary threshold ordering for every actual finite nonzero mixture,
including quadratic components and odd degrees. -/
theorem dynamicalThreshold_le_staticThreshold :
    Thresholds.dynamicalThreshold μ.xi ≤ Thresholds.staticThreshold μ.xi := by
  apply Thresholds.dynamicalThreshold_le_staticThreshold μ.xi_zero
  · intro r hr
    exact (μ.hasDerivAt_xi r).continuousAt.continuousWithinAt
  · intro r hr
    exact (μ.hasDerivAt_xi r).differentiableAt
  · intro r hr
    exact μ.xi_pos hr.1
  · refine ⟨∑ p ∈ μ.coeff.support, μ.coeff p * (p : ℝ), ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact μ.A_le_coefficient_sum hr
  · exact ⟨1 / 2, by norm_num, μ.A_pos (by norm_num)⟩

/-- The dynamical threshold is strictly positive for every genuine mixture. -/
theorem dynamicalThreshold_pos : 0 < Thresholds.dynamicalThreshold μ.xi :=
  Real.sqrt_pos.mpr (inv_pos.mpr μ.A_sSup_pos)

/-- The static threshold is strictly positive for every genuine mixture. -/
theorem staticThreshold_pos : 0 < Thresholds.staticThreshold μ.xi :=
  μ.dynamicalThreshold_pos.trans_le μ.dynamicalThreshold_le_staticThreshold

/-- The defining dynamical square identity for the actual finite mixture. -/
theorem dynamicalThreshold_sq : Thresholds.dynamicalThreshold μ.xi ^ 2 =
    (sSup (Thresholds.A μ.xi '' Set.Ioo 0 1))⁻¹ :=
  Real.sq_sqrt (inv_nonneg.mpr μ.A_sSup_pos.le)

/-- Exact scalar static-threshold criterion for an actual canonical mixture. -/
theorem Phi_nonpos_iff_le_staticThreshold {β : ℝ} (hβ : 0 ≤ β) :
    (∀ r ∈ Set.Ioo 0 1, Thresholds.Phi μ.xi β r ≤ 0) ↔
      β ≤ Thresholds.staticThreshold μ.xi :=
  Thresholds.Phi_nonpos_iff_le_staticThreshold (fun _ hr => μ.xi_pos hr.1) hβ

/-- Strict scalar replica symmetry below the static threshold for an actual
canonical mixture. -/
theorem Phi_neg_of_lt_staticThreshold {β : ℝ} (hβ : 0 ≤ β)
    (hlt : β < Thresholds.staticThreshold μ.xi) :
    ∀ r ∈ Set.Ioo 0 1, Thresholds.Phi μ.xi β r < 0 :=
  Thresholds.Phi_neg_of_lt_staticThreshold (fun _ hr => μ.xi_pos hr.1) hβ hlt

end SlowEquilibration.FiniteMixture
