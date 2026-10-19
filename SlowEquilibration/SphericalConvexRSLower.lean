-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalConvexHSTypicality
public import SlowEquilibration.SphericalEvenRSLower

@[expose] public section

/-!
# The actual replica-symmetric thermodynamic lower bound for convex covariances

The explicit HS truncated partition has its planted first moment and second
moment proved from the original tensor model. Paley--Zygmund and the genuine
Gaussian pressure concentration then give the annealed lower limit below
the true static threshold. The conclusion is for the literal spherical
quenched pressure and assumes no thermodynamic pressure formula.
-/

noncomputable section
namespace SlowEquilibration.SphericalModel

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology BigOperators ENNReal

set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine quenched spherical pressure attains the annealed lower
limit for convex covariances below beta_s. All truncation estimates are theorems
about the actual tensor realization, rather than input moment premises. -/
theorem convex_quenchedPressure_eventually_ge_annealed_sub (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β ε : ℝ}
    (hβ : 0 < β) (hβs : β < Thresholds.staticThreshold μ.xi) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, β^2*μ.xi 1/2-ε ≤ quenchedPressure (n+1) μ β := by
  have hB : 0 < β^2*μ.xi 1 := mul_pos (sq_pos_of_pos hβ) (μ.xi_pos (by norm_num))
  obtain ⟨δ,hδ,hgap⟩ := exists_hs_overlap_scale hB (half_pos hε)
  obtain ⟨η,hη,hfirst⟩ := convex_hs_planted_half_eventually μ hconv hβ hβs hδ
  have hlog : Tendsto (fun n : ℕ => Real.log 4/((n+1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have ht := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (Real.log 4)
    simpa only [Nat.cast_add,Nat.cast_one,mul_zero,div_eq_mul_inv,one_div,one_mul] using ht
  filter_upwards [hfirst,hs_tail_comparison_eventually hgap,
    hlog.eventually (gt_mem_nhds (half_pos hε))] with n hfirst htail hlog
  have htail' : 2*Real.exp (-((ε/2)^2*((n+1 : ℕ) : ℝ))/(2*β^2*μ.xi 1)) <
      Real.exp (-(((n+1 : ℕ) : ℝ)*β^2*μ.xi 1*δ^2))/32 := by
    simpa only [mul_assoc] using htail
  have hp := pressure_lower_of_hs_planted_half (show 1 ≤ n+1 by omega) μ hβ
    hδ.1.le hδ.2.le hη.le (half_pos hε) hfirst htail'
  have he : (annealedExponent (n+1) (mixtureCoefficients μ) β-Real.log 4)/((n+1 : ℕ) : ℝ) =
      β^2*μ.xi 1/2-Real.log 4/((n+1 : ℕ) : ℝ) := by
    unfold annealedExponent
    rw [covariancePolynomial_mixture]
    field_simp
  rw [he] at hp
  linarith

/-- The literal thermodynamic spherical RS pressure for every finite
mixture below its static threshold. This is obtained from genuine HS
truncation and concentration, together with the finite-volume Jensen upper. -/
theorem convex_quenchedPressure_tendsto_annealed (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β : ℝ}
    (hβ : 0 < β) (hβs : β < Thresholds.staticThreshold μ.xi) :
    Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 (β^2*μ.xi 1/2)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [convex_quenchedPressure_eventually_ge_annealed_sub μ hconv hβ hβs (half_pos hε)] with n hn
  have hu := quenchedPressure_le_annealed (show 1 ≤ n+1 by omega) μ hβ
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith

/-- The endpoint lower bound follows from the actual finite-volume temperature
monotonicity and the strict subcritical theorem. This also includes zero
temperature parameter, where the normalized partition is exactly one. -/
theorem convex_quenchedPressure_eventually_ge_annealed_sub_le_static (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β ε : ℝ}
    (hβ : 0 ≤ β) (hβs : β ≤ Thresholds.staticThreshold μ.xi) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, β^2*μ.xi 1/2-ε ≤ quenchedPressure (n+1) μ β := by
  rcases eq_or_lt_of_le hβ with hzero | hβpos
  · subst β
    exact Filter.Eventually.of_forall fun n => by simp [hε.le]
  have hc : 0 < μ.xi 1 := μ.xi_pos (by norm_num)
  let d : ℝ := min (β/2) (ε/(2*β*μ.xi 1))
  have hd : 0 < d := lt_min (half_pos hβpos) (by positivity)
  have hdβ : d ≤ β/2 := min_le_left _ _
  have hdε : d*(2*β*μ.xi 1) ≤ ε :=
    (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  have hβ' : 0 < β-d := by linarith
  have hβ's : β-d < Thresholds.staticThreshold μ.xi := by linarith
  have hclose : β^2*μ.xi 1/2-ε/2 ≤ (β-d)^2*μ.xi 1/2 := by
    nlinarith [mul_nonneg (sq_nonneg d) hc.le]
  filter_upwards [convex_quenchedPressure_eventually_ge_annealed_sub μ hconv
    hβ' hβ's (half_pos hε)] with n hn
  have hmono := quenchedPressure_monotoneOn (show 1 ≤ n+1 by omega) μ
    (mem_Ici.mpr hβ'.le) (mem_Ici.mpr hβ) (show β-d ≤ β by linarith)
  linarith

/-- The actual spherical replica-symmetric pressure formula for every even
finite mixture throughout the closed interval from zero to beta_s. -/
theorem convex_quenchedPressure_tendsto_annealed_le_static (μ : FiniteMixture)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β : ℝ}
    (hβ : 0 ≤ β) (hβs : β ≤ Thresholds.staticThreshold μ.xi) :
    Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 (β^2*μ.xi 1/2)) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [convex_quenchedPressure_eventually_ge_annealed_sub_le_static μ hconv
    hβ hβs (half_pos hε)] with n hn
  have hu := (quenchedPressure_mem_annealed_interval (show 1 ≤ n+1 by omega) μ hβ).2
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hu)]
  linarith

end SlowEquilibration.SphericalModel
