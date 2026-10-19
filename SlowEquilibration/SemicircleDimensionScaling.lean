-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SemicircleInsidePotential
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

/-!
# Actual semicircle potential under a change of GOE dimension

The dimension fraction `τ` rescales the physical variance from `b` to `bτ`.
The literal semicircle logarithmic integral satisfies an all-real-shift
bound with error `(1-τ)/2`. This applies to the actual tangent dimension
`n=N-2`, and includes the logarithmic variance normalizer.
-/

namespace SlowEquilibration.SemicirclePotential

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open Set

def quadraticGap (u : ℝ) : ℝ := u^2/4-1/2-potential u

lemma quadraticGap_hasDerivAt {u : ℝ} (hu : 2 < u) :
    HasDerivAt quadraticGap (Real.sqrt (u^2-4)/2) u := by
  have hp := (((hasDerivAt_id u).pow 2).div_const 4).sub_const (1/2)
  convert hp.sub (potential_hasDerivAt_explicit hu) using 1
  · rfl
  · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
    ring

theorem quadraticGap_strictMonoOn : StrictMonoOn quadraticGap (Ici (2 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 2)
  · have hp := SemicircleWholeLine.potential_continuous
    have hc : Continuous quadraticGap := by unfold quadraticGap; fun_prop
    exact hc.continuousOn
  · intro u hu
    have hu' : 2 < u := by simpa only [interior_Ici, mem_Ioi] using hu
    rw [(quadraticGap_hasDerivAt hu').deriv]
    apply div_pos _ (by norm_num : (0 : ℝ) < 2)
    apply Real.sqrt_pos.mpr
    nlinarith

/-- Actual whole-line quadratic upper branch, strict outside the edge. -/
theorem potential_le_quadratic (u : ℝ) : potential u ≤ u^2/4-1/2 := by
  by_cases hu : |u| ≤ 2
  · rw [potential_eq_inside u hu]
  · have hu' : 2 < |u| := lt_of_not_ge hu
    have h := quadraticGap_strictMonoOn (show (2 : ℝ) ∈ Ici 2 from le_rfl)
      (show |u| ∈ Ici 2 from hu'.le) hu'
    have he : potential |u| = potential u := by
      rcases le_or_gt 0 u with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_neg h, SemicircleWholeLine.potential_even]
    rw [quadraticGap, potential_eq_inside (2 : ℝ) (by norm_num)] at h
    norm_num only at h
    rw [quadraticGap, he, sq_abs] at h
    linarith

def scaledRemainder (u τ : ℝ) : ℝ := τ*potential (u/Real.sqrt τ)+τ/2

lemma scaled_argument_gt_two {u τ : ℝ} (hu : 2 < u) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    2 < u/Real.sqrt τ := by
  have hs0 : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hs1 : Real.sqrt τ ≤ 1 := Real.sqrt_le_one.mpr hτ1
  apply (lt_div_iff₀ hs0).mpr
  linarith

lemma scaledRemainder_hasDerivAt {u τ : ℝ} (hu : 2 < u) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    HasDerivAt (scaledRemainder u)
      (Real.log ((u/Real.sqrt τ+Real.sqrt ((u/Real.sqrt τ)^2-4))/2)) τ := by
  have hs0 : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hs2 := Real.sq_sqrt hτ.le
  have hv := (hasDerivAt_const τ u).div (Real.hasDerivAt_sqrt hτ.ne') hs0.ne'
  have hv' : HasDerivAt (fun t : ℝ => u/Real.sqrt t) (-(u/Real.sqrt τ)/(2*τ)) τ := by
    convert hv using 1
    simp only [zero_mul, zero_sub]
    rw [hs2]
    field_simp
  have harg := scaled_argument_gt_two hu hτ hτ1
  have hp := (hasDerivAt_id τ).mul ((potential_hasDerivAt_explicit harg).comp τ hv')
  convert hp.add ((hasDerivAt_id τ).div_const 2) using 1
  · rfl
  · simp only [id_eq, one_mul, Function.comp_def]
    rw [potential_explicit harg]
    field_simp
    ring

theorem scaledRemainder_monotoneOn {u : ℝ} (hu : 2 < u) :
    MonotoneOn (scaledRemainder u) (Ioc (0 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc 0 1)
  · intro τ hτ
    exact (scaledRemainder_hasDerivAt hu hτ.1 hτ.2).continuousAt.continuousWithinAt
  · intro τ hτ
    have hτ' : τ ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ioc] using hτ
    exact (scaledRemainder_hasDerivAt hu hτ'.1 hτ'.2.le).differentiableAt.differentiableWithinAt
  · intro τ hτ
    have hτ' : τ ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Ioc] using hτ
    rw [(scaledRemainder_hasDerivAt hu hτ'.1 hτ'.2.le).deriv]
    apply Real.log_nonneg
    have hv := scaled_argument_gt_two hu hτ'.1 hτ'.2.le
    have hs := Real.sqrt_nonneg ((u/Real.sqrt τ)^2-4)
    linarith

/-- Genuine all-real-shift dimension scaling, with its uniform exact error. -/
theorem potential_dimension_scaling_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (u : ℝ) :
    τ*potential (u/Real.sqrt τ) ≤ potential u+(1-τ)/2 := by
  have hs0 : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have habs : potential |u| = potential u := by
    rcases le_or_gt 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, SemicircleWholeLine.potential_even]
  have hscaledabs : potential (|u|/Real.sqrt τ) = potential (u/Real.sqrt τ) := by
    rcases le_or_gt 0 u with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_neg h, neg_div, SemicircleWholeLine.potential_even]
  by_cases hu : |u| ≤ 2
  · have hp := mul_le_mul_of_nonneg_left (potential_le_quadratic (u/Real.sqrt τ)) hτ.le
    rw [potential_eq_inside u hu]
    have heq : τ*((u/Real.sqrt τ)^2/4-1/2) = u^2/4-τ/2 := by
      rw [div_pow, Real.sq_sqrt hτ.le]
      field_simp
    linarith
  · have hu' : 2 < |u| := lt_of_not_ge hu
    have hm := scaledRemainder_monotoneOn hu'
      (show τ ∈ Ioc (0 : ℝ) 1 from ⟨hτ,hτ1⟩) (show (1 : ℝ) ∈ Ioc 0 1 from by norm_num) hτ1
    simp only [scaledRemainder, Real.sqrt_one, div_one, one_mul, habs, hscaledabs] at hm
    linarith

theorem physical_potential_dimension_scaling_le {b τ : ℝ} (hb : 0 < b)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (k : ℝ) :
    τ*potential (k/Real.sqrt (b*τ)) ≤ potential (k/Real.sqrt b)+(1-τ)/2 := by
  have he : k/Real.sqrt (b*τ) = (k/Real.sqrt b)/Real.sqrt τ := by
    rw [Real.sqrt_mul hb.le, div_div]
  rw [he]
  exact potential_dimension_scaling_le hτ hτ1 _

/-- The variance-normalized potential also has a uniform scaling error. -/
theorem physical_rate_dimension_scaling_le {b τ : ℝ} (hb : 0 < b)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (k : ℝ) :
    τ*(Real.log (b*τ)/2+potential (k/Real.sqrt (b*τ))) ≤
      Real.log b/2+potential (k/Real.sqrt b)+(1-τ)*(1+|Real.log b|)/2 := by
  have hp := physical_potential_dimension_scaling_le hb hτ hτ1 k
  have hl := Real.log_nonpos hτ.le hτ1
  have hm : τ*Real.log τ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hτ.le hl
  have hlog : -Real.log b ≤ |Real.log b| := neg_le_abs _
  have hs := mul_le_mul_of_nonneg_left hlog (by linarith : 0 ≤ 1-τ)
  rw [Real.log_mul hb.ne' hτ.ne']
  nlinarith

/-- Actual tangent dimension `N-2`, with a uniform error of `1/N`. -/
theorem potential_tangent_dimension_le (N : ℕ) (hN : 3 ≤ N) (u : ℝ) :
    (((N-2 : ℕ) : ℝ)/(N : ℝ))*potential
      (u/Real.sqrt (((N-2 : ℕ) : ℝ)/(N : ℝ))) ≤ potential u+1/(N : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hn : 0 < ((N-2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N-2 by omega)
  have hle : ((N-2 : ℕ) : ℝ)/(N : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hNr).mpr
    norm_cast
    omega
  have h := potential_dimension_scaling_le (div_pos hn hNr) hle u
  have herror : (1-((N-2 : ℕ) : ℝ)/(N : ℝ))/2 = 1/(N : ℝ) := by
    rw [Nat.cast_sub (show 2 ≤ N by omega)]
    norm_num only [Nat.cast_ofNat]
    field_simp
    ring
  rwa [herror] at h

theorem physical_rate_tangent_dimension_le (N : ℕ) (hN : 3 ≤ N) {b : ℝ}
    (hb : 0 < b) (k : ℝ) :
    (((N-2 : ℕ) : ℝ)/(N : ℝ))*(Real.log (b*(((N-2 : ℕ) : ℝ)/(N : ℝ)))/2+
      potential (k/Real.sqrt (b*(((N-2 : ℕ) : ℝ)/(N : ℝ))))) ≤
        Real.log b/2+potential (k/Real.sqrt b)+(1+|Real.log b|)/(N : ℝ) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hn : 0 < ((N-2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < N-2 by omega)
  have hle : ((N-2 : ℕ) : ℝ)/(N : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hNr).mpr
    norm_cast
    omega
  have h := physical_rate_dimension_scaling_le hb (div_pos hn hNr) hle k
  have herror : (1-((N-2 : ℕ) : ℝ)/(N : ℝ))*(1+|Real.log b|)/2 =
      (1+|Real.log b|)/(N : ℝ) := by
    rw [Nat.cast_sub (show 2 ≤ N by omega)]
    norm_num only [Nat.cast_ofNat]
    field_simp
    ring
  rwa [herror] at h

/-- Exact uniform error for any genuine positive finite codimension,
including both the full-sphere and latitude-sphere Hessians. -/
theorem potential_codimension_le (N j : ℕ) (hj : j < N) (u : ℝ) :
    (((N-j : ℕ) : ℝ)/(N : ℝ))*potential
      (u/Real.sqrt (((N-j : ℕ) : ℝ)/(N : ℝ))) ≤
        potential u+(j : ℝ)/(2*(N : ℝ)) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hn : 0 < ((N-j : ℕ) : ℝ) := by exact_mod_cast (show 0 < N-j by omega)
  have hle : ((N-j : ℕ) : ℝ)/(N : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hNr).mpr
    norm_cast
    omega
  have h := potential_dimension_scaling_le (div_pos hn hNr) hle u
  have herror : (1-((N-j : ℕ) : ℝ)/(N : ℝ))/2 = (j : ℝ)/(2*(N : ℝ)) := by
    rw [Nat.cast_sub hj.le]
    field_simp
    ring
  rwa [herror] at h

theorem physical_rate_codimension_le (N j : ℕ) (hj : j < N) {b : ℝ}
    (hb : 0 < b) (k : ℝ) :
    (((N-j : ℕ) : ℝ)/(N : ℝ))*(Real.log (b*(((N-j : ℕ) : ℝ)/(N : ℝ)))/2+
      potential (k/Real.sqrt (b*(((N-j : ℕ) : ℝ)/(N : ℝ))))) ≤
        Real.log b/2+potential (k/Real.sqrt b)+
          (j : ℝ)*(1+|Real.log b|)/(2*(N : ℝ)) := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hn : 0 < ((N-j : ℕ) : ℝ) := by exact_mod_cast (show 0 < N-j by omega)
  have hle : ((N-j : ℕ) : ℝ)/(N : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hNr).mpr
    norm_cast
    omega
  have h := physical_rate_dimension_scaling_le hb (div_pos hn hNr) hle k
  have herror : (1-((N-j : ℕ) : ℝ)/(N : ℝ))*(1+|Real.log b|)/2 =
      (j : ℝ)*(1+|Real.log b|)/(2*(N : ℝ)) := by
    rw [Nat.cast_sub hj.le]
    field_simp
    ring
  rwa [herror] at h

end
end SlowEquilibration.SemicirclePotential
