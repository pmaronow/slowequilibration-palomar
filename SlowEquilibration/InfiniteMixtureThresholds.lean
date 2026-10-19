-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureDynamical
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Actual threshold bounds and exclusion of the zero endpoint for the
infinite source mixtures. No polynomial truncation or nondegenerate contact
hypothesis is used. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set Filter
open scoped Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (μ : InfiniteMixture)

theorem exists_positive_coefficient : ∃ p : ℕ,2≤p ∧ 0<μ.coeff p := by
  have he : ∃ p,μ.coeff p≠0 := by
    by_contra h
    apply μ.nonzero
    funext p
    exact not_ne_iff.mp (not_exists.mp h p)
  obtain ⟨p,hp⟩ := he
  exact ⟨p,by by_contra h;exact hp (μ.zero_below_two p (by omega)),lt_of_le_of_ne (μ.nonneg p) hp.symm⟩

theorem xi_pos {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) : 0<μ.xi r := by
  obtain ⟨p,hp,hc⟩ := μ.exists_positive_coefficient
  exact (μ.summable_xi (abs_le.mpr ⟨by linarith [hr.1],hr.2.le⟩)).tsum_pos
    (fun p => mul_nonneg (μ.nonneg _) (pow_nonneg hr.1.le _)) p (mul_pos hc (pow_pos hr.1 _))

theorem A_pos {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) : 0<μ.A r := by
  obtain ⟨p,hp,hc⟩ := μ.exists_positive_coefficient
  have hs : Summable (fun p => μ.dividedCoefficients p*r^p) :=
    .of_norm_bounded μ.summable_dividedCoefficients
      (μ.norm_divided_term_le (abs_le.mpr ⟨by linarith [hr.1],hr.2.le⟩))
  apply mul_pos (sub_pos.mpr hr.2)
  apply hs.tsum_pos (fun p => mul_nonneg (μ.dividedCoefficients_nonneg _) (pow_nonneg hr.1.le _)) (p-2)
  apply mul_pos _ (pow_pos hr.1 _)
  simp only [dividedCoefficients,show p-2+2=p by omega]
  exact mul_pos (Nat.cast_pos.mpr (by omega)) hc

theorem A_le_sum_divided {r : ℝ} (hr : r∈Icc (0:ℝ) 1) :
    μ.A r ≤ ∑' p,μ.dividedCoefficients p := by
  have hs : Summable (fun p => μ.dividedCoefficients p*r^p) :=
    .of_norm_bounded μ.summable_dividedCoefficients
      (μ.norm_divided_term_le (abs_le.mpr ⟨by linarith [hr.1],hr.2⟩))
  have hsum : (∑' p,μ.dividedCoefficients p*r^p) ≤ ∑' p,μ.dividedCoefficients p := by
    apply hs.tsum_le_tsum _ μ.summable_dividedCoefficients
    intro p
    exact mul_le_of_le_one_right (μ.dividedCoefficients_nonneg _) (pow_le_one₀ hr.1 hr.2)
  calc
    μ.A r ≤ 1*(∑' p,μ.dividedCoefficients p*r^p) := mul_le_mul_of_nonneg_right
      (by linarith [hr.1]) (tsum_nonneg (fun p => mul_nonneg (μ.dividedCoefficients_nonneg _) (pow_nonneg hr.1 _)))
    _ ≤ _ := by simpa using hsum

/-- The literal supremum used in the manuscript threshold definition. -/
def Amax : ℝ := sSup (Thresholds.A μ.xi '' Ioo 0 1)

theorem A_image_bddAbove : BddAbove (Thresholds.A μ.xi '' Ioo 0 1) := by
  refine ⟨∑' p,μ.dividedCoefficients p,?_⟩
  rintro _ ⟨r,hr,rfl⟩
  rw [← μ.A_eq_threshold hr]
  exact μ.A_le_sum_divided ⟨hr.1.le,hr.2.le⟩

theorem A_le_Amax {r : ℝ} (hr : r∈Ioo (0:ℝ) 1) : μ.A r≤μ.Amax := by
  rw [μ.A_eq_threshold hr]
  exact le_csSup μ.A_image_bddAbove ⟨r,hr,rfl⟩

theorem Amax_pos : 0<μ.Amax :=
  (μ.A_pos (show (1/2:ℝ)∈Ioo 0 1 by norm_num)).trans_le (μ.A_le_Amax (by norm_num))

theorem dynamicalThreshold_sq : Thresholds.dynamicalThreshold μ.xi^2=μ.Amax⁻¹ :=
  Real.sq_sqrt (inv_nonneg.mpr μ.Amax_pos.le)

theorem A_zero_le_Amax : μ.A 0≤μ.Amax := by
  have ht : Tendsto μ.A (𝓝[>] (0:ℝ)) (𝓝 (μ.A 0)) :=
    (μ.analyticOnNhd_A 0 (by norm_num)).continuousAt.tendsto.mono_left inf_le_left
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin, eventually_nhdsWithin_of_eventually_nhds (show ∀ᶠ r : ℝ in 𝓝 0,r<1 from Iio_mem_nhds (by norm_num))] with r hr h1
  exact μ.A_le_Amax ⟨hr,h1⟩

theorem A_le_Amax_closed {r : ℝ} (hr : r∈Icc (0:ℝ) 1) : μ.A r≤μ.Amax := by
  rcases hr.1.eq_or_lt with h0 | h0
  · subst r;exact μ.A_zero_le_Amax
  rcases hr.2.eq_or_lt with h1 | h1
  · subst r;simpa using μ.Amax_pos.le
  exact μ.A_le_Amax ⟨h0,h1⟩

/-- Sub-static temperatures bound the true extended A at zero. This follows
by integrating the positive derivative of Φ if the bound were violated. -/
theorem zero_dynamical_bound_of_lt_static {β : ℝ} (hβ : 0≤β)
    (hβs : β<Thresholds.staticThreshold μ.xi) : β^2*μ.A 0≤1 := by
  by_contra h
  have h0 : 1<β^2*μ.A 0 := lt_of_not_ge h
  have he : ∀ᶠ r in 𝓝 (0:ℝ),1<β^2*μ.A r :=
    ((μ.analyticOnNhd_A 0 (by norm_num)).continuousAt.const_mul (β^2)).eventually (lt_mem_nhds h0)
  obtain ⟨l,u,hu,hs⟩ := he.exists_Ioo_subset
  let r := min (u/2) (1/2)
  have hr : 0<r := lt_min (by linarith [hu.2]) (by norm_num)
  have hr1 : r<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hru : r<u := lt_of_le_of_lt (min_le_left _ _) (by linarith [hu.2])
  have hcont : ContinuousOn (Thresholds.Phi μ.xi β) (Icc 0 r) := by
    intro x hx
    exact (Thresholds.hasDerivAt_Phi
      ((μ.hasDerivAt_xi ⟨by linarith [hx.1],lt_of_le_of_lt hx.2 hr1⟩).differentiableAt)
      (lt_of_le_of_lt hx.2 hr1)).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn (Thresholds.Phi μ.xi β) (Icc 0 r) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 r) hcont
    intro x hx
    have hx' : x∈Ioo 0 r := by simpa only [interior_Icc] using hx
    have hx01 : x∈Ioo (0:ℝ) 1 := ⟨hx'.1,hx'.2.trans hr1⟩
    rw [Thresholds.deriv_Phi (μ.hasDerivAt_xi ⟨by linarith [hx'.1],hx01.2⟩).differentiableAt hx01,
      ← μ.A_eq_threshold hx01]
    exact mul_pos (div_pos hx01.1 (sub_pos.mpr hx01.2)) (sub_pos.mpr (hs ⟨by linarith [hu.1,hx'.1],hx'.2.trans hru⟩))
  have hh := hmono (show (0:ℝ)∈Icc 0 r from ⟨le_rfl,hr.le⟩) ⟨hr.le,le_rfl⟩ hr
  have hn := Thresholds.Phi_neg_of_lt_staticThreshold (fun x hx => μ.xi_pos hx) hβ hβs r ⟨hr,hr1⟩
  have hz : Thresholds.Phi μ.xi β 0=0 := by simp [Thresholds.Phi]
  rw [hz] at hh
  linarith

/-- The strict dynamical/static gap excludes the left endpoint from the
maximizer set; no quadratic-term restriction is imposed. -/
theorem A_zero_lt_Amax (hgap : Thresholds.dynamicalThreshold μ.xi<Thresholds.staticThreshold μ.xi) :
    μ.A 0<μ.Amax := by
  let β := (Thresholds.dynamicalThreshold μ.xi+Thresholds.staticThreshold μ.xi)/2
  have hβd : Thresholds.dynamicalThreshold μ.xi<β := by dsimp [β];linarith
  have hβs : β<Thresholds.staticThreshold μ.xi := by dsimp [β];linarith
  have hd : 0≤Thresholds.dynamicalThreshold μ.xi := Real.sqrt_nonneg _
  have hβ : 0<β := hd.trans_lt hβd
  have hsq : μ.Amax⁻¹<β^2 := by
    rw [← μ.dynamicalThreshold_sq]
    exact (sq_lt_sq₀ hd hβ.le).mpr hβd
  rw [inv_eq_one_div] at hsq
  have hm : 1<β^2*μ.Amax := (div_lt_iff₀ μ.Amax_pos).mp hsq
  have hbound := μ.zero_dynamical_bound_of_lt_static hβ.le hβs
  by_contra h
  have hh := mul_le_mul_of_nonneg_left (le_of_not_gt h) (sq_nonneg β)
  linarith

end SlowEquilibration.InfiniteMixture
