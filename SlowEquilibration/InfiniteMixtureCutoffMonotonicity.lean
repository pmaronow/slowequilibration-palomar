-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureCutoffTrial

/-! The omitted high-degree dynamical terms are increasing on each compact
subinterval of [0,1). Thus nonnegative cutoffs preserve the actual decreasing
cusp branch once the cutoff is sufficiently large. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem dynamical_power_monotone {k : ℕ} (hk : 1 ≤ k) {R : ℝ}
    (hR : ((k:ℝ)+1)*R ≤ k) : MonotoneOn (fun r : ℝ => (1-r)*r^k) (Icc 0 R) := by
  have hd (r : ℝ) : HasDerivAt (fun r : ℝ => (1-r)*r^k)
      (r^(k-1)*((k:ℝ)-((k:ℝ)+1)*r)) r := by
    convert ((hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_id r)).mul ((hasDerivAt_id r).pow k) using 1
    · ext x
      rfl
    · simp only [Pi.sub_apply,Pi.pow_apply,id_eq]
      have hp : r^k = r^(k-1)*r := by
        conv_lhs => rw [show k=k-1+1 by omega]
        rw [pow_succ]
      rw [hp]
      ring
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 R)
    (by fun_prop)
    (fun r _ => (hd r).hasDerivWithinAt)
  intro r hr
  have hr' : r ∈ Icc (0:ℝ) R := interior_subset hr
  apply mul_nonneg (pow_nonneg hr'.1 _)
  nlinarith [mul_le_mul_of_nonneg_left hr'.2 (show 0 ≤ (k:ℝ)+1 by positivity)]

private theorem high_dynamical_terms_monotone (μ : InfiniteMixture) {R : ℝ} (hR : R < 1) :
    ∃ K : ℕ, ∀ p ≥ K,
      MonotoneOn (fun r : ℝ => μ.coeff p*(p:ℝ)*(1-r)*r^(p-2)) (Icc 0 R) := by
  obtain ⟨K,hK⟩ := exists_nat_gt (3+(1-R)⁻¹)
  refine ⟨K,fun p hp => ?_⟩
  have hden : 0 < 1-R := sub_pos.mpr hR
  have hcast : 3+(1-R)⁻¹ < (p:ℝ) := hK.trans_le (by exact_mod_cast hp)
  have hp3 : 3 ≤ p := by
    have hi := inv_pos.mpr hden
    have h : (3:ℝ) < p := by linarith
    exact_mod_cast h.le
  have hb : (((p-2:ℕ):ℝ)+1)*R ≤ ((p-2:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 2≤p)]
    norm_num
    have hh := (mul_lt_mul_of_pos_right hcast hden)
    rw [add_mul,inv_mul_cancel₀ hden.ne'] at hh
    nlinarith
  have hm := dynamical_power_monotone (by omega : 1≤p-2) hb
  intro x hx y hy hxy
  have hh := mul_le_mul_of_nonneg_left (hm hx hy hxy)
    (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p))
  simpa only [mul_assoc] using hh

/-- Exact order control of the true omitted tail, proved by limits of finite
nonnegative polynomial tails. -/
theorem cutoffA_tail_monotone_eventually (μ : InfiniteMixture) {R : ℝ}
    (hR0 : 0 ≤ R) (hR1 : R < 1) :
    ∀ᶠ P in atTop, MonotoneOn (fun r => μ.A r-μ.cutoffA P r) (Icc 0 R) := by
  obtain ⟨K,hK⟩ := high_dynamical_terms_monotone μ hR1
  filter_upwards [eventually_ge_atTop K] with P hP
  intro x hx y hy hxy
  have hx1 : x ∈ Icc (0:ℝ) 1 := ⟨hx.1,hx.2.trans hR1.le⟩
  have hy1 : y ∈ Icc (0:ℝ) 1 := ⟨hy.1,hy.2.trans hR1.le⟩
  apply le_of_tendsto_of_tendsto
    ((μ.cutoffA_tendstoUniformlyOn.tendsto_at hx1).sub_const (μ.cutoffA P x))
    ((μ.cutoffA_tendstoUniformlyOn.tendsto_at hy1).sub_const (μ.cutoffA P y))
  filter_upwards [eventually_ge_atTop P] with Q hQ
  simp only [cutoffA]
  rw [← Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hQ),
    ← Finset.sum_Ico_eq_sub _ (Nat.succ_le_succ hQ)]
  apply Finset.sum_le_sum
  intro p hp
  exact hK p (by have := (Finset.mem_Ico.mp hp).1; omega) hx hy hxy

namespace CuspCoordinate
variable {μ : InfiniteMixture} (c : CuspCoordinate μ)

/-- The exact normal form gives strict decrease throughout the right branch. -/
theorem strictAntiOn_A_right : StrictAntiOn μ.A (Icc μ.qD (c.rightRoot c.radius)) := by
  have hL := c.left_lt_qD c.radius_pos le_rfl
  have hzero : (0:ℝ) ∈ Icc (-c.radius) c.radius := by
    constructor <;> linarith [c.radius_pos]
  intro x hx y hy hxy
  obtain ⟨s,hs,rfl⟩ := c.mem_coordinate_image ⟨hL.le.trans hx.1,hx.2⟩
  obtain ⟨t,ht,rfl⟩ := c.mem_coordinate_image ⟨hL.le.trans hy.1,hy.2⟩
  have hs0 : 0 ≤ s := by
    by_contra hn
    have hh := c.monotone hs hzero (lt_of_not_ge hn)
    rw [c.zero] at hh
    linarith [hx.1]
  have ht0 : 0 ≤ t := by
    by_contra hn
    have hh := c.monotone ht hzero (lt_of_not_ge hn)
    rw [c.zero] at hh
    linarith [hy.1]
  have hst : s < t := (c.monotone.lt_iff_lt hs ht).mp (by linarith)
  have hpow : s^(2*c.m) < t^(2*c.m) :=
    (pow_lt_pow_iff_left₀ hs0 ht0 (by have := c.m_pos; omega)).mpr hst
  rw [c.normal s hs,c.normal t ht]
  exact div_lt_div_of_pos_left μ.Amax_pos
    (by have := c.a_pos; positivity)
    (by nlinarith [c.a_pos])

/-- The genuine cutoff polynomial eventually retains strict decrease on
the right cusp branch; there can be no artificial superlevel holes there. -/
theorem basedCutoff_strictAntiOn_A_right_eventually (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀) :
    ∀ᶠ n in atTop, StrictAntiOn (Thresholds.A (μ.basedCutoff P₀ h₀ n).xi)
      (Icc μ.qD (c.rightRoot c.radius)) := by
  have hi := (c.roots_interior c.radius_pos.le le_rfl).2
  have hqi : 0 < μ.qD := by
    have hh := c.interior 0 (show (0:ℝ) ∈ Icc (-c.radius) c.radius by
      constructor <;> linarith [c.radius_pos])
    simpa only [c.zero,add_zero] using hh.1
  have ht := (show Tendsto (fun n => P₀+n) atTop atTop by
    simpa [Nat.add_comm] using tendsto_add_atTop_nat P₀)
      (μ.cutoffA_tail_monotone_eventually hi.1.le hi.2)
  filter_upwards [ht] with n hn x hx y hy hxy
  have hA := c.strictAntiOn_A_right hx hy hxy
  have htail := hn ⟨hqi.le.trans hx.1,hx.2⟩ ⟨hqi.le.trans hy.1,hy.2⟩ hxy.le
  unfold basedCutoff
  rw [μ.finiteCutoff_A_eq _ _ (hqi.trans_le hx.1).ne',
    μ.finiteCutoff_A_eq _ _ (hqi.trans_le hy.1).ne']
  linarith

end CuspCoordinate
end SlowEquilibration.InfiniteMixture
