-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureCutoffThreshold

/-! Uniform convergence of the actual cutoff dynamical polynomials, and
convergence of their literal scalar dynamical thresholds. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set Filter
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (μ : InfiniteMixture)

/-- The continuous polynomial extension at the removable singularity zero. -/
def cutoffA (P : ℕ) (r : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (P+1), μ.coeff p * (p:ℝ) * (1-r) * r^(p-2)

private theorem dynamical_term_bound {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) (p : ℕ) :
    ‖μ.coeff p * (p:ℝ) * (1-r) * r^(p-2)‖ ≤ (p:ℝ)*μ.coeff p := by
  have hp : 0 ≤ r^(p-2) := pow_nonneg hr.1 _
  rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p)) (sub_nonneg.mpr hr.2)) hp)]
  have hb : (1-r)*r^(p-2) ≤ 1 := by
    calc
      _ ≤ 1*r^(p-2) := mul_le_mul_of_nonneg_right (by linarith [hr.1]) hp
      _ ≤ 1 := by simpa using pow_le_one₀ hr.1 hr.2 (n := p-2)
  nlinarith [mul_le_mul_of_nonneg_left hb (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p))]

private theorem A_eq_tsum {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    μ.A r = ∑' p, μ.coeff p * (p:ℝ) * (1-r) * r^(p-2) := by
  have hs : Summable (fun p => μ.coeff p * (p:ℝ) * (1-r) * r^(p-2)) :=
    .of_norm_bounded (by simpa using μ.summable_moment (k := 1) (by omega))
      (μ.dynamical_term_bound hr)
  rw [← hs.sum_add_tsum_nat_add 2]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,
    μ.zero_below_two 0 (by omega),μ.zero_below_two 1 (by omega),zero_mul,add_zero]
  rw [A,← tsum_mul_left]
  apply tsum_congr
  intro p
  simp only [dividedCoefficients,show p+2-2=p by omega]
  ring

theorem cutoffA_le {P : ℕ} {r : ℝ} (hr : r ∈ Icc (0:ℝ) 1) :
    μ.cutoffA P r ≤ μ.A r := by
  rw [μ.A_eq_tsum hr]
  apply Summable.sum_le_tsum _ (fun p _ =>
    mul_nonneg (mul_nonneg (mul_nonneg (μ.nonneg p) (Nat.cast_nonneg p))
      (sub_nonneg.mpr hr.2)) (pow_nonneg hr.1 _))
  exact .of_norm_bounded (by simpa using μ.summable_moment (k := 1) (by omega))
    (μ.dynamical_term_bound hr)

/-- Uniform convergence includes both endpoints of the physical overlap interval. -/
theorem cutoffA_tendstoUniformlyOn :
    TendstoUniformlyOn μ.cutoffA μ.A atTop (Icc (0:ℝ) 1) := by
  have h := tendstoUniformlyOn_tsum_nat
    (show Summable (fun p : ℕ => (p:ℝ)*μ.coeff p) by
      simpa using μ.summable_moment (k := 1) (by omega))
    (fun p r hr => μ.dynamical_term_bound hr p)
  have hh : TendstoUniformlyOn μ.cutoffA
      (fun r => ∑' p, μ.coeff p * (p:ℝ) * (1-r) * r^(p-2)) atTop (Icc 0 1) :=
    fun v hv => (tendsto_add_atTop_nat 1).eventually (h v hv)
  exact hh.congr_right (fun r hr => (μ.A_eq_tsum hr).symm)

theorem finiteCutoff_A_eq (P : ℕ) (hP : ∃ p,p≤P ∧ 0<μ.coeff p)
    {r : ℝ} (hr : r ≠ 0) :
    Thresholds.A (finiteCutoff μ P hP).xi r = μ.cutoffA P r := by
  rw [(finiteCutoff μ P hP).A_eq_polynomial hr]
  have hs : (finiteCutoff μ P hP).coeff.support ⊆ Finset.range (P+1) := by
    intro p hp
    have hh := Finsupp.mem_support_iff.mp hp
    rw [finiteCutoff_coeff] at hh
    by_contra h
    have hn : ¬p≤P := by simpa only [Finset.mem_range,Nat.lt_succ_iff] using h
    simp [hn] at hh
  change (finiteCutoff μ P hP).coeff.sum (fun p c => c*(p:ℝ)*(1-r)*r^(p-2)) = _
  rw [Finsupp.sum_of_support_subset _ hs (fun p c => c*(p:ℝ)*(1-r)*r^(p-2))
    (by intro p _;simp)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [finiteCutoff_coeff,if_pos (by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hp)]

theorem finiteCutoff_A_le (P : ℕ) (hP : ∃ p,p≤P ∧ 0<μ.coeff p)
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) :
    Thresholds.A (finiteCutoff μ P hP).xi r ≤ Thresholds.A μ.xi r := by
  rw [μ.finiteCutoff_A_eq P hP hr.1.ne',← μ.A_eq_threshold hr]
  exact μ.cutoffA_le ⟨hr.1.le,hr.2.le⟩

/-- A sequence of genuine cutoffs containing one fixed positive coefficient. -/
def basedCutoff (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀) (n : ℕ) : FiniteMixture :=
  finiteCutoff μ (P₀+n) ⟨P₀,Nat.le_add_right P₀ n,h₀⟩

theorem basedCutoff_A_tendsto (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀)
    {r : ℝ} (hr : r ∈ Ioo (0:ℝ) 1) :
    Tendsto (fun n => Thresholds.A (μ.basedCutoff P₀ h₀ n).xi r)
      atTop (𝓝 (Thresholds.A μ.xi r)) := by
  have h := (μ.cutoffA_tendstoUniformlyOn.tendsto_at ⟨hr.1.le,hr.2.le⟩).comp
    (show Tendsto (fun n => P₀+n) atTop atTop by simpa [Nat.add_comm] using tendsto_add_atTop_nat P₀)
  simpa only [basedCutoff,μ.finiteCutoff_A_eq _ _ hr.1.ne',μ.A_eq_threshold hr,Function.comp_def] using h

theorem basedCutoff_Amax_le (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀) (n : ℕ) :
    sSup (Thresholds.A (μ.basedCutoff P₀ h₀ n).xi '' Ioo 0 1) ≤ μ.Amax := by
  have hne : (Thresholds.A (μ.basedCutoff P₀ h₀ n).xi '' Ioo 0 1).Nonempty :=
    ⟨_,1/2,by norm_num,rfl⟩
  apply csSup_le hne
  rintro _ ⟨r,hr,rfl⟩
  exact (μ.finiteCutoff_A_le _ _ hr).trans (le_csSup μ.A_image_bddAbove ⟨r,hr,rfl⟩)

/-- The actual cutoff suprema converge without any uniqueness of maximizers. -/
theorem basedCutoff_Amax_tendsto (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀) :
    Tendsto (fun n => sSup (Thresholds.A (μ.basedCutoff P₀ h₀ n).xi '' Ioo 0 1))
      atTop (𝓝 μ.Amax) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    obtain ⟨a,⟨r,hr,rfl⟩,hbr⟩ := exists_lt_of_lt_csSup
      (show (Thresholds.A μ.xi '' Ioo 0 1).Nonempty from ⟨_,1/2,by norm_num,rfl⟩) hb
    filter_upwards [(μ.basedCutoff_A_tendsto P₀ h₀ hr).eventually (Ioi_mem_nhds hbr)] with n hn
    exact hn.trans_le (le_csSup (μ.basedCutoff P₀ h₀ n).A_image_bddAbove ⟨r,hr,rfl⟩)
  · intro b hb
    exact Eventually.of_forall (fun n => (μ.basedCutoff_Amax_le P₀ h₀ n).trans_lt hb)

/-- Convergence of the literal source dynamical thresholds. -/
theorem basedCutoff_dynamicalThreshold_tendsto (P₀ : ℕ) (h₀ : 0 < μ.coeff P₀) :
    Tendsto (fun n => Thresholds.dynamicalThreshold (μ.basedCutoff P₀ h₀ n).xi)
      atTop (𝓝 (Thresholds.dynamicalThreshold μ.xi)) := by
  exact ((μ.basedCutoff_Amax_tendsto P₀ h₀).inv₀ μ.Amax_pos.ne').sqrt

end SlowEquilibration.InfiniteMixture
