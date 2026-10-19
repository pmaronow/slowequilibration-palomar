-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.MixtureThresholds
public import Mathlib.Analysis.Calculus.LHopital

@[expose] public section

/-! The actual quadratic coefficient is strictly subcritical at every
strictly replica-symmetric temperature, including mixed odd covariances. -/

noncomputable section
namespace SlowEquilibration.FiniteMixture
open Set Filter
open scoped Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def reducedCovariance (μ : FiniteMixture) (r : ℝ) : ℝ :=
  ∑p ∈ μ.coeff.support,μ.coeff p*r^(p-2)

theorem reducedCovariance_continuous (μ : FiniteMixture) :
    Continuous μ.reducedCovariance := by unfold reducedCovariance; fun_prop

theorem reducedCovariance_zero (μ : FiniteMixture) : μ.reducedCovariance 0=μ.coeff 2 := by
  unfold reducedCovariance
  rw [Finset.sum_eq_single 2]
  · simp
  · intro p hp hp2
    have hdeg := μ.degree_ge_two hp
    simp [zero_pow (show p-2≠0 by omega)]
  · intro hp
    simp [Finsupp.notMem_support_iff.mp hp]

theorem xi_eq_reducedCovariance (μ : FiniteMixture) (r : ℝ) :
    μ.xi r=μ.reducedCovariance r*r^2 := by
  unfold xi reducedCovariance
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hdeg := μ.degree_ge_two hp
  rw [mul_assoc,← pow_add,show p-2+2=p by omega]

theorem xi_quadratic_lower (μ : FiniteMixture) {r : ℝ} (hr : 0≤r) :
    μ.coeff 2*r^2≤μ.xi r := by
  unfold xi
  by_cases h2 : 2∈μ.coeff.support
  · exact Finset.single_le_sum (fun p hp => mul_nonneg (μ.nonneg p) (pow_nonneg hr p)) h2
  · simp only [Finsupp.notMem_support_iff.mp h2,zero_mul]
    exact Finset.sum_nonneg fun p hp => mul_nonneg (μ.nonneg p) (pow_nonneg hr _)

private theorem staticNumerator_div_sq_tendsto :
    Tendsto (fun r : ℝ => (-r-Real.log (1-r))/r^2) (𝓝[>] 0) (𝓝 (1/2:ℝ)) := by
  have hlim : Tendsto (fun r : ℝ => (r/(1-r))/(2*r)) (𝓝[>] 0) (𝓝 (1/2:ℝ)) := by
    have h : Tendsto (fun r : ℝ => 1/(2*(1-r))) (𝓝[>] 0) (𝓝 (1/2:ℝ)) := by
      have hc : ContinuousAt (fun r : ℝ => 1/(2*(1-r))) 0 := by
        fun_prop (disch := norm_num)
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    apply h.congr'
    filter_upwards [self_mem_nhdsWithin] with r hr
    change 0<r at hr
    field_simp
  apply HasDerivAt.lhopital_zero_right_on_Ioo (show (0:ℝ)<1 by norm_num)
    (f' := fun r => r/(1-r)) (g' := fun r => 2*r)
  · intro r hr
    have hne : 1-r≠0 := (sub_pos.mpr hr.2).ne'
    have hlog := ((hasDerivAt_const r (1:ℝ)).sub (hasDerivAt_id r)).log hne
    convert (hasDerivAt_id r).neg.sub hlog using 1
    · rfl
    · dsimp
      field_simp
      ring
  · intro r hr
    convert hasDerivAt_pow 2 r using 1
    norm_num
  · intro r hr
    exact mul_ne_zero (by norm_num) hr.1.ne'
  · have h : ContinuousAt (fun r : ℝ => -r-Real.log (1-r)) 0 := by
      fun_prop (disch := norm_num)
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  · have h : ContinuousAt (fun r : ℝ => r^2) 0 := by fun_prop
    simpa using h.tendsto.mono_left nhdsWithin_le_nhds
  · exact hlim

/-- The actual coefficient of degree two lies below the limiting static
constraint; no pressure or thermodynamic hypothesis occurs here. -/
theorem quadratic_static_bound (μ : FiniteMixture) {β : ℝ}
    (hβ : 0≤β) (hβs : β≤Thresholds.staticThreshold μ.xi) :
    β^2*μ.coeff 2≤1/2 := by
  have hPhi := (Thresholds.Phi_nonpos_iff_le_staticThreshold
    (fun r hr => μ.xi_pos hr.1) hβ).mpr hβs
  apply ge_of_tendsto staticNumerator_div_sq_tendsto
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ)<1 by norm_num)] with r hr
  apply (le_div_iff₀ (sq_pos_of_pos hr.1)).mpr
  have hh := mul_le_mul_of_nonneg_left (μ.xi_quadratic_lower hr.1.le) (sq_nonneg β)
  have hφ := hPhi r hr
  dsimp [Thresholds.Phi] at hφ
  nlinarith

/-- Strict source temperature gives a strict quadratic margin, including the
case of a vanishing quadratic coefficient. -/
theorem quadratic_subcritical (μ : FiniteMixture) {β : ℝ}
    (hβ : 0≤β) (hβs : β<Thresholds.staticThreshold μ.xi) :
    β^2*μ.coeff 2<1/2 := by
  let b := (β+Thresholds.staticThreshold μ.xi)/2
  have hbb : β<b := by dsimp [b]; linarith
  have hb0 : 0≤b := hβ.trans hbb.le
  have hbs : b≤Thresholds.staticThreshold μ.xi := by dsimp [b]; linarith
  have hh := μ.quadratic_static_bound hb0 hbs
  by_cases h2 : μ.coeff 2=0
  · simp [h2]
  · have h2pos := lt_of_le_of_ne (μ.nonneg 2) (Ne.symm h2)
    have hsq : β^2<b^2 := (sq_lt_sq₀ hβ hb0).mpr hbb
    exact (mul_lt_mul_of_pos_right hsq h2pos).trans_le hh

theorem xi_abs_le (μ : FiniteMixture) (r : ℝ) : |μ.xi r|≤μ.xi |r| := by
  unfold xi
  calc
    _ ≤ ∑p ∈ μ.coeff.support,|μ.coeff p*r^p| := Finset.abs_sum_le_sum_abs _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [abs_mul,abs_of_nonneg (μ.nonneg p),abs_pow]

/-- A genuine fixed central window with a strict quadratic exponential budget
exists for every strictly subcritical canonical mixture, independent of N. -/
theorem exists_subcritical_quadratic_window (μ : FiniteMixture) {β : ℝ}
    (hβ : 0<β) (hβs : β<Thresholds.staticThreshold μ.xi) :
    ∃δ∈Ioo (0:ℝ) 1,∃κ>0,β^2*κ<1/2 ∧
      ∀r : ℝ,|r|≤δ → |μ.xi r|≤κ*r^2 := by
  have hb2 : 0<β^2 := sq_pos_of_pos hβ
  have hstrict := μ.quadratic_subcritical hβ.le hβs
  let κ := (μ.coeff 2+1/(2*β^2))/2
  have hck : μ.coeff 2<κ := by
    have hh : μ.coeff 2<1/(2*β^2) := (lt_div_iff₀ (by positivity)).mpr (by nlinarith)
    dsimp [κ]
    linarith
  have hk : 0<κ := lt_of_le_of_lt (μ.nonneg 2) hck
  have hbudget : β^2*κ<1/2 := by dsimp [κ]; field_simp; nlinarith
  have he : ∀ᶠ r in 𝓝 (0:ℝ),μ.reducedCovariance r<κ :=
    (μ.reducedCovariance_continuous.continuousAt).eventually
      (gt_mem_nhds (by simpa [μ.reducedCovariance_zero] using hck))
  obtain ⟨ρ,hρ,hρsub⟩ := Metric.mem_nhds_iff.mp he
  let δ := min (ρ/2) (1/2:ℝ)
  have hδ : 0<δ := lt_min (by positivity) (by norm_num)
  refine ⟨δ,⟨hδ,by dsimp [δ]; linarith [min_le_right (ρ/2) (1/2:ℝ)]⟩,κ,hk,hbudget,?_⟩
  intro r hr
  have hs : μ.reducedCovariance |r|<κ := hρsub (by
    simp only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_abs]
    have hδρ : δ≤ρ/2 := min_le_left _ _
    linarith)
  calc
    |μ.xi r| ≤ μ.xi |r| := μ.xi_abs_le r
    _ = μ.reducedCovariance |r| * r^2 := by rw [μ.xi_eq_reducedCovariance, sq_abs]
    _ ≤ _ := mul_le_mul_of_nonneg_right hs.le (sq_nonneg _)

end SlowEquilibration.FiniteMixture
