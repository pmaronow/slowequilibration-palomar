-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPResidual
public import SlowEquilibration.MixtureSubcriticalQuadratic
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Calculus.LHopital

@[expose] public section

/-! The uniform quadratic residual margin of source Proposition5.11(2).
The certificate supplies the positive limit at zero; the actual finite
covariance and spherical entropy supply the divergence at one. -/

namespace SlowEquilibration.SphericalTAPResidualMargin

noncomputable section
open Set Filter
open SphericalTAPCertificate SphericalTAPResidual
open scoped Topology

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem covariance_continuous (μ : FiniteMixture) : Continuous μ.xi := by
  unfold FiniteMixture.xi
  fun_prop

theorem xi2_zero (μ : FiniteMixture) : μ.xi2 0 = 2*μ.coeff 2 := by
  unfold FiniteMixture.xi2
  rw [Finset.sum_eq_single 2]
  · simp [FiniteMixture.curvatureCoeff, mul_comm]
  · intro p hp hp2
    have hdeg := μ.degree_ge_two hp
    simp [zero_pow (show p-2 ≠ 0 by omega)]
  · intro hp
    simp [FiniteMixture.curvatureCoeff, Finsupp.notMem_support_iff.mp hp]

private theorem entropy_ratio_tendsto :
    Tendsto (fun t : ℝ => (-t-Real.log (1-t))/t^2) (𝓝[>] 0) (𝓝 (1/2 : ℝ)) := by
  have hlim : Tendsto (fun t : ℝ => (t/(1-t))/(2*t)) (𝓝[>] 0) (𝓝 (1/2 : ℝ)) := by
    have hc : ContinuousAt (fun t : ℝ => 1/(2*(1-t))) 0 := by
      fun_prop (disch := norm_num)
    have hh : Tendsto (fun t : ℝ => 1/(2*(1-t))) (𝓝[>] 0) (𝓝 (1/2 : ℝ)) := by
      simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    field_simp
  apply HasDerivAt.lhopital_zero_right_on_Ioo (show (0 : ℝ) < 1 by norm_num)
    (f' := fun t => t/(1-t)) (g' := fun t => 2*t)
  · intro t ht
    have hne : 1-t ≠ 0 := (sub_pos.mpr ht.2).ne'
    have hl := ((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).log hne
    convert (hasDerivAt_id t).neg.sub hl using 1
    · rfl
    · dsimp
      field_simp
      ring
  · intro t ht
    convert hasDerivAt_pow 2 t using 1
    norm_num
  · intro t ht
    exact mul_ne_zero (by norm_num) ht.1.ne'
  · have hc : ContinuousAt (fun t : ℝ => -t-Real.log (1-t)) 0 := by
      fun_prop (disch := norm_num)
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · have hc : ContinuousAt (fun t : ℝ => t^2) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  · exact hlim

/-- The actual finite-mixture RS potential has its exact quadratic
ratio limit, including a nonzero degree-two coefficient. -/
theorem negative_Phi_ratio_tendsto (μ : FiniteMixture) (β : ℝ) :
    Tendsto (fun t : ℝ => -Thresholds.Phi μ.xi β t/t^2)
      (𝓝[>] 0) (𝓝 (1/2-β^2*μ.coeff 2)) := by
  have hr : Tendsto μ.reducedCovariance (𝓝[>] (0 : ℝ))
      (𝓝 (μ.reducedCovariance 0)) :=
    μ.reducedCovariance_continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  rw [μ.reducedCovariance_zero] at hr
  have hh := entropy_ratio_tendsto.sub (hr.const_mul (β^2))
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  rw [Thresholds.Phi, μ.xi_eq_reducedCovariance]
  field_simp [ht.ne']
  ring

/-- The spherical logarithmic entropy forces the literal RS potential
to diverge to minus infinity at overlap one. -/
theorem Phi_tendsto_atBot (μ : FiniteMixture) (β : ℝ) :
    Tendsto (Thresholds.Phi μ.xi β) (𝓝[<] (1 : ℝ)) atBot := by
  have hl : Tendsto (fun t : ℝ => 1-t) (𝓝[<] 1) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun t : ℝ => 1-t) := continuous_const.sub continuous_id
      have hh : Tendsto (fun t : ℝ => 1-t) (𝓝[<] (1 : ℝ)) (𝓝 ((1 : ℝ)-1)) :=
        hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      simpa only [sub_self] using hh
    · filter_upwards [self_mem_nhdsWithin] with t ht
      change 0 < 1-t
      change t < 1 at ht
      linarith
  have hlog := Real.tendsto_log_nhdsGT_zero.comp hl
  have hbase : Tendsto (fun t : ℝ => β^2*μ.xi t+t) (𝓝[<] 1) (𝓝 (β^2*μ.xi 1+1)) :=
    (((covariance_continuous μ).const_mul (β^2)).add continuous_id).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  exact hbase.add_atBot hlog

/-- Pointwise strict RS and the genuine strictly subcritical quadratic
coefficient imply a global uniform quadratic gap on the whole open interval. -/
theorem uniform_quadratic_gap (μ : FiniteMixture) (β : ℝ)
    (hneg : ∀ t ∈ Ioo (0 : ℝ) 1, Thresholds.Phi μ.xi β t < 0)
    (hquad : β^2*μ.xi2 0 < 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ t ∈ Ioo (0 : ℝ) 1, κ*t^2 ≤ -Thresholds.Phi μ.xi β t := by
  let a := 1/2-β^2*μ.coeff 2
  have ha : 0 < a := by rw [xi2_zero] at hquad; dsimp [a]; nlinarith
  have hnear0 : {t : ℝ | a/2 < -Thresholds.Phi μ.xi β t/t^2} ∈ 𝓝[>] 0 :=
    (negative_Phi_ratio_tendsto μ β).eventually (lt_mem_nhds (by change a/2 < a; linarith))
  obtain ⟨u, hu, hleft⟩ :=
    (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset (show (0 : ℝ) < 1/3 by norm_num)).mp hnear0
  have hnear1 : {t : ℝ | Thresholds.Phi μ.xi β t ≤ -1} ∈ 𝓝[<] 1 :=
    (Phi_tendsto_atBot μ β).eventually (eventually_le_atBot (-1))
  obtain ⟨v, hv, hright⟩ :=
    (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset (show (2/3 : ℝ) < 1 by norm_num)).mp hnear1
  let f : ℝ → ℝ := fun t => -Thresholds.Phi μ.xi β t/t^2
  have huv : u < v := by linarith [hu.2, hv.1]
  have hf : ContinuousOn f (Icc u v) := by
    apply ContinuousOn.div
    · apply ContinuousOn.neg
      unfold Thresholds.Phi
      apply ContinuousOn.add
      · exact ((covariance_continuous μ).const_mul (β^2)).continuousOn.add continuousOn_id
      · apply ContinuousOn.log (continuousOn_const.sub continuousOn_id)
        intro t ht
        exact (show 0 < 1-t by linarith [ht.2, hv.2]).ne'
    · exact continuousOn_id.pow 2
    · intro t ht
      exact pow_ne_zero 2 (show 0 < t by linarith [hu.1, ht.1]).ne'
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.mpr huv.le) hf
  have ht₀range : t₀ ∈ Ioo (0 : ℝ) 1 := ⟨hu.1.trans_le ht₀.1, ht₀.2.trans_lt hv.2⟩
  have hminpos : 0 < f t₀ := div_pos (neg_pos.mpr (hneg t₀ ht₀range))
    (sq_pos_of_pos ht₀range.1)
  let κ := min (a/2) (min (f t₀) 1)
  have hκ : 0 < κ := lt_min (half_pos ha) (lt_min hminpos zero_lt_one)
  refine ⟨κ, hκ, ?_⟩
  intro t ht
  apply (le_div_iff₀ (sq_pos_of_pos ht.1)).mp
  by_cases htu : t < u
  · exact (min_le_left _ _).trans (hleft ⟨ht.1, htu⟩).le
  by_cases hvt : v < t
  · have hh : Thresholds.Phi μ.xi β t ≤ -1 := hright ⟨hvt, ht.2⟩
    have hs : t^2 ≤ 1 := by nlinarith [ht.1, ht.2]
    have h1 : 1 ≤ f t := (le_div_iff₀ (sq_pos_of_pos ht.1)).mpr (by linarith)
    exact ((min_le_right _ _).trans (min_le_right _ _)).trans h1
  · exact ((min_le_right _ _).trans (min_le_left _ _)).trans
      (hmin ⟨le_of_not_gt htu, le_of_not_gt hvt⟩)

/-- Exact source Proposition5.11(2): one uniform strictly positive
κ_res controls the true original contact potential after residual rescaling. -/
theorem certificate_residual_margin {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ t ∈ Ioo (0 : ℝ) 1,
      κ*t^2 ≤ CSStructure.potential μ β (CrisantiSommers.twoAtom x Q) (Q+(1-Q)*t) := by
  obtain ⟨κ,hκ,hgap⟩ := uniform_quadratic_gap
    (μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)) β
    (residual_Phi_neg h) (residual_replicon_lt_one h)
  refine ⟨κ,hκ,?_⟩
  intro t ht
  have hh := hgap t ht
  rw [residual_Phi_eq_neg_potential h ht, neg_neg] at hh
  exact hh

end
end SlowEquilibration.SphericalTAPResidualMargin
