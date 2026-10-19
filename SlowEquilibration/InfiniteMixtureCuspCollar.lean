-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureCuspBarrierEpsilon

@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set Filter Asymptotics
open scoped Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 2000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem hasDerivAt_cuspTrialPressure (μ : InfiniteMixture) (β : ℝ) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (μ.cuspTrialPressure β)
      (r / (2 * (1 - r)) * (β ^ 2 * μ.A r - 1)) r := by
  have hξ := (μ.analyticOnNhd_xi r ⟨by linarith [hr.1],hr.2⟩).differentiableAt
  have hd := ((Thresholds.hasDerivAt_Phi (β := β) hξ hr.2).const_add (β^2*μ.xi 1)).div_const 2
  convert hd using 1
  · ext x
    simp only [cuspTrialPressure,Thresholds.Phi]
    ring
  · rw [μ.A_eq_threshold hr,Thresholds.A]
    field_simp [hr.1.ne',(sub_pos.mpr hr.2).ne']

/-- A literal pressure-loss estimate on any interval inside the superlevel set. -/
theorem cuspTrialPressure_cost_bound (μ : InfiniteMixture) {β l u R ε : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (huR : u ≤ R) (hR : R < 1) (hε : 0 ≤ ε)
    (hβ : β^2*μ.Amax=1+ε)
    (hD : Ioo l u ⊆ Thresholds.plateauSuperlevel μ.xi β) :
    0 ≤ μ.cuspTrialPressure β u - μ.cuspTrialPressure β l ∧
    μ.cuspTrialPressure β u - μ.cuspTrialPressure β l ≤
      (1 / (2 * (1 - R))) * ε * (u-l) := by
  let f := μ.cuspTrialPressure β
  let L : ℝ := 1 / (2 * (1 - R))
  have hLi : 0 ≤ L := by dsimp [L]; positivity
  have hi (r : ℝ) (hr : r ∈ Icc l u) : r ∈ Ioo (0 : ℝ) 1 :=
    ⟨hl.trans_le hr.1,hr.2.trans_lt (huR.trans_lt hR)⟩
  have hc : ContinuousOn f (Icc l u) := fun r hr =>
    (μ.hasDerivAt_cuspTrialPressure β (hi r hr)).continuousAt.continuousWithinAt
  have hdf : DifferentiableOn ℝ f (interior (Icc l u)) := fun r hr =>
    (μ.hasDerivAt_cuspTrialPressure β (hi r (interior_subset hr))).differentiableAt.differentiableWithinAt
  have hd (r : ℝ) (hr : r ∈ interior (Icc l u)) :
      0 ≤ deriv f r ∧ deriv f r ≤ L * ε := by
    have hri := hi r (interior_subset hr)
    have hrD := hD (by simpa only [interior_Icc] using hr)
    have hA : 0 ≤ β^2*μ.A r-1 := by
      rw [μ.A_eq_threshold hri]
      linarith [hrD.2]
    have hA' : β^2*μ.A r-1 ≤ ε := by
      have ha := mul_le_mul_of_nonneg_left (μ.A_le_Amax_closed ⟨hri.1.le,hri.2.le⟩) (sq_nonneg β)
      linarith [hβ]
    have hw0 : 0 ≤ r / (2 * (1-r)) :=
      div_nonneg hri.1.le (mul_nonneg (by norm_num) (sub_nonneg.mpr hri.2.le))
    have hw : r / (2 * (1-r)) ≤ L := by
      dsimp [L]
      gcongr
      · exact hri.2.le
      · exact (interior_subset hr).2.trans huR
    rw [(μ.hasDerivAt_cuspTrialPressure β hri).deriv]
    exact ⟨mul_nonneg hw0 hA,mul_le_mul hw hA' hA hLi⟩
  constructor
  · have hh := (convex_Icc l u).mul_sub_le_image_sub_of_le_deriv hc hdf
      (fun r hr => (hd r hr).1) l ⟨le_rfl,hlu⟩ u ⟨hlu,le_rfl⟩ hlu
    simpa using hh
  · exact (convex_Icc l u).image_sub_le_mul_sub_of_deriv_le hc hdf
      (fun r hr => (hd r hr).2) l ⟨le_rfl,hlu⟩ u ⟨hlu,le_rfl⟩ hlu

namespace CuspCoordinate
variable {μ : InfiniteMixture} (c : CuspCoordinate μ)

def collarLeft (ε : ℝ) : ℝ := c.qMinus ε + ε / 2
def collarRight (ε : ℝ) : ℝ := c.qMinus ε + ε

def collarCost (ε : ℝ) : ℝ :=
  μ.cuspTrialPressure (c.epsilonTemperature ε) (c.collarRight ε) -
    μ.cuspTrialPressure (c.epsilonTemperature ε) (c.qMinus ε)

def collarGap (ε : ℝ) : ℝ :=
  μ.cuspTrialPressure (c.epsilonTemperature ε) (Thresholds.qStar μ.xi (c.epsilonTemperature ε)) -
    μ.cuspTrialPressure (c.epsilonTemperature ε) (c.collarRight ε)

private theorem roots_nested {h : ℝ} (hh : 0 ≤ h) (hr : h ≤ c.radius) :
    c.leftRoot c.radius ≤ c.leftRoot h ∧ c.rightRoot h ≤ c.rightRoot c.radius := by
  have hn : -h ∈ Icc (-c.radius) c.radius := by constructor <;> linarith [c.radius_pos]
  have hp : h ∈ Icc (-c.radius) c.radius := by constructor <;> linarith [c.radius_pos]
  constructor
  · exact add_le_add le_rfl (c.monotone.monotoneOn
      ⟨le_rfl,by linarith [c.radius_pos]⟩ hn (by linarith))
  · exact add_le_add le_rfl (c.monotone.monotoneOn hp
      ⟨by linarith [c.radius_pos],le_rfl⟩ hr)

private theorem scale_collar_order :
    ∀ᶠ h in 𝓝[>] (0 : ℝ), c.leftRoot h + c.a*h^(2*c.m) < c.rightRoot h := by
  let F : ℝ → ℝ := fun h => c.rightRoot h - c.leftRoot h - c.a*h^(2*c.m)
  have hk : 2*c.m-1 ≠ 0 := by have := c.m_pos; omega
  have hr : HasDerivAt c.rightRoot 1 0 := c.derivative.const_add μ.qD
  have hl : HasDerivAt c.leftRoot (-1) 0 := by
    change HasDerivAt (fun x : ℝ => μ.qD + c.g (-x)) (-1) 0
    have hn : HasDerivAt (fun x : ℝ => -x) (-1) 0 := (hasDerivAt_id 0).neg
    simpa only [Function.comp_def,neg_zero,mul_neg_one] using
      ((show HasDerivAt c.g 1 (-0) by simpa using c.derivative).comp 0 hn).const_add μ.qD
  have hF : HasDerivAt F 2 0 := by
    convert (hr.sub hl).sub (((hasDerivAt_id (0 : ℝ)).pow (2*c.m)).const_mul c.a) using 1
    · rfl
    · norm_num [hk]
  have hF0 : F 0 = 0 := by simp [F,leftRoot,rightRoot,zero_pow (by have := c.m_pos; omega : 2*c.m ≠ 0)]
  have hpos := hF.tendsto_slope_zero_right.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 2))
  filter_upwards [self_mem_nhdsWithin,hpos] with h hh hp
  simp only [zero_add,hF0,sub_zero,smul_eq_mul] at hp
  have hf : 0 < F h := (mul_pos_iff_of_pos_left (inv_pos.mpr hh)).mp hp
  dsimp [F] at hf
  linarith

/-- The source collar is actually inside the final superlevel component. -/
theorem collar_eventually :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c.qMinus ε < c.collarLeft ε ∧ c.collarLeft ε < c.collarRight ε ∧
      c.collarRight ε < c.qPlus ε ∧
      Thresholds.qStar μ.xi (c.epsilonTemperature ε) = c.qPlus ε ∧
      Ioo (c.qMinus ε) (c.qPlus ε) ⊆ Thresholds.plateauSuperlevel μ.xi (c.epsilonTemperature ε) ∧
      c.qMinus ε ∈ Ioo (0 : ℝ) 1 ∧
      c.qPlus ε ≤ c.rightRoot c.radius := by
  have hs := c.rootScale_tendsto c.scale_collar_order
  have hr := c.rootScale_tendsto (eventually_nhdsWithin_of_eventually_nhds
    (Iio_mem_nhds c.radius_pos))
  filter_upwards [self_mem_nhdsWithin,hs,hr,c.epsilon_roots_eventually] with ε hε hs hr he
  change 0 < ε at hε
  have hscale := c.rootScale_pos hε
  change c.leftRoot (c.rootScale ε) + c.a * c.rootScale ε ^ (2*c.m) < c.rightRoot (c.rootScale ε) at hs
  rw [c.rootScale_pow hε.le] at hs
  have hn := c.roots_nested hscale.le hr.le
  refine ⟨by dsimp [collarLeft]; linarith,by dsimp [collarLeft,collarRight]; linarith,
    hs,he.2.2.2.2.2.2,?_,he.2.2.1,hn.2⟩
  intro r hri
  apply (c.local_superlevel_iff hscale hr.le ?_ ?_).mpr hri
  · rw [c.epsilonTemperature_eq hε.le]
    exact c.temperature_sq _
  · exact ⟨hn.1.trans hri.1.le,hri.2.le.trans hn.2⟩

/-- The exact collar width loses only `O(ε²)` trial pressure. -/
theorem collarCost_bound_eventually :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 ≤ c.collarCost ε ∧ c.collarCost ε ≤
        (1 / (2 * (1 - c.rightRoot c.radius))) * ε^2 := by
  filter_upwards [self_mem_nhdsWithin,c.collar_eventually] with ε hε he
  have hi := (c.roots_interior c.radius_pos.le le_rfl).2
  have hh := μ.cuspTrialPressure_cost_bound he.2.2.2.2.2.1.1
    (he.1.trans he.2.1).le (he.2.2.1.le.trans he.2.2.2.2.2.2) hi.2 hε.le
    (by rw [c.epsilonTemperature_eq hε.le,c.temperature_sq,c.rootScale_pow hε.le])
    (fun r hr => he.2.2.2.2.1 ⟨hr.1,hr.2.trans he.2.2.1⟩)
  simpa only [collarCost,collarRight,add_sub_cancel_left,pow_two,mul_assoc] using hh

theorem collarCost_isBigO : c.collarCost =O[𝓝[>] (0 : ℝ)] (fun ε => ε^2) := by
  apply IsBigO.of_bound (1 / (2 * (1 - c.rightRoot c.radius)))
  filter_upwards [c.collarCost_bound_eventually] with ε he
  simpa only [Real.norm_of_nonneg he.1,Real.norm_of_nonneg (sq_nonneg ε)] using he.2

theorem collarGap_eq_eventually :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), c.collarGap ε = c.epsilonBarrier ε - c.collarCost ε := by
  filter_upwards [c.collar_eventually] with ε he
  simp only [collarGap,epsilonBarrier,collarCost,he.2.2.2.1]
  ring

/-- Collar loss relative to the barrier scale has the source exponent. -/
theorem collarCost_relative_remainder :
    (fun ε : ℝ => c.collarCost ε /
      (c.barrierCoefficient * ε ^ (1 + ((2*c.m : ℕ) : ℝ)⁻¹)))
      =O[𝓝[>] (0 : ℝ)] (fun ε => ε ^ (1 - ((2*c.m : ℕ) : ℝ)⁻¹)) := by
  have hO := c.collarCost_isBigO.mul
    (isBigO_refl (fun ε : ℝ => (ε ^ (1 + ((2*c.m : ℕ) : ℝ)⁻¹))⁻¹) (𝓝[>] (0 : ℝ)))
  apply (hO.const_mul_left c.barrierCoefficient⁻¹).congr' ?_ ?_
  · exact Filter.Eventually.of_forall (fun ε => by dsimp only; ring)
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    change ε ^ 2 * (ε ^ (1 + ((2*c.m : ℕ) : ℝ)⁻¹))⁻¹ = _
    rw [← Real.rpow_natCast,← div_eq_mul_inv,← Real.rpow_sub hε]
    congr 1
    norm_num
    ring

/-- Equation (inf-collar-gap), for the literal pressure gap and actual collar. -/
theorem collarGap_relative_remainder :
    (fun ε : ℝ => c.collarGap ε /
      (c.barrierCoefficient * ε ^ (1 + ((2*c.m : ℕ) : ℝ)⁻¹)) - 1)
      =O[𝓝[>] (0 : ℝ)] (fun ε =>
        ε ^ ((2*c.m : ℕ) : ℝ)⁻¹ + ε ^ (1 - ((2*c.m : ℕ) : ℝ)⁻¹)) := by
  have hO := c.epsilonBarrier_relative_remainder.add_add c.collarCost_relative_remainder.neg_left
  apply hO.congr' ?_ ?_
  · filter_upwards [c.collarGap_eq_eventually] with ε hε
    rw [hε]
    ring
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hε.le _),Real.norm_of_nonneg (Real.rpow_nonneg hε.le _)]

theorem collarGap_normalized_tendsto_one :
    Tendsto (fun ε : ℝ => c.collarGap ε /
      (c.barrierCoefficient * ε ^ (1 + ((2*c.m : ℕ) : ℝ)⁻¹))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hk : (1 : ℝ) < ((2*c.m : ℕ) : ℝ) := by have := c.m_pos; exact_mod_cast (by omega : 1 < 2*c.m)
  have hp : 0 < ((2*c.m : ℕ) : ℝ)⁻¹ := inv_pos.mpr (by linarith)
  have hq : 0 < 1 - ((2*c.m : ℕ) : ℝ)⁻¹ := sub_pos.mpr ((inv_lt_one₀ (by linarith)).mpr hk)
  have ht : Tendsto (fun x : ℝ => x) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hz := (ht.rpow_const_nhds_zero hp).add (ht.rpow_const_nhds_zero hq)
  have he := c.collarGap_relative_remainder.trans_tendsto (by simpa using hz)
  exact tendsto_sub_nhds_zero_iff.mp he

/-- The quantitative barrier needed for every fixed source tolerance. -/
theorem collarGap_lower_eventually {θ : ℝ} (hθ : 0 < θ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (1-θ) * (c.barrierCoefficient * ε ^ (1 + ((2*c.m : ℕ) : ℝ)⁻¹)) < c.collarGap ε := by
  have hh := c.collarGap_normalized_tendsto_one.eventually
    (lt_mem_nhds (by linarith : 1-θ < (1 : ℝ)))
  filter_upwards [self_mem_nhdsWithin,hh] with ε hε he
  exact (lt_div_iff₀ (mul_pos c.barrierCoefficient_pos (Real.rpow_pos_of_pos hε _))).mp he

/-- The manuscript's literal admissibility clauses for the constructed collar. -/
theorem admissible_collar_eventually :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      0 < c.collarLeft ε ∧ c.collarLeft ε < c.collarRight ε ∧
      c.collarRight ε < Thresholds.qStar μ.xi (c.epsilonTemperature ε) ∧
      ∀ r ∈ Ioo (c.collarLeft ε) (Thresholds.qStar μ.xi (c.epsilonTemperature ε)),
        1 < c.epsilonTemperature ε ^ 2 * Thresholds.A μ.xi r := by
  filter_upwards [c.collar_eventually] with ε he
  rw [he.2.2.2.1]
  exact ⟨he.2.2.2.2.2.1.1.trans he.1,he.2.1,he.2.2.1,
    fun r hr => (he.2.2.2.2.1 ⟨he.1.trans hr.1,hr.2⟩).2⟩

/-- The collar retains the fixed positive overlap used in the mode count. -/
theorem collarLeft_above_half_eventually :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), μ.qD / 2 < c.collarLeft ε := by
  have hroot : Tendsto c.rootScale (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    c.rootScale_tendsto.mono_right nhdsWithin_le_nhds
  have hneg : Tendsto (fun ε : ℝ => -c.rootScale ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [neg_zero] using hroot.neg
  have hg : Tendsto (fun ε : ℝ => c.g (-c.rootScale ε)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [c.zero,Function.comp_def] using c.analytic.continuousAt.tendsto.comp hneg
  have hε : Tendsto (fun ε : ℝ => ε / 2) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_nhdsWithin_of_tendsto_nhds ((continuous_id.div_const (2 : ℝ)).tendsto (0 : ℝ)))
  have ht : Tendsto c.collarLeft (𝓝[>] (0 : ℝ)) (𝓝 μ.qD) := by
    change Tendsto (fun ε => μ.qD + c.g (-c.rootScale ε) + ε / 2) _ _
    simpa only [add_zero] using (tendsto_const_nhds.add hg).add hε
  have hi : 0 < μ.qD := by
    have hh := c.interior 0 (show (0 : ℝ) ∈ Icc (-c.radius) c.radius by constructor <;> linarith [c.radius_pos])
    simpa only [c.zero,add_zero] using hh.1
  exact ht.eventually (lt_mem_nhds (by linarith : μ.qD / 2 < μ.qD))

theorem collar_width (ε : ℝ) : c.collarRight ε - c.collarLeft ε = ε / 2 := by
  simp only [collarRight,collarLeft]
  ring

end CuspCoordinate
end SlowEquilibration.InfiniteMixture
