-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSPureModels
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
# Pure-spin scalar static parameters

The function upsilon is defined by its genuine ordinary integral. Its
logarithmic expression, continuity, strict decrease, limiting values, and
the unique scalar root are derived rather than postulated.
-/

namespace SlowEquilibration.PureScalarStatic

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

/-- The ordinary scalar integral appearing in the pure-spin stationarity
equations, with its continuous value at zero included. -/
def upsilon (z : ℝ) : ℝ := ∫ t in (0 : ℝ)..1, (1-t)/(1+z*t)

theorem upsilon_integrand_continuousOn {z : ℝ} (hz : 0 ≤ z) :
    ContinuousOn (fun t : ℝ => (1-t)/(1+z*t)) (Icc (0 : ℝ) 1) := by
  apply (continuous_const.sub continuous_id).continuousOn.div
    (continuous_const.add (continuous_const.mul continuous_id)).continuousOn
  intro t ht
  change 1+z*t ≠ 0
  exact ne_of_gt (by have := mul_nonneg hz ht.1; linarith)

/-- Exact analytic evaluation of the ordinary scalar integral. -/
theorem upsilon_eq {z : ℝ} (hz : 0 < z) :
    upsilon z = ((1+z)*Real.log (1+z)-z)/z^2 := by
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun t : ℝ => ((1+z)*Real.log (1+z*t)-z*t)/z^2)
        ((1-t)/(1+z*t)) t := by
    intro t ht
    have ht0 : 0 ≤ t := by
      rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
      exact ht.1
    have hden : 1+z*t ≠ 0 := ne_of_gt (by have := mul_nonneg hz.le ht0; linarith)
    have hlin := (hasDerivAt_const t (1 : ℝ)).add ((hasDerivAt_id t).const_mul z)
    have hlog := hlin.log hden
    convert ((hlog.const_mul (1+z)).sub ((hasDerivAt_id t).const_mul z)).div_const (z^2) using 1
    · ext s
      rfl
    · dsimp
      field_simp [hden, hz.ne']
      ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((upsilon_integrand_continuousOn hz.le).intervalIntegrable_of_Icc (by norm_num))
  simpa only [upsilon, mul_one, mul_zero, add_zero, Real.log_one, sub_zero, zero_div] using hi

/-- The endpoint value is the actual integral of `1-t`. -/
theorem upsilon_zero : upsilon 0 = (1/2 : ℝ) := by
  unfold upsilon
  simp only [zero_mul, add_zero, div_one]
  have hconst : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
    continuous_const.intervalIntegrable 0 1
  have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 1 :=
    continuous_id.intervalIntegrable 0 1
  rw [intervalIntegral.integral_sub hconst hid]
  norm_num [integral_id]

/-- Genuine continuity on the whole nonnegative parameter interval,
obtained by integrating an actual globally continuous clamped kernel. -/
theorem continuousOn_upsilon : ContinuousOn upsilon (Ici (0 : ℝ)) := by
  let f : ℝ → ℝ → ℝ := fun z t => (1-t)/(1+max z 0*max t 0)
  have hf : Continuous f.uncurry := by
    apply (continuous_const.sub continuous_snd).div
      (continuous_const.add ((continuous_fst.max continuous_const).mul
        (continuous_snd.max continuous_const)))
    intro x
    change 1+max x.1 0*max x.2 0 ≠ 0
    exact ne_of_gt (by have := mul_nonneg (le_max_right x.1 0) (le_max_right x.2 0); linarith)
  have hc := continuous_parametric_integral_of_continuous (μ := volume) hf
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) 1))
  apply hc.continuousOn.congr
  intro z hz
  unfold upsilon
  rw [intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp [f]
  rw [max_eq_left hz, max_eq_left ht.1]

/-- Strict monotonicity is proved by strict comparison of the actual
integrands, with a strict witness at the midpoint. -/
theorem strictAntiOn_upsilon : StrictAntiOn upsilon (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := hx
  have hy0 : 0 ≤ y := hy
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0 : ℝ) < 1) (upsilon_integrand_continuousOn hy)
    (upsilon_integrand_continuousOn hx)
  · intro t ht
    have hdx : 0 < 1+x*t := by have := mul_nonneg hx ht.1.le; linarith
    have hdy : 0 < 1+y*t := by have := mul_nonneg hy ht.1.le; linarith
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr ht.2) hdx
      (by nlinarith [mul_nonneg (sub_pos.mpr hxy).le ht.1.le])
  · refine ⟨1/2, by norm_num, ?_⟩
    have hdx : 0 < 1+x*(1/2) := by linarith
    have hdy : 0 < 1+y*(1/2) := by linarith
    exact div_lt_div_of_pos_left (by norm_num) hdx (by nlinarith)

/-- The true scalar function tends to zero at infinity. -/
theorem tendsto_upsilon_atTop : Tendsto upsilon atTop (𝓝 (0 : ℝ)) := by
  have hi : Tendsto (fun z : ℝ => 1/z) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hl : Tendsto (fun z : ℝ => Real.log (1+z)/z) atTop (𝓝 (0 : ℝ)) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero).comp
      (tendsto_atTop_add_const_left atTop (1 : ℝ) tendsto_id)
    apply h.congr'
    filter_upwards with z
    simp only [pow_one, one_mul, Function.comp_def, id_eq]
    congr 1
    ring
  have hh : Tendsto (fun z : ℝ => (1+1/z)*(Real.log (1+z)/z)-1/z) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.add hi).mul hl |>.sub hi
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
  rw [upsilon_eq hz]
  field_simp [hz.ne']
  ring

/-- Each pure degree at least three has exactly one positive root of the
ordinary scalar stationarity equation `upsilon(z)=1/p`. -/
theorem existsUnique_upsilon_root (p : ℕ) (hp : 3 ≤ p) :
    ∃! z : ℝ, 0 < z ∧ upsilon z = 1/(p : ℝ) := by
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have htarget : 0 < 1/(p : ℝ) := by positivity
  have htargetHalf : 1/(p : ℝ) < (1/2 : ℝ) := by
    exact (div_lt_div_iff₀ (by positivity : (0 : ℝ) < p) (by norm_num)).mpr (by linarith)
  obtain ⟨z, hz0, hzlow⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    (tendsto_upsilon_atTop.eventually (gt_mem_nhds htarget))).exists
  have hcont : ContinuousOn upsilon (Icc (0 : ℝ) z) :=
    continuousOn_upsilon.mono Icc_subset_Ici_self
  obtain ⟨w, hw, hweq⟩ := intermediate_value_Icc' hz0.le hcont
    ⟨hzlow.le, by simpa only [upsilon_zero] using htargetHalf.le⟩
  have hw0 : 0 < w := by
    by_contra hn
    have hwzero : w = 0 := le_antisymm (le_of_not_gt hn) hw.1
    rw [hwzero, upsilon_zero] at hweq
    linarith
  refine ⟨w, ⟨hw0, hweq⟩, ?_⟩
  intro v hv
  exact strictAntiOn_upsilon.injOn hv.1.le hw0.le (hv.2.trans hweq.symm)

/-- The scalar parameter is selected from the proved unique positive root. -/
def zParameter (p : ℕ) (hp : 3 ≤ p) : ℝ :=
  Classical.choose (existsUnique_upsilon_root p hp)

theorem zParameter_spec (p : ℕ) (hp : 3 ≤ p) :
    0 < zParameter p hp ∧ upsilon (zParameter p hp) = 1/(p : ℝ) :=
  (Classical.choose_spec (existsUnique_upsilon_root p hp)).1

/-- The static critical overlap associated with a scalar parameter. -/
def staticOverlap (z : ℝ) : ℝ := z/(1+z)

theorem staticOverlap_mem_Ioo {z : ℝ} (hz : 0 < z) :
    staticOverlap z ∈ Ioo (0 : ℝ) 1 := by
  unfold staticOverlap
  refine ⟨div_pos hz (by linarith), ?_⟩
  exact (div_lt_one (by linarith : 0 < 1+z)).mpr (by linarith)

/-- Exact scalar sign identity under the genuine change of variables
`z=r/(1-r)`. -/
theorem staticDerivativeNumerator_eq (p : ℕ) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    r^2/(1-r)-(p : ℝ)*(-r-Real.log (1-r)) =
      r^2/(1-r)*(1-(p : ℝ)*upsilon (r/(1-r))) := by
  have hden : 1-r ≠ 0 := (sub_pos.mpr hr.2).ne'
  have hz : 0 < r/(1-r) := div_pos hr.1 (sub_pos.mpr hr.2)
  have hsum : 1+r/(1-r) = (1-r)⁻¹ := by field_simp [hden]; ring
  rw [upsilon_eq hz, hsum, Real.log_inv]
  field_simp [hden, hr.1.ne']
  ring

/-- Actual derivative of the ordinary pure-spin static ratio, with the
positive power factor and its scalar sign numerator explicitly separated. -/
theorem hasDerivAt_staticRatio_pure (p : ℕ) (hp : 1 ≤ p)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (Thresholds.staticRatio (fun x : ℝ => x^p))
      (r^(p-1)/(r^p)^2*(r^2/(1-r)-(p : ℝ)*(-r-Real.log (1-r)))) r := by
  have hden : 1-r ≠ 0 := (sub_pos.mpr hr.2).ne'
  have hpow : r^p = r^(p-1)*r := by
    rw [← pow_succ]
    congr 1
    omega
  have hlog := ((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).log hden
  have hnum := (hasDerivAt_id r).neg.sub hlog
  convert hnum.div (hasDerivAt_pow p r) (pow_ne_zero p hr.1.ne') using 1
  · ext x
    rfl
  · dsimp
    rw [hpow]
    field_simp [hden, hr.1.ne', pow_ne_zero (p-1) hr.1.ne']
    ring

theorem staticRatio_pure_continuousOn (p : ℕ) :
    ContinuousOn (Thresholds.staticRatio (fun x : ℝ => x^p)) (Ioo (0 : ℝ) 1) := by
  apply ((continuous_id.neg).continuousOn.sub
    ((continuous_const.sub continuous_id).continuousOn.log (fun r hr =>
      (sub_pos.mpr hr.2).ne'))).div (continuous_pow p).continuousOn
  intro r hr
  exact pow_ne_zero p hr.1.ne'

/-- The actual static ratio strictly decreases before the unique scalar
root overlap and strictly increases after it. -/
theorem staticRatio_pure_strict_monotonicity (p : ℕ) (hp : 3 ≤ p)
    {z : ℝ} (hz : 0 < z) (hroot : upsilon z = 1/(p : ℝ)) :
    StrictAntiOn (Thresholds.staticRatio (fun x : ℝ => x^p)) (Ioc (0 : ℝ) (staticOverlap z)) ∧
    StrictMonoOn (Thresholds.staticRatio (fun x : ℝ => x^p)) (Ico (staticOverlap z) 1) := by
  have hq := staticOverlap_mem_Ioo hz
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hpInv : (p : ℝ)*(1/(p : ℝ)) = 1 := by field_simp
  have hderivSign (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      deriv (Thresholds.staticRatio (fun x : ℝ => x^p)) r =
        r^(p-1)/(r^p)^2*(r^2/(1-r)*(1-(p : ℝ)*upsilon (r/(1-r)))) := by
    rw [(hasDerivAt_staticRatio_pure p (by omega) hr).deriv, staticDerivativeNumerator_eq p hr]
  have hfactor (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) 1) :
      0 < r^(p-1)/(r^p)^2 ∧ 0 < r^2/(1-r) := by
    have hr0 := hr.1
    have hden := sub_pos.mpr hr.2
    constructor <;> positivity
  constructor
  · apply strictAntiOn_of_deriv_neg (convex_Ioc 0 (staticOverlap z))
    · exact (staticRatio_pure_continuousOn p).mono (fun r hr => ⟨hr.1, hr.2.trans_lt hq.2⟩)
    · intro r hr
      have hr' : r ∈ Ioo (0 : ℝ) (staticOverlap z) := by simpa only [interior_Ioc] using hr
      have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hr'.1, hr'.2.trans hq.2⟩
      have hzr : 0 < r/(1-r) := div_pos hr'.1 (sub_pos.mpr hr01.2)
      have hzrz : r/(1-r) < z := by
        apply (div_lt_iff₀ (sub_pos.mpr hr01.2)).mpr
        have h := (lt_div_iff₀ (by linarith : 0 < 1+z)).mp hr'.2
        nlinarith
      have hu := strictAntiOn_upsilon hzr.le hz.le hzrz
      rw [hroot] at hu
      have hneg : 1-(p : ℝ)*upsilon (r/(1-r)) < 0 := by
        have hm := mul_lt_mul_of_pos_left hu hpR
        rw [hpInv] at hm
        linarith
      rw [hderivSign r hr01]
      exact mul_neg_of_pos_of_neg (hfactor r hr01).1
        (mul_neg_of_pos_of_neg (hfactor r hr01).2 hneg)
  · apply strictMonoOn_of_deriv_pos (convex_Ico (staticOverlap z) 1)
    · exact (staticRatio_pure_continuousOn p).mono (fun r hr => ⟨hq.1.trans_le hr.1, hr.2⟩)
    · intro r hr
      have hr' : r ∈ Ioo (staticOverlap z) 1 := by simpa only [interior_Ico] using hr
      have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hq.1.trans hr'.1, hr'.2⟩
      have hzr : 0 < r/(1-r) := div_pos hr01.1 (sub_pos.mpr hr01.2)
      have hzzr : z < r/(1-r) := by
        apply (lt_div_iff₀ (sub_pos.mpr hr01.2)).mpr
        have h := (div_lt_iff₀ (by linarith : 0 < 1+z)).mp hr'.1
        nlinarith
      have hu := strictAntiOn_upsilon hz.le hzr.le hzzr
      rw [hroot] at hu
      have hpos : 0 < 1-(p : ℝ)*upsilon (r/(1-r)) := by
        have hm := mul_lt_mul_of_pos_left hu hpR
        rw [hpInv] at hm
        linarith
      rw [hderivSign r hr01]
      exact mul_pos (hfactor r hr01).1 (mul_pos (hfactor r hr01).2 hpos)

/-- The scalar root overlap is the unique global minimum of the actual
pure-spin static ratio on the full physical interval. -/
theorem staticRatio_pure_unique_minimum (p : ℕ) (hp : 3 ≤ p)
    {z : ℝ} (hz : 0 < z) (hroot : upsilon z = 1/(p : ℝ)) :
    ∀ r ∈ Ioo (0 : ℝ) 1,
      Thresholds.staticRatio (fun x : ℝ => x^p) (staticOverlap z) ≤
        Thresholds.staticRatio (fun x : ℝ => x^p) r ∧
      (Thresholds.staticRatio (fun x : ℝ => x^p) (staticOverlap z) =
        Thresholds.staticRatio (fun x : ℝ => x^p) r ↔ r = staticOverlap z) := by
  have hq := staticOverlap_mem_Ioo hz
  obtain ⟨ha, hm⟩ := staticRatio_pure_strict_monotonicity p hp hz hroot
  intro r hr
  rcases lt_trichotomy r (staticOverlap z) with hlt | heq | hgt
  · have h := ha ⟨hr.1, hlt.le⟩ ⟨hq.1, le_rfl⟩ hlt
    exact ⟨h.le, ⟨fun he => (h.ne he).elim, fun he => (hlt.ne he).elim⟩⟩
  · simp [heq]
  · have h := hm ⟨le_rfl, hq.2⟩ ⟨hgt.le, hr.2⟩ hgt
    exact ⟨h.le, ⟨fun he => (h.ne he).elim, fun he => (hgt.ne he.symm).elim⟩⟩

/-- Exact value of the genuine pure-spin static minimum, deduced from the
root equation and actual global minimum rather than assumed stationarity. -/
theorem staticRatio_pure_at_root (p : ℕ) (hp : 3 ≤ p)
    {z : ℝ} (hz : 0 < z) (hroot : upsilon z = 1/(p : ℝ)) :
    let q := staticOverlap z
    Thresholds.staticRatio (fun x : ℝ => x^p) q =
      1/((p : ℝ)*q^(p-2)*(1-q)) := by
  let q := staticOverlap z
  have hq := staticOverlap_mem_Ioo hz
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hzchange : q/(1-q) = z := by
    dsimp [q, staticOverlap]
    field_simp [show 1+z ≠ 0 by linarith]
    ring
  have hD := staticDerivativeNumerator_eq p hq
  rw [hzchange, hroot, mul_one_div_cancel hpR.ne', sub_self, mul_zero] at hD
  have hnum : -q-Real.log (1-q) = q^2/((p : ℝ)*(1-q)) := by
    apply (eq_div_iff (mul_ne_zero hpR.ne' (sub_pos.mpr hq.2).ne')).mpr
    have hD' : q^2 = ((p : ℝ)*(-q-Real.log (1-q)))*(1-q) := by
      apply (div_eq_iff (sub_pos.mpr hq.2).ne').mp
      linarith
    nlinarith
  have hpow : q^p = q^(p-2)*q^2 := by
    rw [← pow_add]
    congr 1
    omega
  change (-q-Real.log (1-q))/q^p = 1/((p : ℝ)*q^(p-2)*(1-q))
  rw [hnum, hpow]
  have hq0 : q ≠ 0 := hq.1.ne'
  have hq1 : 1-q ≠ 0 := (sub_pos.mpr hq.2).ne'
  field_simp [hpR.ne', hq0, hq1, pow_ne_zero (p-2) hq0]

/-- The manuscript's explicit pure static-threshold formula, with its
unique scalar parameter constructed from the actual ordinary integral. -/
theorem pure_staticThreshold_sq (p : ℕ) (hp : 3 ≤ p) :
    let q := staticOverlap (zParameter p hp)
    Thresholds.staticThreshold (fun x : ℝ => x^p)^2 =
      1/((p : ℝ)*q^(p-2)*(1-q)) := by
  obtain ⟨hz, hroot⟩ := zParameter_spec p hp
  have hq := staticOverlap_mem_Ioo hz
  have hmin := staticRatio_pure_unique_minimum p hp hz hroot
  have hleast : IsLeast (Thresholds.staticRatio (fun x : ℝ => x^p) '' Ioo (0 : ℝ) 1)
      (Thresholds.staticRatio (fun x : ℝ => x^p) (staticOverlap (zParameter p hp))) := by
    refine ⟨⟨_, hq, rfl⟩, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact (hmin r hr).1
  rw [Thresholds.staticThreshold_sq (fun r hr => pow_pos hr.1 p), hleast.csInf_eq]
  exact staticRatio_pure_at_root p hp hz hroot

end

end SlowEquilibration.PureScalarStatic
