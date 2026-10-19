-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.LatitudeGroundPrimalMinimum

/-! The actual minimum has the coupled one-step equations, including both
endpoints of the location interval. No stationarity equation is assumed. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.LatitudeGroundTrial
open Set Filter
open scoped Topology
set_option maxHeartbeats 600000

theorem primalAtBottom_hasDerivAt_location (χ χ₁ : ℝ → ℝ) {α s b : ℝ}
    (hχ : HasDerivAt χ (χ₁ s) s) (hα : 0 < α) (hb : 0 < b)
    (hL : 0 < b+α*(1-s)) :
    HasDerivAt (fun t => primalAtBottom χ χ₁ α t b)
      (α*(s/(b+α*(1-s))^2-χ₁ s)/2) s := by
  have hlin := (hasDerivAt_const s b).add
    (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).const_mul α)
  have hquot := (hasDerivAt_id s).div hlin hL.ne'
  have hlog := ((hlin.div_const b).log (div_ne_zero hL.ne' hb.ne')).div_const α
  have hdiff := ((hasDerivAt_const s (χ 1)).sub hχ).const_mul α
  have hh := ((((hasDerivAt_const s (b*χ₁ 1)).add hdiff).add hquot).add hlog).div_const 2
  have hfun : (fun t => primalAtBottom χ χ₁ α t b)=
      (fun t => (b*χ₁ 1+α*(χ 1-χ t)+t/(b+α*(1-t))+
        Real.log ((b+α*(1-t))/b)/α)/2) := by
    funext t
    exact primalAtBottom_eq χ χ₁ α t b
  rw [hfun]
  convert hh using 1
  · ext t
    rfl
  · dsimp only [Pi.sub_apply,Pi.div_apply,Pi.mul_apply,Pi.add_apply,id_eq]
    have hLn : b+α-α*s ≠ 0 := by convert hL.ne' using 1;ring
    field_simp [hα.ne',hb.ne',hL.ne',hLn]
    ring

theorem derivative_nonnegative_at_interval_left {f : ℝ → ℝ} {v : ℝ}
    (hd : HasDerivAt f v 0) (hmin : ∀ t ∈ Icc (0 : ℝ) 1, f 0 ≤ f t) :
    0 ≤ v := by
  have hm : IsMinOn f (Icc (0 : ℝ) 1) 0 := hmin
  have ht : (1 : ℝ) ∈ posTangentConeAt (Icc (0 : ℝ) 1) 0 := by
    apply mem_posTangentConeAt_of_segment_subset
    simpa only [zero_add] using (convex_Icc (0 : ℝ) 1).segment_subset
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨le_rfl,by norm_num⟩)
      (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 from ⟨by norm_num,le_rfl⟩)
  simpa using hm.isLocalMinOn.hasFDerivWithinAt_nonneg
    hd.hasFDerivAt.hasFDerivWithinAt ht

theorem exists_coupled_primal_minimum (χ χ₁ : ℝ → ℝ) {α : ℝ}
    (hα : 0 < α) (hχ : ∀ t, HasDerivAt χ (χ₁ t) t)
    (hmono : MonotoneOn χ (Icc (0 : ℝ) 1)) (hχ₁ : 0 < χ₁ 1)
    (hχ₀ : 0 ≤ χ₁ 0) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ b > 0,
      (∀ t ∈ Icc (0 : ℝ) 1, ∀ c > 0,
        primalAtBottom χ χ₁ α s b ≤ primalAtBottom χ χ₁ α t c) ∧
      χ₁ s=s/(b+α*(1-s))^2 ∧
      χ₁ 1-χ₁ s=(1-s)/((b+α*(1-s))*b) := by
  have hc : Continuous χ := continuous_iff_continuousAt.mpr
    (fun t => (hχ t).continuousAt)
  obtain ⟨s,hs,b,hb,hmin⟩ := exists_global_primal_minimum χ χ₁ hα hc.continuousOn hmono hχ₁
  let L := b+α*(1-s)
  have hL : 0 < L := by
    have hn := mul_nonneg hα.le (sub_nonneg.mpr hs.2)
    dsimp [L]
    linarith
  have hbot : L-α*(1-s)=b := by dsimp [L];ring
  have hlocal : IsLocalMin (fun c => primalAtBottom χ χ₁ α s c) b := by
    filter_upwards [Ioi_mem_nhds hb] with c hc
    exact hmin s hs c hc
  have hdheight : HasDerivAt (fun c => primalAtBottom χ χ₁ α s c)
      ((χ₁ 1-s/L^2-(1-s)/(L*b))/2) b := by
    have hd := (primal_hasDerivAt_height χ χ₁ hL hα (by rw [hbot];exact hb)).comp b
      ((hasDerivAt_id b).add_const (α*(1-s)))
    convert hd using 1
    · ext c
      rfl
    · rw [hbot]
      ring
  have hheight := hlocal.hasDerivAt_eq_zero hdheight
  have hdlocation := primalAtBottom_hasDerivAt_location χ χ₁ (hχ s) hα hb hL
  have hcoupled : χ₁ s=s/L^2 := by
    by_cases hsone : s=1
    · rw [hsone] at hheight ⊢
      simp only [sub_self,zero_div] at hheight
      linarith
    by_cases hszero : s=0
    · have hmin0 : ∀ t ∈ Icc (0 : ℝ) 1,
          primalAtBottom χ χ₁ α 0 b ≤ primalAtBottom χ χ₁ α t b := by
        intro t ht
        simpa only [hszero] using hmin t ht b hb
      have hd0 := hdlocation
      rw [hszero] at hd0
      have hv := derivative_nonnegative_at_interval_left hd0 hmin0
      simp only [zero_div,zero_sub] at hv
      have hprod : α*χ₁ 0=0 := by nlinarith [mul_nonneg hα.le hχ₀]
      have he := (mul_eq_zero.mp hprod).resolve_left hα.ne'
      rw [hszero,zero_div,he]
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hszero)
      have hslt : s < 1 := lt_of_le_of_ne hs.2 hsone
      have hloc : IsLocalMin (fun t => primalAtBottom χ χ₁ α t b) s := by
        filter_upwards [Icc_mem_nhds hspos hslt] with t ht
        exact hmin t ht b hb
      have hv := hloc.hasDerivAt_eq_zero hdlocation
      have hprod : α*(s/L^2-χ₁ s)=0 := by change α*(s/L^2-χ₁ s)/2=0 at hv;linarith
      have he := (mul_eq_zero.mp hprod).resolve_left hα.ne'
      linarith
  refine ⟨s,hs,b,hb,hmin,hcoupled,?_⟩
  change χ₁ 1-χ₁ s=(1-s)/(L*b)
  linarith

end SlowEquilibration.LatitudeGroundTrial
