-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Tactic

/-! A nonconstant real analytic function at a genuine local maximum has a
strictly negative leading coefficient of finite positive even order. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.RealAnalyticMaximumOrder
open Set Filter
open scoped Topology
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Exact normalized analytic contact factorization at a positive local
maximum. The finite even order and the sign are conclusions. -/
theorem exists_even_contact {f : ℝ → ℝ} {q : ℝ}
    (hf : AnalyticAt ℝ f q) (hM : 0<f q)
    (hmax : ∀ᶠ x in 𝓝 q,f x≤f q)
    (hconstant : ¬∀ᶠ x in 𝓝 q,f x=f q) :
    ∃ (m : ℕ) (a : ℝ) (φ : ℝ → ℝ),1≤m ∧ 0<a ∧ AnalyticAt ℝ φ 0 ∧ φ 0=1 ∧
      ∀ᶠ y in 𝓝 (0:ℝ),f (q+y)=f q*(1-a*y^(2*m)*φ y) := by
  have hfa : AnalyticAt ℝ (fun x => f x-f q) q := hf.sub analyticAt_const
  have hnot : ¬∀ᶠ x in 𝓝 q,f x-f q=0 := by simpa only [sub_eq_zero] using hconstant
  obtain ⟨n,g,hg,hg0,hfact⟩ := hfa.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hnot
  have hn : n≠0 := by
    intro hn
    have h := hfact.self_of_nhds
    simp only [hn,sub_self,pow_zero,one_smul] at h
    exact hg0 h.symm
  have hgneg : g q<0 := by
    by_contra hle
    have hpos : 0<g q := lt_of_le_of_ne (le_of_not_gt hle) (Ne.symm hg0)
    have he : ∀ᶠ x in 𝓝 q,0<g x ∧ f x≤f q ∧ f x-f q=(x-q)^n*g x := by
      filter_upwards [hg.continuousAt.eventually (lt_mem_nhds hpos),hmax,hfact] with x hx hm he
      exact ⟨hx,hm,he⟩
    obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp he
    have hx : dist (q+δ/2) q<δ := by rw [Real.dist_eq];simp only [add_sub_cancel_left];rw [abs_of_pos (by positivity)];linarith
    obtain ⟨hp,hm,hf⟩ := hd hx
    have hpow : 0<(q+δ/2-q)^n := pow_pos (by linarith) n
    nlinarith [mul_pos hpow hp]
  have hEven : Even n := by
    by_contra he
    have hodd : Odd n := Nat.not_even_iff_odd.mp he
    have hev : ∀ᶠ x in 𝓝 q,g x<0 ∧ f x≤f q ∧ f x-f q=(x-q)^n*g x := by
      filter_upwards [hg.continuousAt.eventually (gt_mem_nhds hgneg),hmax,hfact] with x hx hm he
      exact ⟨hx,hm,he⟩
    obtain ⟨δ,hδ,hd⟩ := Metric.eventually_nhds_iff.mp hev
    have hx : dist (q-δ/2) q<δ := by
      rw [Real.dist_eq,show q-δ/2-q= -(δ/2) by ring,abs_neg,abs_of_pos (by positivity)]
      linarith
    obtain ⟨hp,hm,hf⟩ := hd hx
    have hpow : (q-δ/2-q)^n<0 := hodd.pow_neg_iff.mpr (by linarith)
    nlinarith [mul_pos_of_neg_of_neg hpow hp]
  obtain ⟨m,hm⟩ := hEven
  have hnm : n=2*m := by omega
  have hm1 : 1≤m := by omega
  let φ : ℝ → ℝ := fun y => g (q+y)/g q
  refine ⟨m,-g q/f q,φ,hm1,div_pos (neg_pos.mpr hgneg) hM,?_,?_,?_⟩
  · have hga : AnalyticAt ℝ g (q+0) := by simpa using hg
    exact (hga.comp (analyticAt_const.add analyticAt_id)).div_const
  · simp [φ,hg0]
  · have ht : Tendsto (fun y : ℝ => q+y) (𝓝 0) (𝓝 q) := by
      have hh : Tendsto (fun y : ℝ => q+y) (𝓝 0) (𝓝 (q+0)) := tendsto_const_nhds.add tendsto_id
      rwa [add_zero] at hh
    filter_upwards [ht.eventually hfact] with y hy
    simp only [smul_eq_mul,add_sub_cancel_left,hnm] at hy
    dsimp only [φ]
    field_simp
    nlinarith [hy]

end SlowEquilibration.RealAnalyticMaximumOrder
