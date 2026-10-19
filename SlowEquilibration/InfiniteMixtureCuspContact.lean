-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureThresholds
public import SlowEquilibration.RealAnalyticMaximumOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-! The actual maximizer and finite even contact asserted in Theorem 1.7,
derived from source summability and the strict dynamical/static threshold gap. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture
open Set Filter
open scoped Topology
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (μ : InfiniteMixture)

/-- All global maximizers on the literal closed source interval. -/
def globalMaximizers : Set ℝ := {r | r∈Icc (0:ℝ) 1 ∧ μ.A r=μ.Amax}

/-- The source chooses the rightmost global maximizer, even when several exist. -/
def qD : ℝ := sSup μ.globalMaximizers

theorem globalMaximizers_nonempty : μ.globalMaximizers.Nonempty := by
  have hcont : ContinuousOn μ.A (Icc (0:ℝ) 1) :=
    μ.continuousOn_A.mono (fun x hx => ⟨by linarith [hx.1],hx.2⟩)
  obtain ⟨q,hq,hm⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by norm_num)) hcont
  refine ⟨q,hq,le_antisymm (μ.A_le_Amax_closed hq) ?_⟩
  apply csSup_le (show (Thresholds.A μ.xi '' Ioo 0 1).Nonempty from
    ⟨Thresholds.A μ.xi (1/2),1/2,by norm_num,rfl⟩)
  rintro _ ⟨r,hr,rfl⟩
  rw [← μ.A_eq_threshold hr]
  exact hm ⟨hr.1.le,hr.2.le⟩

theorem globalMaximizers_isCompact : IsCompact μ.globalMaximizers := by
  have hcont : Continuous (fun r : Icc (0:ℝ) 1 => μ.A r) :=
    continuousOn_iff_continuous_domRestrict.mp (μ.continuousOn_A.mono (fun x hx => ⟨by linarith [hx.1],hx.2⟩))
  have hc : IsCompact {r : Icc (0:ℝ) 1 | μ.A r=μ.Amax} :=
    (isClosed_eq hcont continuous_const).isCompact
  have hi := hc.image continuous_subtype_val
  convert hi using 1
  ext r
  simp only [globalMaximizers,mem_ofPred_eq,mem_image,Subtype.exists,exists_and_right,exists_eq_right,exists_prop]

theorem globalMaximizers_subset_interior
    (hgap : Thresholds.dynamicalThreshold μ.xi<Thresholds.staticThreshold μ.xi) :
    μ.globalMaximizers ⊆ Ioo (0:ℝ) 1 := by
  intro r hr
  obtain ⟨hr,he⟩ := hr
  constructor
  · refine lt_of_le_of_ne hr.1 ?_
    intro h
    have hz := μ.A_zero_lt_Amax hgap
    rw [h] at hz
    exact hz.ne he
  · refine lt_of_le_of_ne hr.2 ?_
    intro h
    have hz := μ.Amax_pos
    rw [h,μ.A_one] at he
    linarith

theorem globalMaximizers_finite
    (hgap : Thresholds.dynamicalThreshold μ.xi<Thresholds.staticThreshold μ.xi) :
    μ.globalMaximizers.Finite := by
  let f : ℝ → ℝ := fun r => μ.A r-μ.Amax
  have ha : AnalyticOnNhd ℝ f (Ioo (-1:ℝ) 1) := μ.analyticOnNhd_A.sub analyticOnNhd_const
  have hz : f 0≠0 := sub_ne_zero.mpr (μ.A_zero_lt_Amax hgap).ne
  have hd := ha.preimage_zero_mem_codiscreteWithin hz (by norm_num : (0:ℝ)∈Ioo (-1:ℝ) 1)
    ((convex_Ioo (-1:ℝ) 1).isConnected ⟨0,by norm_num⟩)
  have hs : μ.globalMaximizers ⊆ Ioo (-1:ℝ) 1 := by
    intro r hr
    have hh := μ.globalMaximizers_subset_interior hgap hr
    exact ⟨by linarith [hh.1],hh.2⟩
  have hfin := μ.globalMaximizers_isCompact.finite_sdiff_of_mem_codiscreteWithin
    (Filter.codiscreteWithin_mono hs hd)
  have he : μ.globalMaximizers \ (f ⁻¹' {0}ᶜ)=μ.globalMaximizers := by
    ext r
    simp only [Set.mem_sdiff,mem_preimage,mem_compl_iff,mem_singleton_iff,not_not]
    exact ⟨And.left,fun hr => ⟨hr,sub_eq_zero.mpr hr.2⟩⟩
  rwa [he] at hfin

theorem qD_mem_globalMaximizers
    (hgap : Thresholds.dynamicalThreshold μ.xi<Thresholds.staticThreshold μ.xi) :
    μ.qD∈μ.globalMaximizers := μ.globalMaximizers_nonempty.csSup_mem (μ.globalMaximizers_finite hgap)

theorem qD_mem_interior
    (hgap : Thresholds.dynamicalThreshold μ.xi<Thresholds.staticThreshold μ.xi) :
    μ.qD∈Ioo (0:ℝ) 1 := μ.globalMaximizers_subset_interior hgap (μ.qD_mem_globalMaximizers hgap)

theorem globalMaximizer_le_qD {q : ℝ} (hq : q∈μ.globalMaximizers) : q≤μ.qD :=
  le_csSup μ.globalMaximizers_isCompact.bddAbove hq

/-- The literal rightmost maximizer has finite even contact, with an analytic
unit factor. Neither uniqueness nor nondegeneracy of the maximum is assumed. -/
theorem qD_even_contact
    (hgap : Thresholds.dynamicalThreshold μ.xi<Thresholds.staticThreshold μ.xi) :
    ∃ (m : ℕ) (a : ℝ) (φ : ℝ → ℝ),1≤m ∧ 0<a ∧ AnalyticAt ℝ φ 0 ∧ φ 0=1 ∧
      ∀ᶠ y in 𝓝 (0:ℝ),μ.A (μ.qD+y)=μ.Amax*(1-a*y^(2*m)*φ y) := by
  have hq := μ.qD_mem_interior hgap
  have hqe := (μ.qD_mem_globalMaximizers hgap).2
  have hqi : μ.qD∈Ioo (-1:ℝ) 1 := ⟨by linarith [hq.1],hq.2⟩
  have hmax : ∀ᶠ x in 𝓝 μ.qD,μ.A x≤μ.A μ.qD := by
    filter_upwards [isOpen_Ioo.mem_nhds hq] with x hx
    rw [hqe]
    exact μ.A_le_Amax hx
  let f : ℝ → ℝ := fun r => μ.A r-μ.Amax
  have ha : AnalyticOnNhd ℝ f (Ioo (-1:ℝ) 1) := μ.analyticOnNhd_A.sub analyticOnNhd_const
  have h0 : analyticOrderAt f 0=0 := analyticOrderAt_eq_zero.mpr (Or.inr (sub_ne_zero.mpr (μ.A_zero_lt_Amax hgap).ne))
  have hne := ha.analyticOrderAt_ne_top_of_isPreconnected (convex_Ioo (-1:ℝ) 1).isPreconnected
    (by norm_num : (0:ℝ)∈Ioo (-1:ℝ) 1) hqi (by rw [h0];simp)
  have hnot : ¬∀ᶠ x in 𝓝 μ.qD,μ.A x=μ.A μ.qD := by
    intro h
    apply hne
    apply analyticOrderAt_eq_top.mpr
    filter_upwards [h] with x hx
    exact sub_eq_zero.mpr (hx.trans hqe)
  have hh := RealAnalyticMaximumOrder.exists_even_contact (μ.analyticOnNhd_A _ hqi)
    (by rw [hqe];exact μ.Amax_pos) hmax hnot
  simpa only [hqe] using hh

/-- The literal normalized Taylor expansion in the statement of Theorem 1.7,
with an actual big-O remainder of order 2m+1. -/
theorem qD_cusp_expansion
    (hgap : Thresholds.dynamicalThreshold μ.xi<Thresholds.staticThreshold μ.xi) :
    ∃ (m : ℕ) (a : ℝ),1≤m ∧ 0<a ∧
      (fun y : ℝ => μ.A (μ.qD+y)/μ.Amax-(1-a*y^(2*m))) =O[𝓝 (0:ℝ)]
        (fun y : ℝ => y^(2*m+1)) := by
  obtain ⟨m,a,φ,hm,ha,hφ,hφ0,hfact⟩ := μ.qD_even_contact hgap
  refine ⟨m,a,hm,ha,?_⟩
  have hu : (fun y : ℝ => φ y-1) =O[𝓝 (0:ℝ)] (fun y : ℝ => y) := by
    simpa only [hφ0,sub_zero] using hφ.differentiableAt.isBigO_sub
  have hb := ((Asymptotics.isBigO_refl (fun y : ℝ => y^(2*m)) (𝓝 (0:ℝ))).mul hu).const_mul_left (-a)
  have hb' : (fun y : ℝ => -a*(y^(2*m)*(φ y-1))) =O[𝓝 (0:ℝ)] (fun y : ℝ => y^(2*m+1)) := by
    simpa only [pow_succ] using hb
  apply hb'.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards [hfact] with y hy
  rw [hy,mul_div_cancel_left₀ _ μ.Amax_pos.ne']
  ring

end SlowEquilibration.InfiniteMixture
