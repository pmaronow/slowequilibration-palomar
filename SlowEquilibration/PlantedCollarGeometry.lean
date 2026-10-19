-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PlantedTrialGeometry

@[expose] public section

/-!
# Actual finite-mixture collars at the dynamical endpoint

Finite polynomial roots rule out oscillation just left of the actual strict
superlevel supremum. This includes degenerate endpoint roots and does not
identify the endpoint as the largest root.
-/

namespace SlowEquilibration.FiniteMixture

noncomputable section
open Set Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- The actual finite polynomial equal to `β²A(r)-1` away from zero. -/
def dynamicalLevelPolynomial (μ : FiniteMixture) (β : ℝ) : Polynomial ℝ :=
  Polynomial.C (β^2)*(∑ p ∈ μ.coeff.support,
    Polynomial.C (μ.coeff p)*Polynomial.C (p : ℝ)*
      (Polynomial.C 1-Polynomial.X)*Polynomial.X^(p-2))-Polynomial.C 1

theorem dynamicalLevelPolynomial_eval (μ : FiniteMixture) (β : ℝ)
    {r : ℝ} (hr : r ≠ 0) :
    (μ.dynamicalLevelPolynomial β).eval r = β^2*Thresholds.A μ.xi r-1 := by
  rw [μ.A_eq_polynomial hr]
  simp [dynamicalLevelPolynomial, Polynomial.eval_finsetSum]

theorem dynamicalLevelPolynomial_eval_one (μ : FiniteMixture) (β : ℝ) :
    (μ.dynamicalLevelPolynomial β).eval 1 = -1 := by
  simp [dynamicalLevelPolynomial, Polynomial.eval_finsetSum]

theorem dynamicalLevelPolynomial_ne_zero (μ : FiniteMixture) (β : ℝ) :
    μ.dynamicalLevelPolynomial β ≠ 0 := by
  intro h
  have hh := congrArg (fun p : Polynomial ℝ => p.eval 1) h
  rw [μ.dynamicalLevelPolynomial_eval_one] at hh
  norm_num at hh

/-- The genuine finite-mixture strict superlevel contains an entire left
neighborhood of its actual supremum. Finiteness of polynomial roots supplies
this result, including multiple roots at the endpoint. -/
theorem exists_left_qStar_superlevel (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    ∃ δ : ℝ, 0 < δ ∧ δ < Thresholds.qStar μ.xi β ∧
      ∀ r ∈ Ioo (Thresholds.qStar μ.xi β-δ) (Thresholds.qStar μ.xi β),
        1 < β^2*Thresholds.A μ.xi r := by
  classical
  let q := Thresholds.qStar μ.xi β
  let P := μ.dynamicalLevelPolynomial β
  have hq : q ∈ Ioo (0 : ℝ) 1 := (μ.qStar_solves_plateau hβ).1
  have hlevel : β^2*Thresholds.A μ.xi q = 1 :=
    (Thresholds.plateau_iff hq).mpr (μ.qStar_solves_plateau hβ).2
  have hfinite : Set.Finite {r : ℝ | P.IsRoot r} :=
    Polynomial.finite_setOfPred_isRoot (μ.dynamicalLevelPolynomial_ne_zero β)
  let Z := {r : ℝ | P.IsRoot r}\{q}
  have hclosed : IsClosed Z := hfinite.sdiff.isClosed
  have hnbh : Zᶜ ∈ 𝓝 q := hclosed.isOpen_compl.mem_nhds (by simp [Z])
  obtain ⟨ε, hε, heps⟩ := Metric.mem_nhds_iff.mp hnbh
  let δ := min ε (q/2)
  have hδ : 0 < δ := lt_min hε (by linarith [hq.1])
  have hδq : δ < q := (min_le_right ε (q/2)).trans_lt (by linarith [hq.1])
  have hnoRoot : ∀ r ∈ Ioo (q-δ) q, ¬P.IsRoot r := by
    intro r hr hroot
    have hdist : dist r q < ε := by
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr hr.2)]
      have hδε : δ ≤ ε := min_le_left _ _
      linarith [hr.1]
    have hm : r ∈ Z := ⟨hroot, by simp only [mem_singleton_iff]; exact hr.2.ne⟩
    exact (heps (Metric.mem_ball.mpr hdist)) hm
  have hne := μ.plateauSuperlevel_nonempty hβ
  have hbelow : q-δ < sSup (Thresholds.plateauSuperlevel μ.xi β) := by
    change q-δ < q
    linarith
  obtain ⟨r₀, hr₀, hr₀low⟩ := exists_lt_of_lt_csSup hne hbelow
  have hr₀le : r₀ ≤ q := le_csSup (μ.plateauSuperlevel_bddAbove β) hr₀
  have hr₀ne : r₀ ≠ q := by
    intro heq
    rw [heq] at hr₀
    exact (not_lt_of_ge hlevel.le) hr₀.2
  have hr₀q : r₀ < q := lt_of_le_of_ne hr₀le hr₀ne
  have hr₀int : r₀ ∈ Ioo (q-δ) q := ⟨hr₀low, hr₀q⟩
  have hP₀ : 0 < P.eval r₀ := by
    rw [μ.dynamicalLevelPolynomial_eval β hr₀.1.1.ne']
    linarith [hr₀.2]
  refine ⟨δ, hδ, hδq, ?_⟩
  intro r hr
  have hr0 : 0 < r := by linarith [hr.1]
  have hpositive : 0 < P.eval r := by
    by_contra hn
    have hneg : P.eval r < 0 := lt_of_le_of_ne (le_of_not_gt hn)
      (by intro heq; exact hnoRoot r hr heq)
    by_cases hrr₀ : r ≤ r₀
    · obtain ⟨w, hw, hweq⟩ := intermediate_value_Icc hrr₀ P.continuous.continuousOn
        ⟨hneg.le, hP₀.le⟩
      exact hnoRoot w ⟨hr.1.trans_le hw.1, hw.2.trans_lt hr₀q⟩ hweq
    · have hr₀r : r₀ ≤ r := (lt_of_not_ge hrr₀).le
      obtain ⟨w, hw, hweq⟩ := intermediate_value_Icc' hr₀r P.continuous.continuousOn
        ⟨hneg.le, hP₀.le⟩
      exact hnoRoot w ⟨hr₀low.trans_le hw.1, hw.2.trans_lt hr.2⟩ hweq
  rw [μ.dynamicalLevelPolynomial_eval β hr0.ne'] at hpositive
  linarith

end

end SlowEquilibration.FiniteMixture

namespace SlowEquilibration.SphericalModel

noncomputable section
open Set

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- The manuscript's literal admissible collar condition. -/
def IsAdmissibleCollar (μ : FiniteMixture) (β q₁ q₂ : ℝ) : Prop :=
  0 < q₁ ∧ q₁ < q₂ ∧ q₂ < Thresholds.qStar μ.xi β ∧
    ∀ r ∈ Ioo q₁ (Thresholds.qStar μ.xi β), 1 < β^2*Thresholds.A μ.xi r

/-- Genuine collars can begin above any fixed overlap below the actual
endpoint, with their superlevel condition derived from finite roots. -/
theorem exists_admissibleCollar_above (μ : FiniteMixture) {β a : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (ha : a < Thresholds.qStar μ.xi β) :
    ∃ q₁ q₂ : ℝ, a < q₁ ∧ IsAdmissibleCollar μ β q₁ q₂ := by
  obtain ⟨δ, hδ0, hδq, hlevel⟩ := μ.exists_left_qStar_superlevel hβ
  let q := Thresholds.qStar μ.xi β
  let b := max a (q-δ)
  let q₁ := (b+q)/2
  let q₂ := (q₁+q)/2
  have hbq : b < q := max_lt ha (by linarith)
  have hb0 : 0 < b := (by linarith : 0 < q-δ).trans_le (le_max_right a (q-δ))
  have hb₁ : b < q₁ := by dsimp [q₁]; linarith
  have h₁q : q₁ < q := by dsimp [q₁]; linarith
  have h₁₂ : q₁ < q₂ := by dsimp [q₂]; linarith
  have h₂q : q₂ < q := by dsimp [q₂]; linarith
  refine ⟨q₁, q₂, (le_max_left a (q-δ)).trans_lt hb₁,
    hb0.trans hb₁, h₁₂, h₂q, ?_⟩
  intro r hr
  apply hlevel r
  exact ⟨((le_max_right a (q-δ)).trans_lt hb₁).trans hr.1, hr.2⟩

/-- The actual collars meet the exact spin-level constraint used in the
main memory theorem, with no collar existence hypothesis. -/
theorem exists_admissibleCollar_above_sqrt (μ : FiniteMixture) {β b : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β)
    (hb : b ∈ Ioo (0 : ℝ) ((Thresholds.qStar μ.xi β)^2)) :
    ∃ q₁ q₂ : ℝ, Real.sqrt b < q₁ ∧ IsAdmissibleCollar μ β q₁ q₂ := by
  have hq := (μ.qStar_solves_plateau hβ).1
  have hs : Real.sqrt b < Thresholds.qStar μ.xi β := by
    nlinarith [Real.sq_sqrt hb.1.le, Real.sqrt_nonneg b, hq.1, hb.2]
  exact exists_admissibleCollar_above μ hβ hs

theorem plantedProfileTrial_deriv_eq (μ : FiniteMixture) (β : ℝ)
    {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    deriv (plantedProfileTrial μ β) r =
      r/(2*(1-r))*(β^2*Thresholds.A μ.xi r-1) := by
  rw [(plantedProfileTrial_hasDerivAt μ β hr.2).deriv]
  unfold Thresholds.A
  rw [(μ.hasDerivAt_xi r).deriv]
  field_simp [hr.1.ne', (sub_pos.mpr hr.2).ne']

/-- The literal trial pressure is nonincreasing on the true right-hand
plateau tail, including degenerate roots and later tangencies. -/
theorem plantedProfileTrial_antitoneOn_after_qStar (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    AntitoneOn (plantedProfileTrial μ β) (Ico (Thresholds.qStar μ.xi β) 1) := by
  have hq := (μ.qStar_solves_plateau hβ).1
  apply antitoneOn_of_deriv_nonpos (convex_Ico _ 1)
  · intro r hr
    exact (plantedProfileTrial_hasDerivAt μ β hr.2).continuousAt.continuousWithinAt
  · intro r hr
    have hr' : r ∈ Ioo (Thresholds.qStar μ.xi β) 1 := by
      simpa only [interior_Ico] using hr
    exact (plantedProfileTrial_hasDerivAt μ β hr'.2).differentiableAt.differentiableWithinAt
  · intro r hr
    have hr' : r ∈ Ioo (Thresholds.qStar μ.xi β) 1 := by
      simpa only [interior_Ico] using hr
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hq.1.trans hr'.1, hr'.2⟩
    rw [plantedProfileTrial_deriv_eq μ β hr01]
    apply mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg hr01.1.le (by linarith [hr01.2]))
    exact sub_nonpos.mpr (μ.A_le_one_of_qStar_lt hr01 hr'.1)

/-- On a literal admissible collar the actual trial is strictly increasing
all the way to the endpoint. No sign or monotonicity conclusion is a premise. -/
theorem plantedProfileTrial_strictMonoOn_collar (μ : FiniteMixture) {β q₁ q₂ : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) (hc : IsAdmissibleCollar μ β q₁ q₂) :
    StrictMonoOn (plantedProfileTrial μ β) (Icc q₁ (Thresholds.qStar μ.xi β)) := by
  have hq := (μ.qStar_solves_plateau hβ).1
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · intro r hr
    exact (plantedProfileTrial_hasDerivAt μ β (hr.2.trans_lt hq.2)).continuousAt.continuousWithinAt
  · intro r hr
    have hr' : r ∈ Ioo q₁ (Thresholds.qStar μ.xi β) := by
      simpa only [interior_Icc] using hr
    have hr01 : r ∈ Ioo (0 : ℝ) 1 := ⟨hc.1.trans hr'.1, hr'.2.trans hq.2⟩
    rw [plantedProfileTrial_deriv_eq μ β hr01]
    exact mul_pos (div_pos hr01.1 (by linarith [hr01.2]))
      (sub_pos.mpr (hc.2.2.2 r hr'))

/-- Literal collar gap. -/
def plantedCollarGap (μ : FiniteMixture) (β q₂ : ℝ) : ℝ :=
  (Thresholds.Phi μ.xi β (Thresholds.qStar μ.xi β)-Thresholds.Phi μ.xi β q₂)/2

theorem plantedCollarGap_eq (μ : FiniteMixture) (β q₂ : ℝ) :
    plantedCollarGap μ β q₂ = plantedProfileTrial μ β (Thresholds.qStar μ.xi β)-
      plantedProfileTrial μ β q₂ := by
  unfold plantedCollarGap
  rw [plantedProfileTrial_eq_annealed_add_Phi, plantedProfileTrial_eq_annealed_add_Phi]
  ring

theorem plantedCollarGap_pos (μ : FiniteMixture) {β q₁ q₂ : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) (hc : IsAdmissibleCollar μ β q₁ q₂) :
    0 < plantedCollarGap μ β q₂ := by
  rw [plantedCollarGap_eq]
  exact sub_pos.mpr (plantedProfileTrial_strictMonoOn_collar μ hβ hc
    ⟨hc.2.1.le, hc.2.2.1.le⟩ ⟨(hc.2.1.trans hc.2.2.1).le, le_rfl⟩ hc.2.2.1)

/-- The actual trial is bounded by its core value throughout the entire
cap, and by its strictly smaller collar value on the collar. -/
theorem plantedProfileTrial_cap_collar_bounds (μ : FiniteMixture) {β q₁ q₂ : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) (hc : IsAdmissibleCollar μ β q₁ q₂) :
    (∀ r ∈ Ico q₁ 1, plantedProfileTrial μ β r ≤
      β^2*μ.xi 1/2-plantedCoreCost μ β) ∧
    (∀ r ∈ Icc q₁ q₂, plantedProfileTrial μ β r ≤
      β^2*μ.xi 1/2-plantedCoreCost μ β-plantedCollarGap μ β q₂) := by
  have hq := (μ.qStar_solves_plateau hβ).1
  have hmono := (plantedProfileTrial_strictMonoOn_collar μ hβ hc).monotoneOn
  have hanti := plantedProfileTrial_antitoneOn_after_qStar μ hβ
  have hq₁q : q₁ ≤ Thresholds.qStar μ.xi β := (hc.2.1.trans hc.2.2.1).le
  constructor
  · intro r hr
    rw [← plantedProfileTrial_qStar_eq]
    by_cases hrq : r ≤ Thresholds.qStar μ.xi β
    · exact hmono ⟨hr.1, hrq⟩ ⟨hq₁q, le_rfl⟩ hrq
    · have hqr : Thresholds.qStar μ.xi β ≤ r := (lt_of_not_ge hrq).le
      exact hanti ⟨le_rfl, hq.2⟩ ⟨hqr, hr.2⟩ hqr
  · intro r hr
    rw [plantedCollarGap_eq, ← plantedProfileTrial_qStar_eq]
    have hbound := hmono ⟨hr.1, hr.2.trans hc.2.2.1.le⟩
      ⟨hc.2.1.le, hc.2.2.1.le⟩ hr.2
    linarith

/-- Complete actual scalar cap/collar certificate at every requested spin
level below `qStar²`. All collars, gaps, and trial inequalities are derived
from the literal thresholds of the finite mixture. -/
theorem exists_plantedTrial_certificate (μ : FiniteMixture) {β b : ℝ}
    (hβd : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β < Thresholds.staticThreshold μ.xi)
    (hb : b ∈ Ioo (0 : ℝ) ((Thresholds.qStar μ.xi β)^2)) :
    ∃ q₁ q₂ : ℝ, Real.sqrt b < q₁ ∧ IsAdmissibleCollar μ β q₁ q₂ ∧
      0 < plantedCoreCost μ β ∧ 0 < plantedCollarGap μ β q₂ ∧
      (∀ r ∈ Ico q₁ 1, plantedProfileTrial μ β r ≤
        β^2*μ.xi 1/2-plantedCoreCost μ β) ∧
      (∀ r ∈ Icc q₁ q₂, plantedProfileTrial μ β r ≤
        β^2*μ.xi 1/2-plantedCoreCost μ β-plantedCollarGap μ β q₂) := by
  obtain ⟨q₁, q₂, hbq, hc⟩ := exists_admissibleCollar_above_sqrt μ hβd hb
  obtain ⟨hcap, hcollar⟩ := plantedProfileTrial_cap_collar_bounds μ hβd hc
  exact ⟨q₁, q₂, hbq, hc, plantedCoreCost_pos μ hβd hβs,
    plantedCollarGap_pos μ hβd hc, hcap, hcollar⟩

end

end SlowEquilibration.SphericalModel
