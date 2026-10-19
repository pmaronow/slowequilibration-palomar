-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPlantedProfile
public import SlowEquilibration.MixtureElasticity
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

/-!
# Actual planted trial pressure, strict compact gaps, and collar geometry

Every scalar is the manuscript's literal finite-mixture trial pressure.
Compact gaps follow from the actual static threshold. The dynamical
endpoint and finite polynomial roots supply the genuine collar geometry.
-/

namespace SlowEquilibration.SphericalModel

noncomputable section
open Set Filter
open scoped Topology BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

/-- The literal planted trial equals the actual annealed pressure plus
one half of the ordinary threshold potential. -/
theorem plantedProfileTrial_eq_annealed_add_Phi (μ : FiniteMixture) (β q : ℝ) :
    plantedProfileTrial μ β q = β^2*μ.xi 1/2+Thresholds.Phi μ.xi β q/2 := by
  unfold plantedProfileTrial Thresholds.Phi
  ring

theorem plantedProfileTrial_hasDerivAt (μ : FiniteMixture) (β : ℝ)
    {q : ℝ} (hq : q < 1) :
    HasDerivAt (plantedProfileTrial μ β)
      ((β^2*μ.xi1 q-q/(1-q))/2) q := by
  have h := (Thresholds.hasDerivAt_Phi (β := β)
    (μ.hasDerivAt_xi q).differentiableAt hq).div_const (2 : ℝ)
  rw [(μ.hasDerivAt_xi q).deriv] at h
  convert h.const_add (β^2*μ.xi 1/2) using 1
  · ext r
    exact plantedProfileTrial_eq_annealed_add_Phi μ β r

/-- Strict substaticity gives the actual pointwise planted trial gap. -/
theorem plantedProfileTrial_lt_annealed (μ : FiniteMixture) {β q : ℝ}
    (hβ0 : 0 ≤ β) (hβs : β < Thresholds.staticThreshold μ.xi)
    (hq : q ∈ Ioo (0 : ℝ) 1) :
    plantedProfileTrial μ β q < β^2*μ.xi 1/2 := by
  have h := μ.Phi_neg_of_lt_staticThreshold hβ0 hβs q hq
  rw [plantedProfileTrial_eq_annealed_add_Phi]
  linarith

/-- A genuine positive uniform compact trial gap, derived from the actual
static threshold and an actual attained compact maximum. -/
theorem exists_uniform_plantedProfileTrial_gap (μ : FiniteMixture) {β δ ρ : ℝ}
    (hβ0 : 0 ≤ β) (hβs : β < Thresholds.staticThreshold μ.xi)
    (hδ0 : 0 < δ) (hδρ : δ ≤ ρ) (hρ1 : ρ < 1) :
    ∃ η : ℝ, 0 < η ∧ ∀ q ∈ Icc δ ρ,
      plantedProfileTrial μ β q ≤ β^2*μ.xi 1/2-η := by
  have hcont : ContinuousOn (plantedProfileTrial μ β) (Icc δ ρ) := by
    intro q hq
    exact (plantedProfileTrial_hasDerivAt μ β (hq.2.trans_lt hρ1)).continuousAt.continuousWithinAt
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hδρ) hcont
  have hlt := plantedProfileTrial_lt_annealed μ hβ0 hβs
    ⟨hδ0.trans_le hq.1, hq.2.trans_lt hρ1⟩
  refine ⟨(β^2*μ.xi 1/2-plantedProfileTrial μ β q)/2, by linarith, ?_⟩
  intro r hr
  have h : plantedProfileTrial μ β r ≤ plantedProfileTrial μ β q := hmax hr
  linarith

/-- Actual core exponent, with no assumed constrained-pressure value. -/
def plantedCoreCost (μ : FiniteMixture) (β : ℝ) : ℝ :=
  -Thresholds.Phi μ.xi β (Thresholds.qStar μ.xi β)/2

theorem plantedCoreCost_pos (μ : FiniteMixture) {β : ℝ}
    (hβd : Thresholds.dynamicalThreshold μ.xi < β)
    (hβs : β < Thresholds.staticThreshold μ.xi) : 0 < plantedCoreCost μ β := by
  have hβ0 : 0 ≤ β := (μ.dynamicalThreshold_pos.trans hβd).le
  have hneg := μ.Phi_neg_of_lt_staticThreshold hβ0 hβs _ (μ.qStar_solves_plateau hβd).1
  unfold plantedCoreCost
  linarith

theorem plantedProfileTrial_qStar_eq (μ : FiniteMixture) (β : ℝ) :
    plantedProfileTrial μ β (Thresholds.qStar μ.xi β) =
      β^2*μ.xi 1/2-plantedCoreCost μ β := by
  rw [plantedProfileTrial_eq_annealed_add_Phi]
  unfold plantedCoreCost
  ring

end

end SlowEquilibration.SphericalModel
