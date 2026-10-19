-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PlantedCollarGeometry
public import Mathlib.Order.Interval.Set.Infinite

@[expose] public section

/-! # Genuine unique cap maximum at qStar without nondegeneracy

Later tangencies are allowed. The nonzero literal finite polynomial rules
out a flat trial interval, so the actual nonincreasing tail is strictly lower.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set Filter
open scoped Topology
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Every true latitude strictly to the right of qStar has strictly smaller
trial pressure, including mixtures with later degenerate tangencies. -/
theorem plantedProfileTrial_lt_after_qStar (μ : FiniteMixture) {β r : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β)
    (hqr : Thresholds.qStar μ.xi β<r) (hr : r<1) :
    plantedProfileTrial μ β r<plantedProfileTrial μ β (Thresholds.qStar μ.xi β) := by
  let q := Thresholds.qStar μ.xi β
  let P := μ.dynamicalLevelPolynomial β
  have hq : q∈Ioo (0:ℝ) 1 := (μ.qStar_solves_plateau hβ).1
  have hanti := plantedProfileTrial_antitoneOn_after_qStar μ hβ
  have hle : plantedProfileTrial μ β r≤plantedProfileTrial μ β q :=
    hanti ⟨le_rfl,hq.2⟩ ⟨hqr.le,hr⟩ hqr.le
  apply lt_of_le_of_ne hle
  intro heq
  have hconstant : ∀ s∈Icc q r,plantedProfileTrial μ β s=plantedProfileTrial μ β q := by
    intro s hs
    apply le_antisymm (hanti ⟨le_rfl,hq.2⟩ ⟨hs.1,hs.2.trans_lt hr⟩ hs.1)
    have hh := hanti ⟨hs.1,hs.2.trans_lt hr⟩ ⟨hqr.le,hr⟩ hs.2
    rwa [heq] at hh
  have hroot : Ioo q r⊆{s : ℝ | P.IsRoot s} := by
    intro s hs
    have hs01 : s∈Ioo (0:ℝ) 1 := ⟨hq.1.trans hs.1,hs.2.trans hr⟩
    have hevent : plantedProfileTrial μ β=ᶠ[𝓝 s] fun _ => plantedProfileTrial μ β q := by
      filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
      exact hconstant t ⟨ht.1.le,ht.2.le⟩
    have hd := hevent.deriv_eq
    simp only [deriv_const] at hd
    rw [plantedProfileTrial_deriv_eq μ β hs01] at hd
    have hp : 0<s/(2*(1-s)) := div_pos hs01.1 (by have hs1 := hs01.2; linarith)
    have hz : β^2*Thresholds.A μ.xi s-1=0 := (mul_eq_zero.mp hd).resolve_left hp.ne'
    change P.eval s=0
    rw [FiniteMixture.dynamicalLevelPolynomial_eval μ β hs01.1.ne']
    exact hz
  exact (Set.Ioo_infinite hqr)
    ((Polynomial.finite_setOfPred_isRoot (μ.dynamicalLevelPolynomial_ne_zero β)).subset hroot)

/-- The true admissible cap trial has exactly one maximizing latitude,
with no curvature or nondegeneracy assumption at that latitude. -/
theorem plantedProfileTrial_unique_cap_maximum (μ : FiniteMixture) {β q₁ q₂ : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi<β) (hc : IsAdmissibleCollar μ β q₁ q₂)
    {r : ℝ} (hr : r∈Ico q₁ 1)
    (hmax : plantedProfileTrial μ β (Thresholds.qStar μ.xi β)≤plantedProfileTrial μ β r) :
    r=Thresholds.qStar μ.xi β := by
  have hq₁ : q₁≤Thresholds.qStar μ.xi β := (hc.2.1.trans hc.2.2.1).le
  rcases lt_trichotomy r (Thresholds.qStar μ.xi β) with hlt|heq|hgt
  · have hh := plantedProfileTrial_strictMonoOn_collar μ hβ hc
      ⟨hr.1,hlt.le⟩ ⟨hq₁,le_rfl⟩ hlt
    exact False.elim (not_lt_of_ge hmax hh)
  · exact heq
  · exact False.elim (not_lt_of_ge hmax (plantedProfileTrial_lt_after_qStar μ hβ hgt hr.2))

end
end SlowEquilibration.SphericalModel
