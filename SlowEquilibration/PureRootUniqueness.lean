-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureStationarity
public import SlowEquilibration.PureRootLocation

@[expose] public section

namespace SlowEquilibration.PureStationarity

noncomputable section
open Set MeasureTheory CrisantiSommers PureScalarStatic CSParisiMeasure

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def purePlateauShape (p : ℕ) (r : ℝ) : ℝ := r^(p-2)*(1-r)^2

theorem purePlateauShape_hasDerivAt (p : ℕ) (hp : 3 ≤ p) (r : ℝ) :
    HasDerivAt (purePlateauShape p)
      (r^(p-3)*(1-r)*((p : ℝ)-2-(p : ℝ)*r)) r := by
  have hpow : r^(p-2) = r^(p-3)*r := by rw [← pow_succ]; congr 1; omega
  have h := (hasDerivAt_pow (p-2) r).mul
    (((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).pow 2)
  convert h using 1
  · ext s
    rfl
  · dsimp
    rw [show p-2-1 = p-3 by omega, hpow, Nat.cast_sub (by omega : 2 ≤ p)]
    norm_num
    ring

/-- The actual scalar pure-root location places its static overlap inside
the strictly decreasing branch of the plateau shape. -/
theorem staticOverlap_gt_plateau_turning (p : ℕ) (hp : 4 ≤ p) :
    ((p : ℝ)-2)/(p : ℝ) < staticOverlap (zParameter p (by omega)) := by
  have hpR : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have hz := (zParameter_spec p (by omega)).1
  have hzbound := zParameter_gt_twice_shifted p hp
  unfold staticOverlap
  apply (div_lt_div_iff₀ (by linarith : (0 : ℝ) < p) (by linarith : 0 < 1+zParameter p (by omega))).mpr
  nlinarith

theorem purePlateauShape_strictAntiOn (p : ℕ) (hp : 4 ≤ p) :
    StrictAntiOn (purePlateauShape p) (Ioo (staticOverlap (zParameter p (by omega))) 1) := by
  have hq := staticOverlap_mem_Ioo (zParameter_spec p (by omega)).1
  have hturn := staticOverlap_gt_plateau_turning p hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  apply strictAntiOn_of_deriv_neg (convex_Ioo _ _)
  · unfold purePlateauShape
    fun_prop
  · intro r hr
    have hr' : r ∈ Ioo (staticOverlap (zParameter p (by omega))) 1 := by
      simpa only [interior_Ioo] using hr
    have hr0 : 0 < r := hq.1.trans hr'.1
    have hden : 0 < 1-r := sub_pos.mpr hr'.2
    have hcross := (div_lt_iff₀ hpR).mp (hturn.trans hr'.1)
    rw [(purePlateauShape_hasDerivAt p (by omega) r).deriv]
    exact mul_neg_of_pos_of_neg (mul_pos (pow_pos hr0 _) hden) (by linarith)

/-- Genuine uniqueness of the pure positive plateau root on the entire
branch specified in the manuscript. -/
theorem pure_plateau_root_unique (p : ℕ) (hp : 4 ≤ p) {β Q R : ℝ}
    (hQ : Q ∈ Ioo (staticOverlap (zParameter p (by omega))) 1)
    (hR : R ∈ Ioo (staticOverlap (zParameter p (by omega))) 1)
    (hβ : β ≠ 0)
    (hQroot : β^2*(p : ℝ)*(1+zParameter p (by omega))*Q^(p-2)*(1-Q)^2 = 1)
    (hRroot : β^2*(p : ℝ)*(1+zParameter p (by omega))*R^(p-2)*(1-R)^2 = 1) : Q = R := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hz : 1+zParameter p (by omega) ≠ 0 := by
    have h := (zParameter_spec p (by omega)).1
    linarith
  have hc : β^2*(p : ℝ)*(1+zParameter p (by omega)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hβ) hpR) hz
  apply (purePlateauShape_strictAntiOn p hp).injOn hQ hR
  apply mul_left_cancel₀ hc
  change (β^2*(p : ℝ)*(1+zParameter p (by omega)))*purePlateauShape p Q =
    (β^2*(p : ℝ)*(1+zParameter p (by omega)))*purePlateauShape p R
  unfold purePlateauShape
  simpa only [mul_assoc] using hQroot.trans hRroot.symm

/-- The manuscript's pure plateau equation has exactly one solution on
`(q_s,1)`, and that solution is the overlap of the actual canonical law. -/
theorem existsUnique_pure_plateau_root (p : ℕ) (hp : 4 ≤ p) {β : ℝ}
    (hβ : Thresholds.staticThreshold (fun r : ℝ => r^p) < β) :
    ∃! Q : ℝ, Q ∈ Ioo (staticOverlap (zParameter p (by omega))) 1 ∧
      β^2*(p : ℝ)*(1+zParameter p (by omega))*Q^(p-2)*(1-Q)^2 = 1 := by
  obtain ⟨x, hx, Q, hQ, hlaw, hxformula, hroot, hcurv, hpositive⟩ :=
    canonical_pure_parameters p (by omega) hβ
  have hβne : β ≠ 0 := by
    intro heq
    rw [heq] at hroot
    norm_num at hroot
  exact ⟨Q, ⟨hQ, hroot⟩, fun R hR =>
    pure_plateau_root_unique p hp hR.1 hQ hβne hR.2 hroot⟩

end

end SlowEquilibration.PureStationarity
