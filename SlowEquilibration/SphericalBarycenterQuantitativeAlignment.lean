module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalBarycenterAlignment
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-! # Genuine dimension-uniform alignment from actual cap denominator bounds -/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace
variable {N : ℕ}

/-- The source alignment error becomes uniformly small at a threshold
depending only on the fixed profile and denominator exponent. -/
theorem alignment_error_eventually (K a q₁ : ℝ) (ha : a < 2*K) (hq₁ : 0 < q₁) :
    ∀ᶠ N : ℕ in atTop, (1+q₁)*Real.exp (-(2*K-a)*(N:ℝ)) ≤ q₁/4 := by
  have ht : Tendsto (fun N : ℕ => (1+q₁)*Real.exp (-(2*K-a)*(N:ℝ))) atTop (𝓝 (0:ℝ)) := by
    have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop.const_mul_atTop (show 0<2*K-a by linarith))
    simpa only [Function.comp_apply, neg_mul, mul_zero] using he.const_mul (1+q₁)
  exact (ht.eventually (gt_mem_nhds (show (0:ℝ)<q₁/4 by positivity))).mono (fun _ h => h.le)

/-- Actual cap-mass pressure input and the true source plateaus force the
literal barycenter's 3q₁/4 alignment. No alignment or analytic premise is
supplied in place of the constructed Gibbs observable. -/
theorem barycenter_alignment_of_cap_mass_lower (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (K q₁ q₂ a : ℝ)
    (hq₁ : 0 < q₁) (hlow : ∀ r ∈ Icc (-1:ℝ) q₁, h r = K)
    (hhigh : ∀ r ∈ Icc q₂ 1, h r = 0) (x : Vector N) (hx : OnSphere x)
    (hcap : Real.exp (-a*(N:ℝ)) ≤ (gibbsLaw N β H).real (cap x q₂))
    (hsmall : (1+q₁)*Real.exp (-(2*K-a)*(N:ℝ)) ≤ q₁/4) :
    3*q₁/4 ≤ inner ℝ (spin x) (barycenter β H h x) := by
  have hd : Real.exp (-a*(N:ℝ)) ≤ denominator β H h x :=
    hcap.trans (denominator_cap_lower hN β hH hh q₂ hhigh x hx)
  have hp := denominator_pos hN β hH hh x
  have he := barycenter_alignment_lower hN β hH hh K q₁ (by linarith) hlow x hx
  have hr : (1+q₁)*Real.exp (-2*K*(N:ℝ))/denominator β H h x ≤
      (1+q₁)*Real.exp (-(2*K-a)*(N:ℝ)) := by
    have hi := div_le_div_of_nonneg_left
      (mul_nonneg (by linarith : (0:ℝ) ≤ 1+q₁) (Real.exp_pos (-2*K*(N:ℝ))).le)
      (Real.exp_pos (-a*(N:ℝ))) hd
    have hratio : (1+q₁)*Real.exp (-2*K*(N:ℝ))/Real.exp (-a*(N:ℝ)) =
        (1+q₁)*Real.exp (-(2*K-a)*(N:ℝ)) := by
      rw [mul_div_assoc, ← Real.exp_sub]
      congr 2
      ring
    exact hi.trans_eq hratio
  linarith

end
end SlowEquilibration.SphericalBarycenter
