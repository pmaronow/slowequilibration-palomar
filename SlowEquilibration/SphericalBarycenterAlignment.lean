module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalBarycenterMeans

@[expose] public section

/-! # Actual cap denominator and plateau alignment bounds -/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {N : ℕ}

/-- A zero-weight plateau on the literal high-overlap cap gives the actual
source cap-mass lower bound for d_N. -/
theorem denominator_cap_lower (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (q₂ : ℝ)
    (hzero : ∀ r ∈ Icc q₂ 1, h r = 0) (x : Vector N) (hx : OnSphere x) :
    (gibbsLaw N β H).real (cap x q₂) ≤ denominator β H h x := by
  let := gibbsLaw_probability hN β hH
  have hp : Continuous (fun u : Vector N => (psi h x u)^2) :=
    ((psi_joint_contDiff hh).continuous.comp (continuous_id.prodMk continuous_const)).pow 2
  have hi := integral_mono_ae ((integrable_const (1:ℝ)).indicator (cap_measurable x q₂))
    (integrable_gibbs_of_continuous hN β hH hp) (by
      filter_upwards [gibbsLaw_support hN β H] with u hu
      by_cases hc : u ∈ cap x q₂
      · have hR := overlap_mem_Icc_of_norm_sq hN x u ((onSphere_iff_norm_sq x).mp hx) hu
        have hl : q₂ ≤ overlap x u := by
          change q₂ ≤ inner ℝ u x / (N:ℝ) at hc
          simpa only [overlap, real_inner_comm] using hc
        rw [Set.indicator_of_mem hc, psi_sq, hzero _ ⟨hl,hR.2⟩]
        simp
      · rw [Set.indicator_of_notMem hc]
        exact sq_nonneg _)
  rw [integral_indicator (cap_measurable x q₂), setIntegral_const] at hi
  simp only [smul_eq_mul, mul_one] at hi
  convert! hi using 1

/-- The literal low-overlap plateau yields the manuscript's alignment
bound, including the exact exponential error divided by its actual d_N. -/
theorem barycenter_alignment_lower (hN : 1 ≤ N) (β : ℝ) {H : Vector N → ℝ}
    (hH : Continuous H) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (K q₁ : ℝ)
    (hq₁ : -1 < q₁) (hplateau : ∀ r ∈ Icc (-1:ℝ) q₁, h r = K)
    (x : Vector N) (hx : OnSphere x) :
    q₁-(1+q₁)*Real.exp (-2*K*(N:ℝ))/denominator β H h x ≤
      inner ℝ (spin x) (barycenter β H h x) := by
  let := gibbsLaw_probability hN β hH
  let c : ℝ := (1+q₁)*Real.exp (-2*K*(N:ℝ))
  have hc : 0 ≤ c := mul_nonneg (by linarith) (Real.exp_pos _).le
  have hp : Continuous (fun u : Vector N => (psi h x u)^2) :=
    ((psi_joint_contDiff hh).continuous.comp (continuous_id.prodMk continuous_const)).pow 2
  have hR : Continuous (fun u : Vector N => overlap x u) := by unfold overlap; fun_prop
  have ha : ∀ᵐ u ∂gibbsLaw N β H,
      q₁*(psi h x u)^2-c ≤ (psi h x u)^2*overlap x u := by
    filter_upwards [gibbsLaw_support hN β H] with u hu
    have hRu := overlap_mem_Icc_of_norm_sq hN x u ((onSphere_iff_norm_sq x).mp hx) hu
    by_cases hlo : overlap x u ≤ q₁
    · rw [psi_sq, hplateau _ ⟨hRu.1,hlo⟩]
      have he : Real.exp (-2*(N:ℝ)*K) = Real.exp (-2*K*(N:ℝ)) := by congr 1; ring
      rw [he]
      dsimp [c]
      nlinarith [Real.exp_pos (-2*K*(N:ℝ)), hRu.1]
    · have hm := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge hlo)) (sq_nonneg (psi h x u))
      linarith
  have hi := integral_mono_ae
    ((integrable_gibbs_of_continuous hN β hH hp).const_mul q₁ |>.sub (integrable_const c))
    (integrable_gibbs_of_continuous hN β hH (hp.mul hR)) ha
  simp only [Pi.sub_apply, Pi.mul_apply] at hi
  rw [integral_sub ((integrable_gibbs_of_continuous hN β hH hp).const_mul q₁)
    (integrable_const c), integral_const_mul] at hi
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  change q₁*denominator β H h x-c ≤ ∫ u, (psi h x u)^2*overlap x u ∂gibbsLaw N β H at hi
  rw [barycenter_alignment_eq hN β hH hh x, integral_weightedLaw hN β hH hh x]
  simp only [smul_eq_mul]
  have hd := denominator_pos hN β hH hh x
  have him := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hd.le)
  dsimp [c] at him
  convert him using 1 <;> field_simp <;> ring

end
end SlowEquilibration.SphericalBarycenter
