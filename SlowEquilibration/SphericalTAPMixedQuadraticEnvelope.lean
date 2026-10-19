-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPMixedLineUniformCurvature

@[expose] public section

/-! The one-dimensional strong-concavity calculus used along each physical
mixed line segment. -/

namespace SlowEquilibration.SphericalTAPMixedQuadraticEnvelope
noncomputable section
open Set
open scoped Topology
set_option autoImplicit false

/-- A negative second-derivative margin on `[0,1]` gives the exact Gaussian
quadratic tangent inequality, with the source normalization `c/2`. -/
theorem quadratic_upper_of_second_derivative
    {f : ℝ → ℝ} {c : ℝ}
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ f t)
    (hf' : ∀ t ∈ Icc (0 : ℝ) 1, DifferentiableAt ℝ (deriv f) t)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) 1, deriv (deriv f) t ≤ -c) :
    f 1 ≤ f 0+deriv f 0-c/2 := by
  let F : ℝ → ℝ := fun t => -f t-c*t^2/2
  have hpoly (t : ℝ) : HasDerivAt (fun s : ℝ => c*s^2/2) (c*t) t := by
    convert (((hasDerivAt_id t).pow 2).const_mul c).div_const 2 using 1
    · funext s
      simp [id_eq]
    · simp [id_eq]
      ring
  have hFderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      deriv F t = -deriv f t-c*t := by
    have hh := ((hf t ht).hasDerivAt.neg.sub (hpoly t))
    change HasDerivAt F (-deriv f t-c*t) t at hh
    exact hh.deriv
  have hFdiff (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      DifferentiableAt ℝ F t := by
    have hh := ((hf t ht).hasDerivAt.neg.sub (hpoly t))
    change HasDerivAt F (-deriv f t-c*t) t at hh
    exact hh.differentiableAt
  have hFderiv2 (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
      deriv (deriv F) t = -deriv (deriv f) t-c := by
    have hevent : deriv F =ᶠ[𝓝 t] (fun s => -deriv f s-c*s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hFderiv s (Ioo_subset_Icc_self hs)
    rw [hevent.deriv_eq]
    have hpoly' : HasDerivAt (fun s : ℝ => c*s) c t := by
      simpa [id_eq] using (hasDerivAt_id t).const_mul c
    exact (((hf' t (Ioo_subset_Icc_self ht)).hasDerivAt.neg.sub hpoly').deriv)
  have hFcont : ContinuousOn F (Icc (0 : ℝ) 1) :=
    fun t ht => (hFdiff t ht).continuousAt.continuousWithinAt
  have hFd : DifferentiableOn ℝ F (interior (Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    exact fun t ht => (hFdiff t (Ioo_subset_Icc_self ht)).differentiableWithinAt
  have hFdd : DifferentiableOn ℝ (deriv F) (interior (Icc (0 : ℝ) 1)) := by
    rw [interior_Icc]
    intro t ht
    have hevent : deriv F =ᶠ[𝓝 t] (fun s => -deriv f s-c*s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hFderiv s (Ioo_subset_Icc_self hs)
    have hpoly' : DifferentiableAt ℝ (fun s : ℝ => c*s) t := by fun_prop
    have hh : DifferentiableAt ℝ (fun s => -deriv f s-c*s) t :=
      (hf' t (Ioo_subset_Icc_self ht)).neg.sub hpoly'
    exact (hh.congr_of_eventuallyEq hevent).differentiableWithinAt
  have hFconvex : ConvexOn ℝ (Icc (0 : ℝ) 1) F := by
    apply convexOn_of_deriv2_nonneg (convex_Icc 0 1) hFcont hFd hFdd
    intro t ht
    have ht' : t ∈ Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using ht
    simp only [Function.iterate_succ_apply, Function.iterate_zero, id_eq]
    rw [hFderiv2 t ht']
    linarith [hcurv t (Ioo_subset_Icc_self ht')]
  have hFzero : HasDerivAt F (-deriv f 0) 0 := by
    have hh := ((hf 0 ⟨le_refl _,zero_le_one⟩).hasDerivAt.neg.sub (hpoly 0))
    convert hh using 1
    ring
  have hslope := hFconvex.le_slope_of_hasDerivAt
    (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_refl _,zero_le_one⟩)
    (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one,le_refl _⟩)
    zero_lt_one hFzero
  dsimp [F] at hslope
  simp [slope_def_field] at hslope
  linarith

end
end SlowEquilibration.SphericalTAPMixedQuadraticEnvelope
