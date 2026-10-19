-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.C1SphericalGraph
public import SlowEquilibration.UniformSmoothC2Approximation

@[expose] public section

namespace SlowEquilibration.SphericalForm

open Filter Metric Set
open SphericalModel SphericalAging.HardSphereDynamics
open scoped Topology ContDiff

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A genuine compact C² cutoff agrees with the original function as a
germ at every point of the actual physical sphere. The bump is one on an
open ball containing that sphere. -/
theorem exists_C2_cutoff_agree_near_sphere {N : ℕ}
    (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) :
    ∃ g : Vector N → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      ∀ x, OnSphere x → g =ᶠ[𝓝 x] f := by
  let r : ℝ := (N : ℝ)+1
  have hr : 0 < r := by dsimp only [r]; positivity
  let φ : ContDiffBump (0 : Vector N) := ⟨r, r+1, hr, by linarith⟩
  let g : Vector N → ℝ := fun x => φ x*f x
  refine ⟨g, φ.contDiff.mul hf, φ.hasCompactSupport.mul_right, ?_⟩
  intro x hx
  have hxsq : ‖x‖^2 = (N : ℝ) := (onSphere_iff_norm_sq x).mp hx
  have hxnorm : ‖x‖ < r := by
    dsimp only [r]
    nlinarith [norm_nonneg x, Nat.cast_nonneg (α := ℝ) N]
  have hxball : x ∈ ball (0 : Vector N) φ.rIn := by
    simpa only [mem_ball, dist_zero_right] using hxnorm
  have hφ := φ.eventuallyEq_one_of_mem_ball hxball
  exact hφ.mono (fun y hy => by dsimp only [g]; rw [hy]; simp only [Pi.one_apply, one_mul])

/-- Compact C² cutoff preserving actual values and the actual first and
second Frechet derivatives on every point of the physical sphere. Derivative
agreement follows from genuine neighborhood equality, not from a specified
jet or a derivative identity supplied as an assumption. -/
theorem exists_C2_cutoff {N : ℕ} (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) :
    ∃ g : Vector N → ℝ, ContDiff ℝ 2 g ∧ HasCompactSupport g ∧
      ∀ x, OnSphere x → g x = f x ∧ fderiv ℝ g x = fderiv ℝ f x ∧
        fderiv ℝ (fderiv ℝ g) x = fderiv ℝ (fderiv ℝ f) x := by
  obtain ⟨g, hg, hcg, hnear⟩ := exists_C2_cutoff_agree_near_sphere f hf
  refine ⟨g, hg, hcg, ?_⟩
  intro x hx
  have he := hnear x hx
  have hd : fderiv ℝ g =ᶠ[𝓝 x] fderiv ℝ f := he.fderiv
  exact ⟨he.eq_of_nhds, he.fderiv_eq, hd.fderiv_eq⟩

end
end SlowEquilibration.SphericalForm
