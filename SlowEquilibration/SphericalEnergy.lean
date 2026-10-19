module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalForm
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-!
# The actual spherical Gibbs Dirichlet energy

Every integral in this file is against the Gibbs measure constructed from
`SphericalModel.sphereLaw`. The surface gradient is the actual projected
ambient Riesz gradient, independent of the smooth ambient extension.
-/

namespace SlowEquilibration.SphericalForm

noncomputable section
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Filter Set
open SphericalModel
open SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped BigOperators InnerProductSpace Topology

/-- Continuous observables are integrable against the actual Gibbs law. -/
theorem integrable_gibbs_of_continuous {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) {f : Vector N → ℝ}
    (hf : Continuous f) : Integrable f (gibbsLaw N β H) := by
  let := gibbsLaw_probability hN β hH
  have hs : ∀ᵐ x ∂gibbsLaw N β H,
      x ∈ Metric.closedBall (0 : Vector N) (Real.sqrt (N : ℝ)) :=
    (sphereLaw_mem_closedBall hN).filter_mono (gibbsLaw_absolutelyContinuous β H).ae_le
  have hi := hf.continuousOn.integrableOn_compact
    (isCompact_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))) (μ := gibbsLaw N β H)
  simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hs] using hi

theorem surfaceGradient_continuous {N : ℕ} {f : Vector N → ℝ}
    (hf : ContDiff ℝ 1 f) : Continuous (surfaceGradient f) := by
  unfold surfaceGradient gradient
  exact (tangentProjection_continuous N).clm_apply
    ((InnerProductSpace.toDual ℝ (Vector N)).symm.continuous.comp
      (hf.continuous_fderiv (by norm_num)))

/-- The manuscript's actual spherical Dirichlet pairing. -/
def dirichletForm (N : ℕ) (β : ℝ) (H f g : Vector N → ℝ) : ℝ :=
  ∫ x, inner ℝ (surfaceGradient f x) (surfaceGradient g x) ∂gibbsLaw N β H

/-- The manuscript's actual scalar Dirichlet energy. -/
def dirichletEnergy (N : ℕ) (β : ℝ) (H f : Vector N → ℝ) : ℝ :=
  dirichletForm N β H f f

theorem dirichlet_integrand_integrable {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H f g : Vector N → ℝ} (hH : Continuous H)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    Integrable (fun x => inner ℝ (surfaceGradient f x) (surfaceGradient g x))
      (gibbsLaw N β H) :=
  integrable_gibbs_of_continuous hN β hH
    ((surfaceGradient_continuous hf).inner (surfaceGradient_continuous hg))

theorem dirichletForm_symmetric (N : ℕ) (β : ℝ) (H f g : Vector N → ℝ) :
    dirichletForm N β H f g = dirichletForm N β H g f := by
  unfold dirichletForm
  congr 1
  funext x
  exact real_inner_comm _ _

theorem dirichletEnergy_eq_integral_norm_sq (N : ℕ) (β : ℝ) (H f : Vector N → ℝ) :
    dirichletEnergy N β H f =
      ∫ x, ‖surfaceGradient f x‖ ^ 2 ∂gibbsLaw N β H := by
  simp only [dirichletEnergy, dirichletForm, real_inner_self_eq_norm_sq]

theorem dirichletEnergy_nonneg (N : ℕ) (β : ℝ) (H f : Vector N → ℝ) :
    0 ≤ dirichletEnergy N β H f := by
  rw [dirichletEnergy_eq_integral_norm_sq]
  exact integral_nonneg (fun _ => sq_nonneg _)

@[simp] theorem surfaceGradient_const {N : ℕ} (c : ℝ) (x : Vector N) :
    surfaceGradient (fun _ => c) x = 0 := by
  rw [surfaceGradient, gradient_fun_const, map_zero]

@[simp] theorem dirichletForm_const_left (N : ℕ) (β : ℝ) (H g : Vector N → ℝ)
    (c : ℝ) : dirichletForm N β H (fun _ => c) g = 0 := by
  simp [dirichletForm]

@[simp] theorem dirichletForm_const_right (N : ℕ) (β : ℝ) (H f : Vector N → ℝ)
    (c : ℝ) : dirichletForm N β H f (fun _ => c) = 0 := by
  simp [dirichletForm]

/-- The pairing descends to smooth functions on the actual sphere. -/
theorem dirichletForm_eq_of_agree_on_sphere {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H f g f' g' : Vector N → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hf' : Differentiable ℝ f') (hg' : Differentiable ℝ g')
    (hff' : ∀ x, OnSphere x → f x = f' x)
    (hgg' : ∀ x, OnSphere x → g x = g' x) :
    dirichletForm N β H f g = dirichletForm N β H f' g' := by
  apply integral_congr_ae
  filter_upwards [gibbsLaw_support hN β H] with x hx
  have hs : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
  rw [surfaceGradient_eq_of_agree_on_sphere (by omega) f f' x hs (hf x) (hf' x) hff',
    surfaceGradient_eq_of_agree_on_sphere (by omega) g g' x hs (hg x) (hg' x) hgg']

/-- Actual Gibbs density regularity, proved from the exponential formula. -/
theorem gibbsDensity_contDiff {N : ℕ} (β : ℝ) {H : Vector N → ℝ}
    (hH : ContDiff ℝ 1 H) : ContDiff ℝ 1 (gibbsDensity N β H) := by
  exact ((contDiff_const.mul hH).exp).div_const _

/-- The logarithmic derivative of the actual Gibbs density along rotations. -/
theorem lieDerivative_gibbsDensity {N : ℕ} (β : ℝ) {H : Vector N → ℝ}
    (hH : ContDiff ℝ 1 H) (A : Operator N) (x : Vector N) :
    lieDerivative A (gibbsDensity N β H) x =
      β * gibbsDensity N β H x * lieDerivative A H x := by
  have hh := (((hH.differentiable (by norm_num) x).hasFDerivAt.const_mul β).exp).mul_const
    (partition N β H)⁻¹
  unfold lieDerivative gibbsDensity
  simp only [div_eq_mul_inv]
  rw [hh.fderiv]
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

/-- Integration by parts against the actual Gibbs probability law, obtained
from the proved rotation invariance of the radial Gaussian sphere law. -/
theorem gibbs_lie_integration_by_parts {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H f g : Vector N → ℝ} (hH : ContDiff ℝ 1 H)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (A : Operator N) (hA : star A = -A) :
    (∫ x, f x * lieDerivative A g x ∂gibbsLaw N β H) =
      -(∫ x, g x * (lieDerivative A f x + β * f x * lieDerivative A H x)
        ∂gibbsLaw N β H) := by
  let ρ := gibbsDensity N β H
  have hρ : ContDiff ℝ 1 ρ := gibbsDensity_contDiff β hH
  calc
    _ = ∫ x, (ρ x * f x) * lieDerivative A g x ∂sphereLaw N := by
      rw [integral_gibbsLaw hN β hH.continuous]
      congr 1
      funext x
      dsimp [ρ]
      ring
    _ = -(∫ x, g x * lieDerivative A (fun y => ρ y * f y) x ∂sphereLaw N) :=
      sphere_lie_integration_by_parts (by omega) A hA (hρ.mul hf) hg
    _ = -(∫ x, ρ x * (g x * (lieDerivative A f x + β * f x * lieDerivative A H x))
        ∂sphereLaw N) := by
      congr 1
      apply integral_congr_ae
      apply ae_of_all
      intro x
      dsimp only
      rw [lieDerivative_mul A hρ hf]
      dsimp [ρ]
      rw [lieDerivative_gibbsDensity β hH A x]
      ring
    _ = _ := by rw [integral_gibbsLaw hN β hH.continuous]

end
end SlowEquilibration.SphericalForm
