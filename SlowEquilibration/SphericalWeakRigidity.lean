module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalFormCore
public import Mathlib.Analysis.Calculus.Deriv.Inv

@[expose] public section

/-!
# Genuine distributional rigidity of the completed spherical form

Actual weighted rotation integration by parts extends to the actual graph
completion. A zero-energy graph point therefore annihilates every unweighted
rotation test, using the reciprocal of the actual positive Gibbs density.
-/

namespace SlowEquilibration.SphericalForm
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
open Set MeasureTheory Filter
open SphericalModel SphericalAging.HardSphereDynamics
open SphericalAging.SphericalIntegrationByParts
open scoped InnerProductSpace Topology ContDiff

/-- The exact weighted rotation integration by parts identity on the
actual completed energy graph, proved by genuine smooth-core density. -/
theorem completed_rotation_integration_by_parts {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H g : Vector N → ℝ} (hH : ContDiff ℝ 1 H) (hg : ContDiff ℝ 1 g)
    (ij : Fin N × Fin N) (u : sphericalSobolevGraph hN β H hH.continuous) :
    inner ℝ ((sphericalEnergyGradientMap hN β H hH.continuous u) ij)
      (gibbsToL2 hN β H hH.continuous g hg.continuous) =
    -gradientScale N * inner ℝ (sphericalEnergyL2Map hN β H hH.continuous u)
      (gibbsToL2 hN β H hH.continuous
        (fun x => lieDerivative (coordinateRotation ij.1 ij.2) g x +
          β * g x * lieDerivative (coordinateRotation ij.1 ij.2) H x)
        ((lieDerivative_continuous _ hg).add
          ((continuous_const.mul hg.continuous).mul (lieDerivative_continuous _ hH)))) := by
  let q : Vector N → ℝ := fun x => lieDerivative (coordinateRotation ij.1 ij.2) g x +
      β * g x * lieDerivative (coordinateRotation ij.1 ij.2) H x
  have hq : Continuous q := (lieDerivative_continuous _ hg).add
    ((continuous_const.mul hg.continuous).mul (lieDerivative_continuous _ hH))
  apply (smoothEnergyToGraph_dense hN β H hH.continuous).induction_on
    (p := fun v => inner ℝ ((sphericalEnergyGradientMap hN β H hH.continuous v) ij)
      (gibbsToL2 hN β H hH.continuous g hg.continuous) =
        -gradientScale N * inner ℝ (sphericalEnergyL2Map hN β H hH.continuous v)
          (gibbsToL2 hN β H hH.continuous q hq)) u
  · exact isClosed_eq
      (((PiLp.continuous_apply 2 _ ij).comp
        (sphericalEnergyGradientMap hN β H hH.continuous).continuous).inner continuous_const)
      (continuous_const.mul ((sphericalEnergyL2Map hN β H hH.continuous).continuous.inner continuous_const))
  · intro f
    have hf : ContDiff ℝ 1 (f : Vector N → ℝ) := (smoothCore_contDiff f).of_le (by simp)
    change inner ℝ (gradientScale N • gibbsToL2 hN β H hH.continuous
      (lieDerivative (coordinateRotation ij.1 ij.2) f.val) (lieDerivative_continuous _ hf))
      (gibbsToL2 hN β H hH.continuous g hg.continuous) = _
    rw [real_inner_smul_left, sphericalEnergyL2Map_smooth, gibbsToL2_inner, gibbsToL2_inner]
    have hi := gibbs_lie_integration_by_parts hN β hH hg hf
      (coordinateRotation ij.1 ij.2) (coordinateRotation_skew _ _)
    have he : (∫ x, lieDerivative (coordinateRotation ij.1 ij.2) f.val x * g x
        ∂gibbsLaw N β H) = -(∫ x, f.val x * q x ∂gibbsLaw N β H) := by
      convert hi using 1
      congr 1
      funext x
      exact mul_comm _ _
    rw [he]
    ring

/-- Zero actual completed energy means zero actual completed gradient. -/
theorem completed_energy_zero_iff_gradient_zero {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (u : sphericalSobolevGraph hN β H hH) :
    sphericalCompletedDirichlet hN β H hH u u = 0 ↔
      sphericalEnergyGradientMap hN β H hH u = 0 := by
  rw [sphericalCompletedDirichlet, inner_self_eq_zero]

/-- A true zero-energy graph element annihilates all true weighted
rotation-adjoint tests in actual Gibbs L². -/
theorem zero_energy_annihilates_weighted_rotation {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H g : Vector N → ℝ} (hH : ContDiff ℝ 1 H) (hg : ContDiff ℝ 1 g)
    (ij : Fin N × Fin N) (u : sphericalSobolevGraph hN β H hH.continuous)
    (hE : sphericalCompletedDirichlet hN β H hH.continuous u u = 0) :
    inner ℝ (sphericalEnergyL2Map hN β H hH.continuous u)
      (gibbsToL2 hN β H hH.continuous
        (fun x => lieDerivative (coordinateRotation ij.1 ij.2) g x +
          β * g x * lieDerivative (coordinateRotation ij.1 ij.2) H x)
        ((lieDerivative_continuous _ hg).add
          ((continuous_const.mul hg.continuous).mul (lieDerivative_continuous _ hH)))) = 0 := by
  have hi := completed_rotation_integration_by_parts hN β hH hg ij u
  have hz := (completed_energy_zero_iff_gradient_zero hN β H hH.continuous u).mp hE
  rw [hz] at hi
  simp only [PiLp.zero_apply, inner_zero_left] at hi
  exact (mul_eq_zero.mp hi.symm).resolve_left (neg_ne_zero.mpr (gradientScale_pos hN).ne')

lemma lieDerivative_inv {N : ℕ} (A : Operator N) {g : Vector N → ℝ}
    (hg : ContDiff ℝ 1 g) (x : Vector N) (hx : g x ≠ 0) :
    lieDerivative A (fun y => (g y)⁻¹) x = -(g x ^ 2)⁻¹ * lieDerivative A g x := by
  have hi := (hasDerivAt_inv hx).comp_hasFDerivAt x
    (hg.differentiable (by norm_num) x).hasFDerivAt
  dsimp only [Function.comp_def] at hi
  unfold lieDerivative
  rw [hi.fderiv]
  simp only [smul_apply, smul_eq_mul]

/-- The actual reciprocal Gibbs density cancels the actual Gibbs drift in
all distributional rotation tests. -/
theorem reciprocal_density_rotation_identity {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H p : Vector N → ℝ} (hH : ContDiff ℝ 1 H) (hp : ContDiff ℝ 1 p)
    (A : Operator N) (x : Vector N) :
    lieDerivative A (fun y => (gibbsDensity N β H y)⁻¹ * p y) x +
      β * ((gibbsDensity N β H x)⁻¹ * p x) * lieDerivative A H x =
        (gibbsDensity N β H x)⁻¹ * lieDerivative A p x := by
  have hρ := gibbsDensity_contDiff β hH
  have hn : gibbsDensity N β H x ≠ 0 := (gibbsDensity_pos hN β hH.continuous x).ne'
  have hi : ContDiff ℝ 1 (fun y => (gibbsDensity N β H y)⁻¹) :=
    hρ.inv (fun y => (gibbsDensity_pos hN β hH.continuous y).ne')
  rw [lieDerivative_mul A hi hp, lieDerivative_inv A hρ x hn,
    lieDerivative_gibbsDensity β hH A x]
  field_simp
  ring

/-- A true zero-energy graph point annihilates unweighted rotation tests
expressed in its actual Gibbs Hilbert space. No zero-mode conclusion is an
input to this theorem. -/
theorem zero_energy_annihilates_unweighted_rotation {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H p : Vector N → ℝ} (hH : ContDiff ℝ 1 H) (hp : ContDiff ℝ 1 p)
    (ij : Fin N × Fin N) (u : sphericalSobolevGraph hN β H hH.continuous)
    (hE : sphericalCompletedDirichlet hN β H hH.continuous u u = 0) :
    inner ℝ (sphericalEnergyL2Map hN β H hH.continuous u)
      (gibbsToL2 hN β H hH.continuous
        (fun x => (gibbsDensity N β H x)⁻¹ * lieDerivative (coordinateRotation ij.1 ij.2) p x)
        (((gibbsDensity_continuous β hH.continuous).inv₀
            (fun x => (gibbsDensity_pos hN β hH.continuous x).ne')).mul
          (lieDerivative_continuous _ hp))) = 0 := by
  have hρ := gibbsDensity_contDiff β hH
  have hi : ContDiff ℝ 1 (fun y => (gibbsDensity N β H y)⁻¹) :=
    hρ.inv (fun y => (gibbsDensity_pos hN β hH.continuous y).ne')
  have hz := zero_energy_annihilates_weighted_rotation hN β hH (hi.mul hp) ij u hE
  have he : (fun x => lieDerivative (coordinateRotation ij.1 ij.2)
        (fun y => (gibbsDensity N β H y)⁻¹ * p y) x +
      β * ((gibbsDensity N β H x)⁻¹ * p x) * lieDerivative (coordinateRotation ij.1 ij.2) H x) =
      (fun x => (gibbsDensity N β H x)⁻¹ * lieDerivative (coordinateRotation ij.1 ij.2) p x) := by
    funext x
    exact reciprocal_density_rotation_identity hN β hH hp _ x
  simpa only [he] using hz

end
end SlowEquilibration.SphericalForm
