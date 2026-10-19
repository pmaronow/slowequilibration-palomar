-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGuerraBound

@[expose] public section

namespace SlowEquilibration.SphericalModel

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal RealInnerProductSpace

set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- The literal linear spherical log partition. -/
def linearSphereLogPartition (N : ℕ) (κ : ℝ) (g : Vector N) : ℝ :=
  Real.log (partition N 1 (fun x => Real.sqrt κ*inner ℝ g x))

/-- The fractional Gaussian linear trial. Its zero-mass definition is the
ordinary quenched linear pressure, as in Gaussian logarithmic cascades. -/
def linearSphereOneStepPressure (N : ℕ) (κ a : ℝ) : ℝ :=
  (if a = 0 then ∫ g, linearSphereLogPartition N κ g
      ∂SYK.standardGaussianMeasureOnEuclidean (Fin N)
    else Real.log (∫ g, Real.exp (a*linearSphereLogPartition N κ g)
      ∂SYK.standardGaussianMeasureOnEuclidean (Fin N)) / a) / (N : ℝ)

theorem linearSphereOneStepPressure_zero (N : ℕ) (κ : ℝ) :
    linearSphereOneStepPressure N κ 0 = linearSphereQuenchedPressure N κ := by
  simp [linearSphereOneStepPressure, linearSphereLogPartition, linearSphereQuenchedPressure]

def linearSphereFeature (N : ℕ) (κ : ℝ) (x : Vector N) : Vector N →L[ℝ] ℝ :=
  Real.sqrt κ • innerSL ℝ x

theorem linearSphereFeature_measurable (N : ℕ) (κ : ℝ) : Measurable (linearSphereFeature N κ) :=
  ((innerSL ℝ).continuous.const_smul (Real.sqrt κ)).measurable

theorem linearSphereFeature_bound {N : ℕ} (hN : 1 ≤ N) (κ : ℝ) :
    ∀ᵐ x ∂sphereLaw N, ‖linearSphereFeature N κ x‖ ≤ Real.sqrt κ*Real.sqrt (N : ℝ) := by
  filter_upwards [sphereLaw_support hN] with x hx
  have hxnorm : ‖x‖ = Real.sqrt (N : ℝ) := by rw [← hx, Real.sqrt_sq (norm_nonneg _)]
  simp only [linearSphereFeature, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg κ), innerSL_apply_norm, hxnorm, le_refl]

theorem linearSphereLogPartition_eq_generic (N : ℕ) (κ : ℝ) (g : Vector N) :
    linearSphereLogPartition N κ g =
      GaussianSpinInterpolation.logPartition (sphereLaw N) (linearSphereFeature N κ) g := by
  change Real.log (∫ x, Real.exp (1*(Real.sqrt κ*inner ℝ g x)) ∂sphereLaw N) =
    Real.log (∫ x, GaussianSpinInterpolation.weight (fun _ => 1) (linearSphereFeature N κ) g x ∂sphereLaw N)
  congr 1
  apply integral_congr_ae
  exact .of_forall fun x => by
    simp only [GaussianSpinInterpolation.weight, one_mul, linearSphereFeature,
      smul_apply, smul_eq_mul, innerSL_apply_apply, real_inner_comm]

theorem linearSphereLogPartition_continuous {N : ℕ} (hN : 1 ≤ N) (κ : ℝ) :
    Continuous (linearSphereLogPartition N κ) := by
  have heq := funext (linearSphereLogPartition_eq_generic N κ)
  rw [heq]
  exact (GaussianSpinInterpolation.logPartition_contDiff (sphereLaw N) (linearSphereFeature N κ)
    (linearSphereFeature_measurable N κ) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (linearSphereFeature_bound hN κ)).continuous

theorem abs_linearSphereLogPartition_le {N : ℕ} (hN : 1 ≤ N) (κ : ℝ) (g : Vector N) :
    |linearSphereLogPartition N κ g| ≤ (Real.sqrt κ*Real.sqrt (N : ℝ))*‖g‖ := by
  rw [linearSphereLogPartition_eq_generic]
  exact GaussianSpinInterpolation.abs_logPartition_le (sphereLaw N) (linearSphereFeature N κ)
    (linearSphereFeature_measurable N κ) (linearSphereFeature_bound hN κ) g

/-- Every fractional moment in the actual linear endpoint exists, for every
real exponent, proved from the actual bounded spherical feature. -/
theorem exp_linearSphereLogPartition_integrable {N : ℕ} (hN : 1 ≤ N) (κ a : ℝ) :
    Integrable (fun g => Real.exp (a*linearSphereLogPartition N κ g))
      (SYK.standardGaussianMeasureOnEuclidean (Fin N)) := by
  have hm : AEStronglyMeasurable (fun g => Real.exp (a*linearSphereLogPartition N κ g))
      (SYK.standardGaussianMeasureOnEuclidean (Fin N)) :=
    (Real.continuous_exp.comp ((linearSphereLogPartition_continuous hN κ).const_mul a)).aestronglyMeasurable
  apply (SYK.integrable_exp_mul_norm (ι := Fin N) (|a| *(Real.sqrt κ*Real.sqrt (N : ℝ)))).mono' hm
  exact .of_forall fun g => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ |a*linearSphereLogPartition N κ g| := le_abs_self _
      _ = |a| *|linearSphereLogPartition N κ g| := abs_mul _ _
      _ ≤ |a| *((Real.sqrt κ*Real.sqrt (N : ℝ))*‖g‖) :=
        mul_le_mul_of_nonneg_left (abs_linearSphereLogPartition_le hN κ g) (abs_nonneg _)
      _ = _ := by ring

theorem exp_linearSphereLogPartition_integral_pos {N : ℕ} (hN : 1 ≤ N) (κ a : ℝ) :
    0 < ∫ g, Real.exp (a*linearSphereLogPartition N κ g)
      ∂SYK.standardGaussianMeasureOnEuclidean (Fin N) :=
  integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le)
    (exp_linearSphereLogPartition_integrable hN κ a) |>.mpr (by
      simp [Function.support])

end
end SlowEquilibration.SphericalModel
