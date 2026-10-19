-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedReplicaPlateau
public import SlowEquilibration.GaussianShell

@[expose] public section

/-! # Actual scalar Gaussian projections and spherical normalization

These finite-volume identities retain the literal radial normalization used
by the original spherical measure.
-/
namespace SlowEquilibration.SphericalModel
noncomputable section
open Set MeasureTheory ProbabilityTheory
open SphericalBarycenter SphericalAging.HardSphereDynamics
open scoped Topology InnerProductSpace NNReal ENNReal
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Every genuine unit Gaussian projection has the literal N(0,1) law. -/
theorem unit_gaussian_projection_hasLaw (e : E) (he : ‖e‖=1) :
    HasLaw (fun g : E => inner ℝ e g) (gaussianReal 0 1) (stdGaussian E) := by
  let A := innerSL ℝ e
  have hG : HasGaussianLaw (fun g : E => inner ℝ e g) (stdGaussian E) := by
    simpa only [A,Function.comp_apply,id_eq,innerSL_apply_apply] using
      (IsGaussian.hasGaussianLaw_id (μ := stdGaussian E)).map_fun A
  refine ⟨A.measurable.aemeasurable,?_⟩
  rw [hG.map_eq_gaussianReal]
  have hm : (∫ g : E,inner ℝ e g ∂stdGaussian E)=0 := integral_strongDual_stdGaussian A
  have hv : Var[fun g : E => inner ℝ e g;stdGaussian E]=1 := by
    change Var[A;stdGaussian E]=1
    rw [variance_dual_stdGaussian,innerSL_apply_norm,he,one_pow]
  rw [hm,hv,Real.toNNReal_one]

lemma stdGaussian_real_eq : stdGaussian ℝ=gaussianReal 0 1 := by
  have h := (unit_gaussian_projection_hasLaw (1:ℝ) (by norm_num)).map_eq
  simp only [RCLike.inner_apply,conj_trivial,mul_one] at h
  change Measure.map id (stdGaussian ℝ)=gaussianReal 0 1 at h
  simpa only [Measure.map_id] using h

/-- The actual physical overlap after normalizing a Gaussian is precisely
its unit-axis projection divided by its actual Euclidean radius. -/
theorem overlap_normalize_eq (N : ℕ) (hN : 1 ≤ N) (x g : Vector N) :
    overlap x (SphericalAging.SphereInitialLaw.normalize N g)=inner ℝ (spin x) g/‖g‖ := by
  by_cases hg : g=0
  · subst g
    simp [SphericalAging.SphereInitialLaw.normalize,overlap]
  have hroot : Real.sqrt (N:ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by exact_mod_cast (show 0<N by omega))).ne'
  have hnorm : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  have hs : (Real.sqrt (N:ℝ))^2=(N:ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
  unfold overlap SphericalAging.SphereInitialLaw.normalize spin
  rw [real_inner_smul_right,real_inner_smul_left]
  field_simp
  rw [hs]
  ring

/-- Exact dimension-independent quadratic exponential integral of a unit
projection, transported from the real standard Gaussian. -/
theorem unit_gaussian_projection_exp_sq (e : E) (he : ‖e‖=1) {t : ℝ} (ht : t<1/2) :
    (∫ g : E,Real.exp (t*(inner ℝ e g)^2) ∂stdGaussian E)=(1-2*t)^(-(1:ℝ)/2) := by
  have hf : AEStronglyMeasurable (fun z : ℝ => Real.exp (t*z^2)) (gaussianReal 0 1) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))).aestronglyMeasurable
  have h := (unit_gaussian_projection_hasLaw e he).integral_comp hf
  simp only [Function.comp_apply] at h
  rw [← stdGaussian_real_eq] at h
  rw [h]
  simpa only [Real.norm_eq_abs,sq_abs,Module.finrank_self,Nat.cast_one,neg_div] using
    GaussianShell.integral_exp_norm_sq (E := ℝ) ht

end
end SlowEquilibration.SphericalModel
