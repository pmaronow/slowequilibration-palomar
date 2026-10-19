-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiGroundRSUpper

@[expose] public section

/-! A sharp genuine ground upper admitting a random constant block.
Direct increment comparison removes the unnecessary pointwise variance
restriction of an adjoined-zero comparison. This applies to the literal
source tau_r auxiliary model, including all its degree-zero/one terms. -/

namespace SlowEquilibration.SphericalParisiGroundConstantAllowance

noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum GaussianCompactMaximum
open GaussianCompactFeatureComparison SphericalParisiGroundRSUpper
open PureTensorJetFeatures PureTensorJetBounds
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- Every actual finite ordered-tensor Gaussian field, including a genuine
constant block, satisfies the sharp constant-profile expected ground bound.
The random constant contributes zero to the expectation, through true
Gaussian increment comparison rather than a substituted covariance. -/
theorem actual_expected_maximum_le_all_degrees {N : ℕ} (hN : 0 < N)
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) :
    (∫ g,actualMaximum (N := N) d c g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤
      (N : ℝ)*Real.sqrt (∑ i,(d i : ℝ)*c i) := by
  let : NeZero N := ⟨hN.ne'⟩
  let s : ℝ := ∑ i,(d i : ℝ)*c i
  let L : ℝ := Real.sqrt (N : ℝ)*Real.sqrt s
  let a : UnitSphere N → EuclideanSpace ℝ (Coordinate N d) := fun x => feature d c x.val
  let b : UnitSphere N → Vector N := fun x => L • x.val
  have hs : 0 ≤ s := Finset.sum_nonneg (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hc i))
  have hL : 0 ≤ L := by dsimp [L];positivity
  have ha : Continuous a := (feature_continuous d c).comp continuous_subtype_val
  have hb : Continuous b := continuous_subtype_val.const_smul L
  have hh := expected_supremum_comparison_of_increment_norm a b ha hb (fun x y => by
    rw [show b x-b y=L • (x.val-y.val) by dsimp [b];rw [smul_sub],
      norm_smul,Real.norm_eq_abs,abs_of_nonneg hL]
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hL (norm_nonneg _))).mp
    dsimp [a,L]
    rw [mul_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg N),Real.sq_sqrt hs]
    exact feature_increment_sq_le d c hc x y)
  have hi : Integrable (fun g : Vector N => ⨆ x : UnitSphere N,inner ℝ (b x) g)
      (SYK.standardGaussianMeasureOnEuclidean (Fin N)) :=
    supremum_integrable_of_continuous (fun x => innerSL ℝ (b x))
      ((innerSL ℝ).continuous.comp hb)
  have henv (g : Vector N) : (⨆ x : UnitSphere N,inner ℝ (b x) g) ≤ L*‖g‖ := by
    apply ciSup_le
    intro x
    exact (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans (by
      simp only [b,norm_smul,Real.norm_eq_abs,abs_of_nonneg hL,unit_norm,mul_one]
      exact le_rfl))
  have hg := integral_mono hi (GaussianSpinInterpolation.gaussian_norm_integrable.const_mul L) henv
  rw [integral_const_mul] at hg
  have hroot := mul_le_mul_of_nonneg_left
    (GaussianNormMean.standardGaussian_integral_norm_le_sqrt_card (Fin N)) hL
  change (∫ g,actualMaximum (N := N) d c g
    ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤ _ at hh
  apply ((hh.trans hg).trans hroot).trans_eq
  simp only [Fintype.card_fin]
  dsimp [L]
  calc
    _ = (Real.sqrt (N : ℝ))^2*Real.sqrt s := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

end
end SlowEquilibration.SphericalParisiGroundConstantAllowance
