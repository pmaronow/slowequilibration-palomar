-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiOneStepDualScalar
public import SlowEquilibration.SphericalParisiGroundConstantAllowance
public import SlowEquilibration.GaussianCompactFeatureComparison

@[expose] public section

/-! Exact removal of genuine degree-zero Gaussian tensor blocks in expectation.
The physical field itself is retained: equality of the two expected maxima
is derived from equality of Gaussian increment metrics in both directions.
The literal one-step dual is invariant under this removal. -/

namespace SlowEquilibration.SphericalParisiPositiveDegreeRestriction
noncomputable section
open MeasureTheory Set SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiGroundRSUpper
open GaussianCompactFeatureComparison SphericalParisiOneStepDualScalar
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

abbrev PositiveIndex (d : σ → ℕ) := {i : σ // 0 < d i}
def positiveDegree (d : σ → ℕ) (i : PositiveIndex d) : ℕ := d i.val
def positiveCoefficient (d : σ → ℕ) (c : σ → ℝ) (i : PositiveIndex d) : ℝ := c i.val
def constantCoefficient (d : σ → ℕ) (c : σ → ℝ) : ℝ :=
  ∑ i : {j : σ // ¬0 < d j},c i.val

omit [Fintype σ] [DecidableEq σ] in
theorem positive_degree_ge_one (d : σ → ℕ) (i : PositiveIndex d) :
    1 ≤ positiveDegree d i := i.property

omit [Fintype σ] [DecidableEq σ] in
theorem positive_coefficient_nonnegative (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (i : PositiveIndex d) :
    0 ≤ positiveCoefficient d c i := hc i.val

omit [DecidableEq σ] in
theorem xi_eq_positive_add_constant (d : σ → ℕ) (c : σ → ℝ) (r : ℝ) :
    xi d c r=xi (positiveDegree d) (positiveCoefficient d c) r+constantCoefficient d c := by
  unfold xi positiveDegree positiveCoefficient constantCoefficient
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : σ => 0 < d i)
    (fun i => c i*r^(d i))]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.eq_zero_of_not_pos i.property,pow_zero,mul_one]

omit [DecidableEq σ] in
theorem xi1_eq_positive (d : σ → ℕ) (c : σ → ℝ) (r : ℝ) :
    xi1 d c r=xi1 (positiveDegree d) (positiveCoefficient d c) r := by
  unfold xi1 positiveDegree positiveCoefficient
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : σ => 0 < d i)
    (fun i => c i*(d i : ℝ)*r^(d i-1))]
  have hz : (∑ i : {j : σ // ¬0 < d j},c i.val*(d i.val : ℝ)*r^(d i.val-1))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    simp only [Nat.eq_zero_of_not_pos i.property,Nat.cast_zero,mul_zero,zero_mul]
  rw [hz,add_zero]

omit [DecidableEq σ] in
theorem theta_increment_eq_positive (d : σ → ℕ) (c : σ → ℝ) (r q : ℝ) :
    theta d c r-theta d c q=
      theta (positiveDegree d) (positiveCoefficient d c) r-
        theta (positiveDegree d) (positiveCoefficient d c) q := by
  unfold theta
  rw [xi1_eq_positive d c r,xi1_eq_positive d c q,
    xi_eq_positive_add_constant d c r,xi_eq_positive_add_constant d c q]
  ring

omit [DecidableEq σ] in
theorem oneStepDual_eq_positive (d : σ → ℕ) (c : σ → ℝ) (α q κ : ℝ) :
    oneStepDual d c α q κ=oneStepDual (positiveDegree d) (positiveCoefficient d c) α q κ := by
  unfold oneStepDual
  rw [xi1_eq_positive d c 1,xi1_eq_positive d c q,theta_increment_eq_positive]

theorem actual_increment_norm_eq_positive {N : ℕ} (d : σ → ℕ) (c : σ → ℝ)
    (hc : ∀ i,0 ≤ c i) (x y : UnitSphere N) :
    ‖feature d c x.val-feature d c y.val‖=
      ‖feature (positiveDegree d) (positiveCoefficient d c) x.val-
        feature (positiveDegree d) (positiveCoefficient d c) y.val‖ := by
  have hcpos := positive_coefficient_nonnegative d c hc
  have hfull : ‖feature d c x.val-feature d c y.val‖^2=
      (N : ℝ)*(xi d c 1+xi d c 1-2*xi d c (inner ℝ x.val y.val)) := by
    rw [norm_sub_sq_real,feature_norm_sq d c hc x,feature_norm_sq d c hc y,feature_inner d c hc]
    simp only [xi,one_pow,mul_one]
    ring
  have hpos : ‖feature (positiveDegree d) (positiveCoefficient d c) x.val-
        feature (positiveDegree d) (positiveCoefficient d c) y.val‖^2=
      (N : ℝ)*(xi (positiveDegree d) (positiveCoefficient d c) 1+
        xi (positiveDegree d) (positiveCoefficient d c) 1-
        2*xi (positiveDegree d) (positiveCoefficient d c) (inner ℝ x.val y.val)) := by
    rw [norm_sub_sq_real,feature_norm_sq _ _ hcpos x,feature_norm_sq _ _ hcpos y,
      feature_inner _ _ hcpos]
    simp only [xi,one_pow,mul_one]
    ring
  have heq : ‖feature d c x.val-feature d c y.val‖^2=
      ‖feature (positiveDegree d) (positiveCoefficient d c) x.val-
        feature (positiveDegree d) (positiveCoefficient d c) y.val‖^2 := by
    rw [hfull,hpos,xi_eq_positive_add_constant d c 1,
      xi_eq_positive_add_constant d c (inner ℝ x.val y.val)]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp heq

/-- Equality of the actual Gaussian expected ground energies, including
any genuine degree-zero blocks, rather than a covariance surrogate. -/
theorem actual_expected_maximum_eq_positive {N : ℕ} (hN : 0 < N)
    (d : σ → ℕ) (c : σ → ℝ) (hc : ∀ i,0 ≤ c i) :
    (∫ g,actualMaximum (N := N) d c g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d))=
    (∫ g,actualMaximum (N := N) (positiveDegree d) (positiveCoefficient d c) g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N (positiveDegree d))) := by
  let : NeZero N := ⟨hN.ne'⟩
  let a : UnitSphere N → EuclideanSpace ℝ (Coordinate N d) := fun x => feature d c x.val
  let b : UnitSphere N → EuclideanSpace ℝ (Coordinate N (positiveDegree d)) :=
    fun x => feature (positiveDegree d) (positiveCoefficient d c) x.val
  have ha : Continuous a := (feature_continuous d c).comp continuous_subtype_val
  have hb : Continuous b := (feature_continuous _ _).comp continuous_subtype_val
  have he (x y : UnitSphere N) : ‖a x-a y‖=‖b x-b y‖ :=
    actual_increment_norm_eq_positive d c hc x y
  exact le_antisymm
    (expected_supremum_comparison_of_increment_norm a b ha hb (fun x y => (he x y).le))
    (expected_supremum_comparison_of_increment_norm b a hb ha (fun x y => (he x y).ge))

end
end SlowEquilibration.SphericalParisiPositiveDegreeRestriction
